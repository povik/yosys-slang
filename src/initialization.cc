//
// Yosys slang frontend
//
// Copyright 2025 Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
#include "slang/ast/ASTVisitor.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/Type.h"

#include "slang_frontend.h"
#include "variables.h"

namespace slang_frontend {

template <typename Func> void visit_netlist_variables(NetlistContext &netlist, Func &&visit)
{
	netlist.realm.visit(ast::makeVisitor(
			[&](auto &, const ast::VariableSymbol &symbol) {
				if (symbol.getType().isFixedSize() &&
						symbol.lifetime == ast::VariableLifetime::Static) {
					visit(symbol);
				}
			},
			[&](auto &visitor, const ast::InstanceSymbol &symbol) {
				if (netlist.should_dissolve(symbol))
					visitor.visitDefault(symbol);
			},
			[&](auto &, const ast::ProceduralBlockSymbol &) {
				// TODO: check
				/* do not descend into procedural blocks */
			},
			[&](auto &visitor, const ast::GenerateBlockSymbol &symbol) {
				/* stop at uninstantiated generate blocks */
				if (symbol.isUninstantiated)
					return;
				visitor.visitDefault(symbol);
			}));

	for (auto conn : netlist.realm.parentInstance->getPortConnections()) {
		if (conn->port.kind == ast::SymbolKind::InterfacePort &&
				/* modport */ conn->getIfaceConn().second != nullptr) {
			const ast::Symbol &iface_instance = *conn->getIfaceConn().first;
			const ast::ModportSymbol &ref_modport = *conn->getIfaceConn().second;
			iface_instance.visit(ast::makeVisitor(
					[&](auto &visitor, const ast::InstanceArraySymbol &symbol) {
						// Mock instance array symbols made up by slang don't contain
						// the instances as members, but they do contain them as elements
						for (auto &elem : symbol.elements)
							elem->visit(visitor);
					},
					[&](auto &visitor, const ast::ModportSymbol &modport) {
						// To support interface arrays, we need to match all modports
						// with the same name as ref_modport
						if (!modport.name.compare(ref_modport.name)) {
							visitor.visitDefault(modport);
						}
					},
					[&](auto &, const ast::ModportPortSymbol &port) {
						// TODO: graceful handling
						ast_invariant(port, port.internalSymbol);
						if (ast::VariableSymbol::isKind(port.internalSymbol->kind) &&
								port.getType().isFixedSize()) {
							ast_invariant(
									port, port.internalSymbol->as<ast::VariableSymbol>().lifetime ==
												  ast::VariableLifetime::Static);
							visit(port);
						}
					}));
		}
	}
}

void evaluate_decl_initializers(NetlistContext &netlist, ast::EvalContext &eval_context)
{
	visit_netlist_variables(netlist, [&](const ast::ValueSymbol &symbol) {
		const ast::VariableSymbol *variable = nullptr;
		if (ast::VariableSymbol::isKind(symbol.kind)) {
			variable = &symbol.as<ast::VariableSymbol>();
		} else if (ast::ModportPortSymbol::isKind(symbol.kind)) {
			auto &port = symbol.as<ast::ModportPortSymbol>();
			ast_invariant(port, port.internalSymbol != nullptr);
			ast_invariant(port, ast::VariableSymbol::isKind(port.internalSymbol->kind));
			variable = &port.internalSymbol->as<ast::VariableSymbol>();
		} else {
			ast_unreachable(symbol);
		}

		slang::ConstantValue initval = nullptr;
		if (variable->getInitializer()) {
			initval = variable->getInitializer()->eval(eval_context);
		} else {
			for (const ast::ValueSymbol::PortBackref *backref = symbol.getFirstPortBackref();
					backref; backref = backref->getNextBackreference()) {
				if (backref->port->internalSymbol == &symbol &&
						backref->port->direction == ast::ArgumentDirection::Out &&
						backref->port->getInitializer()) {
					initval = backref->port->getInitializer()->eval(eval_context);
				}
			}
		}
		eval_context.createLocal(&symbol, initval);
	});
}

static const RTLIL::Const reverse_data(RTLIL::Const &orig, int width)
{
	std::vector<RTLIL::State> bits;
	log_assert(orig.size() % width == 0);
	bits.reserve(orig.size());
	for (int i = orig.size() - width; i >= 0; i -= width)
		bits.insert(bits.end(), orig.begin() + i, orig.begin() + i + width);
	return bits;
}

void finalize_variable_initialization(NetlistContext &netlist, ast::EvalContext &eval_context)
{
	visit_netlist_variables(netlist, [&](const ast::ValueSymbol &symbol) {
		const ast::VariableSymbol *variable_symbol = nullptr;
		if (ast::VariableSymbol::isKind(symbol.kind)) {
			variable_symbol = &symbol.as<ast::VariableSymbol>();
		} else if (ast::ModportPortSymbol::isKind(symbol.kind)) {
			auto &port = symbol.as<ast::ModportPortSymbol>();
			ast_invariant(port, port.internalSymbol != nullptr);
			ast_invariant(port, ast::VariableSymbol::isKind(port.internalSymbol->kind));
			variable_symbol = &port.internalSymbol->as<ast::VariableSymbol>();
		} else {
			ast_unreachable(symbol);
		}

		auto variable = Variable::from_symbol(&symbol);
		auto storage = eval_context.findLocal(&symbol);
		log_assert(storage);

		auto converted = netlist.convert_const(*storage, symbol.location);
		if (converted) {
			if (netlist.is_inferred_memory(*variable_symbol)) {
				if (!converted->is_fully_undef()) {
					RTLIL::IdString id = netlist.id(*variable_symbol);
					RTLIL::Memory *m = netlist.canvas->memories.at(id);
					RTLIL::Cell *meminit =
							netlist.canvas->addCell(netlist.new_id(), ID($meminit_v2));
					int abits = 32;
					ast_invariant(*variable_symbol, m->width * m->size == converted->size());
					meminit->setParam(ID::MEMID, id.str());
					meminit->setParam(ID::PRIORITY, 0);
					meminit->setParam(ID::ABITS, abits);
					meminit->setParam(ID::WORDS, m->size);
					meminit->setParam(ID::WIDTH, m->width);
					meminit->setPort(ID::ADDR, m->start_offset);
					bool little_endian =
							variable_symbol->getType().getFixedRange().isLittleEndian();
					meminit->setPort(ID::DATA,
							little_endian ? *converted : reverse_data(*converted, m->width));
					meminit->setPort(ID::EN, RTLIL::Const(RTLIL::S1, m->width));
				}
			} else {
				auto signal = netlist.convert_static(variable);
				// lhs/rhs of connections to be created

				RTLIL::SigSpec cl, cr;
				for (int i = 0; i < converted->size(); i++) {
					VariableBit vbit(variable, i);
					bool register_driven = netlist.register_driven_variables.count(vbit);
					bool driven = netlist.driven_variables.count(vbit);
					// register_driven implies driven
					log_assert(!register_driven || driven);
					if (!register_driven) {
						if (!driven) {
							cl.append(signal[i]);
							cr.append((*converted)[i]);
						}
						// If not register driven, the init attribute
						// must be Sx
#if YOSYS_MAJOR == 0 && YOSYS_MINOR < 58
						converted->bits()[i] = RTLIL::Sx;
#else
						converted->set(i, RTLIL::Sx);
#endif
					}
				}

				if (!converted->is_fully_undef()) {
					log_assert(signal.is_wire());
					RTLIL::Wire *wire = signal.chunks().begin()->wire;
					wire->attributes[ID::init] = *converted;
				}

				netlist.connect(cl, cr);
			}
		}
	});
}

}; // namespace slang_frontend

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

void evaluate_decl_initializers(NetlistContext &netlist)
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

		// Use ProceduralContext to get $meminit emission if the target is a memory
		ProceduralContext context(netlist, ProcessTiming::initial);
		RTLIL::SigSpec value;

		const ast::Expression *initializer = nullptr;

		if (symbol.getInitializer()) {
			initializer = symbol.getInitializer();
		} else {
			for (const ast::ValueSymbol::PortBackref *backref = symbol.getFirstPortBackref();
					backref; backref = backref->getNextBackreference()) {
				if (backref->port->internalSymbol == &symbol &&
						backref->port->direction == ast::ArgumentDirection::Out &&
						backref->port->getInitializer()) {
					initializer = backref->port->getInitializer();
					break;
				}
			}
		}

		if (initializer) {
			context.do_simple_assign(symbol.location, context.eval.variable(symbol),
					context.eval(*initializer), true);
		} else if (!symbol.getType().isFourState()) {
			if (auto converted = netlist.convert_const(
						symbol.getType().getDefaultValue(), variable->location)) {
				context.do_simple_assign(
						symbol.location, context.eval.variable(symbol), *converted, true);
			}
		}
	});
}

void finalize_variable_initialization(NetlistContext &netlist)
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
		if (netlist.is_inferred_memory(*variable_symbol)) {
			// Nothing to do
		} else {
			auto signal = netlist.convert_static(variable);
			RTLIL::SigSpec cl, cr; // lhs/rhs of a new connection
			RTLIL::Const attr_value(RTLIL::Sx, signal.size());
			for (int i = 0; i < signal.size(); i++) {
				VariableBit vbit(variable, i);
				bool register_driven = netlist.register_driven_variables.count(vbit);
				bool driven = netlist.driven_variables.count(vbit);
				// register_driven implies driven
				log_assert(!register_driven || driven);
				RTLIL::State state = netlist.initial_state.at(vbit, RTLIL::Sx);
				if (register_driven) {
#if YOSYS_MAJOR == 0 && YOSYS_MINOR < 58
					attr_value.bits()[i] = state;
#else
					attr_value.set(i, state);
#endif
				} else {
					if (!driven) {
						cl.append(signal[i]);
						cr.append(state);
					}
				}
			}

			if (!attr_value.is_fully_undef()) {
				log_assert(signal.is_wire());
				RTLIL::Wire *wire = signal.chunks().begin()->wire;
				wire->attributes[ID::init] = attr_value;
			}
			netlist.connect(cl, cr);
		}
	});
}

}; // namespace slang_frontend

//
// Yosys slang frontend
//
// Copyright Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
// clang-format off
#include "slang/ast/ASTVisitor.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/EvalContext.h"
#include "slang/ast/SemanticFacts.h"
#include "slang/ast/SystemSubroutine.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/diagnostics/CompilationDiags.h"
#include "slang/diagnostics/DiagnosticEngine.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/driver/Driver.h"
#include "slang/syntax/SyntaxPrinter.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/util/Util.h"

#ifndef SLANG_NO_YOSYS
#include "kernel/bitpattern.h"
#include "kernel/celltypes.h"
#include "kernel/fmt.h"
#include "kernel/register.h"
#include "kernel/rtlil.h"
#include "kernel/sigtools.h"
#include "kernel/utils.h"
#endif

#ifndef SLANG_NO_YOSYS
#include "cases.h"
#endif

#include "slang_frontend.h"
#include "diag.h"
#include "async_pattern.h"
#include "variables.h"

namespace slang_frontend {
static ValuePattern svint_to_pattern(
		NetlistContext &netlist,
		const slang::SVInt &svint, bool wildcard_x, bool wildcard_z,
		slang::SourceLocation loc);
}
#include "statements.h"
#ifndef SLANG_NO_YOSYS
#include "version.h"
#endif
#include "backend_builder.h"

using namespace std::string_literals;

namespace slang_frontend {

static ValuePattern svint_to_pattern(
		NetlistContext &netlist,
		const slang::SVInt &svint, bool wildcard_x, bool wildcard_z,
		slang::SourceLocation loc)
{
	ValuePattern pat;
	pat.bits.reserve(svint.getBitWidth());
	for (int i = 0; i < (int) svint.getBitWidth(); i++)
	switch (svint[i].value) {
	case 0: pat.bits.push_back(PatternBit(ir::S0)); break;
	case 1: pat.bits.push_back(PatternBit(ir::S1)); break;
	case slang::logic_t::X_VALUE:
		pat.bits.push_back(wildcard_x ? PatternBit::wildcard() : PatternBit(ir::Sx));
		break;
	case slang::logic_t::Z_VALUE:
		if (!wildcard_z)
			netlist.add_diag(diag::HighImpedanceUnsupported, loc);
		pat.bits.push_back(wildcard_z ? PatternBit::wildcard() : PatternBit(ir::Sx));
		break;
	}
	return pat;
}

void SynthesisSettings::addOptions(slang::CommandLine &cmdLine) {
	cmdLine.add("--dump-ast", dump_ast, "Dump the AST");
	cmdLine.add("--no-proc", no_proc, "Disable lowering of processes");
	cmdLine.add("--keep-hierarchy", keep_hierarchy,
				"Keep hierarchy (experimental; may crash)");
	cmdLine.add("--best-effort-hierarchy", best_effort_hierarchy,
				"Keep hierarchy in a 'best effort' mode");
	cmdLine.add("--ignore-timing", ignore_timing,
				"Ignore delays for synthesis");
	cmdLine.add("--ignore-initial", ignore_initial,
				"Ignore initial blocks for synthesis");
	cmdLine.add("--ignore-assertions", ignore_assertions,
				"Ignore assertions and formal statements in input");
	cmdLine.add("--unroll-limit", unroll_limit_,
				"Set unrolling limit (default: 4000)", "<limit>");
	cmdLine.add("--no-implicit-memories", no_implicit_memories,
				"Disable implicit memory inference. Without this option used, all variables with at least one unpacked dimension "
				"are candidates for memory inference. With this option used, inference will be restricted to those variables annotated "
				"with one of the following memory style attributes: "
				"ram_block, rom_block, ram_style, rom_style, ramstyle, romstyle, syn_ramstyle, syn_romstyle");
	cmdLine.add("--empty-blackboxes", empty_blackboxes,
				"Assume empty modules are blackboxes");
	cmdLine.add("--ast-compilation-only", ast_compilation_only,
				"For developers: stop after the AST is fully compiled");
	cmdLine.add("--no-default-translate-off-format", no_default_translate_off,
				"Do not interpret any comment directives marking disabled input unless specified with '--translate-off-format'");
	cmdLine.add("--allow-dual-edge-ff", allow_dual_edge_ff,
				"Allow synthesis of dual-edge flip-flops (@(edge))");
	cmdLine.add("--no-synthesis-define", no_synthesis_define,
				"Don't add implicit -D SYNTHESIS");
	cmdLine.add("--blackboxed-module",
				[this](std::string_view value) {
					blackboxed_modules.insert(std::string(value));
					return "";
				},
				"Mark the named module for blackboxing. Whenever an instance of the given module is found in the design"
				"hierarchy, its content will not be elaborated and instead the instance will be imported as a black box.");
	cmdLine.addEnum<UdpHandleMode, UdpHandleMode_traits>(
			"--udp-handling", udp_handling, "Set the processing mode for user defined primitives."
			" When set to 'blackboxes' the UDP is treated as a blackboxed instance."
			" When set to 'error', an error is emitted if a UDP is encountered. By default, the frontend emits an error.");

	// Deprecated section
	cmdLine.add("--compat-mode", compat_mode,
				"Deprecated option which is effectively always on. The old help message was "
				"\"Be relaxed about the synthesis semantics of some language constructs\"");
	cmdLine.add("--extern-modules", extern_modules,
				"Deprecated option which is effectively always on. The old help message was "
				"\"Import as an instantiable blackbox any module which was previously "
				"loaded into the current design with a Yosys command; this allows composing "
				"hierarchy of SystemVerilog and non-SystemVerilog modules\"");
}

namespace ast = slang::ast;
namespace parsing = slang::parsing;

};

namespace slang_frontend {

#ifndef SLANG_NO_YOSYS
static const RTLIL::IdString rtlil_id(const std::string_view &view)
{
	return RTLIL::escape_id(std::string(view));
}
#endif

uint64_t bitstream_member_offset(const ast::FieldSymbol &member)
{
	const ast::Symbol &parent = member.getParentScope()->asSymbol();
	ast_invariant(member, ast::Type::isKind(parent.kind));

	uint64_t bit_offset = member.bitOffset;
	
	const ast::Type &symbol = parent.as<ast::Type>();	
	// Slang stores `FieldSymbol::bitOffset` MSB-first inside unpacked structs, while
	// Yosys works with bitstream-serialization order (LSB-first). This helper
	// mirrors Slang's offset so every caller sees the physical bit index actually
	// used when flattening into a bitstream.
	if (symbol.isUnpackedStruct()) {
		const auto &unpacked = symbol.as<ast::UnpackedStructType>();
		ast_invariant(member, unpacked.bitstreamWidth == unpacked.selectableWidth);
		bit_offset = unpacked.bitstreamWidth - member.bitOffset
				 - member.getType().getBitstreamWidth();
	}
	return bit_offset;
}

const std::string module_type_id(const ast::InstanceBodySymbol &sym)
{
	ast_invariant(sym, sym.parentInstance && sym.parentInstance->isModule());
	std::string instance = sym.getHierarchicalPath();
	if (instance == sym.name)
		return std::string(sym.name);
	else
		return std::string(sym.name) + "$" + instance;
}

ir::Const NetlistContext::convert_svint(const slang::SVInt &svint,
										slang::SourceLocation loc)
{
	std::vector<ir::Trit> bits;
	bits.reserve(svint.getBitWidth());
	for (int i = 0; i < (int) svint.getBitWidth(); i++)
	switch (svint[i].value) {
	case 0: bits.push_back(ir::S0); break;
	case 1: bits.push_back(ir::S1); break;
	case slang::logic_t::X_VALUE: bits.push_back(ir::Sx); break;
	case slang::logic_t::Z_VALUE: {
		add_diag(diag::HighImpedanceUnsupported, loc);
		bits.push_back(ir::Sx); break;
	}
	}
	return bits;
}

const std::optional<ir::Const> NetlistContext::convert_const(const slang::ConstantValue &constval,
															 slang::SourceLocation loc)
{
	if (constval.bad()) {
		// no diagnostic in this case as we assume one has been raised upstream
		return {};
	} else if (constval.isReal()) {
		add_diag(diag::UnsupportedBitConversion, loc) << "real"sv;
		return {};
	} else if (constval.isShortReal()) {
		add_diag(diag::UnsupportedBitConversion, loc) << "shortreal"sv;
		return {};
	} else if (constval.isUnbounded()) {
		add_diag(diag::UnsupportedBitConversion, loc) << "unbounded symbol"sv;
		return {};
	} else if (constval.isMap()) {
		add_diag(diag::UnsupportedBitConversion, loc) << "map"sv;
		return {};
	} else if (constval.isQueue()) {
		add_diag(diag::UnsupportedBitConversion, loc) << "queue"sv;
		return {};
	} else if (constval.isUnion()) {
		add_diag(diag::UnsupportedBitConversion, loc) << "union"sv;
		return {};
	}

	if (constval.isInteger()) {
		return convert_svint(constval.integer(), loc);
	} else if (constval.isUnpacked()) {
		std::vector<ir::Trit> bits;
		bits.reserve(constval.getBitstreamWidth());

		auto elems = constval.elements();
		for (auto it = elems.rbegin(); it != elems.rend(); it++) {
			if (auto piece = convert_const(*it, loc)) {
				bits.insert(bits.end(), piece->begin(), piece->end());
			} else {
				return {};
			}
		}

		log_assert(bits.size() == constval.getBitstreamWidth());
		return bits;
	} else if (constval.isString()) {
		ir::Const ret = convert_svint(constval.convertToInt().integer(), loc);
#ifndef SLANG_NO_YOSYS
		ret.raw_rtlil().flags |= RTLIL::CONST_FLAG_STRING;
#endif
		return ret;
	} else if (constval.isNullHandle()) {
		return {};
	}

	log_abort();
}

};

#ifndef SLANG_NO_YOSYS
#include "cases.h"
#endif
#include "memory.h"

namespace slang_frontend {

#ifndef SLANG_NO_YOSYS
static Yosys::pool<VariableBit> detect_possibly_unassigned_subset(Yosys::pool<VariableBit> &signals, Case *rule, int level=0)
{
	Yosys::pool<VariableBit> remaining = signals;
	bool debug = false;

	for (auto &action : rule->actions) {
		if (debug) {
			log_debug("%saction %s<=%s (mask %s)\n", std::string(level, ' ').c_str(),
					  "FIXME" /* log_signal(action.lvalue) */, log_signal(action.unmasked_rvalue), log_signal(action.mask));
		}

		if (action.mask.is_fully_ones())
		for (auto bit : action.lvalue)
			remaining.erase(bit);
	}

	for (auto switch_ : rule->switches) {
		if (debug) {
			log_debug("%sswitch %s\n", std::string(level, ' ').c_str(), log_signal(switch_->signal));
		}

		if (remaining.empty())
			break;

		Yosys::pool<VariableBit> new_remaining;
		Yosys::BitPatternPool pool(switch_->signal);
		for (auto case_ : switch_->cases) {
			if (!switch_->signal.empty() && pool.empty())
				break;

			if (debug) {
				log_debug("%s case ", std::string(level, ' ').c_str());
				for (auto &compare : case_->compare)
					log_debug("%s ", log_signal(lower_pattern(compare)));
				log_debug("\n");
			}

			bool selectable = false;
			if (case_->compare.empty()) {
				// we have reached a default, by now we know this case is full
				selectable = pool.take_all() || switch_->signal.empty();
			} else {
				for (auto &compare : case_->compare) {
					if (!compare.is_fully_concrete()) {
						if (!pool.empty())
							selectable = true;
					} else {
						if (pool.take(lower_pattern(compare)))
							selectable = true;
					}
				}
			}

			if (selectable) {
				for (auto bit : detect_possibly_unassigned_subset(remaining, case_, level + 2))
					new_remaining.insert(bit);
			}
		}

		if (switch_->full_case || pool.empty())
			remaining.swap(new_remaining);
	}

	return remaining;
}

// extract trigger for side-effect cells like $print, $check
void ProcessTiming::extract_trigger(NetlistContext &netlist, Yosys::Cell *cell, ir::Net enable)
{
	auto &params = cell->parameters;

	cell->setPort(ID::EN, {netlist.LogicAnd(background_enable, enable)});

	switch (kind) {
	case Implicit: {
		params[ID::TRG_ENABLE] = false;
		params[ID::TRG_WIDTH] = 0;
		params[ID::TRG_POLARITY] = {};
		cell->setPort(ID::TRG, {});
		break;
	}
	case EdgeTriggered: {
		params[ID::TRG_ENABLE] = true;
		params[ID::TRG_WIDTH] = triggers.size();
		std::vector<RTLIL::State> pol_bits;
		RTLIL::SigSpec trg_signals;
		for (auto trigger : triggers) {
			pol_bits.push_back(trigger.edge_polarity ? RTLIL::S1 : RTLIL::S0);
			trg_signals.append(trigger.signal);
		}
		params[ID::TRG_POLARITY] = RTLIL::Const(pol_bits);
		cell->setPort(ID::TRG, trg_signals);
		break;
	}
	case Initial: {
		params[ID::TRG_ENABLE] = true;
		params[ID::TRG_WIDTH] = 0;
		params[ID::TRG_POLARITY] = {};
		cell->setPort(ID::TRG, {});
		break;
	}
	default:
		log_abort();
	}
}

// For $check, $print cells
void ProceduralContext::set_effects_trigger(RTLIL::Cell *cell)
{
	ir::Net en = case_enable();
	timing.extract_trigger(netlist, cell, en);
}
#endif // SLANG_NO_YOSYS

ir::Net matches_pattern(NetlistContext &netlist, const ValuePattern &pattern, ir::Value &value)
{
	ir::Value sig, filtered_pat;
	sig.reserve(value.width());
	filtered_pat.reserve(value.width());
	for (int i = 0; i < pattern.size(); i++) {
		if (pattern.bits[i].is_wildcard())
			continue;
		sig.append(value[i]);
		filtered_pat.append(pattern.bits[i].net);
	}
	return sig.empty() ? ir::S1 : netlist.Eq(sig, filtered_pat);	
}

// TODO: revisit against the spec
ir::Value inside_comparison(EvalContext &eval, ir::Value left,
								const ast::Expression &expr)
{
	require(expr, !expr.type->isUnpackedArray());

	if (expr.kind == ast::ExpressionKind::ValueRange) {
		const auto& vexpr = expr.as<ast::ValueRangeExpression>();
		require(expr, vexpr.rangeKind == ast::ValueRangeKind::Simple);
		ast_invariant(expr, vexpr.left().type->isMatching(*vexpr.right().type));
		return eval.netlist.LogicAnd(
			eval.netlist.Ge(left, eval(vexpr.left()), vexpr.left().type->isSigned()),
			eval.netlist.Le(left, eval(vexpr.right()), vexpr.right().type->isSigned())
		);
	} else {
		if (expr.type->isIntegral()) {
			auto const_result = expr.eval(eval.const_);
			require(expr, (bool) const_result);
			ast_invariant(expr, const_result.isInteger());
			auto pat = svint_to_pattern(eval.netlist, const_result.integer(), /* match_x= */ true,
								/* match_z= */ true, expr.sourceRange.start());
			log_assert(pat.size() == left.size());
			return matches_pattern(eval.netlist, pat, left);
		} else {
			ir::Value expr_signal = eval(expr);
			ast_invariant(expr, expr_signal.size() == left.size());
			return eval.netlist.Eq(left, expr_signal);
		}
	}
}

bool NetlistContext::is_inferred_memory(const ast::Symbol &symbol)
{
	return detected_memories.count(&symbol);
}

bool NetlistContext::is_inferred_memory(const ast::Expression &expr)
{
	return ast::ValueExpressionBase::isKind(expr.kind) &&
			is_inferred_memory(expr.as<ast::ValueExpressionBase>().symbol);
}

const ast::InstanceBodySymbol &get_instance_body(SynthesisSettings &settings, const ast::InstanceSymbol &instance)
{
	if (!settings.disable_instance_caching && instance.getCanonicalBody())
		return *instance.getCanonicalBody();
	else
		return instance.body;
}

using VariableState = ProceduralContext::VariableState;

void VariableState::set(VariableBits lhs, ir::Value value)
{
	log_assert(lhs.bitwidth() == (uint64_t)value.size());

	for (uint64_t i = 0; i < lhs.bitwidth(); i++) {
		VariableBit bit = lhs[i];
#if 1
		if (visible_assignments.count(bit) && visible_assignments.at(bit) == value[i])
			continue;
#endif
		if (!pending.revert.count(bit) && !pending.revert_erase.count(bit)) {
			if (visible_assignments.count(bit))
				pending.revert[bit] = visible_assignments.at(bit);
			else
				pending.revert_erase.insert(bit);
		}

		visible_assignments[bit] = value[i];
	}
}

ir::Value VariableState::evaluate(NetlistContext &netlist, VariableBits vbits)
{
	ir::Value ret;
	for (auto vbit : vbits) {
		if (vbit.variable.kind == Variable::Dummy) {
			ret.append(ir::Sx);
		} else if (visible_assignments.count(vbit)) {
			ret.append(visible_assignments.at(vbit));
		} else {
			log_assert(vbit.variable.kind == Variable::Static);
			ret.append(netlist.wire(*vbit.variable.get_symbol())[(int)vbit.offset]);
		}
	}
	return ret;
}

ir::Value VariableState::evaluate(NetlistContext &netlist, VariableChunk vchunk)
{
	ir::Value ret;
	for (uint64_t i = 0; i < vchunk.bitwidth(); i++) {
		if (visible_assignments.count(vchunk[i])) {
			ret.append(visible_assignments.at(vchunk[i]));
		} else {
			log_assert(vchunk.variable.kind == Variable::Static);
			ret.append(netlist.wire(*vchunk.variable.get_symbol())[(int)(vchunk.base + i)]);
		}
	}
	return ret;
}

void VariableState::save(Snapshot &snap)
{
	std::swap(pending, snap);
}

std::pair<VariableBits, ir::Value> VariableState::restore(Snapshot &snap)
{
	VariableBits lreverted;
	ir::Value rreverted;

	for (auto pair : pending.revert)
		lreverted.append(pair.first);
	for (auto bit : pending.revert_erase)
		lreverted.append(bit);
	lreverted.sort();

	rreverted.reserve(lreverted.bitwidth());
	for (auto bit : lreverted)
		rreverted.append(visible_assignments.at(bit));

	for (auto pair : pending.revert)
		visible_assignments[pair.first] = pair.second;
	for (auto bit : pending.revert_erase)
		visible_assignments.erase(bit);

	std::swap(snap, pending);
	return {lreverted, rreverted};
}

int EvalContext::find_nest_level(const ast::Scope *scope)
{
	const ast::Scope *upper_scope = scope;

	while (upper_scope && !scope_nest_level.count(upper_scope))
		upper_scope = upper_scope->asSymbol().getParentScope();

	ast_invariant(scope->asSymbol(), upper_scope != nullptr);
	return scope_nest_level.at(upper_scope);
}

Variable EvalContext::variable(const ast::ValueSymbol &symbol)
{
	if (ast::VariableSymbol::isKind(symbol.kind) &&
			symbol.as<ast::VariableSymbol>().lifetime == ast::VariableLifetime::Automatic) {
		return Variable::from_symbol(&symbol, find_nest_level(symbol.getParentScope()));
	} else {
		return Variable::from_symbol(&symbol);
	}
}

template <typename Vector>
Vector extract_struct_field(Vector value, const ast::MemberAccessExpression &expr)
{
	require(expr, expr.member.kind == ast::SymbolKind::Field);
	const auto &member = expr.member.as<ast::FieldSymbol>();
	require(expr, member.randMode == ast::RandMode::None);
	uint64_t bit_offset = bitstream_member_offset(member);
	return value.extract(bit_offset,
		expr.type->getBitstreamWidth());
}

VariableBits EvalContext::lhs(const ast::Expression &expr, bool silent)
{
	ast_invariant(expr, expr.kind != ast::ExpressionKind::Streaming);

	auto analyzed_lvalue = LValue::analyze(*this, expr, silent);
	if (!analyzed_lvalue) {
		// Return dummy, diagnostic has been issued in analyze
		// if `silent` is not true
		return Variable::dummy(expr.type->getBitstreamWidth());
	}

	if (!analyzed_lvalue->is_static()) {
		if (!silent) {
			netlist.add_diag(diag::UnsupportedLhs, expr.sourceRange);
		}
		return Variable::dummy(expr.type->getBitstreamWidth());
	}

	VariableBits ret = analyzed_lvalue->evaluate_vbits();
	log_assert(ret.bitwidth() == expr.type->getBitstreamWidth());
	return ret;
}

void NetlistContext::register_driven(const VariableBits &vbits)
{
	for (auto bit : vbits)
		driven_variables.insert(bit);
}

void NetlistContext::register_driven(const ast::Symbol &symbol)
{
	register_driven(Variable::from_symbol(&symbol.as<ast::ValueSymbol>()));
}

void NetlistContext::add_continuous_driver(VariableBits lhs, ir::Value rhs)
{
	VariableBits cl;
	ir::Value cr;

	for (auto [base, size, chunk] : lhs.chunk_spans()) {
		if (chunk.variable.is_special_net()) {
			for (uint64_t i = 0; i < size; i++) {
				special_net_drivers[chunk[i]].append(rhs[(int)(base + i)]);
			}
		} else {
			cl.append(chunk);
			cr.append(rhs.extract((int)base, (int)size));
		}
	}

	register_driven(cl);
	connect(convert_static(cl), cr);
}

ir::Value EvalContext::connection_lhs(ast::AssignmentExpression const &assign)
{
	ast_invariant(assign, !assign.timingControl);
	const ast::Expression *rsymbol = &assign.right();
	VariableBits vbits = lhs(assign.left());

	if (rsymbol->kind == ast::ExpressionKind::EmptyArgument &&
			!vbits.has_special_nets()) {
		// early path
		netlist.register_driven(vbits);
		return netlist.convert_static(vbits);
	}

	while (rsymbol->kind == ast::ExpressionKind::Conversion)
		rsymbol = &rsymbol->as<ast::ConversionExpression>().operand();
	ast_invariant(assign, rsymbol->kind == ast::ExpressionKind::EmptyArgument);
	ast_invariant(assign, rsymbol->type->isBitstreamType());

	ir::Value link = netlist.add_placeholder_signal(
								rsymbol->type->getBitstreamWidth());
	netlist.add_continuous_driver(vbits,
			apply_nested_conversion(assign.right(), link));
	return link;
}

VariableBits EvalContext::streaming_lhs(ast::StreamingConcatenationExpression const &expr)
{
	require(expr, expr.isFixedSize());
	VariableBits cat;

	for (auto stream : expr.streams()) {
		require(*stream.operand, !stream.withExpr);
		auto& op = *stream.operand;
		VariableBits item;

		if (op.kind == ast::ExpressionKind::Streaming)
			item = streaming_lhs(op.as<ast::StreamingConcatenationExpression>());
		else
			item = lhs(*stream.operand);

		cat = {cat, item};
	}

	require(expr, expr.getSliceSize() <= std::numeric_limits<int>::max());
	int slice = expr.getSliceSize();
	if (slice == 0) {
		return cat;
	} else {
		VariableBits reorder;
		for (uint64_t i = 0; i < cat.bitwidth(); i += slice)
			reorder = {reorder, cat.extract(i, std::min((uint64_t)slice, cat.bitwidth() - i))};
		return reorder;
	}
}

ir::Value EvalContext::streaming(ast::StreamingConcatenationExpression const &expr)
{
	require(expr, expr.isFixedSize());
	ir::Value cat;

	for (auto stream : expr.streams()) {
		require(*stream.operand, !stream.withExpr);
		auto& op = *stream.operand;
		ir::Value item;

		if (op.kind == ast::ExpressionKind::Streaming)
			item = streaming(op.as<ast::StreamingConcatenationExpression>());
		else
			item = (*this)(*stream.operand);

		cat = {cat, item};
	}

	require(expr, expr.getSliceSize() <= std::numeric_limits<int>::max());
	int slice = expr.getSliceSize();
	if (slice == 0) {
		return cat;
	} else {
		ir::Value reorder;
		for (uint64_t i = 0; i < cat.size(); i += slice)
			reorder = ir::Value({reorder, cat.extract(i, std::min<uint64_t>(slice, cat.size() - i))});
		return reorder;
	}
}

ir::Value EvalContext::apply_conversion(const ast::ConversionExpression &conv, ir::Value op)
{
	const ast::Type &from = conv.operand().type->getCanonicalType();
	const ast::Type &to = conv.type->getCanonicalType();

	log_assert(op.size() == (int) from.getBitstreamWidth());

	if (from.isIntegral() && to.isIntegral()) {
		bool sign_extend = (conv.conversionKind == ast::ConversionKind::Propagated)
								? to.isSigned() : from.isSigned();
		op.extend_u0((int) to.getBitWidth(), sign_extend);
		return op;
	} else if (from.isBitstreamType() && to.isBitstreamType()) {
		require(conv, from.getBitstreamWidth() == to.getBitstreamWidth());
		return op;
	} else {
		unimplemented(conv);
	}
}

ir::Value EvalContext::apply_nested_conversion(const ast::Expression &expr, ir::Value op)
{
	if (expr.kind == ast::ExpressionKind::EmptyArgument) {
		return op;
	} else if (expr.kind == ast::ExpressionKind::Conversion) {
		auto &conv = expr.as<ast::ConversionExpression>();
		ir::Value value = apply_nested_conversion(conv.operand(), op);
		return apply_conversion(conv, value);
	} else {
		log_abort();
	}
}

ir::Value handle_past(EvalContext &eval, const ast::CallExpression &call)
{
	NetlistContext &netlist = eval.netlist;
	ProceduralContext *procedural = eval.procedural;

	// $past(expr) - returns the value of expr from the previous clock cycle
	// $past(expr, num_cycles) - returns the value from num_cycles ago
	// Note: Full signature is $past(expr, num_ticks, gating_expr, clocking_event) but we only support first 2 args
	if (call.arguments().size() > 2) {
		netlist.add_diag(diag::PastGatingClockingUnsupported, call.sourceRange);
		return ir::Value(ir::Sx, call.type->getBitstreamWidth());
	}
	if (procedural == nullptr || procedural->timing.kind == ProcessTiming::Implicit || procedural->timing.triggers.size() != 1) {
		netlist.add_diag(diag::SystemFunctionRequireClockedBlock, call.sourceRange) << call.getSubroutineName();
		return ir::Value(ir::Sx, call.type->getBitstreamWidth());
	}

	// Check num_cycles if specified (2nd argument)
	int num_cycles = 1;
	if (call.arguments().size() >= 2) {
		auto cycles_result = call.arguments()[1]->eval(eval.const_);
		ast_invariant(call, cycles_result.isInteger());
		auto cycles_int = cycles_result.integer().as<int>();
		num_cycles = cycles_int.value();
	}

	auto arg = call.arguments()[0];
	ir::Value current_val = eval(*arg);
	int width = current_val.size();

	// Use the first trigger (clock) from the procedural timing
	auto &trigger = procedural->timing.triggers[0];

	// Create a chain of DFFs for num_cycles delay
	ir::Value prev_val = current_val;
	ir::Value past_wire;

	for (int i = 0; i < num_cycles; i++) {
		past_wire = netlist.add_placeholder_signal(width, "$past");
		netlist.add_dff(netlist.backend->new_id("past"),
			trigger.signal,
			prev_val,
			past_wire,
			trigger.edge_polarity);
		prev_val = past_wire;
	}

	return past_wire;
}

#ifndef SLANG_NO_YOSYS
void handle_display(ProceduralContext &context, const ast::CallExpression &call)
{
	NetlistContext &netlist = context.netlist;
	auto cell = netlist.backend->canvas->addCell(netlist.backend->new_id(), ID($print));
	transfer_attrs(context.netlist, call, cell);
	context.set_effects_trigger(cell);
	cell->parameters[ID::PRIORITY] = --context.effects_priority;
	std::vector<Yosys::VerilogFmtArg> fmt_args;
	for (auto arg : call.arguments()) {
		log_assert(arg);
		Yosys::VerilogFmtArg fmt_arg = {};
		// TODO: location info in fmt_arg
		switch (arg->kind) {
		case ast::ExpressionKind::StringLiteral:
			fmt_arg.type = Yosys::VerilogFmtArg::STRING;
			fmt_arg.str = std::string{arg->as<ast::StringLiteral>().getValue()};
			fmt_arg.sig = {};
			break;
		case ast::ExpressionKind::Call:
			if (arg->as<ast::CallExpression>().getSubroutineName() == "$time") {
				fmt_arg.type = Yosys::VerilogFmtArg::TIME;
				break;
			} else if (arg->as<ast::CallExpression>().getSubroutineName() == "$realtime") {
				fmt_arg.type = Yosys::VerilogFmtArg::TIME;
				fmt_arg.realtime = true;
				break;
			} else {
				[[fallthrough]];
			}
		default:
			fmt_arg.type = Yosys::VerilogFmtArg::INTEGER;
			fmt_arg.sig = context.eval(*arg);
			fmt_arg.signed_ = arg->type->isSigned();
			break;
		}
		fmt_args.push_back(fmt_arg);

	}
	Yosys::Fmt fmt = {};
	// TODO: insert the actual module name
	fmt.parse_verilog(fmt_args, /* sformat_like */ false, /* default_base */ 10,
					  std::string{call.getSubroutineName()}, netlist.backend->canvas->name);
	if (call.getSubroutineName() == "$display")
		fmt.append_literal("\n");
	fmt.emit_rtlil(cell);
}
#endif // SLANG_NO_YOSYS

ir::Value EvalContext::operator()(ast::Expression const &expr)
{
	ir::Value ret;
	size_t repl_count;

	AttributeGuard guard(netlist);
	transfer_attrs(netlist, expr, guard);

	// TODO: Interconnect (untyped) is unimplemented, waiting on slang width resolution
	if (expr.type->isUntypedType())
		unimplemented(expr);

	ast_invariant(expr, expr.kind != ast::ExpressionKind::Streaming);
	if (!(expr.type->isFixedSize() || expr.type->isVoid())) {
		auto &diag = netlist.add_diag(diag::FixedSizeRequired, expr.sourceRange);
		diag << expr.type->toString();
		goto error;
	}

	if (/* flag for testing */ !ignore_ast_constants ||
			expr.kind == ast::ExpressionKind::IntegerLiteral ||
			expr.kind == ast::ExpressionKind::RealLiteral ||
			expr.kind == ast::ExpressionKind::UnbasedUnsizedIntegerLiteral ||
			expr.kind == ast::ExpressionKind::NullLiteral ||
			expr.kind == ast::ExpressionKind::StringLiteral) {
		auto const_result = expr.eval(this->const_);
		if (const_result) {
			auto converted = netlist.convert_const(const_result, expr.sourceRange.start());
			if (converted) {
				ret = *converted;
				goto done;
			} else {
				goto error;
			}
		}
	}

	switch (expr.kind) {
	case ast::ExpressionKind::Assignment:
		{
			auto &assign = expr.as<ast::AssignmentExpression>();
			ast_invariant(expr, procedural != nullptr);

			if (assign.timingControl && !netlist.settings.ignore_timing.value_or(false))
				netlist.add_diag(diag::GenericTimingUnsyn, assign.timingControl->sourceRange);

			const ast::Expression *lvalue_save = lvalue;
			lvalue = &assign.left();
			procedural->assign_rvalue(assign, ret = (*this)(assign.right()));

			// TODO: this is a fixup for a specific scenario, we need to
			// check if there isn't some other general handling of return
			// values we should be doing
			if (assign.left().kind == ast::ExpressionKind::Streaming)
				ret = {};

			lvalue = lvalue_save;
			break;
		}
	case ast::ExpressionKind::Inside:
		{
			auto &inside_expr = expr.as<ast::InsideExpression>();
			ir::Value left = (*this)(inside_expr.left());
			ir::Value hits;
			require(inside_expr, inside_expr.left().type->isIntegral());

			for (auto elem : inside_expr.rangeList())
				hits.append(inside_comparison(*this, left, *elem));

			ret = netlist.ReduceBool(hits);
			ret.extend_u0(expr.type->getBitstreamWidth());
			break;
		}
	case ast::ExpressionKind::HierarchicalValue:
		{
			const ast::ValueSymbol &symbol = expr.as<ast::ValueExpressionBase>().symbol;
			if (!netlist.scopes_remap.count(symbol.getParentScope())
					&& !netlist.check_hier_ref(symbol, expr.sourceRange)) {
				goto error;
			}
		}
		[[fallthrough]];
	case ast::ExpressionKind::NamedValue:
		{
			const ast::Symbol &symbol = expr.as<ast::ValueExpressionBase>().symbol;
			if (netlist.is_inferred_memory(symbol)) {
				netlist.add_diag(diag::BadMemoryExpr, expr.sourceRange);
				goto error;
			}

			if (ast::ParameterSymbol::isKind(symbol.kind)) {
				auto &valsym = symbol.as<ast::ValueSymbol>();
				require(valsym, valsym.getInitializer());
				auto exprconst = valsym.getInitializer()->eval(this->const_);
				require(valsym, exprconst.isInteger());
				return netlist.convert_svint(exprconst.integer(), valsym.location);
			}

			if (ast::ModportPortSymbol::isKind(symbol.kind) &&
					!netlist.scopes_remap.count(symbol.getParentScope())) {
				auto &modport_port = symbol.as<ast::ModportPortSymbol>();
				ast_invariant(symbol, modport_port.getConnectionExpr() != nullptr);
				return (*this)(*modport_port.getConnectionExpr());
			}

			ast_invariant(symbol, ast::ValueSymbol::isKind(symbol.kind));
			Variable variable1 = variable(symbol.as<ast::ValueSymbol>());
			log_assert((bool) variable1);
			if (procedural) {
				if (procedural->timing.kind == ProcessTiming::Initial && ast::NetSymbol::isKind(symbol.kind)) {
					netlist.add_diag(diag::ReadingNetStateFromInitialBlockUnsupported, expr.sourceRange);
					ret = ir::Value(ir::Sx, expr.type->getBitstreamWidth());
					break;
				}
				ret = procedural->substitute_rvalue(variable1);
			} else {
				ret = netlist.convert_static(variable1);
			}
		}
		break;
	case ast::ExpressionKind::UnaryOp:
		{
			const ast::UnaryExpression &unop = expr.as<ast::UnaryExpression>();
			ir::Value left = (*this)(unop.operand());

			using UnOp = ast::UnaryOperator;

			if (unop.op == UnOp::Postincrement || unop.op == UnOp::Preincrement) {
				require(expr, procedural != nullptr);
				ir::Value add1 = netlist.Biop(
						ast::BinaryOperator::Add, left, {ir::S0, ir::S1},
						unop.operand().type->isSigned(), unop.operand().type->isSigned(),
						left.size());
				procedural->do_simple_assign(expr.sourceRange.start(),
											 lhs(unop.operand()), add1, true);
				ret = (unop.op == UnOp::Preincrement) ? add1 : left;
				break;
			}

			if (unop.op == UnOp::Postdecrement || unop.op == UnOp::Predecrement) {
				require(expr, procedural != nullptr);
				ir::Value sub1 = netlist.Biop(
						ast::BinaryOperator::Subtract, left, {ir::S0, ir::S1},
						unop.operand().type->isSigned(), unop.operand().type->isSigned(),
						left.size());
				procedural->do_simple_assign(expr.sourceRange.start(),
											 lhs(unop.operand()), sub1, true);
				ret = (unop.op == UnOp::Predecrement) ? sub1 : left;
				break;
			}

			ret = netlist.Unop(unop.op, left, unop.operand().type->isSigned(),
							   expr.type->getBitstreamWidth());
		}
		break;
	case ast::ExpressionKind::BinaryOp:
		{
			const ast::BinaryExpression &biop = expr.as<ast::BinaryExpression>();
			ir::Value left = (*this)(biop.left());

			bool invert;
			switch (biop.op) {
			case ast::BinaryOperator::WildcardEquality:
				invert = false;
				if (0) {
			case ast::BinaryOperator::WildcardInequality:
				invert = true;
				}

				{
					auto const_result = biop.right().eval(this->const_);
					if (!const_result || !const_result.isInteger()) {
						netlist.add_diag(diag::NonconstWildcardEq, expr.sourceRange);
						return ir::Value(ir::Sx, expr.type->getBitstreamWidth());
					}
					auto pat = svint_to_pattern(netlist, const_result.integer(), true,
												true, biop.right().sourceRange.start());
					return netlist.Unop(
						invert ? ast::UnaryOperator::LogicalNot : ast::UnaryOperator::BitwiseOr,
						matches_pattern(netlist, pat, left),
						false, expr.type->getBitstreamWidth()
					);
				}
			default:
				break;
			}

			ir::Value right = (*this)(biop.right());
			bool a_signed = biop.left().type->isSigned();
			bool b_signed = biop.right().type->isSigned();

			// apply signedness fixups for shift operators
			switch (biop.op) {
			case ast::BinaryOperator::LogicalShiftLeft:
			case ast::BinaryOperator::LogicalShiftRight:
				a_signed = false;
				b_signed = false;
				break;

			case ast::BinaryOperator::ArithmeticShiftLeft:
			case ast::BinaryOperator::ArithmeticShiftRight:
				b_signed = false;
				break;
			default:
				break;
			}

			ret = netlist.Biop(
				biop.op, left, right,
				a_signed, b_signed, expr.type->getBitstreamWidth()
			);
		}
		break;
	case ast::ExpressionKind::Conversion:
		{
			const ast::ConversionExpression &conv = expr.as<ast::ConversionExpression>();
			if (conv.operand().kind != ast::ExpressionKind::Streaming) {
				ret = apply_conversion(conv, (*this)(conv.operand()));
			} else {
				const ast::Type &to = conv.type->getCanonicalType();
				ast_invariant(conv, to.isBitstreamType());

				// evaluate the bitstream
				auto &stream_expr = conv.operand().as<ast::StreamingConcatenationExpression>();
				ir::Value stream = streaming(stream_expr);

				// pad to fit target size
				ast_invariant(conv, stream.size() <= (int) expr.type->getBitstreamWidth());
				ret = {stream, ir::Value(ir::S0, expr.type->getBitstreamWidth() - stream.size())};
			}
		}
		break;
	case ast::ExpressionKind::IntegerLiteral:
		{
			const ast::IntegerLiteral &lit = expr.as<ast::IntegerLiteral>();
			ret = netlist.convert_svint(lit.getValue(), expr.sourceRange.start());
		}
		break;
	case ast::ExpressionKind::RangeSelect:
		{
			const ast::RangeSelectExpression &sel = expr.as<ast::RangeSelectExpression>();
			AddressingResolver addr(*this, sel);
			ret = addr.shift_down((*this)(sel.value()), sel.type->getBitstreamWidth());
		}
		break;
	case ast::ExpressionKind::ElementSelect:
		{
			const ast::ElementSelectExpression &elemsel = expr.as<ast::ElementSelectExpression>();

			if (netlist.is_inferred_memory(elemsel.value())) {
#ifdef SLANG_NO_YOSYS
				log_error("Memory read cells not supported without Yosys\n");
#else
				int width = elemsel.type->getBitstreamWidth();
				std::string id = netlist.id(elemsel.value()
										.as<ast::ValueExpressionBase>().symbol);
				RTLIL::Cell *memrd = netlist.backend->canvas->addCell(netlist.backend->new_id(), ID($memrd_v2));
				memrd->setParam(ID::MEMID, id);
				memrd->setParam(ID::CLK_ENABLE, false);
				memrd->setParam(ID::CLK_POLARITY, false);
				memrd->setParam(ID::TRANSPARENCY_MASK, RTLIL::Const(0, 0));
				memrd->setParam(ID::COLLISION_X_MASK, RTLIL::Const(0, 0));
				memrd->setParam(ID::CE_OVER_SRST, false);
				memrd->setParam(ID::ARST_VALUE, RTLIL::Const(RTLIL::Sx, width));
				memrd->setParam(ID::SRST_VALUE, RTLIL::Const(RTLIL::Sx, width));
				memrd->setParam(ID::INIT_VALUE, RTLIL::Const(RTLIL::Sx, width));
				memrd->setPort(ID::CLK, RTLIL::Sx);
				memrd->setPort(ID::EN, RTLIL::S1);
				memrd->setPort(ID::ARST, RTLIL::S0);
				memrd->setPort(ID::SRST, RTLIL::S0);
				// TODO: signedness
				RTLIL::SigSpec addr = (*this)(elemsel.selector());
				memrd->setPort(ID::ADDR, addr);
				memrd->setParam(ID::ABITS, addr.size());
				ret = netlist.add_placeholder_signal(width);
				memrd->setPort(ID::DATA, ret);
				memrd->setParam(ID::WIDTH, width);
				transfer_attrs(netlist, expr, memrd);
#endif
				break;
			}

			AddressingResolver addr(*this, elemsel);
			ret = addr.mux((*this)(elemsel.value()), elemsel.type->getBitstreamWidth());
		}
		break;
	case ast::ExpressionKind::Concatenation:
		{
			const ast::ConcatenationExpression &concat = expr.as<ast::ConcatenationExpression>();
			for (auto op : concat.operands())
				ret = {ret, (*this)(*op)};
		}
		break;
	case ast::ExpressionKind::SimpleAssignmentPattern:
	case ast::ExpressionKind::StructuredAssignmentPattern:
		{
			repl_count = 1;

			if (0) {
	case ast::ExpressionKind::ReplicatedAssignmentPattern:
				repl_count = *expr.as<ast::ReplicatedAssignmentPatternExpression>()
								.count().eval(const_).integer().as<size_t>();
			}

			auto &pattern_expr = static_cast<const ast::AssignmentPatternExpressionBase&>(expr);

			ret = {};
			for (auto elem : pattern_expr.elements())
				ret = {ret, (*this)(*elem)};
			ret = ret.repeat(repl_count);
		}
		break;
	case ast::ExpressionKind::ConditionalOp:
		{
			const auto &ternary = expr.as<ast::ConditionalExpression>();

			require(expr, ternary.conditions.size() == 1);
			require(expr, !ternary.conditions[0].pattern);

			ret = netlist.Mux(
				(*this)(ternary.right()),
				(*this)(ternary.left()),
				netlist.ReduceBool((*this)(*(ternary.conditions[0].expr)))
			);
		}
		break;
	case ast::ExpressionKind::Replication:
		{
			const auto &repl = expr.as<ast::ReplicationExpression>();
			auto count = repl.count().eval(const_);
			ast_invariant(expr, count.isInteger());
			int reps = count.integer().as<int>().value(); // TODO: checking int cast
			ir::Value concat = (*this)(repl.concat());
			for (int i = 0; i < reps; i++)
				ret.append(concat);
		}
		break;
	case ast::ExpressionKind::MemberAccess:
		{
			const auto &acc = expr.as<ast::MemberAccessExpression>();
			ret = extract_struct_field((*this)(acc.value()), acc);
		}
		break;
	case ast::ExpressionKind::Call:
		{
			const auto &call = expr.as<ast::CallExpression>();
			if (false) {
				// placeholder
#ifndef SLANG_NO_YOSYS
			} else if (call.isSystemCall() && (call.getSubroutineName() == "$display"
					|| call.getSubroutineName() == "$write")) {
				require(expr, procedural != nullptr);
				handle_display(*procedural, call);
#endif
			} else if (call.isSystemCall()) {
				auto name = call.getSubroutineName();
				if (name == "$countones") {
					require(expr, call.arguments().size() == 1);
					auto arg = call.arguments()[0];
					auto sig = (*this)(*arg);
					ret = netlist.CountOnes(sig, (int)call.type->getBitstreamWidth());
				} else if (name == "$past") {
					ret = handle_past(*this, call);
				} else if (name == "$signed" || name == "$unsigned") {
					require(expr, call.arguments().size() == 1);
					ret = (*this)(*call.arguments()[0]);
				} else {
					auto &d = netlist.add_diag(diag::UnsupportedSystemTask, expr.sourceRange);
					d << name;
					if (procedural && procedural->timing.kind == ProcessTiming::Initial)
						d.addNote(diag::NoteIgnoreInitial, expr.sourceRange.start());
					goto error;
				}
			} else {
				const auto &subr = *std::get<0>(call.subroutine);
				if (procedural) {
					ret = StatementExecutor(*procedural).handle_call(call);
				} else {
					require(subr, subr.subroutineKind == ast::SubroutineKind::Function);
					ProceduralContext context(netlist, ProcessTiming::implicit);
					StatementExecutor visitor(context);
					visitor.eval.ignore_ast_constants = ignore_ast_constants;
					ret = visitor.handle_call(call);

#ifndef SLANG_MUX_LOWERING
					RTLIL::Process *proc = netlist.backend->canvas->addProcess(netlist.new_id());
					transfer_attrs(netlist, call, proc);
					context.copy_case_tree_into(proc->root_case);
#endif
				}
			}
		}
		break;
	case ast::ExpressionKind::LValueReference:
		ast_invariant(expr, lvalue != nullptr);
		ret = (*this)(*lvalue);
		break;
	default:
		netlist.add_diag(diag::LangFeatureUnsupported, expr.sourceRange);
		goto error;
	}

	if (0) {
error:
	ret = ir::Value(ir::Sx, expr.type->getBitstreamWidth());
	}

done:
	ast_invariant(expr, ret.width() == expr.type->getBitstreamWidth());
	return ret;
}

ir::Value EvalContext::eval_signed(ast::Expression const &expr)
{
	log_assert(expr.type);

	if (expr.type->isNumeric() && !expr.type->isSigned())
		return {ir::S0, (*this)(expr)};
	else
		return (*this)(expr);
}

EvalContext::EvalContext(NetlistContext &netlist)
	: netlist(netlist), procedural(nullptr),
	  const_(ast::ASTContext(netlist.compilation.getRoot(), ast::LookupLocation::max))
{
}

EvalContext::EvalContext(NetlistContext &netlist, ProceduralContext &procedural)
	: netlist(netlist), procedural(&procedural),
	  const_(ast::ASTContext(netlist.compilation.getRoot(), ast::LookupLocation::max))
{
}

struct PopulateNetlist : public TimingPatternInterpretor, public ast::ASTVisitor<PopulateNetlist, ast::VisitFlags::Statements> {
public:
	HierarchyQueue &queue;
	NetlistContext &netlist;
	SynthesisSettings &settings;
	InferredMemoryDetector mem_detect;
	std::vector<NetlistContext> deferred_modules;

	PopulateNetlist(HierarchyQueue &queue, NetlistContext &netlist)
		: TimingPatternInterpretor(netlist.settings, (DiagnosticIssuer&) netlist, netlist.eval),
		  queue(queue), netlist(netlist), settings(netlist.settings),
		  mem_detect(netlist, settings, std::bind(&NetlistContext::should_dissolve, &netlist, std::placeholders::_1, nullptr), netlist.eval) {}

	void handle_comb_like_process(const ast::ProceduralBlockSymbol &symbol, const ast::Statement &body)
	{
#ifndef SLANG_MUX_LOWERING
		RTLIL::Process *proc = netlist.backend->canvas->addProcess(netlist.new_id());
		transfer_attrs(netlist, body, proc);
#endif

		ProceduralContext procedure(netlist, ProcessTiming::implicit);
		body.visit(StatementExecutor(procedure));

		VariableBits all_driven = procedure.all_driven();

#ifdef SLANG_MUX_LOWERING
		// With mux lowering we emit feedback muxes for latches for now
		VariableBits cl;
		ir::Value cr;
		for (auto driven_bit : all_driven) {
			cl.append(driven_bit);
			cr.append(procedure.vstate.visible_assignments.at(driven_bit));
		}
		netlist.add_continuous_driver(cl, cr);
#else
		Yosys::pool<VariableBit> dangling;
		if (symbol.procedureKind != ast::ProceduralBlockKind::AlwaysComb) {
			Yosys::pool<VariableBit> driven_pool = {all_driven.begin(), all_driven.end()};
			dangling =
				detect_possibly_unassigned_subset(driven_pool, procedure.root_case.get());
		}

		// left-hand side and right-hand side of the connections to be made
		ir::Value cr;
		VariableBits cl, latch_driven;

		for (auto driven_bit : all_driven) {
			if (!dangling.count(driven_bit)) {
				// No latch inferred
				cl.append(driven_bit);
				cr.append(procedure.vstate.visible_assignments.at(driven_bit));
			} else {
				latch_driven.append(driven_bit);
			}
		}

		if (symbol.procedureKind == ast::ProceduralBlockKind::AlwaysLatch && !cl.empty()) {
			for (auto chunk : cl.chunks()) {
				auto &diag = netlist.add_diag(diag::LatchNotInferred, symbol.location);
				diag << chunk.text();
			}
		}

		if (!latch_driven.empty()) {
			// map from a driven signal to the corresponding enable/staging signal
			// TODO: SigSig needlessly costly here
			Yosys::dict<VariableBit, RTLIL::SigSig> signaling;
			RTLIL::SigSpec enables, all_staging;

			latch_driven.sort_and_unify();
			for (auto chunk : latch_driven.chunks()) {
				RTLIL::SigSpec en = netlist.add_placeholder_signal(chunk.bitwidth());
				RTLIL::SigSpec staging = netlist.add_placeholder_signal(chunk.bitwidth());

				for (uint64_t i = 0; i < chunk.bitwidth(); i++) {
					RTLIL::Cell *cell = netlist.backend->canvas->addDlatch(netlist.new_id(), en[i],
											staging[i], netlist.convert_static(chunk[i]), true);
					netlist.driven_variables.insert(chunk[i]);
					netlist.register_driven_variables.insert(chunk[i]);
					transfer_attrs(netlist, symbol, cell);
					signaling[chunk[i]] = {en[i], staging[i]};
				}
				enables.append(en);
				all_staging.append(staging);
			}

			procedure.root_case->aux_actions.push_back(
						{enables, RTLIL::SigSpec(RTLIL::S0, enables.size())});
			procedure.root_case->aux_actions.push_back(
						{all_staging, RTLIL::SigSpec(RTLIL::Sx, all_staging.size())});
			procedure.root_case->insert_latch_signaling(netlist, signaling);
		}

		procedure.copy_case_tree_into(proc->root_case);
		netlist.add_continuous_driver(cl, cr);
#endif
	}

	void handle_ff_process(const ast::ProceduralBlockSymbol &symbol,
						   const ast::SignalEventControl &clock,
						   const ast::StatementBlockSymbol *prologue_block,
						   std::vector<const ast::Statement *> prologue_statements,
						   const ast::Statement &sync_body,
						   std::span<AsyncBranch> async)
	{
		log_assert(symbol.getBody().kind == ast::StatementKind::Timed);
		const auto &timed = symbol.getBody().as<ast::TimedStatement>();

#ifndef SLANG_MUX_LOWERING
		RTLIL::Process *proc = netlist.backend->canvas->addProcess(netlist.new_id());
		transfer_attrs(netlist, timed.stmt, proc);
#endif

		ProcessTiming prologue_timing(ProcessTiming::EdgeTriggered);
		{
			prologue_timing.triggers.push_back({netlist.eval(clock.expr).as_net(), clock.edge == ast::EdgeKind::PosEdge, &clock});
			for (auto &abranch : async)	{
				ir::Value sig = netlist.convert_static(abranch.trigger);
				log_assert(sig.size() == 1);
				prologue_timing.triggers.push_back({sig.as_net(), abranch.polarity, nullptr});
			}
		}
		ProceduralContext prologue(netlist, prologue_timing);
		EnterAutomaticScopeGuard prologue_guard(prologue.eval, prologue_block);
		{
			StatementExecutor visitor(prologue);
			for (auto stmt : prologue_statements)
				stmt->visit(visitor);
		}
#ifndef SLANG_MUX_LOWERING
		prologue.copy_case_tree_into(proc->root_case);
#endif

		struct Aload {
			ir::Net trigger;
			bool trigger_polarity;
			VariableState values;
			const ast::Statement *ast_node;
		};
		std::vector<Aload> aloads;
		ir::Value prior_branch_taken;

		for (auto &async_branch : async) {
			ir::Value sig = netlist.convert_static(async_branch.trigger);
			log_assert(sig.size() == 1);

			ProcessTiming branch_timing(ProcessTiming::Implicit);
			ir::Value sig_depol = async_branch.polarity ? sig : netlist.LogicNot(sig);
			branch_timing.background_enable = netlist.LogicAnd(netlist.LogicNot(prior_branch_taken), sig_depol);
			prior_branch_taken.append(sig_depol);

			ProceduralContext branch(netlist, branch_timing);
			EnterAutomaticScopeGuard branch_guard(branch.eval, prologue_block);

			branch.inherit_state(prologue);
			async_branch.body.visit(StatementExecutor(branch));
#ifndef SLANG_MUX_LOWERING
			branch.copy_case_tree_into(proc->root_case);
#endif
			aloads.push_back({
				sig.as_net(), async_branch.polarity, branch.vstate, &async_branch.body
			});
			// TODO: check for non-constant load values and warn about sim/synth mismatch
		}

		if (aloads.size() > 1) {
			netlist.add_diag(diag::AloadOne, timed.timing.sourceRange);
			return;
		}

		{
			ProcessTiming timing(ProcessTiming::EdgeTriggered);
			timing.background_enable = netlist.LogicNot(prior_branch_taken);
			timing.triggers.push_back({netlist.eval(clock.expr).as_net(), clock.edge == ast::EdgeKind::PosEdge, &clock});

			ProceduralContext sync_procedure(netlist, timing);
			EnterAutomaticScopeGuard guard(sync_procedure.eval, prologue_block);
			sync_procedure.inherit_state(prologue);
			sync_body.visit(StatementExecutor(sync_procedure));
#ifndef SLANG_MUX_LOWERING
			sync_procedure.copy_case_tree_into(proc->root_case);
#endif

			// FIXME: ignores variables not driven from the sync procedure
			VariableBits driven = sync_procedure.all_driven();
			for (VariableChunk driven_chunk : driven.chunks()) {
				const ast::Type *type = &driven_chunk.variable.get_symbol()->getType();
				ir::Value assigned = sync_procedure.vstate.evaluate(netlist, driven_chunk);

				AttributeGuard guard(netlist);
				transfer_attrs(netlist, symbol, guard);

				if (aloads.empty()) {
					for (auto [named_chunk, name] : generate_subfield_names(driven_chunk, type)) {
						log_assert(named_chunk.variable.get_symbol() != nullptr);
						auto symbol = named_chunk.variable.get_symbol();
						std::string base_name = "$driver$"s + netlist.unescaped_id(*symbol) + name;

						if (clock.edge == ast::EdgeKind::BothEdges) {
							netlist.add_dual_edge_aldff(base_name,
														timing.triggers[0].signal,
														ir::S0,
														assigned.extract(named_chunk.base - driven_chunk.base, named_chunk.bitwidth()),
														netlist.convert_static(named_chunk),
														ir::Value(ir::Sx, named_chunk.bitwidth()),
														true);
						} else {
							netlist.add_dff(base_name,
											timing.triggers[0].signal,
											assigned.extract((int)(named_chunk.base - driven_chunk.base), (int)named_chunk.bitwidth()),
											netlist.convert_static(named_chunk),
											timing.triggers[0].edge_polarity);
						}
					}
				} else if (aloads.size() == 1) {
					VariableBits aldff_q;
					VariableBits dffe_q; // fallback

					for (uint64_t i = 0; i < driven_chunk.bitwidth(); i++) {
						// Is this variable bit assigned to from the async branch?
						// Depending on this we either use $aldff or $dffe to drive it
						if (aloads[0].values.visible_assignments.count(driven_chunk[i]))
							aldff_q.append(driven_chunk[i]);
						else
							dffe_q.append(driven_chunk[i]);
					}

					if (!aldff_q.empty()) {
						for (auto driven_chunk2 : aldff_q.chunks())
						for (auto [named_chunk, name] : generate_subfield_names(driven_chunk2, type)) {
							log_assert(named_chunk.variable.get_symbol() != nullptr);
							auto symbol = named_chunk.variable.get_symbol();
							std::string base_name = "$driver$"s + netlist.unescaped_id(*symbol) + name;

							if (clock.edge == ast::EdgeKind::BothEdges) {
								netlist.add_dual_edge_aldff(base_name,
															timing.triggers[0].signal,
															aloads[0].trigger,
															assigned.extract((int)(named_chunk.base - driven_chunk.base), (int)named_chunk.bitwidth()),
															netlist.convert_static(named_chunk),
															aloads[0].values.evaluate(netlist, named_chunk),
															aloads[0].trigger_polarity);
							} else {
								netlist.add_aldff(base_name,
												  timing.triggers[0].signal,
												  aloads[0].trigger,
												  assigned.extract((int)(named_chunk.base - driven_chunk.base), (int)named_chunk.bitwidth()),
												  netlist.convert_static(named_chunk),
												  aloads[0].values.evaluate(netlist, named_chunk),
												  timing.triggers[0].edge_polarity,
												  aloads[0].trigger_polarity);
							}
						}
					}

					if (!dffe_q.empty()) {
						for (auto driven_chunk2 : dffe_q.chunks()) {
							auto &diag = netlist.add_diag(diag::MissingAload, aloads[0].ast_node->sourceRange);
							diag << netlist.id(*driven_chunk2.variable.get_symbol()) + driven_chunk2.slice_text();
							diag.addNote(diag::NoteDuplicateEdgeSense, timed.timing.sourceRange);
						}

						for (auto driven_chunk2 : dffe_q.chunks())
						for (auto [named_chunk, name] : generate_subfield_names(driven_chunk2, type)) {
							log_assert(named_chunk.variable.get_symbol() != nullptr);
							auto symbol = named_chunk.variable.get_symbol();
							std::string base_name = "$driver$"s + netlist.unescaped_id(*symbol) + name;

							netlist.add_dffe(base_name,
											 timing.triggers[0].signal,
											 aloads[0].trigger,
											 assigned.extract((int)(named_chunk.base - driven_chunk.base), (int)named_chunk.bitwidth()),
											 netlist.convert_static(named_chunk),
											 timing.triggers[0].edge_polarity,
											 !aloads[0].trigger_polarity);
						}
					}
				} else {
					log_abort();
				}
			}

			for (auto vbit : driven) {
				netlist.driven_variables.insert(vbit);
				netlist.register_driven_variables.insert(vbit);
			}
		}
	}

	void handle_initial_process(const ast::ProceduralBlockSymbol &, const ast::Statement &body) {
		if (settings.ignore_initial.value_or(false))
			return;

		ProceduralContext procedure(netlist, ProcessTiming::initial);
		body.visit(StatementExecutor(procedure));
	}

	void handle(const ast::ProceduralBlockSymbol &symbol)
	{
		interpret(symbol);
	}

	void handle(const ast::NetSymbol &symbol)
	{
		if (symbol.getInitializer())
			netlist.add_continuous_driver(Variable::from_symbol(&symbol),
				netlist.eval(*symbol.getInitializer()));
	}

	void handle(const ast::PortSymbol &symbol)
	{
		if (symbol.getParentScope()->getContainingInstance() != &netlist.realm)
			return;

		if (!symbol.internalSymbol || symbol.internalSymbol->name.compare(symbol.name)) {
			netlist.add_diag(diag::PortCorrespondence, symbol.location);
			return;
		}

#ifdef SLANG_NO_YOSYS
		{
			ir::Value sig = netlist.wire(*symbol.internalSymbol);
			std::string name = netlist.id(*symbol.internalSymbol);
			switch (symbol.direction) {
			case ast::ArgumentDirection::In:
				netlist.register_driven(*symbol.internalSymbol);
				netlist.add_input(name, sig);
				break;
			case ast::ArgumentDirection::InOut:
				netlist.register_driven(*symbol.internalSymbol);
				netlist.add_input(name, sig);
				netlist.add_output(name, sig);
				break;
			case ast::ArgumentDirection::Out:
				netlist.add_output(name, sig);
				break;
			default:
				break;
			}
		}
#else
		RTLIL::Wire *w = netlist.wire(*symbol.internalSymbol).raw().as_wire();
		log_assert(w);
		switch (symbol.direction) {
		case ast::ArgumentDirection::In:
			if (is_special_net(*symbol.internalSymbol)) {
				auto &diag = netlist.add_diag(diag::InputPortCannotBeSpecialNet, symbol.location);
				auto &net = symbol.internalSymbol->as<ast::NetSymbol>();
				diag << net.netType.name;
				return;
			}
			netlist.register_driven(*symbol.internalSymbol);
			w->port_input = true;
			break;
		case ast::ArgumentDirection::InOut:
			if (is_special_net(*symbol.internalSymbol)) {
				auto &diag = netlist.add_diag(diag::InputPortCannotBeSpecialNet, symbol.location);
				auto &net = symbol.internalSymbol->as<ast::NetSymbol>();
				diag << net.netType.name;
				return;
			}
			netlist.register_driven(*symbol.internalSymbol);
			w->port_input = true;
			w->port_output = true;
			break;
		case ast::ArgumentDirection::Out:
			w->port_output = true;
			break;
		case ast::ArgumentDirection::Ref:
			netlist.add_diag(diag::RefUnsupported, symbol.location);
			break;
		}
#endif
	}

	void handle(const ast::MultiPortSymbol &sym)
	{
		if (sym.getParentScope()->getContainingInstance() != &netlist.realm)
			return;

		netlist.add_diag(diag::MultiportUnsupported, sym.location);
	}

	void inline_port_connection(const ast::PortSymbol &port, ir::Value connection, slang::SourceRange range)
	{
		if (port.isNullPort)
			return;

		VariableBits internal_signal;
		if (auto expr = port.getInternalExpr()) {
			internal_signal = netlist.eval.lhs(*expr);
		} else {
			ast_invariant(port, ast::ValueSymbol::isKind(port.internalSymbol->kind));
			internal_signal = Variable::from_symbol(&port.internalSymbol->as<ast::ValueSymbol>());
		}
		ast_invariant(port, internal_signal.bitwidth() == (uint64_t)connection.size());
		ast_invariant(port, port.direction == ast::ArgumentDirection::In);
		netlist.add_continuous_driver(internal_signal, connection);
	}

	void inline_port_connection(const ast::PortSymbol &port, VariableBits connection, slang::SourceRange range)
	{
		if (port.isNullPort)
			return;

		VariableBits internal_signal;
		if (auto expr = port.getInternalExpr()) {
			internal_signal = netlist.eval.lhs(*expr);
		} else {
			ast_invariant(port, ast::ValueSymbol::isKind(port.internalSymbol->kind));
			internal_signal = Variable::from_symbol(&port.internalSymbol->as<ast::ValueSymbol>());
		}
		log_assert(internal_signal.bitwidth() == connection.bitwidth());

		switch (port.direction) {
		case ast::ArgumentDirection::Out:
			netlist.add_continuous_driver(connection, netlist.convert_static(internal_signal));
			break;
		case ast::ArgumentDirection::In:
			netlist.add_continuous_driver(internal_signal, netlist.convert_static(connection));
			break;
		case ast::ArgumentDirection::InOut:
		case ast::ArgumentDirection::Ref:
			ast_unreachable(port);
		}
	}

	void inline_port_connection_driver(const ast::PortSymbol &port, ir::Value connection, slang::SourceRange range)
	{
		if (port.isNullPort)
			return;

		VariableBits internal_signal;
		if (auto expr = port.getInternalExpr()) {
			internal_signal = netlist.eval.lhs(*expr);
		} else {
			ast_invariant(port, ast::ValueSymbol::isKind(port.internalSymbol->kind));
			internal_signal = Variable::from_symbol(&port.internalSymbol->as<ast::ValueSymbol>());
		}
		ast_invariant(port, internal_signal.bitwidth() == (uint64_t)connection.size());
		ast_invariant(port, port.direction == ast::ArgumentDirection::Out);
		netlist.connect(connection, netlist.convert_static(internal_signal));
	}

	void handle(const ast::InstanceSymbol &sym)
	{
		if (sym.getDefinition().definitionKind == ast::DefinitionKind::Program) {
			netlist.add_diag(diag::ProgramUnsupported, sym.location);
			return;
		}

#ifdef SLANG_NO_YOSYS
		if (sym.isModule() && netlist.is_blackbox(sym.body.getDefinition())) {
			std::vector<BackendGraphBuilderBase::PortConnection> ports;

			for (auto *conn : sym.getPortConnections()) {
				if (!conn->getExpression())
					continue;
				auto &expr = *conn->getExpression();

				if (conn->port.kind != ast::SymbolKind::Port)
					continue;

				auto &port = conn->port.as<ast::PortSymbol>();
				BackendGraphBuilderBase::PortConnection::Direction dir;
				ir::Value sig;

				switch (port.direction) {
				case ast::ArgumentDirection::In:
					dir = BackendGraphBuilderBase::PortConnection::kInput;
					sig = netlist.eval(expr);
					break;
				case ast::ArgumentDirection::Out: {
					dir = BackendGraphBuilderBase::PortConnection::kOutput;
					ast_invariant(expr, ast::AssignmentExpression::isKind(expr.kind));
					auto &assign = expr.as<ast::AssignmentExpression>();
					sig = netlist.eval.connection_lhs(assign);
					break;
				}
				case ast::ArgumentDirection::InOut:
					dir = BackendGraphBuilderBase::PortConnection::kInOut;
					sig = netlist.eval(expr);
					break;
				default:
					continue;
				}

				ports.push_back({std::string(port.name), dir, sig});
			}

			netlist.add_instance(std::string(sym.body.name), std::move(ports));
			return;
		}
#else
		// blackboxes get special handling no matter the hierarchy mode
		if (sym.isModule() && netlist.is_blackbox(sym.body.getDefinition())) {
			RTLIL::Cell *cell = netlist.backend->canvas->addCell(netlist.id(sym), RTLIL::escape_id(std::string(sym.body.name)));
			cell->set_string_attribute(ID::hdlname, netlist.hdlname(sym));

			for (auto *conn : sym.getPortConnections()) {
				slang::SourceLocation loc;
				if (auto expr = conn->getExpression())
					loc = expr->sourceRange.start();
				else
					loc = sym.location;

				switch (conn->port.kind) {
				case ast::SymbolKind::MultiPort:
				case ast::SymbolKind::InterfacePort: {
					auto &diag = netlist.add_diag(diag::UnsupportedBlackboxConnection, loc);
					diag << (conn->port.kind == ast::SymbolKind::MultiPort ? "multi"s : "interface"s);
					break;
				}
				case ast::SymbolKind::Port: {
					auto &port = conn->port.as<ast::PortSymbol>();
					if (!conn->getExpression())
						continue;
					auto &expr = *conn->getExpression();
					switch (port.direction) {
					case ast::ArgumentDirection::InOut:
					case ast::ArgumentDirection::Out: {
						ast_invariant(expr, ast::AssignmentExpression::isKind(expr.kind));
						auto &assign = expr.as<ast::AssignmentExpression>();
						cell->setPort(rtlil_id(conn->port.name), netlist.eval.connection_lhs(assign));
						break;
					}
					case ast::ArgumentDirection::In: {
						cell->setPort(rtlil_id(conn->port.name), netlist.eval(expr));
						break;
					}
					case ast::ArgumentDirection::Ref: {
						auto &diag = netlist.add_diag(diag::RefUnsupported, loc);
						diag << port.name;
					}
					}
					break;
				}
				default:
					ast_unreachable(sym);
				}
			}

			sym.body.visit(ast::makeVisitor([&](auto&, const ast::ParameterSymbol &symbol) {
				auto converted = netlist.convert_const(symbol.getValue(), symbol.location);
				if (converted) {
					if (symbol.isImplicitString(slang::SourceRange(sym.location, sym.location))
							&& converted->size() % 8 == 0) {
						converted->raw_rtlil().flags |= RTLIL::CONST_FLAG_STRING;
					}
					cell->setParam(RTLIL::escape_id(std::string(symbol.name)), converted->to_rtlil());
				}
			}, [&](auto&, const ast::TypeParameterSymbol &symbol) {
				netlist.add_diag(diag::BboxTypeParameter, symbol.location);
			}, [&](auto&, const ast::InstanceSymbol&) {
				// no-op
			}));
			transfer_attrs(netlist, sym, cell);
			export_blackbox_to_rtlil(netlist, sym, netlist.backend->canvas->design);
			return;
		}
#endif // SLANG_NO_YOSYS

		if (netlist.should_dissolve(sym)) {
			sym.body.visit(*this);

			for (auto *conn : sym.getPortConnections()) {
				// Empty connections ".foo()" are without effect
				if (!conn->getExpression())
					continue;
				auto &expr = *conn->getExpression();

				switch (conn->port.kind) {
				case ast::SymbolKind::InterfacePort:
				case ast::SymbolKind::ModportPort:
					// Interface port connections are handled by transparent named value
					// lookup through the port
					continue;

				case ast::SymbolKind::MultiPort: {
					auto &multiport = conn->port.as<ast::MultiPortSymbol>();
					switch (multiport.direction) {
					case ast::ArgumentDirection::In: {
						ir::Value connection = netlist.eval(expr);
						int offset = 0;
						for (auto component : multiport.ports) {
							int width = component->getType().getBitstreamWidth();
							inline_port_connection(*component, connection.extract(offset, width), expr.sourceRange);
							offset += width;
						}
						ast_invariant(expr, offset == (int) multiport.getType().getBitstreamWidth());
						break;
					}
					case ast::ArgumentDirection::Out: {
						ast_invariant(expr, expr.kind == ast::ExpressionKind::Assignment);
						auto &assign = expr.as<ast::AssignmentExpression>();

						if (assign.right().kind != ast::ExpressionKind::EmptyArgument) {
							// If for all components in multiport.ports the component direction
							// was out, we could handle this case via connection_lhs with a bit of
							// extra effort. For now we issue a blanket error.
							auto &diag = netlist.add_diag(diag::MultiPortConversion, expr.sourceRange);
							diag << multiport.name;
							break;
						}

						VariableBits connection = netlist.eval.lhs(assign.left());
						ast_invariant(expr, connection.bitwidth() == multiport.getType().getBitstreamWidth());
						int offset = 0;
						for (auto component : multiport.ports) {
							int width = component->getType().getBitstreamWidth();
							inline_port_connection(*component, connection.extract(offset, width), expr.sourceRange);
							offset += width;
						}
						ast_invariant(expr, offset == (int) multiport.getType().getBitstreamWidth());
						break;
					}
					case ast::ArgumentDirection::InOut: {
						auto &diag = netlist.add_diag(diag::InlinedInOutUnsupported, expr.sourceRange);
						diag << multiport.name;
						break;
					}
					case ast::ArgumentDirection::Ref: {
						auto &diag = netlist.add_diag(diag::RefUnsupported, expr.sourceRange);
						diag << multiport.name;
						break;
					}
					}
					break;
				}
				case ast::SymbolKind::Port: {
					auto &port = conn->port.as<ast::PortSymbol>();
					switch (port.direction) {
					case ast::ArgumentDirection::In:
						inline_port_connection(port, netlist.eval(expr), expr.sourceRange);
						break;
					case ast::ArgumentDirection::Out: {
						ast_invariant(expr, ast::AssignmentExpression::isKind(expr.kind));
						auto &assign = expr.as<ast::AssignmentExpression>();
						inline_port_connection_driver(port, netlist.eval.connection_lhs(assign), expr.sourceRange);	
						break;
					}
					case ast::ArgumentDirection::InOut: {
						auto &diag = netlist.add_diag(diag::InlinedInOutUnsupported, expr.sourceRange);
						diag << port.name;
						break;
					}
					case ast::ArgumentDirection::Ref: {
						auto &diag = netlist.add_diag(diag::RefUnsupported, expr.sourceRange);
						diag << port.name;
						break;
					}
					}
					break;
				}
				default:
					ast_unreachable(conn->port);
				}
			}
		} else {
#ifdef SLANG_NO_YOSYS
			log_error("Hierarchical (non-dissolved) module instantiation not supported without Yosys\n");
			(void)sym;
#else
			log_assert(sym.isModule());
			auto ref_body = &get_instance_body(settings, sym);
			ast_invariant(sym, ref_body->parentInstance != nullptr);
			auto [submodule, inserted] = queue.get_or_emplace(ref_body, netlist, *ref_body->parentInstance);

			RTLIL::Cell *cell = netlist.backend->canvas->addCell(netlist.id(sym), RTLIL::escape_id(module_type_id(*ref_body)));
			cell->set_string_attribute(ID::hdlname, netlist.hdlname(sym));
			for (auto *conn : sym.getPortConnections()) {
				slang::SourceLocation loc;
				if (auto expr = conn->getExpression())
					loc = expr->sourceRange.start();
				else
					loc = sym.location;

				switch (conn->port.kind) {
				case ast::SymbolKind::Port: {
					if (!conn->getExpression())
						continue;
					auto &expr = *conn->getExpression();
					ir::Value signal;
					if (expr.kind == ast::ExpressionKind::Assignment) {
						auto &assign = expr.as<ast::AssignmentExpression>();
						signal = netlist.eval.connection_lhs(assign);
					} else {
						signal = netlist.eval(expr);
					}
					cell->setPort(rtlil_id(conn->port.name), signal);
					break;
				}
				case ast::SymbolKind::InterfacePort: {
					if (!conn->getIfaceConn().second) {
						netlist.add_diag(diag::ModportRequired, loc);
						if (inserted) {
							submodule.disabled = true;
						}
						continue;
					}

					const ast::Symbol &iface_instance = *conn->getIfaceConn().first;
					const ast::ModportSymbol &ref_modport = *conn->getIfaceConn().second;
					std::span<const slang::ConstantRange> array_range;

					const ast::Scope *iface_scope;
					switch (iface_instance.kind) {
					case ast::SymbolKind::InstanceArray: {
						iface_scope = static_cast<const ast::Scope *>(
										&iface_instance.as<ast::InstanceArraySymbol>());
						auto range1 = conn->port.as<ast::InterfacePortSymbol>().getDeclaredRange();
						ast_invariant(conn->port, range1.has_value());
						array_range = range1.value();
						break;
					}
					case ast::SymbolKind::Instance:
						iface_scope = static_cast<const ast::Scope *>(
										&iface_instance.as<ast::InstanceSymbol>().body);
						break;
					default:
						log_abort();
						break;
					}

					std::string hierpath_suffix = "";
					int array_level = 0;

					iface_instance.visit(ast::makeVisitor(
						[&](auto &visitor, const ast::InstanceArraySymbol &symbol) {
							// Mock instance array symbols made up by slang don't contain
							// the instances as members, but they do contain them as elements
							std::string save = hierpath_suffix;
							int i = 0;
							for (auto &elem : symbol.elements) {
								auto dim = array_range[array_level];
								int hdl_index = dim.lower() + i;
								i++;
								hierpath_suffix += "[" + std::to_string(hdl_index) + "]";
								array_level++;
								elem->visit(visitor);
								array_level--;
								hierpath_suffix = save;
							}
						},
						[&](auto &visitor, const ast::ModportSymbol &modport) {
							// To support interface arrays, we need to match all modports
							// with the same name as ref_modport
							if (!modport.name.compare(ref_modport.name)) {
								if (inserted) {
									submodule.scopes_remap[&static_cast<const ast::Scope&>(modport)] =
															submodule.id(conn->port) + hierpath_suffix;
								}
								visitor.visitDefault(modport);
							}
						},
						[&](auto&, const ast::ModportPortSymbol &port) {
							ir::Value port_sig;
							if (inserted) {
								port_sig = submodule.add_wire(port);
								RTLIL::Wire *w = port_sig.raw_.as_wire();
								log_assert(w);
								switch (port.direction) {
								case ast::ArgumentDirection::In:
									submodule.register_driven(Variable::from_symbol(&port));
									w->port_input = true;
									break;
								case ast::ArgumentDirection::Out:
									w->port_output = true;
									break;
								case ast::ArgumentDirection::InOut:
									submodule.register_driven(Variable::from_symbol(&port));
									w->port_input = true;
									w->port_output = true;
									break;
								case ast::ArgumentDirection::Ref:
									netlist.add_diag(diag::RefUnsupported, port.location);
									break;
								default:
									log_abort();
								}
							} else {
								port_sig = submodule.wire(port);
							}

							ast_invariant(port, port.internalSymbol);
							const ast::Scope *parent = port.getParentScope();
							ast_invariant(port, parent->asSymbol().kind == ast::SymbolKind::Modport);
							const ast::ModportSymbol &modport = parent->asSymbol().as<ast::ModportSymbol>();

							RTLIL::IdString port_name = port_sig.raw_.as_wire()->name;
							if (netlist.scopes_remap.count(&modport)) {
								cell->setPort(port_name, netlist.wire(port));
							} else {
								cell->setPort(port_name, netlist.wire(*port.internalSymbol));
								if (port.direction == ast::ArgumentDirection::Out || port.direction == ast::ArgumentDirection::InOut)
									netlist.register_driven(*port.internalSymbol);
							}
						}
					));
					break;
				}
				case ast::SymbolKind::MultiPort: {
					netlist.add_diag(diag::MultiportUnsupported, loc);
					break;
				}
				default:
					ast_unreachable(conn->port);
				}
			}
			transfer_attrs(netlist, sym, cell);
#endif // SLANG_NO_YOSYS
		}
	}

	void handle(const ast::ContinuousAssignSymbol &sym)
	{
		if (sym.getDelay() && !settings.ignore_timing.value_or(false))
			netlist.add_diag(diag::GenericTimingUnsyn, sym.getDelay()->sourceRange);

		const ast::AssignmentExpression &expr = sym.getAssignment().as<ast::AssignmentExpression>();
		ast_invariant(expr, !expr.timingControl);

		ir::Value rvalue = netlist.eval(expr.right());

		if (expr.left().kind == ast::ExpressionKind::Streaming) {
			auto& stream_lexpr = expr.left().as<ast::StreamingConcatenationExpression>();
			VariableBits lvalue = netlist.eval.streaming_lhs(stream_lexpr);
			ast_invariant(expr, (uint64_t)rvalue.size() >= lvalue.bitwidth());

			netlist.add_continuous_driver(lvalue, rvalue.extract(0, lvalue.bitwidth()));
			return;
		}

		netlist.add_continuous_driver(netlist.eval.lhs(expr.left()), rvalue);
	}

	void handle(const ast::GenerateBlockSymbol &sym)
	{
		if (sym.isUninstantiated)
			return;
		visitDefault(sym);
	}

	void handle(const ast::GenerateBlockArraySymbol &sym)
	{
		visitDefault(sym);
	}

	void detect_memories(const ast::InstanceBodySymbol &body)
	{
		mem_detect.process(body);
		netlist.detected_memories = mem_detect.memory_candidates;
	}

	void add_internal_wires(const ast::InstanceBodySymbol &body)
	{
		std::unordered_set<const slang::ast::SubroutineSymbol *> visited_subroutines;
		body.visit(ast::makeVisitor([&](auto&, const ast::ValueSymbol &sym) {
			if (!sym.getType().isFixedSize())
				return;

			if (sym.kind != ast::SymbolKind::Variable
					&& sym.kind != ast::SymbolKind::Net
					&& sym.kind != ast::SymbolKind::FormalArgument)
				return;

			if (sym.kind == ast::SymbolKind::Variable
					&& sym.as<ast::VariableSymbol>().lifetime == ast::VariableLifetime::Automatic)
				return;

			if (sym.kind == ast::SymbolKind::Net) {
				auto &net = sym.as<ast::NetSymbol>();
				switch (net.netType.netKind) {
				case ast::NetType::TriAnd:
				case ast::NetType::TriOr:
				case ast::NetType::Tri0:
				case ast::NetType::Tri1:
				case ast::NetType::TriReg:
				case ast::NetType::Supply0:
				case ast::NetType::Supply1:
					{
						auto &diag = netlist.add_diag(diag::NetTypeUnsupported, sym.location);
						diag << net.netType.name;
					}
					break;
				default:
					break;
				}
			}

			std::string kind{ast::toString(sym.kind)};
			log_debug("Adding %s (%s)\n", netlist.id(sym).c_str(), kind.c_str());

			if (netlist.is_inferred_memory(sym)) {
#ifdef SLANG_NO_YOSYS
				log_error("Memory inference not supported without Yosys\n");
#else
				RTLIL::Memory *m = new RTLIL::Memory;
				m->set_string_attribute(ID::hdlname, netlist.hdlname(sym));
				transfer_attrs(netlist, sym, m);
				m->name = netlist.id(sym);
				m->width = sym.getType().getArrayElementType()->getBitstreamWidth();
				auto range = sym.getType().getFixedRange();
				m->start_offset = range.lower();
				m->size = range.width();
				netlist.backend->canvas->memories[m->name] = m;
				netlist.emitted_mems[m->name] = {};

				log_debug("Memory inferred for variable %s (size: %d, width: %d)\n",
						  log_id(m->name), m->size, m->width);
#endif
			} else {
				netlist.add_wire(sym);
			}
		}, [&](auto& visitor, const ast::InstanceSymbol& sym) {
			if (netlist.should_dissolve(sym))
				visitor.visitDefault(sym);
		}, [&](auto& visitor, const ast::CallExpression &call) {
			if (call.isSystemCall())
				return;
			auto* subroutine = std::get<0>(call.subroutine);
			subroutine->visit(visitor);
		}, [&](auto& visitor, const ast::SubroutineSymbol& subroutine) {
			if (visited_subroutines.contains(&subroutine))
				return;

			visited_subroutines.emplace(&subroutine);
			visitor.visitDefault(subroutine);
		}, [&](auto& visitor, const ast::GenerateBlockSymbol& sym) {
			/* stop at uninstantiated generate blocks */
			if (sym.isUninstantiated)
				return;
			visitor.visitDefault(sym);
		}));
	}

	void handle(const ast::InstanceBodySymbol &body)
	{
		if (&body == &netlist.realm) {
			// This is the containing instance body for this netlist;
			// find inferred memories
			detect_memories(body);
			// add all internal wires before we enter the body
			add_internal_wires(body);
			// Evaluate inline initializers on variables
			evaluate_decl_initializers(netlist);
			// Visit the body for the bulk of processing
			visitDefault(body);
			// Now transfer initializers (possibly updated from initial statements)
			// onto the netlist
			finalize_variable_initialization(netlist);
			finalize_special_nets(netlist);
		} else {
			visitDefault(body);
		}
	}

	void handle(const ast::UninstantiatedDefSymbol &sym)
	{
#ifdef SLANG_NO_YOSYS
		(void)sym;
		return;
#else
		if (sym.isChecker()) {
			netlist.add_diag(diag::LangFeatureUnsupported, sym.location);
			return;
		}

		if (!sym.paramExpressions.empty()) {
			netlist.add_diag(diag::NoParamsOnUnkBboxes, sym.location);
			return;
		}

		RTLIL::Cell *cell = netlist.backend->canvas->addCell(netlist.id(sym),
													rtlil_id(sym.definitionName));
		cell->set_string_attribute(ID::hdlname, netlist.hdlname(sym));
		transfer_attrs(netlist, sym, cell);

		auto port_names = sym.getPortNames();
		auto port_conns = sym.getPortConnections();
		ast_invariant(sym, port_names.size() == port_conns.size());
		for (int i = 0; i < (int) port_names.size(); i++) {
			auto &expr = port_conns[i]->as<ast::SimpleAssertionExpr>().expr;
			RTLIL::IdString port_id = port_names[i].empty()
				? Yosys::stringf("$%d", i + 1)
				: RTLIL::escape_id(std::string{port_names[i]});

			VariableBits vbits = netlist.eval.lhs(expr, true);
			if (!vbits.has_dummy_bits()) {
				netlist.register_driven(vbits);
				cell->setPort(port_id, netlist.convert_static(vbits));
			} else {
				if (!port_names[i].empty()) {
					auto &d = netlist.add_diag(diag::GuessingInputPort, expr.sourceRange);
					d << port_names[i] << sym.definitionName;
				}
				cell->setPort(port_id, netlist.eval(expr));
			}
		}
#endif // SLANG_NO_YOSYS
	}

	void handle(const ast::ClockingBlockSymbol& symbol) {
		if (!netlist.settings.ignore_timing.value_or(false))
			netlist.add_diag(diag::GenericTimingUnsyn, symbol.location);
	}

	void handle(const ast::Type&) {}
	void handle(const ast::NetType&) {}
	void handle(const ast::ForwardingTypedefSymbol&) {}
	void handle(const ast::TransparentMemberSymbol&) {}
	void handle(const ast::SubroutineSymbol&) {}
	void handle(const ast::ParameterSymbol&) {}
	void handle(const ast::TypeParameterSymbol&) {}
	void handle(const ast::WildcardImportSymbol&) {}
	void handle(const ast::ExplicitImportSymbol&) {}
	void handle(const ast::GenvarSymbol&) {}
	void handle(const ast::VariableSymbol&) {}
	void handle(const ast::EmptyMemberSymbol&) {}
	void handle(const ast::ModportSymbol&) {}
	void handle(const ast::InterfacePortSymbol&) {}
	void handle(const ast::GenericClassDefSymbol&) {}
	void handle(const ast::LetDeclSymbol&) {}
	void handle(const ast::SpecparamSymbol&) {}
	void handle(const ast::DefParamSymbol&) {}
	void handle(const ast::SpecifyBlockSymbol&) {}

	void handle(const ast::StatementBlockSymbol &sym)
	{
		visitDefault(sym);
	}

	void handle(const ast::InstanceArraySymbol &sym)
	{
		visitDefault(sym);
	}

	void handle(const ast::PrimitiveInstanceSymbol &sym)
	{
#ifdef SLANG_NO_YOSYS
		(void)sym;
		return;
#else
		auto ports = sym.getPortConnections();
		auto type = sym.primitiveType.name;
		auto id = (!sym.name.compare("")) ? netlist.backend->new_id() : netlist.id(sym);
		RTLIL::IdString op;
		bool inv_y = false;
		RTLIL::Cell *cell;
		ast_invariant(sym, ports.front()->kind == ast::ExpressionKind::Assignment);
		auto &assign = ports.front()->as<ast::AssignmentExpression>();
		auto y = netlist.eval.connection_lhs(assign);
		switch (sym.primitiveType.primitiveKind) {
		case ast::PrimitiveSymbol::PrimitiveKind::NInput:
			{
				// and, or, xor, xnor, nand, nor
				if (!type.compare("and")) {
					op = (ports.size() == 3) ? ID($and) : ID($reduce_and);
				} else if (!type.compare("or")) {
					op = (ports.size() == 3) ? ID($or) : ID($reduce_or);
				} else if (!type.compare("nand")) {
					op = (ports.size() == 3) ? ID($and) : ID($reduce_and);
					inv_y = 1;
				} else if (!type.compare("nor")) {
					op = (ports.size() == 3) ? ID($or) : ID($reduce_or);
					inv_y = 1;
				} else if (!type.compare("xor")) {
					op = (ports.size() == 3) ? ID($xor) : ID($reduce_xor);
				} else if (!type.compare("xnor")) {
					op = (ports.size() == 3) ? ID($xnor) : ID($reduce_xnor);
				} else {
					ast_unreachable(sym);
				}
				cell = netlist.backend->canvas->addCell(id, op);
				if (ports.size() == 3) {
					// word-level primitive cell for 2 input ports
					cell->setPort(ID::A, netlist.eval(*ports[1]));
					cell->setPort(ID::B, netlist.eval(*ports[2]));
				} else {
					// reduce_* cell for 3 or more input ports
					RTLIL::SigSpec a;
					for (auto port : ports)
						if (port != ports.front())
							a.append(netlist.eval(*port));
					cell->setPort(ID::A, a);
				}
				cell->setPort(ID::Y, y);
				break;
			}
		case ast::PrimitiveSymbol::PrimitiveKind::NOutput:
			{
				// buf, not
				// Last port is input, all others are outputs
				if (!type.compare("buf")) {
					op = ID($buf);
				} else if (!type.compare("not")) {
					op = ID($not);
				} else {
					ast_unreachable(sym);
				}
				cell = netlist.backend->canvas->addCell(id, op);
				cell->setPort(ID::A, netlist.eval(*(ports.back())));
				cell->setPort(ID::Y, y);
				for (auto port : ports) {
					if (port != ports.front() && port != ports.back()) {
						auto &assign = port->as<ast::AssignmentExpression>();
						netlist.backend->canvas->connect(cell->getPort(ID::Y), netlist.eval.connection_lhs(assign));
					}
				}
				break;
			}
		case ast::PrimitiveSymbol::PrimitiveKind::UserDefined:
			{
				if (settings.udp_handling.has_value() && *settings.udp_handling == UdpHandleMode::blackboxes) {
					RTLIL::Cell *cell = netlist.backend->canvas->addCell(id, RTLIL::escape_id(std::string(sym.primitiveType.name)));
					cell->set_string_attribute(ID::hdlname, netlist.hdlname(sym));
					transfer_attrs(netlist, sym, cell);
					const auto& ports = sym.primitiveType.ports;

					for (int i = 0; i < sym.getPortConnections().size(); ++i) {
						const auto *conn= sym.getPortConnections()[i];
						if (!conn)
							continue;

						const auto& port = ports[i];
						if (port->direction != ast::PrimitivePortDirection::In) {
							auto &assign = conn->as<ast::AssignmentExpression>();
							cell->setPort(RTLIL::escape_id(std::string(port->name)), netlist.eval.connection_lhs(assign));
						} else {
							cell->setPort(RTLIL::escape_id(std::string(port->name)), netlist.eval(*conn));
						}
					}
				} else {
					netlist.add_diag(diag::UdpUnsupported, sym.location);
				}
				return;
			}
		default:
			{
				if (!type.compare("pulldown")) {
					// pulldown is equivalent to: buffer with constant 0 input
					cell = netlist.backend->canvas->addCell(id, ID($buf));
					cell->setPort(ID::A, RTLIL::S0);
					cell->setPort(ID::Y, y);
				} else if (!type.compare("pullup")) {
					// pullup is equivalent to: buffer with constant 1 input
					cell = netlist.backend->canvas->addCell(id, ID($buf));
					cell->setPort(ID::A, RTLIL::S1);
					cell->setPort(ID::Y, y);
				} else if (!type.compare("bufif0") || !type.compare("bufif1") ||
				           !type.compare("notif0") || !type.compare("notif1") ||
					         !type.compare("pmos")   || !type.compare("rpmos")  ||
					         !type.compare("nmos")   || !type.compare("rnmos")) {
					// These are all tri-state buffers, some having inverted enable/output
					// Use $mux instead of $tribuf to avoid Yosys issues...
					bool inv_a = false;
					bool inv_en = false;
					if (!type.compare("notif0")) {
						inv_a = inv_en = true;
					} else if (!type.compare("notif1")) {
						inv_a = true;
					} else if (!type.compare("bufif0")) {
						inv_en = true;
					} else if (!type.compare("pmos")) {
						inv_en = true;
					} else if (!type.compare("rpmos")) {
						inv_en = true;
					}
					auto in = netlist.eval(*ports[1]);
					if (inv_a) {
						auto mid_wire = netlist.add_placeholder_signal(in.size(), id + "_mid", true);
						auto inv_cell = netlist.backend->canvas->addNot(id + "_ainv", in, mid_wire);
						in = mid_wire;
						transfer_attrs(netlist, sym, inv_cell);
					}
					ir::Value a = inv_en ? in : ir::Value(RTLIL::SigSpec(RTLIL::Sz));
					ir::Value b = inv_en ? ir::Value(RTLIL::SigSpec(RTLIL::Sz)) : in;
					auto en = netlist.eval(*ports[2]);
					cell = netlist.backend->canvas->addMux(id, a, b, en, y);
				} else if (!type.compare("cmos") || !type.compare("rcmos")) {
					// cmos (w, datain, ncontrol, pcontrol);
					// is equivalent to:
					// nmos (w, datain, ncontrol); pmos (w, datain, pcontrol);
					// Use $mux instead of $tribuf to avoid Yosys issues...
					auto a = netlist.eval(*ports[1]);
					auto n_en = netlist.eval(*ports[2]);
					auto p_en = netlist.eval(*ports[3]);
					auto nmos = netlist.backend->canvas->addMux(id + "_n", RTLIL::Sz, a, n_en, y);
					auto pmos = netlist.backend->canvas->addMux(id + "_p", a, RTLIL::Sz, p_en, y);
					transfer_attrs(netlist, sym, nmos);
					cell = pmos; // transfer_attrs to pmos after switch block
				} else {
					// bidir (tran/rtran/tranif0/rtranif0/tranif1/rtranif1) are unsupported
					netlist.add_diag(diag::PrimTypeUnsupported, sym.location);
				}
			}
		}
		cell->fixup_parameters();
		transfer_attrs(netlist, sym, cell);
		if (inv_y) {
			// Invert output signal where needed
			netlist.backend->canvas->rename(cell->name, id + "_yinv");
			auto mid_wire = netlist.add_placeholder_signal(y.size(), id + "_mid", true);
			auto inv_cell = netlist.backend->canvas->addNot(id, mid_wire, y);
			cell->setPort(ID::Y, mid_wire);
			transfer_attrs(netlist, sym, inv_cell);
		}
#endif // SLANG_NO_YOSYS
	}

	void handle(const ast::PropertySymbol &sym) {
		if (!netlist.settings.ignore_assertions.value_or(false)) {
			netlist.add_diag(diag::SVAUnsupported, sym.location);
		}
	}

	void handle(const ast::Symbol &sym)
	{
		unimplemented(sym);
	}
};

static void build_hierpath2(NetlistContext &netlist,
							std::ostringstream &s, const ast::Scope *scope,
							const std::string &sep = ".")
{
	if (!scope ||
		static_cast<const ast::Scope *>(&netlist.realm) == scope)
		return;

	if (netlist.scopes_remap.count(scope)) {
		s << netlist.scopes_remap.at(scope) << sep;
		return;
	}

	const ast::Symbol *symbol = &scope->asSymbol();

	if (symbol->kind == ast::SymbolKind::InstanceBody)
		symbol = symbol->as<ast::InstanceBodySymbol>().parentInstance;
	if (symbol->kind == ast::SymbolKind::CheckerInstanceBody)
		symbol = symbol->as<ast::CheckerInstanceBodySymbol>().parentInstance;

	if (auto parent = symbol->getParentScope())
		build_hierpath2(netlist, s, parent, sep);

	if (symbol->kind == ast::SymbolKind::GenerateBlockArray) {
		auto &array = symbol->as<ast::GenerateBlockArraySymbol>();
		s << array.getExternalName();
	} else if (symbol->kind == ast::SymbolKind::GenerateBlock) {
		auto &block = symbol->as<ast::GenerateBlockSymbol>();
		if (auto index = block.arrayIndex) {
			s << "[" << index->toString(slang::LiteralBase::Decimal, false) << "]" << sep;
		} else {
			s << block.getExternalName() << sep;
		}
	} else if (symbol->kind == ast::SymbolKind::Instance ||
			   symbol->kind == ast::SymbolKind::CheckerInstance) {
		s << symbol->name;

		auto &inst = symbol->as<ast::InstanceSymbolBase>();
		if (!inst.arrayPath.empty()) {
			slang::SmallVector<slang::ConstantRange, 8> dimensions;
			inst.getArrayDimensions(dimensions);

			for (size_t i = 0; i < inst.arrayPath.size(); i++)
				s << "[" << ((int) inst.arrayPath[i]) + dimensions[i].lower() << "]";
		}

		s << sep;
	} else if (symbol->kind == ast::SymbolKind::InstanceArray) {
		s << symbol->name;
	} else if (!symbol->name.empty()) {
		s << symbol->name << sep;
	} else if (symbol->kind == ast::SymbolKind::StatementBlock) {
		s << "$" << (int) symbol->getIndex() << sep;
	}
}

static bool build_hierpath3(const ast::Scope *relative_to,
							std::ostringstream &s, const ast::Scope *scope)
{
	log_assert(scope);

	if (relative_to == scope)
		return false;

	const ast::Symbol *symbol = &scope->asSymbol();

	if (symbol->kind == ast::SymbolKind::InstanceBody)
		symbol = symbol->as<ast::InstanceBodySymbol>().parentInstance;
	if (symbol->kind == ast::SymbolKind::CheckerInstanceBody)
		symbol = symbol->as<ast::CheckerInstanceBodySymbol>().parentInstance;

	bool pending;
	if (auto parent = symbol->getParentScope()) {
		pending = build_hierpath3(relative_to, s, parent);
	} else {
		log_abort();
	}

	if ((symbol->kind == ast::SymbolKind::GenerateBlockArray ||
			symbol->kind == ast::SymbolKind::GenerateBlock ||
			symbol->kind == ast::SymbolKind::Instance ||
			symbol->kind == ast::SymbolKind::CheckerInstance ||
			!symbol->name.empty() ||
			symbol->kind == ast::SymbolKind::StatementBlock) &&
			pending) {
		s << ".";
		pending = false;
	}

	if (symbol->kind == ast::SymbolKind::GenerateBlockArray) {
		auto &array = symbol->as<ast::GenerateBlockArraySymbol>();
		s << array.getExternalName();
	} else if (symbol->kind == ast::SymbolKind::GenerateBlock) {
		auto &block = symbol->as<ast::GenerateBlockSymbol>();
		if (auto index = block.arrayIndex) {
			s << "[" << index->toString(slang::LiteralBase::Decimal, false) << "]";
		} else {
			s << block.getExternalName();
		}

		pending = true;
	} else if (symbol->kind == ast::SymbolKind::Instance ||
			   symbol->kind == ast::SymbolKind::CheckerInstance) {
		s << symbol->name;

		auto &inst = symbol->as<ast::InstanceSymbolBase>();
		if (!inst.arrayPath.empty()) {
			slang::SmallVector<slang::ConstantRange, 8> dimensions;
			inst.getArrayDimensions(dimensions);

			for (size_t i = 0; i < inst.arrayPath.size(); i++)
				s << "[" << ((int) inst.arrayPath[i]) + dimensions[i].lower() << "]";
		}

		pending = true;
	} else if (symbol->kind == ast::SymbolKind::InstanceArray) {
		s << symbol->name;
	} else if (!symbol->name.empty()) {
		s << symbol->name;

		pending = true;
	} else if (symbol->kind == ast::SymbolKind::StatementBlock) {
		s << "$" << (int) symbol->getIndex();

		pending = true;
	}

	return pending;
}

std::string hierpath_relative_to(const ast::Scope *relative_to, const ast::Scope *scope)
{
	std::ostringstream path;
	build_hierpath3(relative_to, path, scope);
	return path.str();
}

std::string build_hiername(NetlistContext &netlist, const ast::Symbol &symbol,
						   const std::string &sep)
{
	std::ostringstream path;
	build_hierpath2(netlist, path, symbol.getParentScope(), sep);
	path << symbol.name;

	if (symbol.kind == ast::SymbolKind::Instance ||
			symbol.kind == ast::SymbolKind::PrimitiveInstance) {
		auto &inst = symbol.as<ast::InstanceSymbolBase>();
		if (!inst.arrayPath.empty()) {
			slang::SmallVector<slang::ConstantRange, 8> dimensions;
			inst.getArrayDimensions(dimensions);
			for (size_t i = 0; i < inst.arrayPath.size(); i++)
				path << "[" << ((int) inst.arrayPath[i]) + dimensions[i].lower() << "]";
		}
	}

	return path.str();
}

std::string NetlistContext::id(const ast::Symbol &symbol)
{
#ifdef SLANG_NO_YOSYS
	return build_hiername(*this, symbol, ".");
#else
	return RTLIL::escape_id(build_hiername(*this, symbol, "."));
#endif
}

std::string NetlistContext::unescaped_id(const ast::Symbol &symbol)
{
	return build_hiername(*this, symbol, ".");
}

std::string NetlistContext::id(const ast::ValueSymbol &symbol)
{
	return id(static_cast<const ast::Symbol &>(symbol));
}

std::string NetlistContext::hdlname(const ast::Symbol &symbol)
{
	return build_hiername(*this, symbol, " ");
}

bool is_special_net_type(const ast::NetType &type)
{
	switch (type.netKind) {
		case ast::NetType::WAnd:
		case ast::NetType::WOr:
		case ast::NetType::TriAnd:
		case ast::NetType::TriOr:
			return true;
		case ast::NetType::Wire:
		case ast::NetType::Tri:
		case ast::NetType::UWire:
			return false;
		default:
			log_abort();
	}
}

bool is_special_net(const ast::Symbol &symbol)
{
	return ast::NetSymbol::isKind(symbol.kind)
		&& is_special_net_type(symbol.as<ast::NetSymbol>().netType);
}

ir::Value NetlistContext::add_wire(const ast::ValueSymbol &symbol)
{
	auto &type = symbol.getType();

	AttributeGuard guard(*this);
#ifndef SLANG_NO_YOSYS
	guard.set(ID::hdlname, hdlname(symbol));
#endif
	transfer_attrs(*this, symbol, guard);

	ir::Value sig = add_placeholder_signal(type.getBitstreamWidth(), id(symbol), true);

#ifndef SLANG_NO_YOSYS
	if (type.kind == ast::SymbolKind::PackedArrayType &&
			type.as<ast::PackedArrayType>().elementType.isScalar()) {
		auto range = type.getFixedRange();
		auto *w = sig.raw_.as_wire();
		if (!range.isLittleEndian())
			w->upto = true;
		w->start_offset = range.lower();
	}
#endif

	wire_cache[&symbol] = sig;
	if (ast::NetSymbol::isKind(symbol.kind)) {
		auto &net = symbol.as<ast::NetSymbol>();
		if (is_special_net_type(net.netType)) {
			special_net_symbols.push_back(&net);
		}
	}
	return sig;
}

void finalize_special_nets(NetlistContext &netlist)
{
#ifdef SLANG_NO_YOSYS
	(void)netlist;
#else
	for (auto symbol : netlist.special_net_symbols) {
		for (auto bit : VariableBits(Variable::from_symbol(symbol))) {
			switch (symbol->netType.netKind) {
			case ast::NetType::WAnd:
			case ast::NetType::TriAnd: {
				netlist.backend->canvas->addReduceAnd(netlist.backend->new_id("wand"),
					netlist.special_net_drivers[bit],
					netlist.convert_static(bit));
				break;
			}
			case ast::NetType::WOr:
			case ast::NetType::TriOr: {
				netlist.backend->canvas->addReduceOr(netlist.backend->new_id("wor"),
					netlist.special_net_drivers[bit],
					netlist.convert_static(bit));
				break;
			}
			default:
				ast_unreachable(*symbol);
			}
		}
	}
#endif
}

bool NetlistContext::is_blackbox(const ast::DefinitionSymbol &sym, slang::Diagnostic *why_blackbox)
{
	if (sym.cellDefine)
		return true;

	if (settings.blackboxed_modules.contains(sym.name))
		return true;

	for (auto attr : sym.getParentScope()->getCompilation().getAttributes(sym)) {
		if (attr->name == "blackbox"sv && !attr->getValue().isFalse()) {
			if (why_blackbox) {
				auto &note = why_blackbox->addNote(diag::NoteModuleBlackboxBecauseAttribute,
													attr->location);
				note << sym.name;
			}
			return true;
		}
	}

	if (settings.empty_blackboxes.value_or(false)) {
		if (why_blackbox) {
			auto &note = why_blackbox->addNote(diag::NoteModuleBlackboxBecauseEmpty, sym.location);
			note << sym.name;
		}
#ifdef SLANG_NO_YOSYS
		return false;
#else
		return is_decl_empty_module(*sym.getSyntax());
#endif
	}

	return false;
}

bool NetlistContext::should_dissolve(const ast::InstanceSymbol &sym, slang::Diagnostic *why_not_dissolved)
{
	// blackboxes are never dissolved
	if (sym.isModule() && is_blackbox(sym.body.getDefinition())) {
		if (why_not_dissolved) {
			auto &note = why_not_dissolved->addNote(diag::NoteModuleNotDissolvedBecauseBlackbox, sym.location);
			note << sym.body.name;
			// insert note about blackbox reason
			is_blackbox(sym.body.getDefinition(), why_not_dissolved);
		}
		return false;
	}

	// interfaces are always dissolved
	if (sym.isInterface())
		return true;

	// the rest depends on the hierarchy mode
	switch (settings.hierarchy_mode()) {
	case SynthesisSettings::NONE:
		return true;
	case SynthesisSettings::BEST_EFFORT: {
		for (auto *conn : sym.getPortConnections()) {
			switch (conn->port.kind) {
			case ast::SymbolKind::Port:
			case ast::SymbolKind::MultiPort:
				break;
			case ast::SymbolKind::InterfacePort:
				if (!conn->getIfaceConn().second)
					return true;
				break;
			default:
				return true;
				break;
			}
		}

		if (!sym.isModule())
			return true;

		return false;
		}
	case SynthesisSettings::ALL:
		if (why_not_dissolved) {
			auto &note = why_not_dissolved->addNote(diag::NoteModuleNotDissolvedBecauseKeepHierarchy, sym.location);
			note << sym.body.name;
		}
	default:
		return false;
	}
}

const ast::InstanceBodySymbol &NetlistContext::find_symbol_realm(const ast::Symbol &symbol)
{
	const ast::Scope *scope = symbol.getParentScope();

	while (true) {
		const ast::Symbol &scope_symbol = scope->asSymbol();
		if (scope_symbol.kind == ast::SymbolKind::InstanceBody) {
			auto parent = scope_symbol.as<ast::InstanceBodySymbol>().parentInstance;
			log_assert(parent->getParentScope());
			if (parent->getParentScope()->asSymbol().kind == ast::SymbolKind::Root
					|| !should_dissolve(*parent)) {
				return scope_symbol.as<ast::InstanceBodySymbol>();
			} else {
				scope = parent->getParentScope();
			}
		} else {
			scope = scope->asSymbol().getParentScope();
		}
	}
}

const ast::InstanceBodySymbol &NetlistContext::find_common_ancestor(const ast::InstanceBodySymbol &a,
																  	const ast::InstanceBodySymbol &b)
{
	auto path = [&](const ast::InstanceBodySymbol *body) -> std::vector<const ast::InstanceBodySymbol*> {
		std::vector<const ast::InstanceBodySymbol*> path;
		path.push_back(body);
		while (body->parentInstance->getParentScope()->asSymbol().kind !=
					ast::SymbolKind::Root) {
			body = &find_symbol_realm(*body->parentInstance);
			path.push_back(body);
			log_assert(body->parentInstance);
			log_assert(body->parentInstance->getParentScope());
		}
		std::reverse(std::begin(path), std::end(path));
		return path;
	};

	auto pa = path(&a);
	auto pb = path(&b);

	int i = 0;
	for (; i < std::min(pa.size(), pb.size()); i++) {
		if (pa[i] != pb[i])
			break;
	}
	log_assert(i > 0);
	return *pa[i - 1];
}

bool NetlistContext::check_hier_ref(const ast::ValueSymbol &symbol, slang::SourceRange range, bool silent)
{
	const ast::InstanceBodySymbol &symbol_realm = find_symbol_realm(symbol);

	if (&symbol_realm != &realm) {
		auto &diag = add_diag(diag::ReferenceAcrossKeptHierBoundary, range);
		auto &common = find_common_ancestor(symbol_realm, realm);
		if (!silent) {
			if (&symbol_realm != &common) {
				// emit diagnostic for boundary on the hierarchical path to the symbol
				(void) should_dissolve(*symbol_realm.parentInstance, &diag);
			} else {
				// emit diagnostic for boundary on the hierarchical path to the expression
				(void) should_dissolve(*realm.parentInstance, &diag);
			}			
		}
		return false;
	}
	return true;
}

ir::Value NetlistContext::wire(const ast::Symbol &symbol)
{
	auto it = wire_cache.find(&symbol);
	if (it == wire_cache.end())
		wire_missing(*this, symbol);
	return it->second;
}

ir::Value NetlistContext::convert_static(VariableBits bits)
{
	ir::Value ret;

	for (auto vchunk : bits.chunks()) {
		switch (vchunk.variable.kind) {
		case Variable::Static:
			ret.append(wire(*vchunk.variable.get_symbol())
					.extract((int)vchunk.base, (int)vchunk.length));
			break;
		case Variable::Dummy:
			ret.append(add_placeholder_signal(vchunk.length, "dummy"));
			break;
		default:
			log_abort();
		}
	}

	return ret;
}

NetlistContext::NetlistContext(
		std::unique_ptr<BackendGraphBuilder> backend,
		SynthesisSettings &settings,
		ast::Compilation &compilation,
		const ast::InstanceSymbol &instance)
	: settings(settings), compilation(compilation), realm(instance.body), eval(*this)
{
	GraphBuilder::backend = std::move(backend);
#ifndef SLANG_NO_YOSYS
	transfer_attrs(*this, instance.body.getDefinition(), GraphBuilder::backend->canvas);
#endif
}

NetlistContext::NetlistContext(
		NetlistContext &other,
		const ast::InstanceSymbol &instance)
	: NetlistContext(other.backend->start_new_graph(module_type_id(instance.body)), other.settings, other.compilation, instance)
{
	//canvas = design->addModule(module_type_id(instance.body));
}

NetlistContext::~NetlistContext()
{
	backend->finalize();
}

std::vector<slang::DiagCode> forbidden_diag_demotions = {
	slang::diag::UnknownSystemName
};

void catch_forbidden_options(slang::driver::Driver &driver) {
	slang::DiagnosticEngine &engine = driver.diagEngine;

	auto &flags = driver.options.compilationFlags;
	if (flags[ast::CompilationFlags::AllowTopLevelIfacePorts]) {
		slang::Diagnostic diag(diag::NoAllowTopLevelIfacePorts, slang::SourceLocation::NoLocation);
		engine.issue(diag);
		flags[ast::CompilationFlags::AllowTopLevelIfacePorts] = false;
	}

	// FIXME: this doesn't catch demotions which are location specific via pragmas
	for (auto code : forbidden_diag_demotions) {
		if (engine.getSeverity(code, slang::SourceLocation::NoLocation) !=
				slang::DiagnosticSeverity::Error) {
			slang::Diagnostic demotion_diag(diag::ForbiddenDemotion, slang::SourceLocation::NoLocation);
			demotion_diag << engine.getOptionName(code);
			engine.issue(demotion_diag);
			engine.setSeverity(slang::diag::UnknownSystemName, slang::DiagnosticSeverity::Error);
		}
	}
}

void fixup_options(SynthesisSettings &settings, slang::driver::Driver &driver)
{
	if (settings.compat_mode.has_value()) {
		slang::Diagnostic d(diag::DeprecatedOption, slang::SourceLocation::NoLocation);
		d << std::string_view("--compat-mode");
		driver.diagEngine.issue(d);
	}
	if (settings.extern_modules.has_value()) {
		slang::Diagnostic d(diag::DeprecatedOption, slang::SourceLocation::NoLocation);
		d << std::string_view("--extern-modules");
		driver.diagEngine.issue(d);
	}

	if (!settings.no_synthesis_define.value_or(false)) {
		driver.options.defines.push_back("SYNTHESIS=1");
	}

	if (!settings.no_default_translate_off.value_or(false)) {
		auto &format_list = driver.options.translateOffOptions;
		format_list.insert(format_list.end(), {
			"pragma,synthesis_off,synthesis_on",
			"pragma,translate_off,translate_on",
			"synopsys,synthesis_off,synthesis_on",
			"synopsys,translate_off,translate_on",
			"synthesis,translate_off,translate_on",
			"xilinx,translate_off,translate_on",
		});
	}

	auto &flags = driver.options.compilationFlags;

	auto &disable_inst_caching = flags[ast::CompilationFlags::DisableInstanceCaching];
	if (!disable_inst_caching.has_value()) {
		disable_inst_caching = true;
	}
	settings.disable_instance_caching = disable_inst_caching.value();

	// we cannot handle references into unknown modules
	flags[ast::CompilationFlags::DisallowRefsToUnknownInstances] = true;

	// revisit slang#1326 in case of issues with this override
	auto &time_scale = driver.options.timeScale;
	if (!time_scale.has_value()) {
		time_scale = "1ns/1ns";
	}
}

void populate_netlist(HierarchyQueue &hqueue, NetlistContext &netlist)
{
	PopulateNetlist populate(hqueue, netlist);
	netlist.realm.visit(populate);
}

void add_internal_symbols(NetlistContext &netlist, const ast::InstanceBodySymbol &body)
{
	HierarchyQueue dummy_queue;
	PopulateNetlist populate(dummy_queue, netlist);
	populate.add_internal_wires(body);
}

};

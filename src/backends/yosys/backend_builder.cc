//
// Yosys slang frontend
//
// Copyright Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//

#include <memory>

#include "kernel/rtlil.h"

#include "slang_frontend.h"
#include "ir.h"
#include "backend_builder.h"

namespace slang_frontend {

using RTLIL::Cell;
using RTLIL::IdString;

// A compat util to be removed once we drop 0.59 support
#if YOSYS_MAJOR == 0 && YOSYS_MINOR < 59
static IdString id(std::string_view sv)
{
	return std::string(sv);
}
#else
static IdString id(std::string_view sv)
{
	return sv;
}
#endif

std::string BackendGraphBuilder::new_id(std::string base)
{
	if (base.empty())
		return std::string("$") + std::to_string(next_id++);
	else
		return std::string("$") + base + "$" + std::to_string(next_id++);
}

std::pair<std::string, ir::Value> BackendGraphBuilder::add_y_wire(int width)
{
	std::string id = new_id();
	return {id, canvas->addWire(id + "y", width)};
}

void BackendGraphBuilder::bless_cell(RTLIL::Cell *cell)
{
	cell->attributes = staged_attributes;
}

ir::Value BackendGraphBuilder::Demux(ir::Value a, ir::Value s)
{
	auto [id, y] = add_y_wire(a.size() << s.size());
	bless_cell(canvas->addDemux(id, a, s, y));
	return y;
}

ir::Value BackendGraphBuilder::Mux(ir::Value a, ir::Value b, ir::Net s)
{
	auto [id, y] = add_y_wire(a.size());
	bless_cell(canvas->addMux(id, a, b, {s}, y));
	return y;
}

ir::Value BackendGraphBuilder::Bwmux(ir::Value a, ir::Value b, ir::Value s)
{
	auto [id, y] = add_y_wire(a.size());
	bless_cell(canvas->addBwmux(id, a, b, s, y));
	return y;
}

ir::Value BackendGraphBuilder::Shift(ir::Value a, ir::Value b, bool b_signed, uint64_t result_width)
{
	auto [id, y] = add_y_wire(result_width);
	Cell *cell = canvas->addCell(id, ID($shift));
	cell->parameters[Yosys::ID::A_SIGNED] = false;
	cell->parameters[Yosys::ID::B_SIGNED] = b_signed;
	cell->parameters[Yosys::ID::A_WIDTH] = a.size();
	cell->parameters[Yosys::ID::B_WIDTH] = b.size();
	cell->parameters[Yosys::ID::Y_WIDTH] = y.size();
	cell->setPort(Yosys::ID::A, a);
	cell->setPort(Yosys::ID::B, b);
	cell->setPort(Yosys::ID::Y, y);
	bless_cell(cell);
	return y;
}

ir::Value BackendGraphBuilder::Shiftx(ir::Value a, ir::Value s, bool s_signed, uint64_t result_width)
{
	auto [id, y] = add_y_wire(result_width);
	bless_cell(canvas->addShiftx(id, a, s, y, s_signed));
	return y;
}

ir::Value BackendGraphBuilder::Bmux(ir::Value a, ir::Value s)
{
	log_assert(a.size() % (1 << s.size()) == 0);
	log_assert(a.size() >= 1 << s.size());
	int stride = a.size() >> s.size();
	auto [id, y] = add_y_wire(stride);
	bless_cell(canvas->addBmux(id, a, s, y));
	return y;
}

ir::Value BackendGraphBuilder::Biop(ast::BinaryOperator op, ir::Value a, ir::Value b, bool a_signed,
		bool b_signed, uint64_t y_width)
{
	RTLIL::IdString rtlil_op;
	switch (op) {
	case ast::BinaryOperator::Add:              rtlil_op = ID($add); break;
	case ast::BinaryOperator::Subtract:         rtlil_op = ID($sub); break;
	case ast::BinaryOperator::Multiply:         rtlil_op = ID($mul); break;
	case ast::BinaryOperator::Divide:           rtlil_op = ID($div); break;
	case ast::BinaryOperator::Mod:              rtlil_op = ID($mod); break;
	case ast::BinaryOperator::BinaryAnd:        rtlil_op = ID($and); break;
	case ast::BinaryOperator::BinaryOr:         rtlil_op = ID($or); break;
	case ast::BinaryOperator::BinaryXor:        rtlil_op = ID($xor); break;
	case ast::BinaryOperator::BinaryXnor:       rtlil_op = ID($xnor); break;
	case ast::BinaryOperator::Equality:         rtlil_op = ID($eq); break;
	case ast::BinaryOperator::Inequality:       rtlil_op = ID($ne); break;
	case ast::BinaryOperator::CaseInequality:   rtlil_op = ID($nex); break;
	case ast::BinaryOperator::CaseEquality:     rtlil_op = ID($eqx); break;
	case ast::BinaryOperator::GreaterThanEqual: rtlil_op = ID($ge); break;
	case ast::BinaryOperator::GreaterThan:      rtlil_op = ID($gt); break;
	case ast::BinaryOperator::LessThanEqual:    rtlil_op = ID($le); break;
	case ast::BinaryOperator::LessThan:         rtlil_op = ID($lt); break;
	case ast::BinaryOperator::LogicalAnd:       rtlil_op = ID($logic_and); break;
	case ast::BinaryOperator::LogicalOr:        rtlil_op = ID($logic_or); break;
	case ast::BinaryOperator::LogicalImplication:
		rtlil_op = ID($logic_or);
		a = Unop(ast::UnaryOperator::LogicalNot, a, false, 1);
		a_signed = false;
		break;
	case ast::BinaryOperator::LogicalEquivalence:
		rtlil_op = ID($eq);
		a = Unop(ast::UnaryOperator::BitwiseOr, a, false, 1);
		b = Unop(ast::UnaryOperator::BitwiseOr, b, false, 1);
		a_signed = b_signed = false;
		break;
	case ast::BinaryOperator::LogicalShiftLeft:     rtlil_op = ID($shl); break;
	case ast::BinaryOperator::LogicalShiftRight:    rtlil_op = ID($shr); break;
	case ast::BinaryOperator::ArithmeticShiftLeft:  rtlil_op = ID($sshl); break;
	case ast::BinaryOperator::ArithmeticShiftRight: rtlil_op = ID($sshr); break;
	case ast::BinaryOperator::Power:                rtlil_op = ID($pow); break;
	default:                                        log_abort();
	}

	if (a.is_fully_const() && b.is_fully_const()) {
#define OP(type)                                                                                   \
	if (rtlil_op == ID($##type))                                                                         \
		return RTLIL::const_##type(                                                                \
				a.as_const().to_rtlil(), b.as_const().to_rtlil(), a_signed, b_signed, y_width);
		OP(add)
		OP(sub)
		OP(mul)
		OP(divfloor)
		OP(div)
		OP(mod)
		OP(and)
		OP(or)
		OP(xor)
		OP(xnor)
		OP(eq)
		OP(ne)
		OP(nex)
		OP(eqx)
		OP(ge)
		OP(gt)
		OP(le)
		OP(lt)
		OP(logic_and)
		OP(logic_or)
		OP(sshl)
		OP(sshr)
		OP(shl)
		OP(shr)
		OP(pow)
#undef OP
	}

	auto [id, y] = add_y_wire(y_width);
	Cell *cell = canvas->addCell(id, rtlil_op);
	cell->setPort(RTLIL::ID::A, a);
	cell->setPort(RTLIL::ID::B, b);
	cell->setParam(RTLIL::ID::A_WIDTH, a.size());
	cell->setParam(RTLIL::ID::B_WIDTH, b.size());
	cell->setParam(RTLIL::ID::A_SIGNED, a_signed);
	cell->setParam(RTLIL::ID::B_SIGNED, b_signed);
	cell->setParam(RTLIL::ID::Y_WIDTH, y_width);
	cell->setPort(RTLIL::ID::Y, y);
	bless_cell(cell);
	return y;
}

ir::Value BackendGraphBuilder::Unop(ast::UnaryOperator op, ir::Value a, bool a_signed, uint64_t y_width)
{
	bool invert = false;
	RTLIL::IdString rtlil_op;
	using UnOp = ast::UnaryOperator;
	switch (op) {
	case UnOp::Minus:      rtlil_op = ID($neg); break;
	case UnOp::Plus:       rtlil_op = ID($pos); break;
	case UnOp::LogicalNot: rtlil_op = ID($logic_not); break;
	case UnOp::BitwiseNot: rtlil_op = ID($not); break;
	case UnOp::BitwiseOr:  rtlil_op = ID($reduce_or); break;
	case UnOp::BitwiseAnd: rtlil_op = ID($reduce_and); break;
	case UnOp::BitwiseNand:
		rtlil_op = ID($reduce_and);
		invert = true;
		break;
	case UnOp::BitwiseNor:
		rtlil_op = ID($reduce_or);
		invert = true;
		break;
	case UnOp::BitwiseXor:  rtlil_op = ID($reduce_xor); break;
	case UnOp::BitwiseXnor: rtlil_op = ID($reduce_xnor); break;
	default:                log_abort();
	}

	if (a.is_fully_const()) {
		ir::Value const_result;
		bool have_const = false;
#define OP(type)                                                                                   \
	if (rtlil_op == ID($##type)) {                                                                 \
		const_result = RTLIL::const_##type(a.as_const().to_rtlil(), {}, a_signed, false, y_width); \
		have_const = true; }
		OP(pos)
		OP(neg)
		OP(logic_not)
		OP(not)
		OP(reduce_or)
		OP(reduce_and)
		OP(reduce_xor)
		OP(reduce_xnor)
		OP(reduce_bool)
#undef OP
		if (have_const) {
			if (invert) {
				const_result = RTLIL::const_logic_not(const_result.as_const().to_rtlil(), {}, false, false, y_width);
			}
			return const_result;
		}
	}

	auto [id, y] = add_y_wire(y_width);
	Cell *cell = canvas->addCell(id, rtlil_op);
	cell->setPort(RTLIL::ID::A, a);
	cell->setParam(RTLIL::ID::A_WIDTH, a.size());
	cell->setParam(RTLIL::ID::A_SIGNED, a_signed);
	cell->setParam(RTLIL::ID::Y_WIDTH, y_width);
	cell->setPort(RTLIL::ID::Y, y);
	bless_cell(cell);

	ir::Value ret = y;
	if (invert)
		ret = Unop(ast::UnaryOperator::LogicalNot, ret, false, ret.width());
	return ret;
}

void BackendGraphBuilder::connect(ir::Value lhs, ir::Value rhs)
{
	log_assert(lhs.size() == rhs.size());
	if (!lhs.empty()) {
		Cell *cell = canvas->addBuf(new_id(), rhs, lhs);
		bless_cell(cell);
	}
}

void BackendGraphBuilder::set_initialization(ir::Value signal, ir::Const init_value)
{
	if (init_value.is_fully_undef())
		return;
	log_assert(signal.is_wire());
	RTLIL::Wire *wire = signal.chunks().begin()->wire;
	wire->attributes[ID::init] = init_value.to_rtlil();
}

// Synthesizes two single-edge FFs (one posedge, one negedge) with the same D input,
// then uses a mux controlled by the clock to select the appropriate FF output.
void BackendGraphBuilder::add_dual_edge_aldff(const std::string &base_name, ir::Value clk, ir::Value aload,
		ir::Value d, ir::Value q, ir::Value ad, bool aload_polarity)
{
	RTLIL::Wire *pos_q = canvas->addWire(
			canvas->uniquify(Yosys::stringf("%s$pos$q", base_name.c_str())), d.size());

	RTLIL::Wire *neg_q = canvas->addWire(
			canvas->uniquify(Yosys::stringf("%s$neg$q", base_name.c_str())), d.size());

	if (aload.is_fully_def() && aload.size() == 1 && aload.as_bool() != aload_polarity) {
		RTLIL::Cell *pos_ff =
				canvas->addDff(canvas->uniquify(Yosys::stringf("%s$pos", base_name.c_str())), clk,
						d, pos_q, /*edge_polarity=*/true);
		bless_cell(pos_ff);

		// Create negedge FF
		RTLIL::Cell *neg_ff =
				canvas->addDff(canvas->uniquify(Yosys::stringf("%s$neg", base_name.c_str())), clk,
						d, neg_q, /*edge_polarity=*/false);
		bless_cell(neg_ff);
	} else {
		RTLIL::Cell *pos_ff =
				canvas->addAldff(canvas->uniquify(Yosys::stringf("%s$pos", base_name.c_str())), clk,
						aload, d, pos_q, ad,
						/*clk_polarity=*/true, aload_polarity);
		bless_cell(pos_ff);

		RTLIL::Cell *neg_ff =
				canvas->addAldff(canvas->uniquify(Yosys::stringf("%s$neg", base_name.c_str())), clk,
						aload, d, neg_q, ad,
						/*clk_polarity=*/false, aload_polarity);
		bless_cell(neg_ff);
	}

	// behaviour: when clk=0: select neg_q (captures on negedge), when clk=1: select pos_q (captures
	// on posedge)
	RTLIL::Cell *mux = canvas->addMux(canvas->uniquify(Yosys::stringf("%s$mux", base_name.c_str())),
			/*A=*/neg_q, /*B=*/pos_q, /*S=*/clk, /*Y=*/q);
	bless_cell(mux);
}

void BackendGraphBuilder::add_dff(std::string_view name, const ir::Value &clk, const ir::Value &d,
		const ir::Value &q, bool clk_polarity)
{
	RTLIL::Cell *cell = canvas->addDff(canvas->uniquify(id(name)), clk, d, q, clk_polarity);
	bless_cell(cell);
}

void BackendGraphBuilder::add_dffe(std::string_view name, const ir::Value &clk, const ir::Value &en,
		const ir::Value &d, const ir::Value &q, bool clk_polarity, bool en_polarity)
{
	RTLIL::Cell *cell =
			canvas->addDffe(canvas->uniquify(id(name)), clk, en, d, q, clk_polarity, en_polarity);
	bless_cell(cell);
}

void BackendGraphBuilder::add_aldff(std::string_view name, const ir::Value &clk, const ir::Value &aload,
		const ir::Value &d, const ir::Value &q, const ir::Value &ad, bool clk_polarity,
		bool aload_polarity)
{
	RTLIL::Cell *cell = canvas->addAldff(
			canvas->uniquify(id(name)), clk, aload, d, q, ad, clk_polarity, aload_polarity);
	bless_cell(cell);
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

// Private helper
void BackendGraphBuilder::emit_meminit_cell(
		RTLIL::Memory *mem, uint64_t word_offset, bool big_endian, ir::Const data, ir::Const mask)
{
	if (data.empty())
		return;

	int abits = 32; // TODO: error out if abits too low
	int nwords = data.size() / mem->width;
	log_assert(data.size() % mem->width == 0);
	log_assert(mask.size() == mem->width);
	RTLIL::Cell *cell = canvas->addCell(new_id(), ID($meminit_v2));
	cell->setParam(ID::MEMID, mem->name.str());
	cell->setParam(ID::PRIORITY, meminit_prio_counter++);
	cell->setParam(ID::ABITS, abits);
	cell->setParam(ID::WORDS, nwords);
	cell->setParam(ID::WIDTH, mem->width);
	cell->setPort(ID::ADDR,
			mem->start_offset + (big_endian ? (mem->size - word_offset - nwords) : word_offset));
	cell->setPort(
			ID::DATA, big_endian ? reverse_data(data.raw_rtlil(), mem->width) : data.to_rtlil());
	cell->setPort(ID::EN, mask.to_rtlil());
	bless_cell(cell);
}

void BackendGraphBuilder::add_memory_init(
		std::string_view name, uint64_t bit_offset, bool big_endian, ir::Const data)
{
	if (data.empty())
		return;

	RTLIL::Memory *mem = canvas->memories.at(id(name));
	log_assert(mem);

	uint64_t processed = 0;

	using ir::Const;
	using ir::S0;
	using ir::S1;
	using ir::Sx;

	// Depending on the offset alignment with respect to word boundaries
	// we might need to emit up to 3 instances of the `$meminit_v2` cell.
	if (bit_offset % mem->width != 0) {
		int offset_in_cell = bit_offset % mem->width;
		uint64_t length = std::min(mem->width - offset_in_cell, data.size());
		Const data1, mask1;
		data1.append(Const(Sx, offset_in_cell));
		data1.append(data.extract(0, length));
		data1.append(Const(Sx, mem->width - offset_in_cell - length));
		mask1.append(Const(S0, offset_in_cell));
		mask1.append(Const(S1, length));
		mask1.append(Const(S0, mem->width - offset_in_cell - length));
		emit_meminit_cell(mem, bit_offset / mem->width, big_endian, data1, mask1);
		processed += length;
	}

	if (processed < data.size()) {
		log_assert((bit_offset + processed) % mem->width == 0);
		uint64_t length = ((((uint64_t)data.size()) - processed) / mem->width) * mem->width;
		emit_meminit_cell(mem, (bit_offset + processed) / mem->width, big_endian,
				data.extract(processed, length), Const(S1, mem->width));
		processed += length;
	}

	if (processed < data.size()) {
		uint64_t length = data.size() - processed;
		log_assert(length < mem->width);
		Const data1, mask1;
		data1.append(data.extract(0, length));
		data1.append(Const(Sx, mem->width - length));
		mask1.append(Const(S1, length));
		mask1.append(Const(S0, mem->width - length));
		emit_meminit_cell(mem, bit_offset / mem->width, big_endian, data1, mask1);
		processed += length;
	}

	log_assert(processed == data.size());
}

ir::Value BackendGraphBuilder::add_placeholder_signal(
		uint64_t width, std::string_view name_suggestion, bool public_name)
{
	log_assert(width <= (uint64_t)std::numeric_limits<int>::max());
	RTLIL::IdString name;
	if (public_name) {
		name = id(name_suggestion);
	} else {
		name = new_id(std::string(name_suggestion));
	}
	RTLIL::Wire *wire = canvas->addWire(name, (int)width);
	wire->attributes = staged_attributes;
	return wire;
}

std::unique_ptr<BackendGraphBuilder> BackendGraphBuilder::start_new_graph(std::string_view graph_name)
{
	auto backend2 = std::make_unique<BackendGraphBuilder>();
	backend2->canvas = canvas->design->addModule(RTLIL::escape_id(std::string(graph_name)));
	return backend2;
}

void BackendGraphBuilder::finalize()
{
	if (canvas) {
		canvas->fixup_ports();
		canvas->check();
	}
}

}

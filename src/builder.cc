//
// Yosys slang frontend
//
// Copyright Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
#include <limits>

#include "slang_frontend.h"
#include "variables.h"

namespace slang_frontend {

using RTLIL::Cell;
using RTLIL::IdString;
using RTLIL::SigSpec;

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

std::string RTLILBuilder::new_id(std::string base)
{
	if (base.empty())
		return std::string("$") + std::to_string(next_id++);
	else
		return std::string("$") + base + "$" + std::to_string(next_id++);
}

std::pair<std::string, SigSpec> RTLILBuilder::add_y_wire(int width)
{
	std::string id = new_id();
	return {id, canvas->addWire(id + "y", width)};
}

void RTLILBuilder::bless_cell(RTLIL::Cell *cell)
{
	cell->attributes = staged_attributes;
}

SigSpec RTLILBuilder::ReduceBool(SigSpec a)
{
	if (a.is_fully_const())
		return RTLIL::const_reduce_bool(a.as_const(), RTLIL::Const(), false, false, 1);
	if (a.size() == 1)
		return a[0];

	auto [id, y] = add_y_wire(1);
	bless_cell(canvas->addReduceBool(id, a, y, false));
	return y;
}

SigSpec RTLILBuilder::Demux(SigSpec a, SigSpec s)
{
	log_assert(s.size() < 24);
	SigSpec zeropad(RTLIL::S0, a.size());
	if (s.is_fully_const()) {
		int idx_const = s.as_const().as_int();
		return {zeropad.repeat((1 << s.size()) - 1 - idx_const), a, zeropad.repeat(idx_const)};
	}
	auto [id, y] = add_y_wire(a.size() << s.size());
	bless_cell(canvas->addDemux(id, a, s, y));
	return y;
}

SigSpec RTLILBuilder::Le(SigSpec a, SigSpec b, bool is_signed)
{
	if (a.is_fully_const() && b.is_fully_const())
		return RTLIL::const_le(a.as_const(), b.as_const(), is_signed, is_signed, 1);
	auto [id, y] = add_y_wire(1);
	bless_cell(canvas->addLe(id, a, b, y, is_signed));
	return y;
}

SigSpec RTLILBuilder::Ge(SigSpec a, SigSpec b, bool is_signed)
{
	if (a.is_fully_const() && b.is_fully_const())
		return RTLIL::const_ge(a.as_const(), b.as_const(), is_signed, is_signed, 1);
	auto [id, y] = add_y_wire(1);
	bless_cell(canvas->addGe(id, a, b, y, is_signed));
	return y;
}

SigSpec RTLILBuilder::Lt(SigSpec a, SigSpec b, bool is_signed)
{
	if (a.is_fully_const() && b.is_fully_const())
		return RTLIL::const_lt(a.as_const(), b.as_const(), is_signed, is_signed, 1);
	auto [id, y] = add_y_wire(1);
	bless_cell(canvas->addLt(id, a, b, y, is_signed));
	return y;
}

SigSpec RTLILBuilder::Eq(SigSpec a, SigSpec b)
{
	if (a.is_fully_const() && b.is_fully_const())
		return RTLIL::const_eq(a.as_const(), b.as_const(), false, false, 1);
	auto [id, y] = add_y_wire(1);
	bless_cell(canvas->addEq(id, a, b, y, false));
	return y;
}

SigSpec RTLILBuilder::EqWildcard(SigSpec a, SigSpec b)
{
	log_assert(a.size() == b.size());
	log_assert(b.is_fully_const());

	for (int i = a.size() - 1; i >= 0; i--) {
		if (b[i] == RTLIL::Sx || b[i] == RTLIL::Sz) {
			a.remove(i);
			b.remove(i);
		}
	}
	log_assert(a.size() == b.size());
	if (a.is_fully_const() && b.is_fully_const())
		return RTLIL::const_eq(a.as_const(), b.as_const(), false, false, 1);
	auto [id, y] = add_y_wire(1);
	bless_cell(canvas->addEq(id, a, b, y, false));
	return y;
}

SigSpec RTLILBuilder::LogicAnd(SigSpec a, SigSpec b)
{
	if (a.is_fully_zero() || b.is_fully_zero())
		return RTLIL::Const(0, 1);
	if (a.is_fully_def() && b.size() == 1)
		return b;
	if (b.is_fully_def() && a.size() == 1)
		return a;
	auto [id, y] = add_y_wire(1);
	bless_cell(canvas->addLogicAnd(id, a, b, y));
	return y;
}

SigSpec RTLILBuilder::LogicOr(SigSpec a, SigSpec b)
{
	if (a.is_fully_ones() || b.is_fully_ones())
		return RTLIL::Const(1, 1);
	if (a.is_fully_zero() && b.is_fully_zero())
		return RTLIL::Const(0, 1);
	auto [id, y] = add_y_wire(1);
	bless_cell(canvas->addLogicOr(id, a, b, y));
	return y;
}

SigSpec RTLILBuilder::LogicNot(SigSpec a)
{
	if (a.is_fully_const())
		return RTLIL::const_logic_not(a.as_const(), RTLIL::Const(), false, false, -1);
	auto [id, y] = add_y_wire(1);
	bless_cell(canvas->addLogicNot(id, a, y));
	return y;
}

SigSpec RTLILBuilder::Mux(SigSpec a, SigSpec b, SigSpec s)
{
	log_assert(a.size() == b.size());
	log_assert(s.size() == 1);
	if (s[0] == RTLIL::S0)
		return a;
	if (s[0] == RTLIL::S1)
		return b;
	auto [id, y] = add_y_wire(a.size());
	bless_cell(canvas->addMux(id, a, b, s, y));
	return y;
}

SigSpec RTLILBuilder::Bwmux(SigSpec a, SigSpec b, SigSpec s)
{
	log_assert(a.size() == b.size());
	log_assert(a.size() == s.size());
	if (s.is_fully_const()) {
		SigSpec result(RTLIL::Sx, a.size());
		for (int i = 0; i < a.size(); i++) {
			if (s[i] == RTLIL::S0)
				result[i] = a[i];
			else if (s[i] == RTLIL::S1)
				result[i] = b[i];
		}
		return result;
	}
	auto [id, y] = add_y_wire(a.size());
	bless_cell(canvas->addBwmux(id, a, b, s, y));
	return y;
}

SigSpec RTLILBuilder::Shift(SigSpec a, bool a_signed, SigSpec b, bool b_signed, int result_width)
{
	if (a.is_fully_const() && b.is_fully_const())
		return RTLIL::const_shift(a.as_const(), b.as_const(), a_signed, b_signed, result_width);

	if (b.is_fully_const() && b.size() < 24) {
		log_assert(!a.empty());
		int shift_amount = b.as_int(b_signed);
		RTLIL::SigSpec ret;
		int i, j;
		for (i = shift_amount, j = 0; j < result_width; i++, j++) {
			if (a_signed && i >= a.size())
				ret.append(a.msb());
			else if (i >= a.size() || i < 0)
				ret.append(RTLIL::S0);
			else
				ret.append(a[i]);
		}
		return ret;
	}

	auto [id, y] = add_y_wire(result_width);
	Cell *cell = canvas->addCell(id, ID($shift));
	cell->parameters[Yosys::ID::A_SIGNED] = a_signed;
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

SigSpec RTLILBuilder::Shiftx(SigSpec a, SigSpec s, bool s_signed, int result_width)
{
	if (a.is_fully_const() && s.is_fully_const())
		return RTLIL::const_shiftx(a.as_const(), s.as_const(), false, s_signed, result_width);
	auto [id, y] = add_y_wire(result_width);
	bless_cell(canvas->addShiftx(id, a, s, y, s_signed));
	return y;
}

SigSpec RTLILBuilder::Neg(SigSpec a, bool signed_)
{
	if (a.is_fully_const())
		return RTLIL::const_neg(a.as_const(), RTLIL::Const(), signed_, false, a.size() + 1);
	auto [id, y] = add_y_wire(a.size() + 1);
	bless_cell(canvas->addNeg(id, a, y, signed_));
	return y;
}

SigSpec RTLILBuilder::Bmux(SigSpec a, SigSpec s)
{
	log_assert(a.size() % (1 << s.size()) == 0);
	log_assert(a.size() >= 1 << s.size());
	int stride = a.size() >> s.size();
	if (s.is_fully_def()) {
		return a.extract(s.as_const().as_int() * stride, stride);
	}
	auto [id, y] = add_y_wire(stride);
	bless_cell(canvas->addBmux(id, a, s, y));
	return y;
}

SigSpec RTLILBuilder::Not(SigSpec a)
{
	if (a.is_fully_const())
		return RTLIL::const_not(a.as_const(), RTLIL::Const(), false, false, -1);
	auto [id, y] = add_y_wire(a.size());
	bless_cell(canvas->addNot(id, a, y));
	return y;
}

namespace ThreeValued {
int AND(int a, int b)
{
	if (a < 0 || b < 0)
		return -1;
	if (a > 0 && b > 0)
		return 1;
	return 0;
}

int NOT(int lit)
{
	return -lit;
}

int OR(int a, int b)
{
	return NOT(AND(NOT(a), NOT(b)));
}

int XOR(int a, int b)
{
	return OR(AND(a, NOT(b)), AND(NOT(a), b));
}

int XNOR(int a, int b)
{
	return NOT(OR(AND(a, NOT(b)), AND(NOT(a), b)));
}

int CARRY(int a, int b, int c)
{
	if (c > 0)
		return OR(a, b);
	else if (c < -1)
		return AND(a, b);

	return OR(AND(a, b), AND(c, OR(a, b)));
}

int convert(RTLIL::SigBit bit)
{
	if (bit == RTLIL::S1)
		return 1;
	else if (bit == RTLIL::S0)
		return -1;
	else
		return 0;
}
}; // namespace ThreeValued

SigSpec RTLILBuilder::Biop(
		IdString op, SigSpec a, SigSpec b, bool a_signed, bool b_signed, int y_width)
{
	if (a.is_fully_const() && b.is_fully_const()) {
#define OP(type)                                                                                   \
	if (op == ID($##type))                                                                         \
		return RTLIL::const_##type(a.as_const(), b.as_const(), a_signed, b_signed, y_width);
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

	if (op.in(ID($le), ID($lt), ID($gt), ID($ge)) && !a.empty() && !b.empty()) {
		int carry = op.in(ID($le), ID($ge)) ? -1 : 1;
		int al, bl;
		// Defer to three-valued evaluation over a representation of the operators.
		// This is a bit much, but I'm writing this tired and don't trust doing it
		// another way.
		int width = std::max(a.size(), b.size());
		for (int i = 0; i < width; i++) {
			RTLIL::SigBit abit = i < a.size() ? a[i] : (a_signed ? a.msb() : RTLIL::S0);
			RTLIL::SigBit bbit = i < b.size() ? b[i] : (b_signed ? b.msb() : RTLIL::S0);
			al = ThreeValued::convert(abit);
			bl = ThreeValued::convert(bbit);
			if (op.in(ID($gt), ID($ge)))
				std::swap(al, bl);
			if (i != width - 1)
				carry = ThreeValued::CARRY(al, ThreeValued::NOT(bl), carry);
		}
		int result = ThreeValued::XOR(carry, ThreeValued::XNOR(al, bl));
		if (result < 0)
			return SigSpec(RTLIL::S0, y_width);
		if (result > 0) {
			SigSpec ret = {RTLIL::S1};
			ret.extend_u0(y_width);
			return ret;
		}
	}

	if (op == ID($logic_and)) {
		if (a.is_fully_zero() || b.is_fully_zero())
			return SigSpec(RTLIL::S0, y_width);
	}

	if (op == ID($logic_or)) {
		// IMPROVEMENT: condition could be relaxed
		if ((a.is_fully_const() && a.as_bool()) || (b.is_fully_const() && b.as_bool())) {
			SigSpec ret = {RTLIL::S1};
			ret.extend_u0(y_width);
			return ret;
		}
	}

	int msb_zeroes = 0;
	if (op == ID($mul) && !a_signed && !b_signed) {
		int as = a.size(), bs = b.size();
		while (as > 0 && a[as - 1] == RTLIL::S0)
			as--;
		while (bs > 0 && b[bs - 1] == RTLIL::S0)
			bs--;
		msb_zeroes = std::max(0, y_width - (as + bs));
	}

	auto [id, y] = add_y_wire(y_width - msb_zeroes);
	Cell *cell = canvas->addCell(id, op);
	cell->setPort(RTLIL::ID::A, a);
	cell->setPort(RTLIL::ID::B, b);
	cell->setParam(RTLIL::ID::A_WIDTH, a.size());
	cell->setParam(RTLIL::ID::B_WIDTH, b.size());
	cell->setParam(RTLIL::ID::A_SIGNED, a_signed);
	cell->setParam(RTLIL::ID::B_SIGNED, b_signed);
	cell->setParam(RTLIL::ID::Y_WIDTH, y_width - msb_zeroes);
	cell->setPort(RTLIL::ID::Y, y);
	bless_cell(cell);
	return {SigSpec(RTLIL::S0, msb_zeroes), y};
}

SigSpec RTLILBuilder::Unop(IdString op, SigSpec a, bool a_signed, int y_width)
{
	if (a.is_fully_const()) {
#define OP(type)                                                                                   \
	if (op == ID($##type))                                                                         \
		return RTLIL::const_##type(a.as_const(), {}, a_signed, false, y_width);
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
	}

	auto [id, y] = add_y_wire(y_width);
	Cell *cell = canvas->addCell(id, op);
	cell->setPort(RTLIL::ID::A, a);
	cell->setParam(RTLIL::ID::A_WIDTH, a.size());
	cell->setParam(RTLIL::ID::A_SIGNED, a_signed);
	cell->setParam(RTLIL::ID::Y_WIDTH, y_width);
	cell->setPort(RTLIL::ID::Y, y);
	bless_cell(cell);
	return y;
}

void RTLILBuilder::connect(SigSpec lhs, SigSpec rhs)
{
	log_assert(lhs.size() == rhs.size());
	if (!lhs.empty()) {
		Cell *cell = canvas->addBuf(new_id(), rhs, lhs);
		bless_cell(cell);
	}
}

// Synthesizes two single-edge FFs (one posedge, one negedge) with the same D input,
// then uses a mux controlled by the clock to select the appropriate FF output.
void RTLILBuilder::add_dual_edge_aldff(const std::string &base_name, RTLIL::SigSpec clk,
		RTLIL::SigSpec aload, RTLIL::SigSpec d, RTLIL::SigSpec q, RTLIL::SigSpec ad,
		bool aload_polarity)
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

void RTLILBuilder::add_dff(std::string_view name, const RTLIL::SigSpec &clk,
		const RTLIL::SigSpec &d, const RTLIL::SigSpec &q, bool clk_polarity)
{
	RTLIL::Cell *cell = canvas->addDff(canvas->uniquify(id(name)), clk, d, q, clk_polarity);
	bless_cell(cell);
}

void RTLILBuilder::add_dffe(std::string_view name, const RTLIL::SigSpec &clk,
		const RTLIL::SigSpec &en, const RTLIL::SigSpec &d, const RTLIL::SigSpec &q,
		bool clk_polarity, bool en_polarity)
{
	RTLIL::Cell *cell =
			canvas->addDffe(canvas->uniquify(id(name)), clk, en, d, q, clk_polarity, en_polarity);
	bless_cell(cell);
}

void RTLILBuilder::add_aldff(std::string_view name, const RTLIL::SigSpec &clk,
		const RTLIL::SigSpec &aload, const RTLIL::SigSpec &d, const RTLIL::SigSpec &q,
		const RTLIL::SigSpec &ad, bool clk_polarity, bool aload_polarity)
{
	RTLIL::Cell *cell = canvas->addAldff(
			canvas->uniquify(id(name)), clk, aload, d, q, ad, clk_polarity, aload_polarity);
	bless_cell(cell);
}

SigSpec RTLILBuilder::CountOnes(SigSpec sig, int result_width)
{
	SigSpec ret;
	int x = 1, y = 0;
	auto width = sig.size();
	if (width == 0) {
		ret = RTLIL::Const(0, 1);
	} else if (width == 1) {
		// Single bit
		ret = sig;
	} else {
		// Build tree of adders
		std::vector<RTLIL::SigSpec> curr_level;
		for (int i = 0; i < width; i++) {
			RTLIL::SigSpec bit = sig[i];
			bit.extend_u0(result_width);
			curr_level.push_back(bit);
		}

		while (curr_level.size() > 1) {
			std::vector<RTLIL::SigSpec> nxt_level;
			for (size_t i = 0; i + 1 < curr_level.size(); i += 2) {
				auto sum = Biop(
						ID($add), curr_level[i], curr_level[i + 1], false, false, result_width);
				if (sum.size() < result_width)
					sum.extend_u0(result_width);
				nxt_level.push_back(sum);
			}
			if (curr_level.size() % 2 == 1) {
				nxt_level.push_back(curr_level.back());
			}
			curr_level = std::move(nxt_level);
		}
		ret = curr_level[0];
	}
	// Extend to expected type width
	ret.extend_u0(result_width);
	return ret;
}

SigSpec RTLILBuilder::Clog2(SigSpec sig, int result_width)
{
	int width = sig.size();

	if (width == 0)
		return RTLIL::Const(0, result_width);

	SigSpec n_minus_1 = Biop(ID($sub), sig, RTLIL::Const(1, width), false, false, width);

	SigSpec result = RTLIL::Const(0, result_width);
	for (int i = 0; i < width; i++)
		result = Mux(result, RTLIL::Const(i + 1, result_width), n_minus_1[i]);

	SigSpec n_not_zero = ReduceBool(sig);
	return Mux(RTLIL::Const(0, result_width), result, n_not_zero);
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
void RTLILBuilder::emit_meminit_cell(RTLIL::Memory *mem, uint64_t word_offset, bool big_endian,
		RTLIL::Const data, RTLIL::Const mask)
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
	cell->setPort(ID::DATA, big_endian ? reverse_data(data, mem->width) : data);
	cell->setPort(ID::EN, mask);
	bless_cell(cell);
}

void RTLILBuilder::add_memory_init(
		std::string_view name, uint64_t bit_offset, bool big_endian, RTLIL::Const data)
{
	if (data.empty())
		return;

	RTLIL::Memory *mem = canvas->memories.at(id(name));
	log_assert(mem);

	uint64_t processed = 0;

	using RTLIL::Const;
	using RTLIL::S0;
	using RTLIL::S1;
	using RTLIL::Sx;

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
				data.extract(processed, length), RTLIL::Const(S1, mem->width));
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

SigSpec RTLILBuilder::add_placeholder_signal(
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

}; // namespace slang_frontend

//
// Yosys slang frontend
//
// Copyright Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
#include <limits>

#include "slang_frontend.h"
#include "variables.h"
#include "backend_builder.h"

namespace slang_frontend {

ir::Net GraphBuilder::ReduceBool(ir::Value a)
{
	if (a.size() == 1)
		return a[0];

	bool seen_x = false, seen_nonconst = false;
	for (ir::Net bit : a) {
		if (!bit.is_const())
			seen_nonconst = true;
		else if (bit == ir::S1)
			return ir::S1;
		else if (bit == ir::Sx)
			seen_x = true;
	}

	if (!seen_nonconst)
		return seen_x ? ir::Sx : ir::S0;

	return Unop(ast::UnaryOperator::BitwiseOr, a, false, 1).as_net();
}

ir::Value GraphBuilder::Demux(ir::Value a, ir::Value s)
{
	log_assert(s.size() < 24);
	if (s.is_fully_const()) {
		ir::Value zeropad(ir::S0, a.size());
		int idx_const = s.as_const().as_int();
		return {zeropad.repeat((1 << s.size()) - 1 - idx_const), a, zeropad.repeat(idx_const)};
	}

	return backend->Demux(a, s);
}

ir::Net GraphBuilder::Le(ir::Value a, ir::Value b, bool is_signed)
{
	return Biop(ast::BinaryOperator::LessThanEqual, a, b, is_signed, is_signed, 1).as_net();
}

ir::Net GraphBuilder::Ge(ir::Value a, ir::Value b, bool is_signed)
{
	return Biop(ast::BinaryOperator::GreaterThanEqual, a, b, is_signed, is_signed, 1).as_net();
}

ir::Net GraphBuilder::Lt(ir::Value a, ir::Value b, bool is_signed)
{
	return Biop(ast::BinaryOperator::LessThan, a, b, is_signed, is_signed, 1).as_net();
}

ir::Net GraphBuilder::Eq(ir::Value a, ir::Value b)
{
	return Biop(ast::BinaryOperator::Equality, a, b, false, false, 1).as_net();
}

ir::Net GraphBuilder::LogicAnd(ir::Value a, ir::Value b)
{
	if (a.is_fully_zero() || b.is_fully_zero())
		return ir::S0;
	if (a.is_fully_ones() && b.size() == 1)
		return b.as_net();
	if (b.is_fully_ones() && a.size() == 1)
		return a.as_net();

	return Biop(ast::BinaryOperator::LogicalAnd, a, b, false, false, 1).as_net();
}

ir::Net GraphBuilder::LogicOr(ir::Value a, ir::Value b)
{
	if (a.is_fully_ones() || b.is_fully_ones())
		return ir::S1;
	if (a.is_fully_zero() && b.size() == 1)
		return b.as_net();
	if (b.is_fully_zero() && a.size() == 1)
		return a.as_net();

	return Biop(ast::BinaryOperator::LogicalOr, a, b, false, false, 1).as_net();
}

ir::Net GraphBuilder::LogicNot(ir::Value a)
{
	return Unop(ast::UnaryOperator::LogicalNot, a, false, 1).as_net();
}

ir::Value GraphBuilder::Mux(ir::Value a, ir::Value b, ir::Net s)
{
	log_assert(a.size() == b.size());
	if (a == b)
		return a;
	if (a == ir::S0 && b == ir::S1)
		return s;
	if (s == ir::S0)
		return a;
	if (s == ir::S1)
		return b;
	return backend->Mux(a, b, s);
}

ir::Value GraphBuilder::Bwmux(ir::Value a, ir::Value b, ir::Value s)
{
	log_assert(a.size() == b.size());
	log_assert(a.size() == s.size());
	if (s.is_fully_const()) {
		ir::Value result(ir::Sx, a.size());
		for (int i = 0; i < a.size(); i++) {
			if (s[i] == ir::S0)
				result[i] = a[i];
			else if (s[i] == ir::S1)
				result[i] = b[i];
		}
		return result;
	}

	return backend->Bwmux(a, b, s);
}

ir::Value GraphBuilder::Shift(ir::Value a, ir::Value b, bool b_signed, uint64_t result_width)
{
	if (b.is_fully_const() && b.size() < 32) {
		log_assert(!a.empty());
		int shift_amount = b.as_int(b_signed);
		ir::Value ret;
		int i, j;
		for (i = shift_amount, j = 0; j < result_width; i++, j++) {
			if (i >= a.size() || i < 0)
				ret.append(ir::S0);
			else
				ret.append(a[i]);
		}
		return ret;
	}

	return backend->Shift(a, b, b_signed, result_width);
}

ir::Value GraphBuilder::Shiftx(ir::Value a, ir::Value b, bool b_signed, uint64_t result_width)
{
	if (b.is_fully_const() && b.size() < 32) {
		log_assert(!a.empty());
		int shift_amount = b.as_int(b_signed);
		ir::Value ret;
		int i, j;
		for (i = shift_amount, j = 0; j < result_width; i++, j++) {
			if (i >= a.size() || i < 0)
				ret.append(ir::Sx);
			else
				ret.append(a[i]);
		}
		return ret;
	}

	return backend->Shiftx(a, b, b_signed, result_width);
}

ir::Value GraphBuilder::Neg(ir::Value a, bool signed_)
{
	return Unop(ast::UnaryOperator::Minus, a, signed_, a.width() + 1);
}

ir::Value GraphBuilder::Bmux(ir::Value a, ir::Value s)
{
	log_assert(a.size() % (1 << s.size()) == 0);
	log_assert(a.size() >= 1 << s.size());
	int stride = a.size() >> s.size();
	if (s.is_fully_def() && s.width() < 32) {
		return a.extract(s.as_const().as_int() * stride, stride);
	}
	return backend->Bmux(a, s);
}

ir::Value GraphBuilder::Not(ir::Value a)
{
	return Unop(ast::UnaryOperator::BitwiseNot, a, false, a.width());
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

int convert(ir::Net bit)
{
	if (bit == ir::S1)
		return 1;
	else if (bit == ir::S0)
		return -1;
	else
		return 0;
}
}; // namespace ThreeValued

ir::Value GraphBuilder::Biop(ast::BinaryOperator op, ir::Value a, ir::Value b, bool a_signed,
		bool b_signed, uint64_t y_width)
{
	if ((op == ast::BinaryOperator::GreaterThanEqual ||
		 op == ast::BinaryOperator::GreaterThan ||
		 op == ast::BinaryOperator::LessThanEqual ||
		 op == ast::BinaryOperator::LessThan) && !a.empty() && !b.empty()) {
		int carry = (op == ast::BinaryOperator::GreaterThanEqual || op == ast::BinaryOperator::LessThanEqual) ? -1 : 1;
		int al, bl;
		// Defer to three-valued evaluation over a representation of the operators.
		// This is a bit much, but I'm writing this tired and don't trust doing it
		// another way.
		int width = std::max(a.size(), b.size()) + 1;
		for (int i = 0; i < width; i++) {
			ir::Net abit = i < a.size() ? ir::Net(a[i]) : (a_signed ? a.msb() : ir::Net(ir::S0));
			ir::Net bbit = i < b.size() ? ir::Net(b[i]) : (b_signed ? b.msb() : ir::Net(ir::S0));
			al = ThreeValued::convert(abit);
			bl = ThreeValued::convert(bbit);
			if (op == ast::BinaryOperator::GreaterThanEqual || op == ast::BinaryOperator::GreaterThan)
				std::swap(al, bl);
			if (i != width - 1)
				carry = ThreeValued::CARRY(al, ThreeValued::NOT(bl), carry);
		}
		int result = ThreeValued::XOR(carry, ThreeValued::XNOR(al, bl));
		if (result < 0)
			return ir::Value(ir::S0, y_width);
		if (result > 0) {
			ir::Value ret(ir::S1);
			ret.extend_u0(y_width);
			return ret;
		}
	}

	if (op == ast::BinaryOperator::LogicalAnd) {
		if (a.is_fully_zero() || b.is_fully_zero())
			return ir::Value(ir::S0, y_width);
	}

	if (op == ast::BinaryOperator::LogicalOr) {
		// IMPROVEMENT: condition could be relaxed
		if ((a.is_fully_const() && a.as_bool()) || (b.is_fully_const() && b.as_bool())) {
			ir::Value ret(ir::S1);
			ret.extend_u0(y_width);
			return ret;
		}
	}

	uint64_t msb_zeroes = 0;
	if (op == ast::BinaryOperator::Multiply && !a_signed && !b_signed) {
		int as = a.size(), bs = b.size();
		while (as > 0 && a[as - 1] == ir::S0)
			as--;
		while (bs > 0 && b[bs - 1] == ir::S0)
			bs--;
		msb_zeroes = std::max<int>(0, ((int)y_width) - (as + bs));
	}

	return {ir::Value(ir::S0, msb_zeroes), backend->Biop(op, a, b, a_signed, b_signed, y_width - msb_zeroes)};
}

ir::Value GraphBuilder::Unop(ast::UnaryOperator op, ir::Value a, bool a_signed, uint64_t y_width)
{
	return backend->Unop(op, a, a_signed, y_width);
}

ir::Value GraphBuilder::CountOnes(ir::Value sig, int result_width)
{
	ir::Value ret;
	int x = 1, y = 0;
	auto width = sig.size();
	if (width == 0) {
		ret = ir::Value(0, 1);
	} else if (width == 1) {
		// Single bit
		ret = sig;
	} else {
		// Build tree of adders
		std::vector<ir::Value> curr_level;
		for (int i = 0; i < width; i++) {
			ir::Value bit = ir::Net(sig[i]);
			bit.extend_u0(result_width);
			curr_level.push_back(bit);
		}

		while (curr_level.size() > 1) {
			std::vector<ir::Value> nxt_level;
			for (size_t i = 0; i + 1 < curr_level.size(); i += 2) {
				auto sum = Biop(ast::BinaryOperator::Add, curr_level[i], curr_level[i + 1], false,
						false, result_width);
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

ir::Value GraphBuilder::add_placeholder_signal(uint64_t width, std::string_view name_suggestion, bool public_name)
{
	return backend->add_placeholder_signal(width, name_suggestion, public_name);
}

void GraphBuilder::connect(ir::Value target, ir::Value source)
{
	backend->connect(target, source);
}

void GraphBuilder::set_initialization(ir::Value signal, ir::Const init_value)
{
	backend->set_initialization(signal, init_value);
}

void GraphBuilder::add_memory_init(std::string_view name, uint64_t bit_offset,
								   bool big_endian, ir::Const data)
{
	backend->add_memory_init(name, bit_offset, big_endian, data);
}

void GraphBuilder::add_input(std::string_view name, ir::Value signal)
{
	backend->add_input(name, signal);
}

void GraphBuilder::add_output(std::string_view name, ir::Value signal)
{
	backend->add_output(name, signal);
}

void GraphBuilder::add_instance(std::string_view cell_type,
                                std::vector<BackendGraphBuilderBase::PortConnection> ports)
{
	backend->add_instance(cell_type, std::move(ports));
}

void GraphBuilder::add_dual_edge_aldff(const std::string &base_name, ir::Value clk,
									   ir::Value aload, ir::Value d, ir::Value q,
									   ir::Value ad, bool aload_polarity)
{
	backend->add_dual_edge_aldff(base_name, clk, aload, d, q, ad, aload_polarity);
}

void GraphBuilder::add_dff(std::string_view name, const ir::Value &clk, const ir::Value &d,
						   const ir::Value &q, bool clk_polarity)
{
	backend->add_dff(name, clk, d, q, clk_polarity);
}

void GraphBuilder::add_dffe(std::string_view name, const ir::Value &clk, const ir::Value &en,
							const ir::Value &d, const ir::Value &q, bool clk_polarity,
							bool en_polarity)
{
	backend->add_dffe(name, clk, en, d, q, clk_polarity, en_polarity);
}

void GraphBuilder::add_aldff(std::string_view name, const ir::Value &clk, const ir::Value &aload,
							 const ir::Value &d, const ir::Value &q, const ir::Value &ad,
							 bool clk_polarity, bool aload_polarity)
{
	backend->add_aldff(name, clk, aload, d, q, ad, clk_polarity, aload_polarity);
}

}; // namespace slang_frontend

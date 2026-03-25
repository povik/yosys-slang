//
// Yosys slang frontend
//
// Copyright Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
#include "slang/ast/expressions/SelectExpressions.h"
#include "slang/ast/types/Type.h"

// Fix for Yosys declaring ceil_log2 as both inline and non-inline
// but not defining the non-inline one; be sure to include utils.h
// with the inline definition to prevent linkage errors on some
// platforms
#include "kernel/utils.h"

#include "slang_frontend.h"
#include "variables.h"

namespace slang_frontend {

void AddressingResolver::interpret_index(ir::Value signal, int64_t width_down, int64_t width_up)
{
	if (range.isLittleEndian()) {
		base_offset = -range.right - width_down + 1;
		raw_signal = signal;
	} else {
		base_offset = range.right - width_up + 1;

		// We might want some other handling of big-endian
		// indexing.
		raw_signal = netlist.Not(signal);
		base_offset += 1;
	}
}

AddressingResolver::AddressingResolver(EvalContext &eval, const ast::ElementSelectExpression &sel)
	: expr(sel), eval(eval), netlist(eval.netlist)
{
	require(sel, sel.value().type->hasFixedRange());
	range = sel.value().type->getFixedRange();
	interpret_index(eval.eval_signed(sel.selector()));

	stride = sel.type->getBitstreamWidth();
}

AddressingResolver::AddressingResolver(EvalContext &eval, const ast::RangeSelectExpression &sel)
	: expr(sel), eval(eval), netlist(eval.netlist)
{
	require(sel, sel.value().type->hasFixedRange());
	range = sel.value().type->getFixedRange();

	switch (sel.getSelectionKind()) {
	case ast::RangeSelectionKind::Simple: {
		auto lv = sel.left().eval(eval.const_), rv = sel.right().eval(eval.const_);
		ast_invariant(sel, lv.isInteger() && rv.isInteger());
		raw_signal = {ir::S0};

		if (range.isLittleEndian())
			base_offset = rv.integer().as<int64_t>().value() - range.right;
		else
			base_offset = range.right - rv.integer().as<int64_t>().value();
	} break;
	case ast::RangeSelectionKind::IndexedUp: {
		ir::Value signal = eval.eval_signed(sel.left());
		auto rv = sel.right().eval(eval.const_);
		ast_invariant(sel, rv.isInteger());
		interpret_index(signal, 1, rv.integer().as<int64_t>().value());
	} break;
	case ast::RangeSelectionKind::IndexedDown: {
		ir::Value signal = eval.eval_signed(sel.left());
		auto rv = sel.right().eval(eval.const_);
		ast_invariant(sel, rv.isInteger());
		interpret_index(signal, rv.integer().as<int64_t>().value(), 1);
	} break;
	}

	if (sel.value().type->isArray())
		stride = sel.value().type->getArrayElementType()->getBitstreamWidth();
	else
		stride = 1;
}

ir::Value AddressingResolver::shift_up_bitwise(ir::Value val, bool oor_undef, uint64_t output_len)
{
	uint64_t shifted_len = output_len;
	ir::Value val2 = val, shifted;

	if (base_offset > 0) {
		ir::Value padding(oor_undef ? ir::Sx : ir::S0, (uint64_t)base_offset);
		val2 = {val, padding};
	} else if (base_offset < 0) {
		shifted_len += -base_offset;
	}

	if (oor_undef)
		shifted = netlist.Shiftx(val2, netlist.Neg(raw_signal, true), true, shifted_len);
	else
		shifted = netlist.Shift(val2, false, netlist.Neg(raw_signal, true), true, shifted_len);

	if (base_offset < 0)
		return shifted.extract_end(-base_offset);
	else
		return shifted;
}

ir::Value AddressingResolver::shift_up(ir::Value val, bool oor_undef, uint64_t output_len)
{
	if (raw_signal.is_fully_def()) {
		return embed(val, output_len, stride, oor_undef ? ir::Sx : ir::S0);
	} else if (stride == 1) {
		return shift_up_bitwise(val, oor_undef, output_len);
	} else {
		ir::Value ret(ir::Sx, output_len);
		std::vector<bool> written(output_len, false);

		for (uint64_t i = 0; i < stride; i++) {
			ir::Value fin, fout;

			for (uint64_t j = i; j < val.size(); j += stride)
				fin.append(val[j]);

			fout = shift_up_bitwise(fin, oor_undef, (output_len - i + stride - 1) / stride);
			for (uint64_t j = 0; j < fout.size(); j++) {
				ret[j * stride + i] = fout[j];
				written[j * stride + i] = true;
			}
		}

		for (size_t i = 0; i < written.size(); i++) {
			log_assert(written[i]);
		}

		return ret;
	}
}

template <> VariableBits AddressingResolver::extract<VariableBits>(VariableBits val, uint64_t width)
{
	ast_invariant(expr, raw_signal.is_fully_def());
	int64_t iwidth = (int64_t)width;
	int64_t offset = raw_signal.as_const().as_int(true) + base_offset;
	int64_t valsize = (int64_t)val.bitwidth();

	VariableBits ret;
	ret.append(Variable::dummy(std::clamp<int64_t>(-offset * stride, 0, iwidth)));
	int64_t start = std::clamp<int64_t>(offset * stride, 0, valsize);
	int64_t end = std::clamp<int64_t>(offset * stride + iwidth, 0, valsize);
	ret.append(val.extract(start, end - start));
	ret.append(
			Variable::dummy(std::clamp<int64_t>(iwidth - (-offset * stride + valsize), 0, iwidth)));
	log_assert(ret.bitwidth() == width);

	return ret;
}

template <> ir::Value AddressingResolver::extract<ir::Value>(ir::Value val, uint64_t width)
{
	ast_invariant(expr, raw_signal.is_fully_def());
	int64_t iwidth = (int64_t)width;
	int64_t offset = raw_signal.as_const().as_int(true) + base_offset;
	int64_t valsize = (int64_t)val.size();

	ir::Value ret;
	ret.append(ir::Value(ir::Sx, (uint64_t)std::clamp<int64_t>(-offset * stride, 0, iwidth)));
	int64_t start = std::clamp<int64_t>(offset * stride, 0, valsize);
	int64_t end = std::clamp<int64_t>(offset * stride + iwidth, 0, valsize);
	ret.append(val.extract((uint64_t)start, (uint64_t)(end - start)));
	ret.append(ir::Value(ir::Sx,
			(uint64_t)std::clamp<int64_t>(iwidth - (-offset * stride + valsize), 0, iwidth)));
	log_assert((int64_t)ret.size() == iwidth);

	return ret;
}

static ir::Value sign_extend(const ir::Value &value, uint64_t target_width)
{
	if (value.empty())
		return ir::Value(ir::S0, target_width);
	else if (value.width() < target_width)
		return {value.msb().repeat(target_width - value.width()), value};
	else
		return value.extract(0, target_width);
}

ir::Value AddressingResolver::raw_demux(ir::Value val, int64_t from, int64_t to)
{
	log_assert(val.width() == stride);
	ir::Value negative, positive;

	if (from < 0) {
		// Build the negative branch
		uint64_t demux_size = std::bit_ceil((uint64_t)-from);
		uint64_t sel_size = ceil_log2(demux_size);

		ir::Value sel = sign_extend(raw_signal, sel_size);

		// check `raw_signal` is in between -2**sel_size...0
		// which is where the demuxing is valid
		ir::Net valid = netlist.LogicAnd(
				netlist.Ge(raw_signal, {ir::S1, ir::Value(ir::S0, sel_size)}, true),
				netlist.Lt(raw_signal, {ir::S0}, true));

		ir::Value val_gated = netlist.Mux(ir::Value(ir::S0, stride), val, valid);

		negative = netlist.Demux(val_gated, sel).extract_end((stride << sel_size) + from * stride);
		log_assert(negative.width() == (uint64_t)(-from * stride));
	}

	if (to > 0) {
		// Build the nonnegative branch
		uint64_t demux_size = std::bit_ceil((unsigned int)to);
		uint64_t sel_size = ceil_log2(demux_size);

		ir::Value sel = sign_extend(raw_signal, sel_size);

		// check `raw_signal` is in between 0...2**sel_size
		// which is where the demuxing is valid
		ir::Net valid = netlist.LogicAnd(netlist.Ge(raw_signal, {ir::S0}, true),
				netlist.Lt(raw_signal, {ir::S0, ir::S1, ir::Value(ir::S0, sel_size)}, true));

		ir::Value val_gated = netlist.Mux(ir::Value(ir::S0, stride), val, valid);

		ir::Value demux_result = netlist.Demux(val_gated, sel);

		positive = netlist.Demux(val_gated, sel).extract(0, to * stride);
		log_assert(positive.width() == (uint64_t)(to * stride));
	}

	return {positive, negative};
}

ir::Value AddressingResolver::demux(ir::Value val, uint64_t output_len)
{
	log_assert(val.size() == (uint64_t)stride);
	log_assert(output_len % stride == 0);
	ir::Value demuxed = raw_demux(val, -std::max<int64_t>(0, base_offset),
			std::max<int64_t>(0, ((int64_t)output_len / stride) - base_offset));

	return demuxed.extract(std::max<int64_t>(0, -stride * base_offset), output_len);
}

ir::Value AddressingResolver::raw_mux(ir::Value val, int64_t from, int64_t to, uint64_t stride)
{
	log_assert(stride * (to - from) == (int)val.size());
	ir::Value negative(ir::Sx, stride), positive(ir::Sx, stride);

	if (from < 0) {
		// Build the negative branch
		uint64_t mux_size = std::bit_ceil((unsigned int)-from);
		uint64_t sel_size = ceil_log2(mux_size);

		ir::Value val_cut = val.extract(0, -from * stride);
		ir::Value val_padded = {
				val_cut, ir::Value(ir::Sx, (1 << sel_size) * stride - (int)val_cut.size())};

		ir::Value sel = sign_extend(raw_signal, sel_size);
		ir::Net valid = netlist.Ge(raw_signal, {ir::S1, ir::Value(ir::S0, sel_size)}, true);
		negative = netlist.Mux(ir::Value(ir::Sx, stride), netlist.Bmux(val_padded, sel), valid);
	}

	if (to > 0) {
		// Build the positive branch
		uint64_t mux_size = std::bit_ceil((unsigned int)to);
		uint64_t sel_size = ceil_log2(mux_size);

		ir::Value val_cut = val.extract_end(-from * stride);
		ir::Value val_padded = {
				ir::Value(ir::Sx, (1 << sel_size) * stride - (int)val_cut.size()), val_cut};

		ir::Value sel = sign_extend(raw_signal, sel_size);
		ir::Net valid = netlist.Lt(raw_signal, {ir::S0, ir::S1, ir::Value(ir::S0, sel_size)}, true);

		positive = netlist.Mux(ir::Value(ir::Sx, stride), netlist.Bmux(val_padded, sel), valid);
	}

	return netlist.Mux(positive, negative, raw_signal.msb());
}

ir::Value AddressingResolver::mux(ir::Value val, uint64_t output_len)
{
	log_assert(output_len == stride);
	log_assert(val.width() % stride == 0);
	return raw_mux(
			{ir::Value(ir::Sx, std::max<int64_t>(0, base_offset * stride - (int64_t)val.width())),
					val, ir::Value(ir::Sx, std::max<int64_t>(0, stride * -base_offset))},
			-std::max<int64_t>(0, base_offset),
			std::max<int64_t>(0, -base_offset + ((int64_t)(val.width() / stride))), output_len);
}

ir::Value AddressingResolver::shift_down_bitwise(ir::Value val, uint64_t output_len)
{
	uint64_t shifted_len = output_len;
	ir::Value val2 = val, shifted;

	if (base_offset > 0)
		shifted_len += base_offset;
	else if (base_offset < 0)
		val2 = {val, ir::Value(ir::Sx, -base_offset)};

	shifted = netlist.Shiftx(val2, raw_signal, true, shifted_len);

	if (base_offset > 0)
		return shifted.extract_end(base_offset);
	else
		return shifted;
}

ir::Value AddressingResolver::shift_down(ir::Value val, uint64_t output_len)
{
	if (raw_signal.is_fully_def()) {
		return extract(val, output_len);
	} else if (stride == 1) {
		return shift_down_bitwise(val, output_len);
	} else {
		ir::Value ret(ir::Sx, output_len);
		std::vector<bool> written(output_len, false);

		for (int64_t i = 0; i < stride; i++) {
			ir::Value fin, fout;

			for (int64_t j = i; j < val.width(); j += stride)
				fin.append(val[j]);

			fout = shift_down_bitwise(fin, ((int64_t)output_len - i + stride - 1) / stride);
			for (uint64_t j = 0; j < fout.width(); j++) {
				ret[j * stride + i] = fout[j];
				written[j * stride + i] = true;
			}
		}

		for (size_t i = 0; i < ret.width(); i++)
			log_assert(written[i]);

		return ret;
	}
}

ir::Value AddressingResolver::embed(
		ir::Value val, uint64_t output_len, int64_t stride, ir::Trit padding)
{
	ast_invariant(expr, raw_signal.is_fully_def());
	int64_t offset = raw_signal.as_const().as_int(true) + base_offset;

	ir::Value ret;
	ret.append(ir::Value(ir::Trit(padding), std::clamp<int64_t>(offset * stride, 0, output_len)));
	int64_t start = std::clamp<int64_t>(-offset * stride, 0, val.size());
	int64_t end = std::clamp<int64_t>(-offset * stride + output_len, 0, val.size());
	ret.append(val.extract(start, end - start));
	ret.append(ir::Value(ir::Trit(padding),
			std::clamp<int64_t>(
					(int64_t)output_len - offset * stride - (int64_t)val.size(), 0, output_len)));
	log_assert(ret.size() == (uint64_t)output_len);

	return ret;
}

bool AddressingResolver::is_static()
{
	return raw_signal.is_fully_def();
}

}; // namespace slang_frontend

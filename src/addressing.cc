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

void AddressingResolver::interpret_index(RTLIL::SigSpec signal, int width_down, int width_up)
{
	if (range.isLittleEndian()) {
		base_offset = -range.right - width_down + 1;
		raw_signal = signal;
	} else {
		base_offset = range.right - width_up + 1;

		// Sign-extend signal by one bit before inverting. This correctly
		// maps big-endian index i to physical position (range.right - i):
		//   Not(sign_ext(i)) + (range.right + 1) == (-i - 1) + (range.right + 1) == range.right - i.
		// Sign-extension (not zero-extension) is required so that the identity
		// holds for negative indices (e.g. logic [-7:-2]).
		raw_signal = netlist.Not(RTLIL::SigSpec({signal.msb(), signal}));
		base_offset += 1;
	}
}

AddressingResolver::AddressingResolver(EvalContext &eval, const ast::ElementSelectExpression &sel)
	: expr(sel), eval(eval), netlist(eval.netlist)
{
	require(sel, sel.value().type->hasFixedRange());
	range = sel.value().type->getFixedRange();
	// For unpacked arrays, elements are stored sequentially by logical index
	// regardless of the declared range direction.  Normalise big-endian ranges
	// to little-endian so that interpret_index maps element[i] directly to
	// physical position (i - range.lower()), consistent with the memory-inferred path.
	if (sel.value().type->isUnpackedArray() && !range.isLittleEndian())
		range = {(int32_t)range.upper(), (int32_t)range.lower()};
	interpret_index(eval.eval_signed(sel.selector()));

	stride = sel.type->getBitstreamWidth();
}

AddressingResolver::AddressingResolver(EvalContext &eval, const ast::RangeSelectExpression &sel)
	: expr(sel), eval(eval), netlist(eval.netlist)
{
	require(sel, sel.value().type->hasFixedRange());
	range = sel.value().type->getFixedRange();
	// For unpacked arrays, normalise big-endian ranges to little-endian
	// so that element indexing is consistent with the memory-inferred path.
	if (sel.value().type->isUnpackedArray() && !range.isLittleEndian())
		range = {(int32_t)range.upper(), (int32_t)range.lower()};

	switch (sel.getSelectionKind()) {
	case ast::RangeSelectionKind::Simple: {
		auto lv = sel.left().eval(eval.const_), rv = sel.right().eval(eval.const_);
		ast_invariant(sel, lv.isInteger() && rv.isInteger());
		raw_signal = {RTLIL::S0};

		if (range.isLittleEndian())
			base_offset = rv.integer().as<int>().value() - range.right;
		else
			base_offset = range.right - rv.integer().as<int>().value();
	} break;
	case ast::RangeSelectionKind::IndexedUp: {
		RTLIL::SigSpec signal = eval.eval_signed(sel.left());
		auto rv = sel.right().eval(eval.const_);
		ast_invariant(sel, rv.isInteger());
		interpret_index(signal, 1, rv.integer().as<int>().value());
	} break;
	case ast::RangeSelectionKind::IndexedDown: {
		RTLIL::SigSpec signal = eval.eval_signed(sel.left());
		auto rv = sel.right().eval(eval.const_);
		ast_invariant(sel, rv.isInteger());
		interpret_index(signal, rv.integer().as<int>().value(), 1);
	} break;
	}

	if (sel.value().type->isArray())
		stride = sel.value().type->getArrayElementType()->getBitstreamWidth();
	else
		stride = 1;
}

RTLIL::SigSpec AddressingResolver::shift_up_bitwise(
		RTLIL::SigSpec val, bool oor_undef, int output_len)
{
	int shifted_len = output_len;
	RTLIL::SigSpec val2 = val, shifted;

	if (base_offset > 0) {
		RTLIL::SigSpec padding(oor_undef ? RTLIL::Sx : RTLIL::S0, base_offset);
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

RTLIL::SigSpec AddressingResolver::shift_up(RTLIL::SigSpec val, bool oor_undef, int output_len)
{
	if (raw_signal.is_fully_def()) {
		return embed(val, output_len, stride, oor_undef ? RTLIL::Sx : RTLIL::S0);
	} else if (stride == 1) {
		return shift_up_bitwise(val, oor_undef, output_len);
	} else {
		RTLIL::SigSpec ret(RTLIL::Sm, output_len);

		for (int i = 0; i < stride; i++) {
			RTLIL::SigSpec fin, fout;

			for (int j = i; j < val.size(); j += stride)
				fin.append(val[j]);

			fout = shift_up_bitwise(fin, oor_undef, (output_len - i + stride - 1) / stride);
			for (int j = 0; j < fout.size(); j++)
				ret[j * stride + i] = fout[j];
		}

		for (auto bit : ret)
			log_assert(bit != RTLIL::Sm);

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
	ret.append(Variable::dummy(std::clamp<int64_t>(iwidth - (-offset * stride + valsize), 0, iwidth)));
	log_assert(ret.bitwidth() == width);

	return ret;
}

template <>
RTLIL::SigSpec AddressingResolver::extract<RTLIL::SigSpec>(RTLIL::SigSpec val, uint64_t width)
{
	ast_invariant(expr, raw_signal.is_fully_def());
	int64_t iwidth = (int64_t)width;
	int64_t offset = raw_signal.as_const().as_int(true) + base_offset;
	int64_t valsize = (int64_t)val.size();

	RTLIL::SigSpec ret;
	ret.append(RTLIL::SigSpec(RTLIL::Sx, (int)std::clamp<int64_t>(-offset * stride, 0, iwidth)));
	int64_t start = std::clamp<int64_t>(offset * stride, 0, valsize);
	int64_t end = std::clamp<int64_t>(offset * stride + iwidth, 0, valsize);
	ret.append(val.extract((int)start, (int)(end - start)));
	ret.append(RTLIL::SigSpec(
			RTLIL::Sx, (int)std::clamp<int64_t>(iwidth - (-offset * stride + valsize), 0, iwidth)));
	log_assert((int64_t)ret.size() == iwidth);

	return ret;
}

RTLIL::SigSpec AddressingResolver::raw_demux(RTLIL::SigSpec val, int from, int to)
{
	log_assert(val.size() == stride);
	RTLIL::SigSpec negative, positive;

	if (from < 0) {
		// Build the negative branch
		int demux_size = std::bit_ceil((unsigned int)-from);
		int sel_size = ceil_log2(demux_size);

		RTLIL::SigSpec sel = raw_signal;
		sel.extend_u0(sel_size, true);

		// check `raw_signal` is in between -2**sel_size...0
		// which is where the demuxing is valid
		RTLIL::SigSpec valid = netlist.LogicAnd(
				netlist.Ge(raw_signal, {RTLIL::S1, RTLIL::SigSpec(RTLIL::S0, sel_size)}, true),
				netlist.Lt(raw_signal, {RTLIL::S0}, true));

		RTLIL::SigSpec val_gated = netlist.Mux(RTLIL::SigSpec(RTLIL::S0, stride), val, valid);

		negative = netlist.Demux(val_gated, sel).extract_end((stride << sel_size) + from * stride);
		log_assert(negative.size() == -from * stride);
	}

	if (to > 0) {
		// Build the nonnegative branch
		int demux_size = std::bit_ceil((unsigned int)to);
		int sel_size = ceil_log2(demux_size);

		RTLIL::SigSpec sel = raw_signal;
		sel.extend_u0(sel_size, true);

		// check `raw_signal` is in between 0...2**sel_size
		// which is where the demuxing is valid
		RTLIL::SigSpec valid = netlist.LogicAnd(netlist.Ge(raw_signal, {RTLIL::S0}, true),
				netlist.Lt(raw_signal, {RTLIL::S0, RTLIL::S1, RTLIL::SigSpec(RTLIL::S0, sel_size)},
						true));

		RTLIL::SigSpec val_gated = netlist.Mux(RTLIL::SigSpec(RTLIL::S0, stride), val, valid);

		RTLIL::SigSpec demux_result = netlist.Demux(val_gated, sel);

		positive = netlist.Demux(val_gated, sel).extract(0, to * stride);
		log_assert(positive.size() == to * stride);
	}

	return {positive, negative};
}

RTLIL::SigSpec AddressingResolver::demux(RTLIL::SigSpec val, int output_len)
{
	log_assert(val.size() == stride);
	log_assert(output_len % stride == 0);
	RTLIL::SigSpec demuxed = raw_demux(
			val, -std::max(0, base_offset), std::max(0, output_len / stride - base_offset));

	return demuxed.extract(std::max(0, -stride * base_offset), output_len);
}

RTLIL::SigSpec AddressingResolver::raw_mux(RTLIL::SigSpec val, int from, int to, int stride)
{
	log_assert(stride * (to - from) == val.size());
	RTLIL::SigSpec negative(RTLIL::Sx, stride), positive(RTLIL::Sx, stride);

	if (from < 0) {
		// Build the negative branch
		int mux_size = std::bit_ceil((unsigned int)-from);
		int sel_size = ceil_log2(mux_size);

		RTLIL::SigSpec val_cut = val.extract(0, -from * stride);
		RTLIL::SigSpec val_padded = {
				val_cut, RTLIL::SigSpec(RTLIL::Sx, (1 << sel_size) * stride - val_cut.size())};

		RTLIL::SigSpec sel = raw_signal;
		sel.extend_u0(sel_size, true);
		RTLIL::SigSpec valid =
				netlist.Ge(raw_signal, {RTLIL::S1, RTLIL::SigSpec(RTLIL::S0, sel_size)}, true);
		negative = netlist.Mux(
				RTLIL::SigSpec(RTLIL::Sx, stride), netlist.Bmux(val_padded, sel), valid);
	}

	if (to > 0) {
		// Build the positive branch
		int mux_size = std::bit_ceil((unsigned int)to);
		int sel_size = ceil_log2(mux_size);

		RTLIL::SigSpec val_cut = val.extract_end(-from * stride);
		RTLIL::SigSpec val_padded = {
				RTLIL::SigSpec(RTLIL::Sx, (1 << sel_size) * stride - val_cut.size()), val_cut};

		RTLIL::SigSpec sel = raw_signal;
		sel.extend_u0(sel_size, true);
		RTLIL::SigSpec valid = netlist.Lt(
				raw_signal, {RTLIL::S0, RTLIL::S1, RTLIL::SigSpec(RTLIL::S0, sel_size)}, true);

		positive = netlist.Mux(
				RTLIL::SigSpec(RTLIL::Sx, stride), netlist.Bmux(val_padded, sel), valid);
	}

	return netlist.Mux(positive, negative, raw_signal.msb());
}

RTLIL::SigSpec AddressingResolver::mux(RTLIL::SigSpec val, int output_len)
{
	log_assert(output_len == stride);
	log_assert(val.size() % stride == 0);
	return raw_mux({RTLIL::SigSpec(RTLIL::Sx, std::max(0, base_offset * stride - val.size())), val,
						   RTLIL::SigSpec(RTLIL::Sx, std::max(0, stride * -base_offset))},
			-std::max(0, base_offset), std::max(0, -base_offset + val.size() / stride), output_len);
}

RTLIL::SigSpec AddressingResolver::shift_down_bitwise(RTLIL::SigSpec val, int output_len)
{
	int shifted_len = output_len;
	RTLIL::SigSpec val2 = val, shifted;

	if (base_offset > 0)
		shifted_len += base_offset;
	else if (base_offset < 0)
		val2 = {val, RTLIL::SigSpec(RTLIL::Sx, -base_offset)};

	shifted = netlist.Shiftx(val2, raw_signal, true, shifted_len);

	if (base_offset > 0)
		return shifted.extract_end(base_offset);
	else
		return shifted;
}

RTLIL::SigSpec AddressingResolver::shift_down(RTLIL::SigSpec val, int output_len)
{
	if (raw_signal.is_fully_def()) {
		return extract(val, output_len);
	} else if (stride == 1) {
		return shift_down_bitwise(val, output_len);
	} else {
		RTLIL::SigSpec ret(RTLIL::Sm, output_len);

		for (int i = 0; i < stride; i++) {
			RTLIL::SigSpec fin, fout;

			for (int j = i; j < val.size(); j += stride)
				fin.append(val[j]);

			fout = shift_down_bitwise(fin, (output_len - i + stride - 1) / stride);
			for (int j = 0; j < fout.size(); j++)
				ret[j * stride + i] = fout[j];
		}

		for (auto bit : ret)
			log_assert(bit != RTLIL::Sm);

		return ret;
	}
}

RTLIL::SigSpec AddressingResolver::embed(
		RTLIL::SigSpec val, int output_len, int stride, RTLIL::State padding)
{
	ast_invariant(expr, raw_signal.is_fully_def());
	int offset = raw_signal.as_const().as_int(true) + base_offset;

	RTLIL::SigSpec ret;
	ret.append(RTLIL::SigSpec(padding, std::clamp(offset * stride, 0, output_len)));
	int start = std::clamp(-offset * stride, 0, val.size());
	int end = std::clamp(-offset * stride + output_len, 0, val.size());
	ret.append(val.extract(start, end - start));
	ret.append(RTLIL::SigSpec(
			padding, std::clamp(output_len - offset * stride - val.size(), 0, output_len)));
	log_assert(ret.size() == output_len);

	return ret;
}

bool AddressingResolver::is_static()
{
	return raw_signal.is_fully_def();
}

}; // namespace slang_frontend

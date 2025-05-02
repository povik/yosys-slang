//
// Yosys slang frontend
//
// Copyright 2025 Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
#include "slang/ast/expressions/SelectExpressions.h"
#include "slang/ast/types/Type.h"

#include "addressing.h"
#include "slang_frontend.h"
#include "variables.h"

namespace slang_frontend {

template <> RTLIL::SigSpec Addressing<RTLIL::SigSpec>::extract(RTLIL::SigSpec val, int width)
{
	using Signal = RTLIL::SigSpec;

	ast_invariant(expr, raw_signal.is_fully_def());
	int offset = raw_signal.as_const().as_int(true) + base_offset;

	Signal ret;
	ret.append(Signal(RTLIL::Sx, std::clamp(-offset * stride, 0, width)));
	int start = std::clamp(offset * stride, 0, val.size());
	int end = std::clamp(offset * stride + width, 0, val.size());
	ret.append(val.extract(start, end - start));
	ret.append(Signal(RTLIL::Sx, std::clamp(width - (-offset * stride + val.size()), 0, width)));
	log_assert(ret.size() == width);

	return ret;
}

template <> VariableBits Addressing<VariableBits>::extract(VariableBits val, int width)
{
	using Signal = VariableBits;

	ast_invariant(expr, raw_signal.is_fully_def());
	int offset = raw_signal.as_const().as_int(true) + base_offset;

	Signal ret;
	ret.append(Variable::dummy(std::clamp(-offset * stride, 0, width)));
	int start = std::clamp(offset * stride, 0, (int)val.size());
	int end = std::clamp(offset * stride + width, 0, (int)val.size());
	ret.append(val.extract(start, end - start));
	ret.append(Variable::dummy(std::clamp(width - (-offset * stride + (int)val.size()), 0, width)));
	log_assert(ret.size() == width);

	return ret;
}

}; // namespace slang_frontend

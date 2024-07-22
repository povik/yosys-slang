//
// Yosys slang frontend
//
// Copyright 2024 Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
#include "slang_frontend.h"

inline namespace slang_frontend {

using RTLIL::Cell;
using RTLIL::IdString;
using RTLIL::SigSpec;

SigSpec RTLILBuilder::ReduceBool(SigSpec a) {
	if (a.is_fully_const())
		return RTLIL::const_reduce_bool(a.as_const(), RTLIL::Const(), false, false, 1);
	return canvas->ReduceBool(NEW_ID, a, false);
}

SigSpec RTLILBuilder::Sub(SigSpec a, SigSpec b, bool is_signed) {
	if (b.is_fully_ones())
		return a;
	if (a.is_fully_const() && b.is_fully_const())
		return RTLIL::const_sub(a.as_const(), b.as_const(), is_signed, is_signed,
								std::max(a.size(), b.size()) + 1);
	return canvas->Sub(NEW_ID, a, b, is_signed);
}

SigSpec RTLILBuilder::Demux(SigSpec a, SigSpec s) {
	log_assert(s.size() < 24);
	SigSpec zeropad(RTLIL::S0, a.size());
	if (s.is_fully_const()) {
		int idx_const = s.as_const().as_int();
		return {zeropad.repeat((1 << s.size()) - 1 - idx_const),
					a, zeropad.repeat(idx_const)};
	}
	return canvas->Demux(NEW_ID, a, s);
}

SigSpec RTLILBuilder::Le(SigSpec a, SigSpec b, bool is_signed) {
	if (a.is_fully_const() && b.is_fully_const())
		return RTLIL::const_le(a.as_const(), b.as_const(), is_signed, is_signed, 1);
	return canvas->Le(NEW_ID, a, b, is_signed);
}

SigSpec RTLILBuilder::Ge(SigSpec a, SigSpec b, bool is_signed) {
	if (a.is_fully_const() && b.is_fully_const())
		return RTLIL::const_ge(a.as_const(), b.as_const(), is_signed, is_signed, 1);
	return canvas->Ge(NEW_ID, a, b, is_signed);
}

SigSpec RTLILBuilder::Lt(SigSpec a, SigSpec b, bool is_signed) {
	if (a.is_fully_const() && b.is_fully_const())
		return RTLIL::const_lt(a.as_const(), b.as_const(), is_signed, is_signed, 1);
	return canvas->Lt(NEW_ID, a, b, is_signed);
}

SigSpec RTLILBuilder::Eq(SigSpec a, SigSpec b) {
	if (a.is_fully_const() && b.is_fully_const())
		return RTLIL::const_eq(a.as_const(), b.as_const(), false, false, 1);
	return canvas->Eq(NEW_ID, a, b);
}

SigSpec RTLILBuilder::EqWildcard(SigSpec a, SigSpec b) {
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
	return canvas->Eq(NEW_ID, a, b);
}

SigSpec RTLILBuilder::LogicAnd(SigSpec a, SigSpec b) {
	if (a.is_fully_zero() || b.is_fully_zero())
		return RTLIL::Const(0, 1);
	if (a.is_fully_def() && b.size() == 1)
		return b;
	if (b.is_fully_def() && a.size() == 1)
		return a;
	return canvas->LogicAnd(NEW_ID, a, b);
}

SigSpec RTLILBuilder::LogicNot(SigSpec a) {
	return canvas->LogicNot(NEW_ID, a);
}

SigSpec RTLILBuilder::Mux(SigSpec a, SigSpec b, SigSpec s) {
	log_assert(a.size() == b.size());
	log_assert(s.size() == 1);
	if (s[0] == RTLIL::S0)
		return a;
	if (s[0] == RTLIL::S1)
		return b;
	return canvas->Mux(NEW_ID, a, b, s);
}

SigSpec RTLILBuilder::Bwmux(SigSpec a, SigSpec b, SigSpec s) {
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
	return canvas->Bwmux(NEW_ID, a, b, s);
}

SigSpec RTLILBuilder::Shift(SigSpec a, bool a_signed, SigSpec s,
							bool s_signed, int result_width)
{
	SigSpec y = canvas->addWire(NEW_ID, result_width);
	Cell *cell = canvas->addCell(NEW_ID, ID($shift));
	cell->parameters[Yosys::ID::A_SIGNED] = a_signed;
	cell->parameters[Yosys::ID::B_SIGNED] = s_signed;
	cell->parameters[Yosys::ID::A_WIDTH] = a.size();
	cell->parameters[Yosys::ID::B_WIDTH] = s.size();
	cell->parameters[Yosys::ID::Y_WIDTH] = y.size();
	cell->setPort(Yosys::ID::A, a);
	cell->setPort(Yosys::ID::B, s);
	cell->setPort(Yosys::ID::Y, y);
	return y;
}

SigSpec RTLILBuilder::Shiftx(SigSpec a, SigSpec s,
							 bool s_signed, int result_width)
{
	SigSpec y = canvas->addWire(NEW_ID, result_width);
	canvas->addShiftx(NEW_ID, a, s, y, s_signed);
	return y;
}

SigSpec RTLILBuilder::Neg(SigSpec a, bool signed_)
{
	SigSpec y = canvas->addWire(NEW_ID, a.size() + 1);
	canvas->addNeg(NEW_ID, a, y, signed_);
	return y;
}

SigSpec RTLILBuilder::Bmux(SigSpec a, SigSpec s) {
	log_assert(a.size() % (1 << s.size()) == 0);
	log_assert(a.size() >= 1 << s.size());
	int stride = a.size() >> s.size();
	if (s.is_fully_def()) {
		return a.extract(s.as_const().as_int() * stride, stride);
	}
	return canvas->Bmux(NEW_ID, a, s);
}

SigSpec RTLILBuilder::Not(SigSpec a)
{
	return canvas->Not(NEW_ID, a);
}

};

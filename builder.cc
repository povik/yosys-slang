//
// Yosys slang frontend
//
// Copyright 2024 Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
#include "slang_frontend.h"

inline namespace slang_frontend {

RTLIL::SigSpec RTLILBuilder::ReduceBool(RTLIL::SigSpec a) {
	if (a.is_fully_const())
		return RTLIL::const_reduce_bool(a.as_const(), RTLIL::Const(), false, false, 1);
	return canvas->ReduceBool(NEW_ID, a, false);
}

RTLIL::SigSpec RTLILBuilder::Sub(RTLIL::SigSpec a, RTLIL::SigSpec b, bool is_signed) {
	if (b.is_fully_ones())
		return a;
	if (a.is_fully_const() && b.is_fully_const())
		return RTLIL::const_sub(a.as_const(), b.as_const(), is_signed, is_signed,
								std::max(a.size(), b.size()) + 1);
	return canvas->Sub(NEW_ID, a, b, is_signed);
}

RTLIL::SigSpec RTLILBuilder::Demux(RTLIL::SigSpec a, RTLIL::SigSpec s) {
	log_assert(s.size() < 24);
	RTLIL::SigSpec zeropad(RTLIL::S0, a.size());
	if (s.is_fully_const()) {
		int idx_const = s.as_const().as_int();
		return {zeropad.repeat((1 << s.size()) - 1 - idx_const),
					a, zeropad.repeat(idx_const)};
	}
	return canvas->Demux(NEW_ID, a, s);
}

RTLIL::SigSpec RTLILBuilder::Le(RTLIL::SigSpec a, RTLIL::SigSpec b, bool is_signed) {
	if (a.is_fully_const() && b.is_fully_const())
		return RTLIL::const_le(a.as_const(), b.as_const(), is_signed, is_signed, 1);
	return canvas->Le(NEW_ID, a, b, is_signed);
}

RTLIL::SigSpec RTLILBuilder::Ge(RTLIL::SigSpec a, RTLIL::SigSpec b, bool is_signed) {
	if (a.is_fully_const() && b.is_fully_const())
		return RTLIL::const_ge(a.as_const(), b.as_const(), is_signed, is_signed, 1);
	return canvas->Ge(NEW_ID, a, b, is_signed);
}

RTLIL::SigSpec RTLILBuilder::Lt(RTLIL::SigSpec a, RTLIL::SigSpec b, bool is_signed) {
	if (a.is_fully_const() && b.is_fully_const())
		return RTLIL::const_lt(a.as_const(), b.as_const(), is_signed, is_signed, 1);
	return canvas->Lt(NEW_ID, a, b, is_signed);
}

RTLIL::SigSpec RTLILBuilder::Eq(RTLIL::SigSpec a, RTLIL::SigSpec b) {
	if (a.is_fully_const() && b.is_fully_const())
		return RTLIL::const_eq(a.as_const(), b.as_const(), false, false, 1);
	return canvas->Eq(NEW_ID, a, b);
}

RTLIL::SigSpec RTLILBuilder::EqWildcard(RTLIL::SigSpec a, RTLIL::SigSpec b) {
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

RTLIL::SigSpec RTLILBuilder::LogicAnd(RTLIL::SigSpec a, RTLIL::SigSpec b) {
	if (a.is_fully_zero() || b.is_fully_zero())
		return RTLIL::Const(0, 1);
	if (a.is_fully_def() && b.size() == 1)
		return b;
	if (b.is_fully_def() && a.size() == 1)
		return a;
	return canvas->LogicAnd(NEW_ID, a, b);
}

RTLIL::SigSpec RTLILBuilder::LogicNot(RTLIL::SigSpec a) {
	return canvas->LogicNot(NEW_ID, a);
}

RTLIL::SigSpec RTLILBuilder::Mux(RTLIL::SigSpec a, RTLIL::SigSpec b, RTLIL::SigSpec s) {
	log_assert(a.size() == b.size());
	log_assert(s.size() == 1);
	if (s[0] == RTLIL::S0)
		return a;
	if (s[0] == RTLIL::S1)
		return b;
	return canvas->Mux(NEW_ID, a, b, s);
}

RTLIL::SigSpec RTLILBuilder::Bwmux(RTLIL::SigSpec a, RTLIL::SigSpec b, RTLIL::SigSpec s) {
	log_assert(a.size() == b.size());
	log_assert(a.size() == s.size());
	if (s.is_fully_const()) {
		RTLIL::SigSpec result(RTLIL::Sx, a.size());
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

RTLIL::SigSpec RTLILBuilder::Shift(RTLIL::SigSpec a, bool a_signed, RTLIL::SigSpec s,
								   bool s_signed, int result_width)
{
	RTLIL::SigSpec y = canvas->addWire(NEW_ID, result_width);
	RTLIL::Cell *cell = canvas->addCell(NEW_ID, ID($shift));
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

RTLIL::SigSpec RTLILBuilder::Shiftx(RTLIL::SigSpec a, RTLIL::SigSpec s,
								 	bool s_signed, int result_width)
{
	RTLIL::SigSpec y = canvas->addWire(NEW_ID, result_width);
	canvas->addShiftx(NEW_ID, a, s, y, s_signed);
	return y;
}

RTLIL::SigSpec RTLILBuilder::Neg(RTLIL::SigSpec a, bool signed_)
{
	RTLIL::SigSpec y = canvas->addWire(NEW_ID, a.size() + 1);
	canvas->addNeg(NEW_ID, a, y, signed_);
	return y;
}

RTLIL::SigSpec RTLILBuilder::Bmux(RTLIL::SigSpec a, RTLIL::SigSpec s) {
	log_assert(a.size() % (1 << s.size()) == 0);
	log_assert(a.size() >= 1 << s.size());
	int stride = a.size() >> s.size();
	if (s.is_fully_def()) {
		return a.extract(s.as_const().as_int() * stride, stride);
	}
	return canvas->Bmux(NEW_ID, a, s);
}

RTLIL::SigSpec RTLILBuilder::Not(RTLIL::SigSpec a)
{
	return canvas->Not(NEW_ID, a);
}

};

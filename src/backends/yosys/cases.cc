//
// Yosys slang frontend
//
// Copyright Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
#include "cases.h"
#include "diag.h"
#include "slang_frontend.h"

namespace slang_frontend {

Switch::~Switch()
{
	for (auto case_ : cases)
		delete case_;
}

Case *Switch::add_case(std::vector<ValuePattern> compare)
{
	Case *case_ = new Case;
	cases.push_back(case_);
	case_->level = level;
	case_->compare = compare;
	return case_;
}

RTLIL::SigSpec lower_pattern(const ValuePattern &pat)
{
	std::vector<RTLIL::SigBit> bits;
	bits.reserve(pat.size());
	for (auto &bit : pat.bits) {
		if (bit.is_wildcard())
			bits.push_back(RTLIL::Sa);
		else
			bits.push_back(bit.net.raw());
	}
	return RTLIL::SigSpec(bits);
}

RTLIL::SwitchRule *Switch::lower(NetlistContext &netlist)
{
	RTLIL::SwitchRule *rule = new RTLIL::SwitchRule;
	rule->signal = signal;

	if (full_case)
		rule->attributes[ID::full_case] = true;

	if (parallel_case)
		rule->attributes[ID::parallel_case] = true;

	if (statement)
		transfer_attrs(netlist, *statement, rule);

	for (auto case_ : cases) {
		rule->cases.push_back(case_->lower(netlist));
	}

	return rule;
}

bool Switch::trivial()
{
	if (signal.empty() && !statement && !full_case && !parallel_case) {
		if (cases.size() == 1 && cases[0]->compare.empty())
			return true;
	}
	return false;
}

}; // namespace slang_frontend

//
// Yosys slang frontend
//
// Copyright Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
#pragma once

#include "slang/ast/symbols/ValueSymbol.h"

#include "diag.h"
#include "slang_frontend.h"
#include "variables.h"

namespace slang_frontend {

// Lower a ValuePattern to an RTLIL::SigSpec (wildcards become RTLIL::Sa)
RTLIL::SigSpec lower_pattern(const ValuePattern &pat);

// These structures are modeled after RTLIL's SwitchRule and CaseRule, to which
// they are eventually lowered.
//
// There are two key distinctions:
//
//  - we retain slang location and symbol information for the switches and cases
//    in question
//
//  - the LHS of actions represent "HDL intent" rather than actual netlist-level
//    signals, these differ because we need to insert flip-flops or latches, and
//    because we may need to dynamically mask the individual assignments
//
struct Case;
struct Switch
{
	int level;
	const ast::Statement *statement = nullptr;

	ir::Value signal;
	std::vector<Case *> cases;

	bool full_case = false;
	bool parallel_case = false;

	~Switch();
	Case *add_case(std::vector<ValuePattern> compare);
	RTLIL::SwitchRule *lower(NetlistContext &netlist);

	// trivial switch has signal={}, one case, and no special attributes
	bool trivial();
};

struct Case
{
	int level = 0;
	const ast::Statement *statement = nullptr;

	struct Action
	{
		slang::SourceLocation loc;

		VariableBits lvalue;
		ir::Value mask;
		ir::Value unmasked_rvalue;
	};
	std::vector<ValuePattern> compare;
	std::vector<Action> actions;
	std::vector<Switch *> switches;
	std::vector<RTLIL::SigSig> aux_actions;

	~Case()
	{
		for (auto switch_ : switches)
			delete switch_;
	}

	Switch *add_switch(ir::Value signal)
	{
		Switch *sw = new Switch;
		sw->signal = signal;
		sw->level = level + 1;
		switches.push_back(sw);
		return sw;
	}

	void copy_into(NetlistContext &netlist, RTLIL::CaseRule *rule)
	{
		if (statement)
			transfer_attrs(netlist, *statement, rule);

		for (auto &pat : compare)
			rule->compare.push_back(lower_pattern(pat));
		rule->actions.insert(rule->actions.end(), aux_actions.begin(), aux_actions.end());

		std::vector<Switch *>::iterator it, ite;
		it = switches.begin();
		ite = switches.end();
		for (; it != ite; it++) {
			// opportunistic optimization to reduce tree depth: helps runtime of proc_prune
			while (it != ite && it + 1 == ite && (*it)->trivial() && !(*it)->cases[0]->statement) {
				if (!(*it)->cases[0]->aux_actions.empty()) {
					RTLIL::SwitchRule *sw = new RTLIL::SwitchRule;
					rule->switches.push_back(sw);
					sw->signal = {};
					RTLIL::CaseRule *case2 = new RTLIL::CaseRule;
					sw->cases.push_back(case2);
					case2->actions = (*it)->cases[0]->aux_actions;
				}
				ite = (*it)->cases[0]->switches.end();
				it = (*it)->cases[0]->switches.begin();
			}
			if (it == ite)
				break;
			rule->switches.push_back((*it)->lower(netlist));
		}
	}

	RTLIL::CaseRule *lower(NetlistContext &netlist)
	{
		RTLIL::CaseRule *ret = new RTLIL::CaseRule;
		copy_into(netlist, ret);
		return ret;
	}

	void insert_latch_signaling(
			DiagnosticIssuer &issuer, Yosys::dict<VariableBit, RTLIL::SigSig> &map)
	{
		std::vector<Switch *> prepended_switches;
		std::set<VariableBit> has_mask_switches;

		for (auto &action : actions) {
			bool raise_complex = false;
			VariableBits lvalue;
			ir::Value enables, lstaging, rvalue;

			for (uint64_t i = 0; i < action.lvalue.bitwidth(); i++) {
				VariableBit lbit = action.lvalue[i];

				if (map.count(lbit)) {
					auto &mapped = map.at(lbit);

					if (action.mask[i] == ir::S1 && !has_mask_switches.count(lbit)) {
						lvalue.append(lbit);
						lstaging.append(ir::Net(mapped.second));
						enables.append(ir::Net(mapped.first));
						rvalue.append(action.unmasked_rvalue[i]);
					} else {
						Switch *sw = new Switch;
						sw->signal = ir::Net(action.mask[i]);
						sw->level = level + 1;
						sw->statement = statement;
						prepended_switches.push_back(sw);
						Case *case_ = sw->add_case({ir::S1});
						case_->statement = statement;
						case_->aux_actions.push_back(RTLIL::SigSig(RTLIL::SigSpec(mapped.second),
								ir::Value(action.unmasked_rvalue[i])));
						case_->aux_actions.push_back(RTLIL::SigSig(
								RTLIL::SigSpec(mapped.first), RTLIL::SigSpec(RTLIL::S1)));
						has_mask_switches.insert(lbit);
					}
				}
			}

			if (!lstaging.empty()) {
				aux_actions.push_back({RTLIL::SigSpec(lstaging), RTLIL::SigSpec(rvalue)});
				aux_actions.push_back(
						{RTLIL::SigSpec(enables), RTLIL::SigSpec(ir::S1, enables.size())});
			}
		}

		for (auto switch_ : switches)
			for (auto case_ : switch_->cases)
				case_->insert_latch_signaling(issuer, map);

		switches.insert(switches.begin(), prepended_switches.begin(), prepended_switches.end());
	}
};

}; // namespace slang_frontend

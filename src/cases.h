//
// Yosys slang frontend
//
// Copyright 2024 Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
#pragma once
namespace slang_frontend {

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
struct Switch {
	int level;
	const ast::Statement *statement = nullptr;

	RTLIL::SigSpec signal;
	std::vector<Case *> cases;

	bool full_case = false;
	bool parallel_case = false;

	~Switch();
	Case *add_case(std::vector<RTLIL::SigSpec> compare);
	RTLIL::SwitchRule *lower();
};

struct Case {
	int level = 0;
	const ast::Statement *statement = nullptr;

	struct Action {
		slang::SourceLocation loc;

		RTLIL::SigSpec lvalue;
		RTLIL::SigSpec mask;
		RTLIL::SigSpec unmasked_rvalue;
	};
	std::vector<RTLIL::SigSpec> compare;
	std::vector<Action> actions;
	std::vector<Switch *> switches;
	std::vector<RTLIL::SigSig> aux_actions;

	~Case() {
		for (auto switch_ : switches)
			delete switch_;
	}

	Switch *add_switch(RTLIL::SigSpec signal)
	{
		Switch *sw = new Switch;
		sw->signal = signal;
		sw->level = level + 1;
		switches.push_back(sw);
		return sw;
	}

	void copy_into(RTLIL::CaseRule *rule)
	{
		if (statement)
			transfer_attrs(*statement, rule);

		rule->compare = compare;
		rule->actions.insert(rule->actions.end(), aux_actions.begin(), aux_actions.end());

		for (auto switch_ : switches)
			rule->switches.push_back(switch_->lower());
	}

	RTLIL::CaseRule *lower()
	{
		RTLIL::CaseRule *ret = new RTLIL::CaseRule;
		copy_into(ret);
		return ret;
	}

	void insert_latch_signaling(
			DiagnosticIssuer &issuer, Yosys::dict<RTLIL::SigBit, RTLIL::SigSig> map)
	{
		for (auto &action : actions) {
			bool raise_complex = false;
			RTLIL::SigSpec enables, lvalue, lstaging, rvalue;

			for (int i = 0; i < action.lvalue.size(); i++) {
				RTLIL::SigBit lbit = action.lvalue[i];

				if (map.count(lbit)) {
					auto &mapped = map.at(lbit);
					lvalue.append(lbit);
					lstaging.append(mapped.second);
					enables.append(mapped.first);
					rvalue.append(action.unmasked_rvalue[i]);

					if (action.mask[i] != RTLIL::S1)
						raise_complex = true;
				}
			}

			aux_actions.push_back({lstaging, rvalue});
			aux_actions.push_back({enables, RTLIL::SigSpec(RTLIL::S1, enables.size())});

			if (raise_complex) {
				auto &diag = issuer.add_diag(diag::ComplexLatchLHS, action.loc);
				lvalue.sort();
				diag << std::string(log_signal(lvalue));
			}
		}

		for (auto switch_ : switches)
		for (auto case_ : switch_->cases)
			case_->insert_latch_signaling(issuer, map);
	}
};

Switch::~Switch() {
	for (auto case_ : cases)
		delete case_;
}

Case *Switch::add_case(std::vector<RTLIL::SigSpec> compare)
{
	Case *case_ = new Case;
	cases.push_back(case_);
	case_->level = level;
	case_->compare = compare;
	return case_;
}

RTLIL::SwitchRule *Switch::lower()
{
	RTLIL::SwitchRule *rule = new RTLIL::SwitchRule;
	rule->signal = signal;

	if (full_case)
		rule->attributes[ID::full_case] = true;

	if (parallel_case)
		rule->attributes[ID::parallel_case] = true;

	if (statement)
		transfer_attrs(*statement, rule);

	for (auto case_ : cases)
		rule->cases.push_back(case_->lower());

	return rule;
}

};

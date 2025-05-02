//
// Yosys slang frontend
//
// Copyright 2025 Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
#include "slang/ast/Statement.h"

#include "diag.h"
#include "slang_frontend.h"

namespace slang_frontend {

UnrollLimitTracking::UnrollLimitTracking(NetlistContext &netlist, int limit)
	: netlist(netlist), limit(limit)
{}

UnrollLimitTracking::~UnrollLimitTracking()
{
	log_assert(!unrolling);
}

void UnrollLimitTracking::enter_unrolling()
{
	if (!unrolling++) {
		unroll_counter = 0;
		error_issued = false;
		loops.clear();
	}
}

void UnrollLimitTracking::exit_unrolling()
{
	unrolling--;
	log_assert(unrolling >= 0);
}

bool UnrollLimitTracking::unroll_tick(const ast::Statement *symbol)
{
	if (error_issued)
		return false;

	loops.insert(symbol);

	if (++unroll_counter > limit) {
		auto &diag = netlist.add_diag(diag::UnrollLimitExhausted, symbol->sourceRange);
		diag << limit;
		for (auto other_loop : loops) {
			if (other_loop == symbol)
				continue;
			diag.addNote(diag::NoteLoopContributes, other_loop->sourceRange);
		}
		error_issued = true;
		return false;
	}

	return true;
}

}; // namespace slang_frontend

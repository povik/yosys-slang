//
// Yosys slang frontend
//
// Copyright Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//

#include "ir.h"

namespace ir {

Value Net::repeat(uint64_t width)
{
	return Value(*this).repeat(width);
}

}; // namespace ir

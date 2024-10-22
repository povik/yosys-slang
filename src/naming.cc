//
// Yosys slang frontend
//
// Copyright 2024 Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
#include "slang/ast/types/Type.h"
#include "slang/ast/symbols/VariableSymbols.h"

#include "slang_frontend.h"

namespace slang_frontend {

static void subfield_names(RTLIL::SigChunk chunk, int type_offset, const ast::Type *type,
							 std::string prefix, std::vector<NamedChunk> &ret)
{
	type = &type->getCanonicalType();

	if (!chunk.width)
		return;

	if (chunk.offset >= type_offset + type->getBitstreamWidth())
		return;

	if (chunk.offset + chunk.width <= type_offset)
		return;

	if (type->isStruct()) {
		const ast::Scope *scope = &type->as<ast::Scope>();

		for (auto &field : scope->template membersOfType<ast::FieldSymbol>())
			subfield_names(chunk, type_offset + field.bitOffset, &field.getType(),
						   prefix + "." + std::string(field.name), ret);
	} else if (type->isArray() && !type->isSimpleBitVector()) {
		log_assert(type->hasFixedRange());
		auto range = type->getFixedRange();
		const ast::Type *el_type = type->getArrayElementType();
		int stride = el_type->getBitstreamWidth();

		for (int i = range.lower(); i <= range.upper(); i++) {
			int elem_offset = range.translateIndex(i) * stride;
			subfield_names(chunk, type_offset + elem_offset, el_type,
						   prefix + "[" + std::to_string(i) + "]", ret);
		}
	} else {
		int width = type->getBitstreamWidth();
		int lo = std::clamp(chunk.offset - type_offset, 0, width);
		int hi = std::clamp(chunk.offset + chunk.width - type_offset, 0, width);

		log_assert(hi > lo);
		if (lo == 0 && hi == width)
			ret.emplace_back(RTLIL::SigChunk{chunk.wire, type_offset, width}, prefix);
		else
			// TODO: use hdl indices
			ret.emplace_back(RTLIL::SigChunk{chunk.wire, type_offset + lo, hi - lo}, prefix + "[" + std::to_string(hi - 1) + ":" + std::to_string(lo) + "]");
	}
}

std::vector<NamedChunk> generate_subfield_names(RTLIL::SigChunk chunk, const ast::Type *type)
{
	log_assert(chunk.wire);
	log_assert(type->isBitstreamType() && type->isFixedSize());
	log_assert(chunk.wire->width == type->getBitstreamWidth());

	std::vector<NamedChunk> ret;
	subfield_names(chunk, 0, type, RTLIL::unescape_id(chunk.wire->name.str()), ret);

	int sum = 0;
	for (auto pair : ret)
		sum += pair.first.width;
	log_assert(sum == chunk.width);

	return ret;
}

};

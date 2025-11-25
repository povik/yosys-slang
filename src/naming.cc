//
// Yosys slang frontend
//
// Copyright 2024 Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/Type.h"

#include "slang_frontend.h"
#include "variables.h"

namespace slang_frontend {

static void subfield_names(VariableChunk chunk, int type_offset, const ast::Type *type,
		std::string prefix, std::vector<NamedChunk> &ret)
{
	type = &type->getCanonicalType();

	if (!chunk.bitwidth())
		return;

	if (chunk.base >= type_offset + type->getBitstreamWidth())
		return;

	if (chunk.base + chunk.bitwidth() <= type_offset)
		return;

	if (type->isStruct()) {
		const ast::Scope *scope = &type->as<ast::Scope>();

		for (auto &field : scope->template membersOfType<ast::FieldSymbol>()) {
			int field_offset = int(bitstream_member_offset(field));
			subfield_names(chunk, type_offset + field_offset, &field.getType(),
					prefix + "." + std::string(field.name), ret);
		}
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
		int lo = std::clamp(chunk.base - type_offset, 0, width);
		int hi = std::clamp(chunk.base + chunk.bitwidth() - type_offset, 0, width);

		log_assert(hi > lo);
		if (lo == 0 && hi == width)
			ret.emplace_back(VariableChunk{chunk.variable, type_offset, width}, prefix);
		else
			// TODO: use hdl indices
			ret.emplace_back(VariableChunk{chunk.variable, type_offset + lo, hi - lo},
					prefix + "[" + std::to_string(hi - 1) + ":" + std::to_string(lo) + "]");
	}
}

std::vector<NamedChunk> generate_subfield_names(VariableChunk chunk, const ast::Type *type)
{
	log_assert((bool)chunk.variable);
	log_assert(type->isBitstreamType() && type->isFixedSize());
	log_assert(chunk.variable.bitwidth() == type->getBitstreamWidth());

	std::vector<NamedChunk> ret;
	subfield_names(chunk, 0, type, "", ret);

	int sum = 0;
	for (auto pair : ret)
		sum += pair.first.bitwidth();
	log_assert(sum == chunk.bitwidth());

	return ret;
}

}; // namespace slang_frontend

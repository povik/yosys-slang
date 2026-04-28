//
// Yosys slang frontend
//
// Copyright Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
#include <cctype>

#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/Type.h"

#include "slang_frontend.h"
#include "variables.h"

namespace slang_frontend {

static void subfield_names(VariableChunk chunk, uint64_t type_offset, const ast::Type *type,
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
			uint64_t field_offset = bitstream_member_offset(field);
			subfield_names(chunk, type_offset + field_offset, &field.getType(),
					prefix + "." + std::string(field.name), ret);
		}
	} else if (type->isArray() && !type->isSimpleBitVector()) {
		log_assert(type->hasFixedRange());
		auto range = type->getFixedRange();
		const ast::Type *el_type = type->getArrayElementType();
		uint64_t stride = el_type->getBitstreamWidth();

		for (int i = range.lower(); i <= range.upper(); i++) {
			uint64_t elem_offset = range.translateIndex(i) * stride;
			subfield_names(chunk, type_offset + elem_offset, el_type,
					prefix + "[" + std::to_string(i) + "]", ret);
		}
	} else {
		uint64_t width = type->getBitstreamWidth();
		uint64_t lo = chunk.base > type_offset ? std::min(chunk.base - type_offset, width) : 0;
		uint64_t hi = chunk.base + chunk.bitwidth() > type_offset
							  ? std::min(chunk.base + chunk.bitwidth() - type_offset, width)
							  : 0;

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

	uint64_t sum = 0;
	for (auto pair : ret)
		sum += pair.first.bitwidth();
	log_assert(sum == chunk.bitwidth());

	return ret;
}

// Format one raw hierarchy or signal name into an alphanumeric+underscore identifier fragment
// Makes it easy to use and compose in Tcl-style contexts without escaping characters
static std::string format_name_fragment(std::string_view raw)
{
	std::string ret;
	ret.reserve(raw.size() + 8);

	auto push_sep = [&]() {
		if (!ret.empty() && ret.back() != '_')
			ret.push_back('_');
	};

	for (size_t i = 0; i < raw.size(); i++) {
		unsigned char ch = raw[i];

		// Alphanumeric and underscore characters are kept as-is
		if (std::isalnum(ch) || ch == '_') {
			ret.push_back(ch);
			continue;
		}

		// Flatten dotted hierarchy and subfields into underscores
		if (ch == '.') {
			push_sep();
			continue;
		}

		// `$<n>` comes from unnamed scopes; keep it distinct from `[n]`, which is an array index.
		if (ch == '$' && i + 1 < raw.size() && std::isdigit((unsigned char)raw[i + 1])) {
			if (ret.empty() || ret.back() != '_')
				ret.push_back('_');
			ret.push_back('_');
			i++;
			while (i < raw.size() && std::isdigit((unsigned char)raw[i])) {
				ret.push_back(raw[i]);
				i++;
			}
			i--;
			continue;
		}

		// Add packed and unpacked indices as explicit suffixes
		if (ch == '[') {
			push_sep();

			std::string lhs_index;
			size_t j = i + 1;
			while (j < raw.size() && raw[j] != ']' && raw[j] != ':') {
				lhs_index.push_back(raw[j]);
				j++;
			}
			ret.append(lhs_index);

			if (j < raw.size() && raw[j] == ':') {
				// Keep multi-bit slices explicit so ranges remain readable
				j++;
				std::string rhs;
				while (j < raw.size() && raw[j] != ']') {
					rhs.push_back(raw[j]);
					j++;
				}

				if (lhs_index != rhs) {
					ret.append("downto");
					ret.append(rhs);
				}
			}

			while (j < raw.size() && raw[j] != ']')
				j++;
			i = j;
			continue;
		}

		// Collapse any remaining symbols into a separator
		push_sep();
	}

	while (!ret.empty() && ret.back() == '_')
		ret.pop_back();

	return ret;
}

// Format a scope path relative to another scope using the naming fragment rules above.
std::string format_scope_name_fragment(const ast::Scope *relative_to, const ast::Scope *scope)
{
	return format_name_fragment(hierpath_relative_to(relative_to, scope));
}

// Format a signal path plus optional subfield or slice suffix into one name fragment.
std::string format_signal_name_fragment(const ast::Scope *relative_to, const ast::ValueSymbol &symbol,
		std::string_view suffix)
{
	auto *scope = symbol.getParentScope();
	ast_invariant(symbol, scope != nullptr);

	std::string raw = hierpath_relative_to(relative_to, scope);
	if (!raw.empty())
		raw.push_back('.');
	raw.append(symbol.name);
	raw.append(suffix);
	return format_name_fragment(raw);
}

}; // namespace slang_frontend

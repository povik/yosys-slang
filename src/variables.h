//
// Yosys slang frontend
//
// Copyright 2024 Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
#pragma once
#include "slang_frontend.h"

namespace slang_frontend {

struct VariableBit
{
	Variable variable;
	int offset;

	typedef std::tuple<Variable, int> Label;
	Label label() const { return std::make_tuple(variable, offset); }

	bool operator==(const VariableBit &other) const { return label() == other.label(); }
	bool operator<(const VariableBit &other) const { return label() < other.label(); }
#if YS_HASHING_VERSION >= 1
	[[nodiscard]] Yosys::Hasher hash_into(Yosys::Hasher h) const
	{
		h.eat(label());
		return h;
	}
#else
	int hash() const { return Yosys::hash_ops<Label>::hash(label()); }
#endif

	std::string index_text() const
	{
		if (variable.bitwidth() == 1)
			return "";
		else
			return Yosys::stringf("[%d]", offset);
	}

	std::string text() const { return variable.text() + index_text(); }
};

// VariableChunk is to VariableBit
// what RTLIL::SigChunk is to RTLIL::SigBit
struct VariableChunk
{
	Variable variable;
	int base;
	int length;

	int bitwidth() const { return length; }

	VariableBit operator[](int key) const
	{
		log_assert(key >= 0 && key < length);
		return VariableBit{variable, base + key};
	}

	std::string slice_text() const
	{
		if (length == variable.bitwidth())
			return "";
		else if (length > 1)
			// TODO: hdl indices
			return Yosys::stringf("[%d:%d]", base + length - 1, base);
		else
			return Yosys::stringf("[%d]", base);
	}

	std::string text() const { return variable.text() + slice_text(); }
};

class VariableBits : public std::vector<VariableBit>
{
public:
	VariableBits() {}

	VariableBits(const VariableBit &bit) { append(bit); }

	VariableBits(const VariableChunk &chunk)
	{
		for (auto i = 0; i < chunk.bitwidth(); i++)
			append(chunk[i]);
	}

	VariableBits(const Variable &variable)
	{
		for (auto i = 0; i < variable.bitwidth(); i++)
			append(VariableBit{variable, i});
	}

	VariableBits(std::initializer_list<VariableBits> parts)
	{
		for (auto it = std::rbegin(parts); it != std::rend(parts); it++) {
			append(*it);
		}
	}

	void sort_and_unify()
	{
		std::sort(begin(), end());
		auto unified_end = std::unique(begin(), end());
		erase(unified_end, end());
	}

	void append(const VariableBit bit) { push_back(bit); }

	void append(const VariableBits &other) { insert(end(), other.begin(), other.end()); }

	VariableBits extract(int base, int width)
	{
		VariableBits ret;
		for (int i = base, j = 0; j < width; i++, j++)
			ret.push_back((*this)[i]);
		return ret;
	}

	std::vector<VariableChunk> chunks()
	{
		std::vector<VariableChunk> ret;
		bool valid = false;
		VariableChunk chunk;
		for (VariableBit bit : *this) {
			if (valid && bit.variable == chunk.variable &&
					bit.offset == chunk.base + chunk.length) {
				chunk.length++;
			} else {
				if (valid)
					ret.push_back(chunk);
				chunk.variable = bit.variable;
				chunk.base = bit.offset;
				chunk.length = 1;
				valid = true;
			}
		}
		if (valid)
			ret.push_back(chunk);
		return ret;
	}

	int bitwidth() { return (int)size(); }
};

}; // namespace slang_frontend

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

	bool has_dummy_bits()
	{
		for (auto chunk : chunks()) {
			if (chunk.variable.kind == Variable::Dummy)
				return true;
		}
		return false;
	}

	VariableBits extract(int base, int width)
	{
		VariableBits ret;
		for (int i = base, j = 0; j < width; i++, j++)
			ret.push_back((*this)[i]);
		return ret;
	}

	class iterator
	{
	private:
		const VariableBits &bits;
		int offset;
		VariableChunk chunk;

	public:
		using iterator_category = std::input_iterator_tag;
		using value_type = Variable;
		using difference_type = ptrdiff_t;
		using pointer = const Variable *;
		using reference = const Variable &;

		iterator(const VariableBits &bits, int offset) : bits(bits), offset(offset)
		{
			if (offset < bits.size()) {
				chunk = {bits[offset].variable, bits[offset].offset, 1};
				fixup_chunk();
			}
		}

		iterator &operator++()
		{
			offset += chunk.length;
			if (offset < bits.size()) {
				chunk = {bits[offset].variable, bits[offset].offset, 1};
				fixup_chunk();
			}
			return *this;
		}

		void fixup_chunk()
		{
			while (offset + chunk.length < bits.size() &&
					bits[offset + chunk.length].variable == chunk.variable &&
					bits[offset + chunk.length].offset == chunk.base + chunk.length) {
				chunk.length++;
			}
		}

		bool operator==(const iterator &other) const { return offset == other.offset; }
		bool operator!=(const iterator &other) const { return !(*this == other); }
		VariableChunk operator*() const { return chunk; }
	};

	class chunk_list
	{
	public:
		iterator begin() const { return iterator(bits, 0); };
		iterator end() const { return iterator(bits, bits.size()); };

	protected:
		chunk_list(const VariableBits &bits) : bits(bits) {};
		friend class VariableBits;

	private:
		const VariableBits &bits;
	};

	chunk_list chunks() const { return chunk_list(*this); }

	int bitwidth() { return (int)size(); }
};

}; // namespace slang_frontend

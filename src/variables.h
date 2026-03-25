//
// Yosys slang frontend
//
// Copyright Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
#pragma once
#include "slang_frontend.h"
#include <cinttypes>

namespace slang_frontend {

struct VariableBit
{
	Variable variable;
	uint64_t offset;

	typedef std::tuple<Variable, uint64_t> Label;
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
			return Yosys::stringf("[%" PRIu64 "]", offset);
	}

	std::string text() const { return variable.text() + index_text(); }
};

// VariableChunk is to VariableBit
// what RTLIL::SigChunk is to RTLIL::SigBit
struct VariableChunk
{
	Variable variable;
	uint64_t base;
	uint64_t length;

	uint64_t bitwidth() const { return length; }

	VariableBit operator[](uint64_t key) const
	{
		log_assert(key < length);
		return VariableBit{variable, base + key};
	}

	bool operator==(const VariableChunk &other) const
	{
		return variable == other.variable && base == other.base && length == other.length;
	}

	std::string slice_text() const
	{
		if (length == variable.bitwidth())
			return "";
		else if (length > 1)
			// TODO: hdl indices
			return Yosys::stringf("[%" PRIu64 ":%" PRIu64 "]", base + length - 1, base);
		else
			return Yosys::stringf("[%" PRIu64 "]", base);
	}

	std::string text() const { return variable.text() + slice_text(); }
};

class VariableBits
{
	std::variant<VariableChunk, std::vector<VariableBit>> storage_;

	bool is_chunk() const { return std::holds_alternative<VariableChunk>(storage_); }

	VariableChunk &as_chunk() { return std::get<VariableChunk>(storage_); }
	const VariableChunk &as_chunk() const { return std::get<VariableChunk>(storage_); }

	std::vector<VariableBit> &as_bits() { return std::get<std::vector<VariableBit>>(storage_); }
	const std::vector<VariableBit> &as_bits() const
	{
		return std::get<std::vector<VariableBit>>(storage_);
	}

	void unpack()
	{
		if (!is_chunk())
			return;
		VariableChunk chunk = as_chunk();
		std::vector<VariableBit> bits;
		bits.reserve(chunk.length);
		for (uint64_t i = 0; i < chunk.length; i++)
			bits.push_back(chunk[i]);
		storage_ = std::move(bits);
	}

public:
	VariableBits() : storage_(VariableChunk{{}, 0, 0}) {}

	VariableBits(const VariableBit &bit) : storage_(VariableChunk{bit.variable, bit.offset, 1}) {}

	VariableBits(const VariableChunk &chunk) : storage_(chunk) {}

	VariableBits(const Variable &variable)
		: storage_(VariableChunk{variable, 0, variable.bitwidth()})
	{}

	VariableBits(std::initializer_list<VariableBits> parts) : storage_(VariableChunk{{}, 0, 0})
	{
		for (auto it = std::rbegin(parts); it != std::rend(parts); it++) {
			append(*it);
		}
	}

	uint64_t bitwidth() const
	{
		if (is_chunk())
			return as_chunk().length;
		else
			return as_bits().size();
	}

	bool empty() const { return bitwidth() == 0; }

	VariableBit operator[](uint64_t index) const
	{
		if (is_chunk())
			return as_chunk()[index];
		else
			return as_bits()[index];
	}

	bool operator==(const VariableBits &other) const
	{
		if (bitwidth() != other.bitwidth())
			return false;
		if (is_chunk() && other.is_chunk())
			return as_chunk() == other.as_chunk();
		for (uint64_t i = 0; i < bitwidth(); i++)
			if (!((*this)[i] == other[i]))
				return false;
		return true;
	}

	bool operator!=(const VariableBits &other) const { return !(*this == other); }

	void append(const VariableBit bit)
	{
		if (is_chunk()) {
			auto &chunk = as_chunk();
			if (chunk.length == 0) {
				chunk = {bit.variable, bit.offset, 1};
				return;
			}
			if (bit.variable == chunk.variable && bit.offset == chunk.base + chunk.length) {
				chunk.length++;
				return;
			}
			unpack();
		}
		as_bits().push_back(bit);
	}

	void append(const VariableBits &other)
	{
		if (other.empty())
			return;
		if (is_chunk() && other.is_chunk()) {
			auto &chunk = as_chunk();
			auto &other_chunk = other.as_chunk();
			if (chunk.length == 0) {
				chunk = other_chunk;
				return;
			}
			if (chunk.variable == other_chunk.variable &&
					other_chunk.base == chunk.base + chunk.length) {
				chunk.length += other_chunk.length;
				return;
			}
		}
		unpack();
		if (other.is_chunk()) {
			auto &other_chunk = other.as_chunk();
			for (uint64_t i = 0; i < other_chunk.length; i++)
				as_bits().push_back(other_chunk[i]);
		} else {
			auto &bits = as_bits();
			auto &other_bits = other.as_bits();
			bits.insert(bits.end(), other_bits.begin(), other_bits.end());
		}
	}

	void remove(int index)
	{
		unpack();
		auto &bits = as_bits();
		log_assert(index >= 0 && index < (int)bits.size());
		bits.erase(bits.begin() + index);
	}

	void reserve(uint64_t n)
	{
		unpack();
		as_bits().reserve(n);
	}

	VariableBits extract(uint64_t base, uint64_t width) const
	{
		if (is_chunk()) {
			auto &chunk = as_chunk();
			return VariableBits(VariableChunk{chunk.variable, chunk.base + base, width});
		}
		VariableBits ret;
		for (uint64_t i = base, j = 0; j < width; i++, j++)
			ret.append(as_bits()[i]);
		return ret;
	}

	void sort()
	{
		unpack();
		auto &bits = as_bits();
		std::sort(bits.begin(), bits.end());
	}

	void sort_and_unify()
	{
		sort();
		auto &bits = as_bits();
		auto unified_end = std::unique(bits.begin(), bits.end());
		bits.erase(unified_end, bits.end());
	}

	bool has_dummy_bits() const
	{
		if (is_chunk())
			return as_chunk().variable.kind == Variable::Dummy;
		for (auto chunk : chunks()) {
			if (chunk.variable.kind == Variable::Dummy)
				return true;
		}
		return false;
	}

	bool has_special_nets();

	class const_bit_iterator
	{
		const VariableBits *container;
		int index;

	public:
		using iterator_category = std::random_access_iterator_tag;
		using value_type = VariableBit;
		using difference_type = int;

		const_bit_iterator(const VariableBits *container, int index)
			: container(container), index(index)
		{}
		VariableBit operator*() const { return (*container)[index]; }
		const_bit_iterator &operator++()
		{
			index++;
			return *this;
		}
		const_bit_iterator operator++(int)
		{
			auto tmp = *this;
			index++;
			return tmp;
		}
		const_bit_iterator &operator--()
		{
			index--;
			return *this;
		}
		const_bit_iterator operator+(int n) const { return {container, index + n}; }
		const_bit_iterator operator-(int n) const { return {container, index - n}; }
		int operator-(const const_bit_iterator &other) const { return index - other.index; }
		auto operator<=>(const const_bit_iterator &other) const { return index <=> other.index; }
		bool operator==(const const_bit_iterator &other) const = default;
	};

	const_bit_iterator begin() const { return const_bit_iterator(this, 0); }
	const_bit_iterator end() const { return const_bit_iterator(this, bitwidth()); }

	class iterator_base
	{
	protected:
		const VariableBits &container;
		uint64_t offset;
		VariableChunk chunk;

		void incr()
		{
			offset += chunk.length;
			if (offset < container.bitwidth()) {
				log_assert(!container.is_chunk());
				auto &bits = container.as_bits();
				chunk = {bits[offset].variable, bits[offset].offset, 1};
				fixup_chunk();
			}
		}

	public:
		using iterator_category = std::input_iterator_tag;

		iterator_base(const VariableBits &container, uint64_t offset)
			: container(container), offset(offset)
		{
			if (offset < container.bitwidth()) {
				if (container.is_chunk()) {
					chunk = container.as_chunk();
				} else {
					auto &bits = container.as_bits();
					chunk = {bits[offset].variable, bits[offset].offset, 1};
					fixup_chunk();
				}
			}
		}

		void fixup_chunk()
		{
			auto &bits = container.as_bits();
			while (offset + chunk.length < bits.size() &&
					bits[offset + chunk.length].variable == chunk.variable &&
					bits[offset + chunk.length].offset == chunk.base + chunk.length) {
				chunk.length++;
			}
		}

		bool operator==(const iterator_base &other) const { return offset == other.offset; }
		bool operator!=(const iterator_base &other) const { return !(*this == other); }
	};

	class chunk_iterator : public iterator_base
	{
	public:
		using value_type = VariableChunk;
		chunk_iterator(const VariableBits &bits, uint64_t offset) : iterator_base(bits, offset) {}
		VariableChunk operator*() const { return chunk; }
		chunk_iterator &operator++()
		{
			incr();
			return *this;
		}
	};

	class chunk_list
	{
	public:
		chunk_iterator begin() const { return chunk_iterator(bits, 0); };
		chunk_iterator end() const { return chunk_iterator(bits, bits.bitwidth()); };

	protected:
		chunk_list(const VariableBits &bits) : bits(bits) {};
		friend class VariableBits;

	private:
		const VariableBits &bits;
	};

	chunk_list chunks() const { return chunk_list(*this); }

	class chunk_span_iterator : public iterator_base
	{
	public:
		using value_type = std::tuple<size_t, size_t, VariableChunk>;
		chunk_span_iterator(const VariableBits &bits, uint64_t offset) : iterator_base(bits, offset)
		{}
		std::tuple<size_t, size_t, VariableChunk> operator*() const
		{
			return std::make_tuple(offset, chunk.length, chunk);
		}
		chunk_span_iterator &operator++()
		{
			incr();
			return *this;
		}
	};

	class chunk_span_list
	{
	public:
		chunk_span_iterator begin() const { return chunk_span_iterator(bits, 0); };
		chunk_span_iterator end() const { return chunk_span_iterator(bits, bits.bitwidth()); };

	protected:
		chunk_span_list(const VariableBits &bits) : bits(bits) {};
		friend class VariableBits;

	private:
		const VariableBits &bits;
	};

	chunk_span_list chunk_spans() const { return chunk_span_list(*this); }
};

}; // namespace slang_frontend

//
// Yosys slang frontend
//
// Copyright Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
// IR abstraction layer: thin wrappers around RTLIL signal types exposing
// only the interface required by the frontend. Consumers targeting a different
// IR can swap out the implementation while keeping the same surface.
//
// clang-format off
#pragma once
#include "kernel/rtlil.h"

namespace ir {

namespace RTLIL = ::Yosys::RTLIL;

// Four-valued bit constant
struct Trit {
	RTLIL::State raw_;

	constexpr Trit() : raw_(RTLIL::Sx) {}
	constexpr Trit(RTLIL::State s) : raw_(s) {}
	constexpr operator RTLIL::State() const { return raw_; }

	constexpr bool operator==(Trit o) const { return raw_ == o.raw_; }
	constexpr bool operator!=(Trit o) const { return raw_ != o.raw_; }
};

inline constexpr Trit S0{RTLIL::S0};
inline constexpr Trit S1{RTLIL::S1};
inline constexpr Trit Sx{RTLIL::Sx};

// Multi-bit constant value
class Const {
private:
	Const(RTLIL::Const c) : raw_(std::move(c)) {}
	RTLIL::Const raw_;

public:
	Const() {}
	explicit Const(int val, uint64_t width) : raw_(val, width) {}
	explicit Const(Trit t, uint64_t width) : raw_(t.raw_, width) {}
	Const(const std::vector<Trit> &bits) {
		std::vector<RTLIL::State> states;
		states.reserve(bits.size());
		for (auto t : bits) states.push_back(t.raw_);
		raw_ = RTLIL::Const(std::move(states));
	}

	static Const from_rtlil(RTLIL::Const c) {
		return Const(std::move(c));
	}

	RTLIL::Const to_rtlil() const {
		return raw_;
	}

	RTLIL::Const &raw_rtlil() {
		return raw_;
	}

	int size() const { return raw_.size(); }
	bool empty() const { return raw_.empty(); }

	Const extract(int offset, int length) const { return raw_.extract(offset, length); }
	void append(Const other) { raw_.append(other.raw_); }
	void append(Trit t) { raw_.append(t.raw_); }

	int as_int(bool is_signed = false) const { return raw_.as_int(is_signed); }
	bool is_fully_undef() const { return raw_.is_fully_undef(); }

	void set(int i, Trit t)
	{
#if YOSYS_MAJOR == 0 && YOSYS_MINOR < 58
		raw_.bits()[i] = t.raw_;
#else
		raw_.set(i, t.raw_);
#endif
	}

	Trit operator[](int i) const { return raw_[i]; }

	struct const_iterator {
		using iterator_category = std::input_iterator_tag;
		using value_type = Trit;
		using difference_type = std::ptrdiff_t;
		using pointer = const Trit *;
		using reference = Trit;

		decltype(std::declval<const RTLIL::Const>().begin()) it;
		Trit operator*() const { return Trit(*it); }
		const_iterator &operator++() { ++it; return *this; }
		const_iterator operator++(int) { auto tmp = *this; ++it; return tmp; }
		bool operator!=(const const_iterator &o) const { return it != o.it; }
		bool operator==(const const_iterator &o) const { return it == o.it; }
	};

	const_iterator begin() const { return {raw_.begin()}; }
	const_iterator end() const { return {raw_.end()}; }
};

struct Value;

// Single-bit signal reference
struct Net {
	RTLIL::SigBit raw_;

	Net() : raw_() {}
	Net(RTLIL::SigBit b) : raw_(b) {}
	Net(Trit t) : raw_(t.raw_) {}

	operator RTLIL::SigBit() const { return raw_; }
	RTLIL::SigBit& raw() { return raw_; }
	const RTLIL::SigBit& raw() const { return raw_; }

	Value repeat(uint64_t width);

	Trit trit() const { return raw_.data; }

	bool operator==(Net o) const { return raw_ == o.raw_; }
	bool operator!=(Net o) const { return raw_ != o.raw_; }
	bool operator==(Trit t) const { return raw_ == RTLIL::SigBit(t.raw_); }
	bool operator!=(Trit t) const { return raw_ != RTLIL::SigBit(t.raw_); }

	bool is_const() const { return raw_.is_wire() == false; }
	bool is_def() const { return is_const() && (raw_.data == RTLIL::S0 || raw_.data == RTLIL::S1); }

};

// Proxy returned by Value::operator[] for read and write access
class NetProxy {
	RTLIL::SigSpec &spec_;
	int idx_;
public:
	NetProxy(RTLIL::SigSpec &s, int i) : spec_(s), idx_(i) {}
	operator Net() const { return spec_[idx_]; }
	NetProxy& operator=(Net n) { spec_[idx_] = n.raw_; return *this; }
	NetProxy& operator=(const NetProxy &o) { spec_[idx_] = o.spec_[o.idx_]; return *this; }
	bool operator==(Net n) const { return Net(spec_[idx_]) == n; }
	bool operator!=(Net n) const { return Net(spec_[idx_]) != n; }
	bool operator==(Trit t) const { return Net(spec_[idx_]) == t; }
	bool operator!=(Trit t) const { return Net(spec_[idx_]) != t; }
	Trit trit() const { return Net(spec_[idx_]).trit(); }
};

// Multi-bit signal
struct Value {
	RTLIL::SigSpec raw_;

	// Construction
	Value() {}
	Value(RTLIL::SigSpec s) : raw_(std::move(s)) {}
	Value(Net bit) : raw_(bit.raw_) {}
	Value(RTLIL::SigBit bit) : raw_(bit) {}
	Value(Trit t) : raw_(t.raw_, 1) {}
	Value(Trit t, uint64_t width) : raw_(t.raw_, width) {}
	Value(Const c) : raw_(c.raw_rtlil()) {}
	Value(RTLIL::Const c) : raw_(std::move(c)) {}
	explicit Value(int val, int width = 32) : raw_(val, width) {}
	Value(RTLIL::Wire *wire) : raw_(wire) {}

	// Concatenation (MSB-first, matching RTLIL::SigSpec and Verilog semantics)
	Value(std::initializer_list<Value> parts)
	{
		for (auto it = parts.end(); it != parts.begin(); )
			raw_.append((--it)->raw_);
	}

	operator RTLIL::SigSpec() const { return raw_; }
	RTLIL::SigSpec& raw() { return raw_; }
	const RTLIL::SigSpec& raw() const { return raw_; }

	// Sizing
	uint64_t size() const { return raw_.size(); }
	uint64_t width() const { return raw_.size(); }
	bool empty() const { return raw_.empty(); }

	// Element access
	Net operator[](uint64_t i) const { return raw_[i]; }
	NetProxy operator[](uint64_t i) { return NetProxy(raw_, i); }

	// Extraction / manipulation
	Value extract(uint64_t offset, uint64_t width) const { return raw_.extract(offset, width); }
	Value extract_end(uint64_t offset) const { return raw_.extract_end(offset); }
	void append(Net bit) { raw_.append(bit.raw_); }
	void append(const NetProxy &p) { raw_.append(Net(p).raw_); }
	void append(Trit t) { raw_.append(RTLIL::SigBit(t.raw_)); }
	void append(Value other) { raw_.append(other.raw_); }
	void remove(uint64_t index, uint64_t width = 1) { raw_.remove(index, width); }
	Value repeat(uint64_t count) const { return raw_.repeat(count); }
	void extend_u0(uint64_t width, bool is_signed = false) { raw_.extend_u0(width, is_signed); }
	Net msb() const { return raw_.msb(); }
	void reserve(uint64_t) { /* not available on all SigSpec implementations */ }

	// Queries
	bool is_fully_const() const { return raw_.is_fully_const(); }
	bool is_fully_def() const { return raw_.is_fully_def(); }
	bool is_fully_zero() const { return raw_.is_fully_zero(); }
	bool is_fully_ones() const { return raw_.is_fully_ones(); }
	bool is_wire() const { return raw_.is_wire(); }

	// Conversion
	Net as_net() const { log_assert(raw_.size() == 1); return raw_[0]; }
	Const as_const() const { return Const::from_rtlil(raw_.as_const()); }
	bool as_bool() const { return raw_.as_bool(); }
	int as_int(bool is_signed = false) const { return raw_.as_int(is_signed); }

	// For code that needs the raw chunks (e.g. initialization.cc wire access)
	auto chunks() const { return raw_.chunks(); }

	// Iteration (yields RTLIL::SigBit; auto-converts to Net via implicit ctor)
	auto begin() const { return raw_.begin(); }
	auto end() const { return raw_.end(); }

	// Comparison
	bool operator==(const Value& o) const { return raw_ == o.raw_; }
	bool operator!=(const Value& o) const { return raw_ != o.raw_; }
};

} // namespace ir

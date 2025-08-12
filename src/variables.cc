//
// Yosys slang frontend
//
// Copyright 2025 Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
#include "slang/ast/symbols/BlockSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/ValueSymbol.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/Type.h"

#include "slang_frontend.h"

namespace slang_frontend {

Variable Variable::from_symbol(const ast::ValueSymbol *symbol, int depth)
{
	assert(symbol);
	if (ast::VariableSymbol::isKind(symbol->kind) &&
			symbol->as<ast::VariableSymbol>().lifetime == ast::VariableLifetime::Automatic) {
		assert(depth >= 0);
		return Variable(Local, symbol, depth);
	} else {
		assert(depth == -1);
		return Variable(Static, symbol, 0);
	}
}

Variable Variable::escape_flag(int id)
{
	Variable var;
	var.kind = EscapeFlag;
	var.id = id;
	return var;
}

Variable Variable::dummy(int width)
{
	Variable var;
	var.kind = Dummy;
	var.width = width;
	return var;
}

Variable::Variable() : kind(Invalid)
{}

Variable::Variable(enum Kind kind, const ast::ValueSymbol *symbol, int depth)
	: kind(kind), symbol(symbol), depth(depth)
{}

std::vector<const ast::Scope *> scope_path(const ast::Scope *scope, bool stop_at_instance)
{
	std::vector<const ast::Scope *> ret;
	while (scope &&
			!(stop_at_instance && scope->asSymbol().kind == ast::SymbolKind::InstanceBody)) {
		ret.push_back(scope);
		scope = scope->asSymbol().getParentScope();
	}
	std::reverse(ret.begin(), ret.end());
	return ret;
}

bool order_symbols_within_scope(const ast::Symbol *lhs, const ast::Symbol *rhs)
{
	log_assert(lhs != rhs);

	if (lhs->getIndex() != rhs->getIndex())
		return lhs->getIndex() < rhs->getIndex();

	if (lhs->name != rhs->name)
		return lhs->name < rhs->name;

	if (lhs->kind != rhs->kind)
		return lhs->kind < rhs->kind;

	switch (lhs->kind) {
	case ast::SymbolKind::GenerateBlockArray: {
		auto &larray = lhs->as<ast::GenerateBlockArraySymbol>();
		auto &rarray = rhs->as<ast::GenerateBlockArraySymbol>();
		if (larray.constructIndex != rarray.constructIndex)
			return larray.constructIndex < rarray.constructIndex;
		break;
	}
	case ast::SymbolKind::GenerateBlock: {
		auto &lblock = lhs->as<ast::GenerateBlockSymbol>();
		auto &rblock = rhs->as<ast::GenerateBlockSymbol>();
		if (((bool)lblock.arrayIndex) != ((bool)rblock.arrayIndex))
			return ((bool)lblock.arrayIndex) < ((bool)rblock.arrayIndex);
		if (lblock.arrayIndex) {
			if (*lblock.arrayIndex != *rblock.arrayIndex) {
				auto result = (*lblock.arrayIndex) < (*rblock.arrayIndex);
				log_assert(!result.isUnknown());
				return (bool)result;
			}
		} else {
			if (lblock.constructIndex != rblock.constructIndex)
				return lblock.constructIndex < rblock.constructIndex;
		}
		break;
	}
	case ast::SymbolKind::Instance:
	case ast::SymbolKind::CheckerInstance: {
		auto &linst = lhs->as<ast::InstanceSymbolBase>();
		auto &rinst = rhs->as<ast::InstanceSymbolBase>();
		for (int i = 0; i < linst.arrayPath.size() && rinst.arrayPath.size(); i++) {
			if (linst.arrayPath[i] != rinst.arrayPath[i])
				return linst.arrayPath[i] < rinst.arrayPath[i];
		}
		break;
	}
	default: break;
	}

	// Should be unreachable
	log_abort();
}

bool order_scopes(const ast::Scope *lhs, const ast::Scope *rhs)
{
	log_assert(lhs != rhs);

	if (!lhs)
		return true;

	if (!rhs)
		return false;

	bool stop_at_inst = lhs->getContainingInstance() == rhs->getContainingInstance();
	std::vector<const ast::Scope *> lhs_path = scope_path(lhs, stop_at_inst);
	std::vector<const ast::Scope *> rhs_path = scope_path(rhs, stop_at_inst);
	for (int i = 0; i < lhs_path.size() && i < rhs_path.size(); i++) {
		if (lhs_path[i] != rhs_path[i])
			return order_symbols_within_scope(&lhs_path[i]->asSymbol(), &rhs_path[i]->asSymbol());
	}

	log_assert(lhs_path.size() != rhs_path.size());
	return lhs_path.size() < rhs_path.size();
}

bool Variable::operator<(const Variable &other) const
{
	if (kind != other.kind)
		return kind < other.kind;
	if (kind == Local || kind == Static) {
		if (symbol != other.symbol) {
			// Find ordering among the symbols
			if (symbol->getParentScope() != other.symbol->getParentScope())
				return order_scopes(symbol->getParentScope(), other.symbol->getParentScope());
			else
				return order_symbols_within_scope(symbol, other.symbol);
		}
		return false;
	} else if (kind == EscapeFlag) {
		return id < other.id;
	} else if (kind == Dummy) {
		return width < other.width;
	}
	log_abort();
}

Variable::HashLabel Variable::hash_label() const
{
	void *ptr = 0;
	int num = depth;
	switch (kind) {
	case Static:
	case Local:      ptr = (void *)symbol; break;
	case EscapeFlag: num = id; break;
	case Dummy:      num = width; break;
	default:         log_abort();
	}

	return std::make_tuple((int)kind, ptr, num);
}

const ast::ValueSymbol *Variable::get_symbol() const
{
	switch (kind) {
	case Static:
	case Local:  return symbol;
	default:     return nullptr;
	}
}

int Variable::bitwidth() const
{
	switch (kind) {
	case Static:
	case Local:      return (int)symbol->getType().getBitstreamWidth();
	case EscapeFlag: return 1;
	case Dummy:      return width;
	default:         log_abort();
	}
}

Variable::operator bool() const
{
	return kind != Invalid;
}

std::string Variable::text() const
{
	switch (kind) {
	case Static: return get_symbol()->getHierarchicalPath();
	case Local:
		return "(local " + get_symbol()->getHierarchicalPath() + " at nest level " +
			   std::to_string(depth) + ")";
	case EscapeFlag: return "flag#" + std::to_string(id);
	case Dummy:      return "dummy(" + std::to_string(width) + ")";
	default:         log_abort();
	}
}

} // namespace slang_frontend

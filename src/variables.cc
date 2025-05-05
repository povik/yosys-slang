//
// Yosys slang frontend
//
// Copyright 2025 Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
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

Variable Variable::disable_for_scope(const ast::Statement *statement, int depth)
{
	assert(statement);
	return Variable(Disable, statement, depth);
}

Variable Variable::break_for_scope(const ast::Statement *statement, int depth)
{
	assert(statement);
	return Variable(Break, statement, depth);
}

Variable Variable::dummy(int width)
{
	return Variable(Dummy, width);
}

Variable::Variable() : kind(Invalid)
{}

Variable::Variable(enum Kind kind, const ast::ValueSymbol *symbol, int depth)
	: kind(kind), symbol(symbol), depth(depth)
{}

Variable::Variable(enum Kind kind, const ast::Statement *statement, int depth)
	: kind(kind), statement(statement), depth(depth)
{}

Variable::Variable(enum Kind kind, int width) : kind(kind), width(width)
{}

Variable::SortLabel Variable::sort_label() const
{
	void *ptr = 0;
	switch (kind) {
	case Static:
	case Local:   ptr = (void *)symbol; break;
	case Disable:
	case Break:   ptr = (void *)statement; break;
	case Dummy:   break;
	default:      log_abort();
	}

	return std::make_tuple((int)kind, ptr, kind == Dummy ? width : depth);
}

const ast::ValueSymbol *Variable::get_symbol() const
{
	switch (kind) {
	case Static:
	case Local:  return symbol;
	default:     return nullptr;
	}
}

const ast::Statement *Variable::get_statement() const
{
	switch (kind) {
	case Disable:
	case Break:   return statement;
	default:      return nullptr;
	}
}

int Variable::bitwidth() const
{
	switch (kind) {
	case Static:
	case Local:   return (int)symbol->getType().getBitstreamWidth();
	case Disable:
	case Break:   return 1;
	case Dummy:   return width;
	default:      log_abort();
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
	case Disable: return "disable";
	case Break:   return "break";
	case Dummy:   return "dummy(" + std::to_string(width) + ")";
	default:      log_abort();
	}
}

} // namespace slang_frontend

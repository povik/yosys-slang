#pragma once
#include "slang/ast/ASTVisitor.h"
#include "slang/ast/expressions/AssertionExpr.h"
#include "slang/ast/symbols/MemberSymbols.h"
#include <iostream>

#include "slang_frontend.h"

namespace ast = slang::ast;


void handle_sva(const ast::PropertySymbol &sym);

namespace slang_frontend {

// Visitor for handling assertions in initial blocks.
// Only processes ImmediateAssertionStatement nodes, ignoring all other statements.
struct InitialAssertionVisitor : public ast::ASTVisitor<InitialAssertionVisitor, true, false>
{
	NetlistContext &netlist;
	ProceduralContext &context;

	InitialAssertionVisitor(ProceduralContext &context);

	void handle(const ast::ImmediateAssertionStatement &stmt);
};

} // namespace slang_frontend



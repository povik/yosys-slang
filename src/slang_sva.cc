#include "slang_sva.h"
#include "slang/ast/ASTVisitor.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/EvalContext.h"
#include "slang/ast/SystemSubroutine.h"
#include "slang/diagnostics/CompilationDiags.h"
#include "slang/diagnostics/DiagnosticEngine.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/driver/Driver.h"
#include "slang/syntax/SyntaxPrinter.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/text/Json.h"
#include "slang/util/Util.h"

#include "slang/ast/Compilation.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/util/Util.h"
#include "slang/ast/ASTSerializer.h"
#include <iostream>

#include "diag.h"
#include "slang_frontend.h"

using namespace slang;
using namespace slang_frontend;

// InitialAssertionVisitor implementation

InitialAssertionVisitor::InitialAssertionVisitor(ProceduralContext &context)
	: netlist(context.netlist), context(context) {}

void InitialAssertionVisitor::handle(const ast::ImmediateAssertionStatement &stmt)
{
	if (netlist.settings.ignore_assertions.value_or(false))
		return;

	std::string flavor;
	switch (stmt.assertionKind) {
	case ast::AssertionKind::Assert:        flavor = "assert"; break;
	case ast::AssertionKind::Assume:        flavor = "assume"; break;
	case ast::AssertionKind::CoverProperty: flavor = "cover"; break;
	default:
		netlist.add_diag(diag::AssertionUnsupported, stmt.sourceRange);
		return;
	}

	auto cell = netlist.canvas->addCell(netlist.new_id(), ID($check));
	context.set_effects_trigger(cell);
	cell->setParam(ID::FLAVOR, flavor);
	cell->setParam(ID::FORMAT, std::string(""));
	cell->setParam(ID::ARGS_WIDTH, 0);
	cell->setParam(ID::PRIORITY, --context.effects_priority);
	cell->setPort(ID::ARGS, {});
	cell->setPort(ID::A, netlist.ReduceBool(context.eval(stmt.cond)));
	transfer_attrs(stmt, cell);
}

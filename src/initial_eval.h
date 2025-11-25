// clang-format off
#include "slang/ast/ASTVisitor.h"
#include "slang/ast/EvalContext.h"
#include "slang/ast/Expression.h"

namespace SlangInitial {
struct EvalVisitor {
public:
	slang::ast::EvalContext context;
	EvalVisitor(slang::ast::Compilation *compilation, bool ignore_timing = false);

	using ER = slang::ast::Statement::EvalResult;

	// for creating and initializing local variables
	// at module level
	ER visit(const slang::ast::VariableSymbol &sym);

	// for execution of initial procedural blocks
	ER visit(const slang::ast::StatementList &stmt);
	ER visit(const slang::ast::BlockStatement &stmt);
	ER visit(const slang::ast::ReturnStatement &stmt);
	ER visit(const slang::ast::BreakStatement &stmt);
	ER visit(const slang::ast::ContinueStatement &stmt);
	ER visit(const slang::ast::DisableStatement &stmt);
	ER visit(const slang::ast::VariableDeclStatement &stmt);
	ER visit(const slang::ast::ConditionalStatement &stmt);
	ER visit(const slang::ast::CaseStatement &stmt);
	ER visit(const slang::ast::PatternCaseStatement &stmt);
	ER visit(const slang::ast::ForLoopStatement &stmt);
	ER visit(const slang::ast::RepeatLoopStatement &stmt);
	ER visit(const slang::ast::ForeachLoopStatement &stmt);
	ER visit(const slang::ast::WhileLoopStatement &stmt);
	ER visit(const slang::ast::DoWhileLoopStatement &stmt);
	ER visit(const slang::ast::ForeverLoopStatement &stmt);
	ER visit(const slang::ast::ExpressionStatement &stmt);
	ER visit(const slang::ast::ImmediateAssertionStatement &stmt);
	ER visit(const slang::ast::TimedStatement &stmt);
	ER visit(const slang::ast::WaitStatement &stmt);
	ER visit(const slang::ast::EmptyStatement &stmt);
	ER visit(const slang::ast::Statement &);

	// to let clients choose the display handling
	virtual void handleDisplay(const slang::ast::CallExpression &call,
							   const std::vector<slang::ConstantValue> &args);

	bool ignore_timing;
};
};

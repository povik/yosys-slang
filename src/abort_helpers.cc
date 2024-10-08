//
// Yosys slang frontend
//
// Copyright 2024 Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
#include "slang/text/Json.h"
#include "slang/text/SourceManager.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/Expression.h"
#include "slang/ast/Statements.h"
#include "slang/ast/TimingControl.h"

#include "slang_frontend.h"

namespace slang_frontend {

extern ast::Compilation *global_compilation;

static slang::SourceRange source_location(const ast::Symbol &obj)			{ return slang::SourceRange(obj.location, obj.location); }
static slang::SourceRange source_location(const ast::Expression &expr)		{ return expr.sourceRange; }
static slang::SourceRange source_location(const ast::Statement &stmt)		{ return stmt.sourceRange; }
static slang::SourceRange source_location(const ast::TimingControl &stmt)	{ return stmt.sourceRange; }

template<typename T>
[[noreturn]] void unimplemented__(const T &obj, const char *file, int line, const char *condition)
{
	slang::JsonWriter writer;
	writer.setPrettyPrint(true);
	ast::ASTSerializer serializer(*global_compilation, writer);
	serializer.serialize(obj);
	std::cout << writer.view() << std::endl;
	auto loc = source_location(obj);
	log_assert(loc.start().buffer() == loc.end().buffer());

	if (auto sm = global_compilation->getSourceManager()) {
		std::string_view source_text = sm->getSourceText(loc.start().buffer());
		int col_no = sm->getColumnNumber(loc.start());
		const char *line_start = source_text.data() + loc.start().offset() - col_no + 1;
		const char *line_end = line_start;
		while (*line_end && *line_end != '\n' && *line_end != '\r') line_end++;
		std::cout << "Source line "
			<< (sm->isFileLoc(loc.start()) ? sm->getFileName(loc.start()) : "<internal>")
			<< ":" << sm->getLineNumber(loc.start()) << ":" << sm->getColumnNumber(loc.start())
			<< ": " << std::string_view(line_start, line_end) << std::endl;
	}

	log_error("Feature unimplemented at %s:%d, see AST and code line dump above%s%s%s\n",
			  file, line, condition ? " (failed condition \"" : "", condition ? condition : "", condition ? "\")" : "");
}

[[noreturn]] void unimplemented_(const ast::Symbol &obj, const char *file, int line, const char *condition)
{
	unimplemented__(obj, file, line, condition);
}

[[noreturn]] void unimplemented_(const ast::Expression &obj, const char *file, int line, const char *condition)
{
	unimplemented__(obj, file, line, condition);
}

[[noreturn]] void unimplemented_(const ast::Statement &obj, const char *file, int line, const char *condition)
{
	unimplemented__(obj, file, line, condition);
}

[[noreturn]] void unimplemented_(const ast::TimingControl &obj, const char *file, int line, const char *condition)
{
	unimplemented__(obj, file, line, condition);
}

};

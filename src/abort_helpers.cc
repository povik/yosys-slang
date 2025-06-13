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
#include "slang/ast/Statement.h"
#include "slang/ast/TimingControl.h"
#include "slang/ast/types/Type.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/ParameterSymbols.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"

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

[[noreturn]] void wire_missing_(NetlistContext &netlist, const ast::Symbol &symbol, const char *file, int line) {
	std::string hier = netlist.realm.getHierarchicalPath();
	log("While generating the netlist content of HDL instance %s\n\tof module %s\n",
		hier.c_str(), std::string{netlist.realm.getDefinition().name}.c_str());
	std::string params;
	for (auto param : netlist.realm.getParameters()) {
		params += " " + std::string{param->symbol.name};
		switch (param->symbol.kind) {
		case ast::SymbolKind::Parameter:
			params += "=" + param->symbol.as<ast::ParameterSymbol>().getValue().toString();
			break;
		case ast::SymbolKind::TypeParameter:
			params += "=" + param->symbol.as<ast::TypeParameterSymbol>().getTypeAlias().toString();
			break;
		default:
			params += "=<unknown>";
			break;
		}
	}
	log("\twith parameters%s\n", params.c_str());
	std::string hier2 = symbol.getHierarchicalPath();
	log("\twire for symbol %s is missing\n\t(id %s)\n", hier2.c_str(), log_id(netlist.id(symbol)));
	log("remapped scopes:\n");
	for (auto pair : netlist.scopes_remap) {
		std::string hier3 = pair.first->asSymbol().getHierarchicalPath();
		log(" %s -> %s\n", hier3.c_str(), pair.second.c_str());
	}
	if (netlist.scopes_remap.empty()) {
		log(" (none)\n");
	}
	// Ensure previous log() calls are written before exit
	log_flush();
	log_error("Internal frontend error at %s:%d, see details above\n", file, line);
}

};

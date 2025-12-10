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

using namespace slang;

void dump_property(ast::Compilation& compilation, const ast::PropertySymbol& sym) {
      JsonWriter writer;
      writer.setPrettyPrint(true);
	  ast::ASTSerializer serializer(compilation, writer);

      // Get the syntax
      auto* syntax = sym.getSyntax();
      if (!syntax) {
          std::cout << "No syntax for property "
  << sym.name << "\n";
          return;
      }

      // Cast to PropertyDeclarationSyntax
      auto& pds =syntax->as<syntax::PropertyDeclarationSyntax>();

      // Create context and bind the property spec to get the AssertionExpr tree
	  ast::ASTContext context(sym, ast::LookupLocation::max);
	  const ast::AssertionExpr& body = ast::AssertionExpr::bind(*pds.propertySpec, context);

      // NOW serialize the AssertionExpr (not the  Symbol)
      serializer.serialize(body);

      std::cout << "Property: " << sym.name <<
  "\n";
      std::cout << writer.view() << "\n";
  }


/**
 * Handles a property symbol ie:
 *
 * property <name>
 * endproperty
 */
void handle_sva(const ast::PropertySymbol &sym) {
	ast::Compilation compilation;
	// Create JSON serializer
	
	JsonWriter writer;
	writer.setPrettyPrint(true);

	// Serialize a specific symbol
	ast::ASTSerializer serializer(compilation, writer);
	serializer.serialize(sym);

	auto json = writer.view();

	std::cout << json << std::endl;


	dump_property(compilation, sym);


	auto* syntax = sym.getSyntax();
	if (!syntax) return;

	SVAVisitor sva_visitor;
	
	auto& pds = syntax->as<syntax::PropertyDeclarationSyntax>();

	// Create context for binding
	ast::ASTContext context(sym, ast::LookupLocation::max);

	// Bind the property spec -> returns the AssertionExpr tree
	const ast::AssertionExpr& root = ast::AssertionExpr::bind(*pds.propertySpec, context);

	if (root.bad()) return;


	sva_visitor.handle(root);




}

//
// Yosys slang frontend
//
// Copyright 2024 Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
#include "slang/ast/Compilation.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxPrinter.h"

#include "kernel/rtlil.h"

#include "slang_frontend.h"

namespace slang_frontend {

void import_blackboxes_from_rtlil(ast::Compilation &target, RTLIL::Design *source)
{
	using namespace slang;
	using namespace slang::ast;
	using namespace slang::syntax;
	using namespace slang::parsing;

	auto& unit = target.createScriptScope();

	for (auto module : source->modules()) {
		auto token = [&](TokenKind kind, std::string text="", bool space=false, bool eol=false) {
			char *ptr = (char *) target.allocate(text.size(), 1);
			memcpy(ptr, text.data(), text.size());

			SmallVector<Trivia, 2> trivia;
			if (space)
				trivia.push_back(Trivia(TriviaKind::Whitespace, " "sv));
			if (eol)
				trivia.push_back(Trivia(TriviaKind::EndOfLine, "\n"sv));

			return Token(target, kind, trivia.copy(target), std::string_view{ptr, text.size()},
						 SourceLocation::NoLocation);
		};

		auto integer_literal = [&](int value) {
			std::string text = std::to_string(value);
			char *ptr = (char *) target.allocate(text.size(), 1);
			memcpy(ptr, text.data(), text.size());

			return Token(target, TokenKind::IntegerLiteral, {}, std::string_view{ptr, text.size()},
						 SourceLocation::NoLocation, SVInt(value));
		};

		SmallVector<TokenOrSyntax, 16> port_list;

		for (auto portname : module->ports) {
			RTLIL::Wire *port = module->wire(portname);

			TokenKind direction;
			if (port->port_input && !port->port_output)
				direction = TokenKind::InputKeyword;
			else if (port->port_output && !port->port_input)
				direction = TokenKind::OutputKeyword;
			else
				direction = TokenKind::InOutKeyword;

			SmallVector<VariableDimensionSyntax*, 2> dims;
			dims.push_back(
				target.emplace<VariableDimensionSyntax>(
					token(TokenKind::OpenBracket, "", true),
					target.emplace<RangeDimensionSpecifierSyntax>(
						*target.emplace<RangeSelectSyntax>(
							SyntaxKind::SimpleRangeSelect,
							*target.emplace<LiteralExpressionSyntax>(
								SyntaxKind::IntegerLiteralExpression,
								integer_literal(port->width - 1)
							),
							Token(target, TokenKind::Colon, {}, "", SourceLocation::NoLocation),
							*target.emplace<LiteralExpressionSyntax>(
								SyntaxKind::IntegerLiteralExpression,
								integer_literal(0)
							)
						)
					),
					Token(target, TokenKind::CloseBracket, {}, "", SourceLocation::NoLocation)
				)
			);

			port_list.push_back(target.emplace<ImplicitAnsiPortSyntax>(
				*target.emplace<SyntaxList<AttributeInstanceSyntax>>(nullptr),
				*target.emplace<VariablePortHeaderSyntax>(
					Token(),
					token(direction, "", false, true),
					Token(),
					*target.emplace<ImplicitTypeSyntax>(
						Token(),
						*target.emplace<SyntaxList<VariableDimensionSyntax>>(
							dims.copy(target)
						),
						Token()
					)
				),
				*target.emplace<DeclaratorSyntax>(
					token(TokenKind::Identifier, RTLIL::escape_id(port->name.str()), true),
					*target.emplace<SyntaxList<VariableDimensionSyntax>>(nullptr),
					nullptr
				)
			));
			port_list.push_back(token(TokenKind::Comma));
		}
		if (!port_list.empty())
			port_list.pop_back();

		auto header = target.emplace<ModuleHeaderSyntax>(
			SyntaxKind::ModuleHeader,
			token(TokenKind::ModuleKeyword, "", false, true),
			Token(),
			token(TokenKind::Identifier, RTLIL::escape_id(module->name.str()), true),
			*target.emplace<SyntaxList<PackageImportDeclarationSyntax>>(nullptr),
			nullptr, // parameters: todo
			target.emplace<AnsiPortListSyntax>(
				token(TokenKind::OpenParenthesis),
				*target.emplace<SeparatedSyntaxList<MemberSyntax>>(port_list.copy(target)),
				token(TokenKind::CloseParenthesis)
			),
			token(TokenKind::Semicolon)
		);

		SmallVector<TokenOrSyntax, 2> attrs_spec;
		SmallVector<AttributeInstanceSyntax*, 2> attrs;
		attrs_spec.push_back(
			target.emplace<AttributeSpecSyntax>(
				token(TokenKind::Identifier, "blackbox", true),
				nullptr
			)
		);
		attrs.push_back(
			target.emplace<AttributeInstanceSyntax>(
				token(TokenKind::OpenParenthesis),
				token(TokenKind::Star),
				*target.emplace<SeparatedSyntaxList<AttributeSpecSyntax>>(attrs_spec.copy(target)),
				token(TokenKind::Star, "", true),
				token(TokenKind::CloseParenthesis)
			)
		);

		auto syntax = target.emplace<ModuleDeclarationSyntax>(
			SyntaxKind::ModuleDeclaration,
			*target.emplace<SyntaxList<AttributeInstanceSyntax>>(attrs.copy(target)),
			*header,
			*target.emplace<SyntaxList<MemberSyntax>>(nullptr),
			token(TokenKind::EndModuleKeyword, "", false, true),
			nullptr
		);

		target.createDefinition(
			unit,
			LookupLocation::min,
			*syntax
		);

		//std::cout << SyntaxPrinter().print(*syntax).str() << std::endl;
	}
}

};

//
// Yosys slang frontend
//
// Copyright 2024 Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
#include "slang/ast/Compilation.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/ASTVisitor.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxPrinter.h"
#include "slang/syntax/SyntaxTree.h"

#include "kernel/rtlil.h"

#include "slang_frontend.h"
#include "diag.h"

namespace slang_frontend {

void import_blackboxes_from_rtlil(slang::SourceManager &mgr, ast::Compilation &target, RTLIL::Design *source)
{
	using namespace slang;
	using namespace slang::ast;
	using namespace slang::syntax;
	using namespace slang::parsing;

	BumpAllocator alloc;

	auto token = [&](TokenKind kind, std::string text="", bool space=false, bool eol=false) {
		char *ptr = (char *) alloc.allocate(text.size(), 1);
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
		char *ptr = (char *) alloc.allocate(text.size(), 1);
		memcpy(ptr, text.data(), text.size());

		return Token(target, TokenKind::IntegerLiteral, {}, std::string_view{ptr, text.size()},
					 SourceLocation::NoLocation, SVInt(value));
	};

	SmallVector<MemberSyntax*, 16> decls;

	for (auto module : source->modules()) {
		std::string unescaped_id = RTLIL::unescape_id(module->name);

		if (target.tryGetDefinition(unescaped_id, target.getRootNoFinalize()).definition)
			continue;

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
				alloc.emplace<VariableDimensionSyntax>(
					token(TokenKind::OpenBracket, "", true),
					alloc.emplace<RangeDimensionSpecifierSyntax>(
						*alloc.emplace<RangeSelectSyntax>(
							SyntaxKind::SimpleRangeSelect,
							*alloc.emplace<LiteralExpressionSyntax>(
								SyntaxKind::IntegerLiteralExpression,
								integer_literal(port->width - 1)
							),
							Token(target, TokenKind::Colon, {}, "", SourceLocation::NoLocation),
							*alloc.emplace<LiteralExpressionSyntax>(
								SyntaxKind::IntegerLiteralExpression,
								integer_literal(0)
							)
						)
					),
					Token(target, TokenKind::CloseBracket, {}, "", SourceLocation::NoLocation)
				)
			);

			port_list.push_back(alloc.emplace<ImplicitAnsiPortSyntax>(
				*alloc.emplace<SyntaxList<AttributeInstanceSyntax>>(nullptr),
				*alloc.emplace<VariablePortHeaderSyntax>(
					Token(),
					token(direction, "", false, true),
					Token(),
					*alloc.emplace<ImplicitTypeSyntax>(
						Token(),
						*alloc.emplace<SyntaxList<VariableDimensionSyntax>>(
							dims.copy(target)
						),
						Token()
					)
				),
				*alloc.emplace<DeclaratorSyntax>(
					token(TokenKind::Identifier, RTLIL::escape_id(port->name.str()), true),
					*alloc.emplace<SyntaxList<VariableDimensionSyntax>>(nullptr),
					nullptr
				)
			));
			port_list.push_back(token(TokenKind::Comma));
		}
		if (!port_list.empty())
			port_list.pop_back();

		auto header = alloc.emplace<ModuleHeaderSyntax>(
			SyntaxKind::ModuleHeader,
			token(TokenKind::ModuleKeyword, "", false, true),
			Token(),
			token(TokenKind::Identifier, RTLIL::escape_id(module->name.str()), true),
			*alloc.emplace<SyntaxList<PackageImportDeclarationSyntax>>(nullptr),
			nullptr, // parameters: todo
			alloc.emplace<AnsiPortListSyntax>(
				token(TokenKind::OpenParenthesis),
				*alloc.emplace<SeparatedSyntaxList<MemberSyntax>>(port_list.copy(target)),
				token(TokenKind::CloseParenthesis)
			),
			token(TokenKind::Semicolon)
		);

		SmallVector<TokenOrSyntax, 2> attrs_spec;
		SmallVector<AttributeInstanceSyntax*, 2> attrs;
		attrs_spec.push_back(
			alloc.emplace<AttributeSpecSyntax>(
				token(TokenKind::Identifier, "blackbox", true),
				nullptr
			)
		);
		attrs.push_back(
			alloc.emplace<AttributeInstanceSyntax>(
				token(TokenKind::OpenParenthesis),
				token(TokenKind::Star),
				*alloc.emplace<SeparatedSyntaxList<AttributeSpecSyntax>>(attrs_spec.copy(target)),
				token(TokenKind::Star, "", true),
				token(TokenKind::CloseParenthesis)
			)
		);

		auto syntax = alloc.emplace<ModuleDeclarationSyntax>(
			SyntaxKind::ModuleDeclaration,
			*alloc.emplace<SyntaxList<AttributeInstanceSyntax>>(attrs.copy(target)),
			*header,
			*alloc.emplace<SyntaxList<MemberSyntax>>(nullptr),
			token(TokenKind::EndModuleKeyword, "", false, true),
			nullptr
		);

		decls.push_back(syntax);
	}

	auto unit_syntax = alloc.emplace<CompilationUnitSyntax>(
		*target.emplace<SyntaxList<MemberSyntax>>(decls.copy(target)),
		token(TokenKind::EndOfFile, "", false, false)
	);
	auto tree = std::shared_ptr<SyntaxTree>(
		new SyntaxTree(unit_syntax, mgr, std::move(alloc), &target.getDefaultLibrary(), nullptr));
	tree->isLibraryUnit = true;
	target.addSyntaxTree(tree);
}

bool is_decl_empty_module(const slang::syntax::SyntaxNode &syntax)
{
	using namespace slang::syntax;

	if (syntax.kind != SyntaxKind::ModuleDeclaration)
		return false;

	for (auto member : syntax.as<ModuleDeclarationSyntax>().members) {
		switch (member->kind) {
		case SyntaxKind::TypedefDeclaration:
		case SyntaxKind::ForwardTypedefDeclaration:
		case SyntaxKind::ParameterDeclaration:
		case SyntaxKind::TypeParameterDeclaration:
		case SyntaxKind::PortDeclaration:
		case SyntaxKind::ImplicitAnsiPort:
		case SyntaxKind::ExplicitAnsiPort:
		case SyntaxKind::TimeUnitsDeclaration:
		case SyntaxKind::FunctionDeclaration:
		case SyntaxKind::DefParam:
		case SyntaxKind::NetAlias:
			break;

		default:
			return false;
		}
	}

	return true;
}

void export_blackbox_to_rtlil(ast::Compilation &comp, const ast::InstanceSymbol &inst, RTLIL::Design *target)
{
	using namespace slang::ast;
	using namespace slang::syntax;

	RTLIL::IdString name = RTLIL::escape_id(std::string{inst.body.name});

	if (target->module(name)) {
		// Module already exists on the RLTIL side -- nothing to do
		return;
	}

	for (auto instance : comp.getRoot().topInstances) {
		if (!instance->name.compare(inst.name)) {
			// A top module with the same name will be added later, nothing to do
			return;
		}
	}

	RTLIL::Module *mod = target->addModule(name);
	mod->set_bool_attribute(ID(blackbox), true);
	transfer_attrs<const ast::Symbol>((ast::Symbol&) inst.getDefinition(), mod);

	inst.body.visit(ast::makeVisitor([&](auto&, const ast::PortSymbol &port) {
		if (!port.getSyntax() ||
				!port.getType().isFixedSize() ||
				!port.internalSymbol ||
				!port.internalSymbol->getDeclaredType()) {
			inst.body.addDiag(diag::BboxExportPortWidths, port.location);
		} else {
			const DeclaredType *dt = port.internalSymbol->getDeclaredType();
			const SyntaxNode &syntax = *dt->getTypeSyntax();
			const SyntaxList<VariableDimensionSyntax> *dims = nullptr;
			bool rejected = false;

			if (syntax.kind == SyntaxKind::ImplicitType) {
				auto &impl_type = syntax.as<ImplicitTypeSyntax>();
				dims = &impl_type.dimensions;
			} else if (IntegerTypeSyntax::isKind(syntax.kind)) {
				auto &int_type = syntax.as<IntegerTypeSyntax>();
				dims = &int_type.dimensions;
			} else {
				inst.body.addDiag(diag::BboxExportPortWidths, port.location);
				rejected = true;
			}

			if (dims) {
				for (auto dim : *dims) {
					if (!dim->specifier ||
							dim->specifier->kind != SyntaxKind::RangeDimensionSpecifier) {
						inst.body.addDiag(diag::BboxExportPortWidths, port.location);
						break;
					}
					auto &sel = dim->specifier->as<RangeDimensionSpecifierSyntax>().selector;
					if (!RangeSelectSyntax::isKind(sel->kind) ||
							!LiteralExpressionSyntax::isKind(sel->as<RangeSelectSyntax>().left->kind) ||
							!LiteralExpressionSyntax::isKind(sel->as<RangeSelectSyntax>().right->kind)) {
						inst.body.addDiag(diag::BboxExportPortWidths, port.location);
						rejected = true;
						break;
					}
				}
			}

			if (!rejected && dt->getDimensionSyntax()) {
				for (auto dim : *dt->getDimensionSyntax()) {
					if (!dim->specifier ||
							dim->specifier->kind != SyntaxKind::RangeDimensionSpecifier) {
						inst.body.addDiag(diag::BboxExportPortWidths, port.location);
						break;
					}
					auto &sel = dim->specifier->as<RangeDimensionSpecifierSyntax>().selector;

					if (RangeSelectSyntax::isKind(sel->kind)) {
						auto &range = sel->as<RangeSelectSyntax>();
						if (!LiteralExpressionSyntax::isKind(range.left->kind) ||
								!LiteralExpressionSyntax::isKind(range.right->kind)) {
							inst.body.addDiag(diag::BboxExportPortWidths, port.location);
							break;
						}
					} else if (BitSelectSyntax::isKind(sel->kind)) {
						auto &bit = sel->as<BitSelectSyntax>();
						if (!LiteralExpressionSyntax::isKind(bit.expr->kind)) {
							inst.body.addDiag(diag::BboxExportPortWidths, port.location);
							break;
						}
					} else {
						inst.body.addDiag(diag::BboxExportPortWidths, port.location);
						break;
					}
				}
			}
		}

		RTLIL::Wire *wire =
			mod->addWire(RTLIL::escape_id(std::string{port.name}), port.getType().getBitstreamWidth());
		transfer_attrs<const ast::Symbol>(port, wire);

		switch (port.direction) {
		case ast::ArgumentDirection::In:
			wire->port_input = true;
			break;
		case ast::ArgumentDirection::Out:
			wire->port_output = true;
			break;
		case ast::ArgumentDirection::InOut:
			wire->port_input = true;
			wire->port_output = true;
			break;
		default:
			auto &diag = inst.body.addDiag(diag::UnsupportedPortDirection, port.location);
			diag << ast::toString(port.direction);
			break;
		}

		mod->ports.push_back(wire->name);
		wire->port_id = mod->ports.size();
	}, [&](auto&, const ast::ParameterSymbol &param) {
		mod->avail_parameters(RTLIL::escape_id(std::string{param.name}));
	}, [&](auto&, const ast::InstanceSymbol &) {
	}));
}

};

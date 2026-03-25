//
// Yosys slang frontend
//
// Copyright Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//

#include "slang/driver/Driver.h"
#include "slang/ast/ASTSerializer.h"
#include "slang/ast/ASTVisitor.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/SystemSubroutine.h"
#include "slang/ast/symbols/AttributeSymbol.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/diagnostics/CompilationDiags.h"
#include "slang/diagnostics/DiagnosticEngine.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/text/Json.h"

#include "diag.h"
#include "slang_frontend.h"
#include "version.h"
#include "backend_builder.h"

namespace slang_frontend {

namespace syntax = slang::syntax;

ast::Compilation *global_compilation;
const slang::SourceManager *global_sourcemgr;

slang::SourceRange source_location(const ast::Symbol &obj)
{
	return slang::SourceRange(obj.location, obj.location);
}
slang::SourceRange source_location(const ast::Expression &expr)
{
	return expr.sourceRange;
}
slang::SourceRange source_location(const ast::Statement &stmt)
{
	return stmt.sourceRange;
}
slang::SourceRange source_location(const ast::TimingControl &stmt)
{
	return stmt.sourceRange;
}

template <typename T> std::string format_src(const T &obj)
{
	auto sm = global_sourcemgr;
	auto sr = source_location(obj);

	if (!sm->isFileLoc(sr.start()) || !sm->isFileLoc(sr.end()))
		return "";

	if (sr.start() == sr.end()) {
		auto loc = sr.start();
		std::string fn{sm->getFileName(loc)};
		return Yosys::stringf(
				"%s:%d.%d", fn.c_str(), (int)sm->getLineNumber(loc), (int)sm->getColumnNumber(loc));
	} else {
		std::string fn{sm->getFileName(sr.start())};
		return Yosys::stringf("%s:%d.%d-%d.%d", fn.c_str(), (int)sm->getLineNumber(sr.start()),
				(int)sm->getColumnNumber(sr.start()), (int)sm->getLineNumber(sr.end()),
				(int)sm->getColumnNumber(sr.end()));
	}
}

static RTLIL::Const convert_svint_rtlil(const slang::SVInt &svint)
{
	std::vector<RTLIL::State> bits;
	bits.reserve(svint.getBitWidth());
	for (int i = 0; i < (int)svint.getBitWidth(); i++)
		switch (svint[i].value) {
		case 0:                       bits.push_back(RTLIL::State::S0); break;
		case 1:                       bits.push_back(RTLIL::State::S1); break;
		case slang::logic_t::X_VALUE: bits.push_back(RTLIL::State::Sx); break;
		case slang::logic_t::Z_VALUE: bits.push_back(RTLIL::State::Sz); break;
		}
	return bits;
}

const std::optional<RTLIL::Const> convert_const_rtlil(
		NetlistContext &netlist, const slang::ConstantValue &constval, slang::SourceLocation loc)
{
	if (constval.bad()) {
		// no diagnostic in this case as we assume one has been raised upstream
		return {};
	} else if (constval.isReal()) {
		netlist.add_diag(diag::UnsupportedBitConversion, loc) << "real"sv;
		return {};
	} else if (constval.isShortReal()) {
		netlist.add_diag(diag::UnsupportedBitConversion, loc) << "shortreal"sv;
		return {};
	} else if (constval.isUnbounded()) {
		netlist.add_diag(diag::UnsupportedBitConversion, loc) << "unbounded symbol"sv;
		return {};
	} else if (constval.isMap()) {
		netlist.add_diag(diag::UnsupportedBitConversion, loc) << "map"sv;
		return {};
	} else if (constval.isQueue()) {
		netlist.add_diag(diag::UnsupportedBitConversion, loc) << "queue"sv;
		return {};
	} else if (constval.isUnion()) {
		netlist.add_diag(diag::UnsupportedBitConversion, loc) << "union"sv;
		return {};
	}

	if (constval.isInteger()) {
		return convert_svint_rtlil(constval.integer());
	} else if (constval.isUnpacked()) {
		std::vector<RTLIL::State> bits;
		bits.reserve(constval.getBitstreamWidth());

		auto elems = constval.elements();
		for (auto it = elems.rbegin(); it != elems.rend(); it++) {
			if (auto piece = convert_const_rtlil(netlist, *it, loc)) {
				bits.insert(bits.end(), piece->begin(), piece->end());
			} else {
				return {};
			}
		}

		log_assert(bits.size() == constval.getBitstreamWidth());
		return bits;
	} else if (constval.isString()) {
		RTLIL::Const ret = convert_svint_rtlil(constval.convertToInt().integer());
		ret.flags |= RTLIL::CONST_FLAG_STRING;
		return ret;
	} else if (constval.isNullHandle()) {
		return {};
	}

	log_abort();
}

std::optional<RTLIL::Const> convert_attr_value(
		NetlistContext &netlist, const ast::AttributeSymbol *symbol)
{
	auto value = convert_const_rtlil(netlist, symbol->getValue(), symbol->location);
	if (value) {
		// slang converts string literals to integer constants per the spec;
		// we need to look at the syntax tree to recover the information
		if (symbol->getSyntax() && symbol->getSyntax()->kind == syntax::SyntaxKind::AttributeSpec &&
				symbol->getSyntax()->template as<syntax::AttributeSpecSyntax>().value &&
				symbol->getSyntax()->template as<syntax::AttributeSpecSyntax>().value->expr->kind ==
						syntax::SyntaxKind::StringLiteralExpression) {
			value->flags |= RTLIL::CONST_FLAG_STRING;
		}
	}
	return value;
}

static const RTLIL::IdString rtlil_id(const std::string_view &view)
{
	return RTLIL::escape_id(std::string(view));
}

template <typename T>
static void transfer_attrs1(NetlistContext &netlist, T &from, RTLIL::AttrObject *to)
{
	auto src = format_src(from);
	if (!src.empty())
		to->attributes[ID::src] = src;

	for (auto attr : global_compilation->getAttributes(from)) {
		if (auto value = convert_attr_value(netlist, attr)) {
			to->attributes[rtlil_id(attr->name)] = *value;
		}
	}
}

void transfer_attrs(NetlistContext &netlist, const ast::Symbol &from, RTLIL::AttrObject *to)
{
	transfer_attrs1(netlist, from, to);
}
void transfer_attrs(NetlistContext &netlist, const ast::Statement &from, RTLIL::AttrObject *to)
{
	transfer_attrs1(netlist, from, to);
}
void transfer_attrs(NetlistContext &netlist, const ast::Expression &from, RTLIL::AttrObject *to)
{
	transfer_attrs1(netlist, from, to);
}

template <typename T>
static void transfer_attrs1(NetlistContext &netlist, T &from, AttributeGuard &guard)
{
	auto src = format_src(from);
	if (!src.empty())
		guard.set(ID::src, src);

	for (auto attr : global_compilation->getAttributes(from)) {
		if (auto value = convert_attr_value(netlist, attr)) {
			guard.set(rtlil_id(attr->name), *value);
		}
	}
}

void transfer_attrs(NetlistContext &netlist, const ast::Symbol &from, AttributeGuard &to)
{
	transfer_attrs1(netlist, from, to);
}
void transfer_attrs(NetlistContext &netlist, const ast::Statement &from, AttributeGuard &to)
{
	transfer_attrs1(netlist, from, to);
}
void transfer_attrs(NetlistContext &netlist, const ast::Expression &from, AttributeGuard &to)
{
	transfer_attrs1(netlist, from, to);
}

USING_YOSYS_NAMESPACE

struct SlangVersionPass : Pass
{
	SlangVersionPass() : Pass("slang_version", "display revision of slang frontend") {}

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("	slang_version\n");
		log("\n");
		log("Display git revisions of the slang frontend.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, [[maybe_unused]] RTLIL::Design *d) override
	{
		if (args.size() != 1)
			cmd_error(args, 1, "Extra argument");

		log("yosys-slang revision %s\n", YOSYS_SLANG_REVISION);
		log("slang revision %s\n", SLANG_REVISION);
	}
} SlangVersionPass;

static std::vector<std::string> default_options;
static std::vector<std::vector<std::string>> defaults_stack;
static std::string expected_diagnostic;

struct SlangFrontend : Frontend
{
	SlangFrontend() : Frontend("slang", "read SystemVerilog (slang)") {}

	void help() override
	{
		slang::driver::Driver driver;
		driver.addStandardArgs();
		SynthesisSettings settings;
		settings.addOptions(driver.cmdLine);
		log("%s\n", driver.cmdLine.getHelpText("Slang-based SystemVerilog frontend").c_str());
	}

	std::optional<std::string> read_heredoc(std::vector<std::string> &args)
	{
		std::string eot;

		if (!args.empty() && args.back().compare(0, 2, "<<") == 0) {
			eot = args.back().substr(2);
			args.pop_back();
		} else if (args.size() >= 2 && args[args.size() - 2] == "<<") {
			eot = args.back();
			args.pop_back();
			args.pop_back();
		} else {
			return {};
		}

		if (eot.empty())
			log_error("Missing EOT marker for reading a here-document\n");

		std::string buffer;
		bool in_script = current_script_file != nullptr;

		while (true) {
			char line[4096];
			if (!fgets(line, sizeof(line), in_script ? current_script_file : stdin))
				log_error("Unexpected EOF reading a here-document\n");

			const char *p = line;
			while (*p == ' ' || *p == '\t' || *p == '\r' || *p == '\n')
				p++;

			if (!strncmp(p, eot.data(), eot.size()) &&
					(*(p + eot.size()) == '\r' || *(p + eot.size()) == '\n'))
				break;
			else
				buffer += line;
		}

		return buffer;
	}

	// There are three cases handled by this function:
	// 1. Normal mode; no expected diagnostics. Return `false` to continue executing.
	// 2. Test mode; expected diagnostic found. Return `true` to exit early with success.
	// 3a. Test mode; expected diagnostic not found but more could appear later. Return `false`.
	// 3b. Test mode; expected diagnostic not found. Use `log_error()` to exit early with failure.
	bool check_diagnostics(slang::DiagnosticEngine &diagEngine,
			const slang::SmallVector<slang::Diagnostic> &diags, bool last)
	{
		if (expected_diagnostic.empty())
			return false;

		for (auto &diag : diags) {
			auto message = diagEngine.formatMessage(diag);
			if (message == expected_diagnostic) {
				log("Expected diagnostic `%s' found\n", expected_diagnostic.c_str());
				expected_diagnostic.clear();
				return true;
			}
		}
		if (last)
			log_error("Expected diagnostic `%s' but none emitted\n", expected_diagnostic.c_str());
		else
			return false;
	}

	void execute(std::istream *&f, std::string filename, std::vector<std::string> args,
			RTLIL::Design *design) override
	{
		(void)f;
		(void)filename;
		log_header(design, "Executing SLANG frontend.\n");

		// names of RTLIL modules added in this invocation; does not include blackboxes
		std::vector<RTLIL::IdString> emitted_module_names;
		slang::driver::Driver driver;
		driver.addStandardArgs();
		SynthesisSettings settings;
		settings.addOptions(driver.cmdLine);
		diag::setup_messages(driver.diagEngine);

		{
			if (auto heredoc = read_heredoc(args)) {
				auto buffer = driver.sourceManager.assignText(
						"<inlined>", std::string_view{heredoc.value()});
				driver.sourceLoader.addBuffer(buffer);
			}

			args.insert(args.begin() + 1, default_options.begin(), default_options.end());

			std::vector<std::unique_ptr<char[]>> c_args_guard;
			std::vector<char *> c_args;

			for (auto arg : args) {
				char *c = new char[arg.size() + 1];
				strcpy(c, arg.c_str());
				c_args_guard.emplace_back(c);
				c_args.push_back(c);
			}

			if (!driver.parseCommandLine(c_args.size(), &c_args[0]))
				log_cmd_error("Bad command\n");
		}

		fixup_options(settings, driver);
		if (!driver.processOptions())
			log_cmd_error("Bad command\n");
		catch_forbidden_options(driver);

		try {
			if (!driver.parseAllSources())
				log_error("Parsing failed\n");

			auto compilation = driver.createCompilation();

			if (settings.extern_modules.value_or(true))
				import_blackboxes_from_rtlil(driver.sourceManager, *compilation, design);

			if (settings.dump_ast.value_or(false)) {
				slang::JsonWriter writer;
				writer.setPrettyPrint(true);
				ast::ASTSerializer serializer(*compilation, writer);
				serializer.serialize(compilation->getRoot());
				std::cout << writer.view() << std::endl;
			}

			bool in_succesful_failtest = false;

			driver.reportCompilation(*compilation, /* quiet */ false);
			if (check_diagnostics(
						driver.diagEngine, compilation->getAllDiagnostics(), /*last=*/false))
				in_succesful_failtest = true;

			if (driver.diagEngine.getNumErrors()) {
				// Stop here should there have been any errors from AST compilation,
				// PopulateNetlist requires a well-formed AST without error nodes
				(void)driver.reportDiagnostics(/* quiet */ false);
				if (!in_succesful_failtest)
					log_error("Compilation failed\n");
				return;
			}

			if (settings.ast_compilation_only.value_or(false)) {
				(void)driver.reportDiagnostics(/* quiet */ false);
				return;
			}

			global_compilation = &(*compilation);
			global_sourcemgr = compilation->getSourceManager();

			HierarchyQueue hqueue;
			for (auto instance : compilation->getRoot().topInstances) {
				if (instance->getDefinition().definitionKind == ast::DefinitionKind::Program) {
					slang::Diagnostic program_diag(diag::ProgramUnsupported, instance->location);
					driver.diagEngine.issue(program_diag);
					continue;
				}

				auto ref_body = &get_instance_body(settings, *instance);
				log_assert(ref_body->parentInstance);

				auto backend = std::make_unique<BackendGraphBuilder>();
				backend->canvas = design->addModule(RTLIL::escape_id(module_type_id(*ref_body)));
				auto [netlist, new_] = hqueue.get_or_emplace(
						ref_body, std::move(backend), settings, *compilation, *ref_body->parentInstance);
				log_assert(new_);
				netlist.backend->canvas->attributes[ID::top] = 1;
			}

			for (int i = 0; i < (int)hqueue.queue.size(); i++) {
				NetlistContext &netlist = *hqueue.queue[i];
				emitted_module_names.push_back(netlist.backend->canvas->name);

				if (netlist.disabled)
					continue;

				populate_netlist(hqueue, netlist);

				slang::Diagnostics diags;
				diags.append_range(netlist.issued_diagnostics);
				diags.sort(driver.sourceManager);

				if (check_diagnostics(driver.diagEngine, diags, /*last=*/false))
					in_succesful_failtest = true;

				for (int i = 0; i < (int)diags.size(); i++) {
					if (i > 0 && diags[i] == diags[i - 1])
						continue;
					driver.diagEngine.issue(diags[i]);
				}
			}

			if (check_diagnostics(driver.diagEngine, {}, /*last=*/true))
				in_succesful_failtest = true;

			if (!driver.reportDiagnostics(/* quiet */ false)) {
				if (!in_succesful_failtest)
					log_error("Compilation failed\n");
				return;
			}
		} catch (const std::exception &e) {
			log_error("Exception: %s\n", e.what());
		}

		if (!settings.no_proc.value_or(false)) {
			// Hack to get an empty selection in a way compatible with both pre and post Yosys v0.52
			// Front of the selection stack should be a "full selection" at any time, and we can
			// amend it.
			RTLIL::Selection emitted_modules = design->selection_stack.front();
			emitted_modules.full_selection = false;
			for (auto name : emitted_module_names)
				emitted_modules.selected_modules.insert(name);

			design->selection_stack.push_back(emitted_modules);

			log_push();
			call(design, "proc_clean");
			call(design, "tribuf");
			call(design, "proc_rmdead");
			call(design, "proc_prune");
			call(design, "proc_init");
			call(design, "proc_rom");
			call(design, "proc_mux");
			call(design, "proc_clean");
			call(design, "opt_expr -keepdc");
			log_pop();

			design->selection_stack.pop_back();
		}
	}
} SlangFrontend;

struct SlangDefaultsPass : Pass
{
	SlangDefaultsPass() : Pass("slang_defaults", "set default options for read_slang") {}

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("	slang_defaults -add [options]\n");
		log("\n");
		log("Add default options for subsequent calls to read_slang.\n");
		log("\n");
		log("\n");
		log("	slang_defaults -clear\n");
		log("\n");
		log("Clear the list of default options to read_slang.\n");
		log("\n");
		log("\n");
		log("	slang_defaults -push\n");
		log("	slang_defaults -pop\n");
		log("\n");
		log("Push or pop the default option list to a stack. On -push the list isn't cleared.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, [[maybe_unused]] RTLIL::Design *d) override
	{
		if (args.size() < 2)
			cmd_error(args, 1, "Missing argument");

		if (args[1] == "-add") {
			default_options.insert(default_options.end(), args.begin() + 2, args.end());
		} else {
			if (args.size() != 2)
				cmd_error(args, 2, "Extra argument");

			if (args[1] == "-clear") {
				default_options.clear();
			} else if (args[1] == "-push") {
				defaults_stack.push_back(default_options);
			} else if (args[1] == "-pop") {
				if (!defaults_stack.empty()) {
					default_options.swap(defaults_stack.back());
					defaults_stack.pop_back();
				} else {
					default_options.clear();
				}
			} else {
				cmd_error(args, 1, "Unknown option");
			}
		}
	}
} SlangDefaultsPass;

struct TestSlangDiagPass : Pass
{
	TestSlangDiagPass() : Pass("test_slangdiag", "test diagnostics emission by the slang frontend")
	{}

	void help() override { log("Perform internal test of the slang frontend.\n"); }

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing TEST_SLANGDIAG pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-expect" && argidx + 1 < args.size()) {
				std::string message = args[++argidx];
				if (message.front() == '\"' && message.back() == '\"')
					message = message.substr(1, message.size() - 2);
				expected_diagnostic = message;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design, false);
	}
} TestSlangDiagPass;

class TFunc : public ast::SystemSubroutine
{
public:
	TFunc() : ast::SystemSubroutine("$t", ast::SubroutineKind::Function) {}

	const ast::Type &checkArguments(const ast::ASTContext &context, const Args &args,
			slang::SourceRange range, const ast::Expression *) const final
	{
		auto &comp = context.getCompilation();
		if (!checkArgCount(context, false, args, range, 1, 1))
			return comp.getErrorType();
		return comp.getVoidType();
	}

	slang::ConstantValue eval(ast::EvalContext &context, const Args &, slang::SourceRange range,
			const ast::CallExpression::SystemCallInfo &) const final
	{
		notConst(context, range);
		return nullptr;
	}
};

struct TestSlangExprPass : Pass
{
	TestSlangExprPass() : Pass("test_slangexpr", "test expression evaluation within slang frontend")
	{}

	void help() override { log("Perform internal test of the slang frontend.\n"); }

	void execute(std::vector<std::string> args, RTLIL::Design *d) override
	{
		log_header(d, "Executing TEST_SLANGEXPR pass.\n");

		slang::driver::Driver driver;
		driver.addStandardArgs();
		SynthesisSettings settings;
		settings.addOptions(driver.cmdLine);
		diag::setup_messages(driver.diagEngine);

		{
			std::vector<char *> c_args;
			for (auto arg : args) {
				char *c = new char[arg.size() + 1];
				strcpy(c, arg.c_str());
				c_args.push_back(c);
			}
			if (!driver.parseCommandLine(c_args.size(), &c_args[0]))
				log_cmd_error("Bad command\n");
		}

		fixup_options(settings, driver);
		if (!driver.processOptions())
			log_cmd_error("Bad command\n");

		if (!driver.parseAllSources())
			log_error("Parsing failed\n");

		auto compilation = driver.createCompilation();
		auto tfunc = std::make_shared<TFunc>();
		compilation->addSystemSubroutine(tfunc);

		if (settings.dump_ast.value_or(false)) {
			slang::JsonWriter writer;
			writer.setPrettyPrint(true);
			ast::ASTSerializer serializer(*compilation, writer);
			serializer.serialize(compilation->getRoot());
			std::cout << writer.view() << std::endl;
		}

		log_assert(compilation->getRoot().topInstances.size() == 1);
		auto *top = compilation->getRoot().topInstances[0];
		compilation->forceElaborate(top->body);

		driver.reportCompilation(*compilation, /* quiet */ false);
		if (driver.diagEngine.getNumErrors()) {
			(void)driver.reportDiagnostics(/* quiet */ false);
			log_error("Compilation failed\n");
			return;
		}

		global_compilation = &(*compilation);
		global_sourcemgr = compilation->getSourceManager();

		auto backend = std::make_unique<BackendGraphBuilder>();
		backend->canvas = d->addModule("\\top");
		NetlistContext netlist(std::move(backend), settings, *compilation, *top);
		add_internal_symbols(netlist, top->body);

		EvalContext amended_eval(netlist);
		amended_eval.ignore_ast_constants = true;

		int ntests = 0;
		int nfailures = 0;

		top->visit(ast::makeVisitor(
				[&](auto &, const ast::SubroutineSymbol &) {
					// ignore
				},
				[&](auto &, const ast::ExpressionStatement &stmt) {
					assert(stmt.expr.kind == ast::ExpressionKind::Call);
					auto &call = stmt.expr.as<ast::CallExpression>();
					assert(call.getSubroutineName() == "$t");
					auto expr = call.arguments()[0];

					SigSpec ref = netlist.eval(*expr);
					SigSpec test = amended_eval(*expr);

					slang::SourceRange sr = expr->sourceRange;
					std::string_view text =
							global_sourcemgr->getSourceText(sr.start().buffer())
									.substr(sr.start().offset(),
											sr.end().offset() - sr.start().offset());

					if (ref == test) {
						log_debug("%s: %s (ref) == %s (test) # %s\n", format_src(*expr).c_str(),
								log_signal(ref), log_signal(test), std::string(text).c_str());
						ntests++;
					} else {
						log("%s: %s (ref) == %s (test) # %s\n", format_src(*expr).c_str(),
								log_signal(ref), log_signal(test), std::string(text).c_str());
						ntests++;
						nfailures++;
					}
				}));

		if (!nfailures)
			log("%d tests passed.\n", ntests);
		else
			log_error("%d out of %d tests failed.\n", nfailures, ntests);
	}
} TestSlangExprPass;

}; // namespace slang_frontend

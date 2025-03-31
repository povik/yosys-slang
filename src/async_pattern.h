//
// Yosys slang frontend
//
// Copyright 2024 Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
#pragma once
#include "slang_frontend.h"

namespace slang_frontend {

struct TimingPatternInterpretor {
	TimingPatternInterpretor(DiagnosticIssuer& issuer)
		: issuer(issuer) {};

	struct AsyncBranch {
		const ast::Expression &trigger;
		bool polarity;
		const ast::Statement &body;
	};

	virtual void handle_comb_like_process(const ast::ProceduralBlockSymbol &symbol,
										  const ast::Statement &body) = 0;


	virtual void handle_ff_process(const ast::ProceduralBlockSymbol &symbol,
								   const ast::SignalEventControl &clock,
								   std::vector<const ast::Statement *> prologue,
								   const ast::Statement &sync_body,
								   std::span<AsyncBranch> async) = 0;

	virtual void handle_initial_process(const ast::ProceduralBlockSymbol &symbol,
										const ast::Statement &body) = 0;

	void interpret(const ast::ProceduralBlockSymbol &symbol);

private:
	void handle_always(const ast::ProceduralBlockSymbol &symbol);
	void interpret_async_pattern(const ast::ProceduralBlockSymbol &symbol,
								 std::vector<const ast::SignalEventControl *> triggers,
								 const ast::Statement &body);

	DiagnosticIssuer& issuer;
};

};

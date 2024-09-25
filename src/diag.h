//
// Yosys slang frontend
//
// Copyright 2024 Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
#pragma once
#include "slang/diagnostics/Diagnostics.h"
#include "slang/diagnostics/DiagnosticEngine.h"

namespace slang_frontend {
namespace diag {
extern slang::DiagCode IffUnsupported;
extern slang::DiagCode SignalSensitivityAmbiguous;
extern slang::DiagCode EdgeImplicitMixing;
extern slang::DiagCode GenericTimingUnsyn;
extern slang::DiagCode BothEdgesUnsupported;
extern slang::DiagCode NoteSignalEvent;
extern slang::DiagCode ExpectingIfElseAload;
extern slang::DiagCode NoteDuplicateEdgeSense;
extern slang::DiagCode IfElseAloadPolarity;
extern slang::DiagCode IfElseAloadMismatch;
extern slang::DiagCode LatchNotInferred;
extern slang::DiagCode MissingAload;
extern slang::DiagCode NoteProcessDriver;
extern slang::DiagCode AlwaysFFBadTiming;
extern slang::DiagCode ForLoopIndeterminate;
extern slang::DiagCode NoteUnrollCycles;
extern slang::DiagCode MissingStopCondition;
extern slang::DiagCode ComplexLatchLHS;
extern slang::DiagCode BadMemoryExpr;
extern slang::DiagCode MemoryNotInferred;
extern slang::DiagCode NoteUsageBlame;
extern slang::DiagCode UnrollLimitExhausted;
extern slang::DiagCode NoteLoopContributes;
void setup_messages(slang::DiagnosticEngine &engine);
};
};

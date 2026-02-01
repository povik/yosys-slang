//
// Yosys slang frontend
//
// Copyright 2024 Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
#pragma once
#include "slang/diagnostics/DiagnosticEngine.h"
#include "slang/diagnostics/Diagnostics.h"

namespace slang_frontend {
namespace diag {
extern slang::DiagCode IffUnsupported;
extern slang::DiagCode SignalSensitivityAmbiguous;
extern slang::DiagCode EdgeImplicitMixing;
extern slang::DiagCode GenericTimingUnsyn;
extern slang::DiagCode BothEdgesUnsupported;
extern slang::DiagCode WaitStatementUnsupported;
extern slang::DiagCode NoteSignalEvent;
extern slang::DiagCode ExpectingIfElseAload;
extern slang::DiagCode NoteDuplicateEdgeSense;
extern slang::DiagCode IfElseAloadPolarity;
extern slang::DiagCode IfElseAloadMismatch;
extern slang::DiagCode LatchNotInferred;
extern slang::DiagCode MissingAload;
extern slang::DiagCode NoteProcessDriver;
extern slang::DiagCode AlwaysFFBadTiming;
extern slang::DiagCode MissingStopCondition;
extern slang::DiagCode BadMemoryExpr;
extern slang::DiagCode MemoryNotInferred;
extern slang::DiagCode NoteUsageBlame;
extern slang::DiagCode UnrollLimitExhausted;
extern slang::DiagCode NoteLoopContributes;
extern slang::DiagCode NonconstWildcardEq;
extern slang::DiagCode AssertionUnsupported;
extern slang::DiagCode LangFeatureUnsupported;
extern slang::DiagCode UnsupportedLhs;
extern slang::DiagCode ArgumentTypeUnsupported;
extern slang::DiagCode LangFeatureUnsupported;
extern slang::DiagCode MultiportUnsupported;
extern slang::DiagCode UnsupportedBlackboxConnection;
extern slang::DiagCode UnsupportedPortDirection;
extern slang::DiagCode ModportRequired;
extern slang::DiagCode FixedSizeRequired;
extern slang::DiagCode AloadOne;
extern slang::DiagCode BadInlinedPortConnection;
extern slang::DiagCode NoParamsOnUnkBboxes;
extern slang::DiagCode ConnNameRequiredOnUnkBboxes;
extern slang::DiagCode BboxTypeParameter;
extern slang::DiagCode BboxExportPortWidths;
extern slang::DiagCode NoteIgnoreInitial;
extern slang::DiagCode PortCorrespondence;
extern slang::DiagCode UnsynthesizableFeature;
extern slang::DiagCode SVAUnsupported;
extern slang::DiagCode ExpectStatementUnsupported;
extern slang::DiagCode ProgramUnsupported;
extern slang::DiagCode ForbiddenDemotion;
extern slang::DiagCode UdpUnsupported;
extern slang::DiagCode PrimTypeUnsupported;
extern slang::DiagCode ReferenceAcrossKeptHierBoundary;
extern slang::DiagCode NoteModuleBlackboxBecauseAttribute;
extern slang::DiagCode NoteModuleBlackboxBecauseEmpty;
extern slang::DiagCode NoteModuleNotDissolvedBecauseBlackbox;
extern slang::DiagCode NoteModuleNotDissolvedBecauseKeepHierarchy;
extern slang::DiagCode BlockingAssignmentAfterNonblocking;
extern slang::DiagCode NonblockingAssignmentAfterBlocking;
extern slang::DiagCode NotePreviousAssignment;
extern slang::DiagCode NetTypeUnsupported;
extern slang::DiagCode NoAllowTopLevelIfacePorts;
extern slang::DiagCode RefUnsupported;
extern slang::DiagCode InlinedInOutUnsupported;
extern slang::DiagCode PastGatingClockingUnsupported;
extern slang::DiagCode SystemFunctionRequireClockedBlock;
extern slang::DiagCode UnsupportedBitConversion;

void setup_messages(slang::DiagnosticEngine &engine);
}; // namespace diag
}; // namespace slang_frontend

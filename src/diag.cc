//
// Yosys slang frontend
//
// Copyright 2024 Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
#include "slang_frontend.h"
#include "diag.h"

namespace slang_frontend {

using DiagCode = slang::DiagCode;
using DiagGroup = slang::DiagGroup;
using DiagSubsystem = slang::DiagSubsystem;
using Diagnostic = slang::Diagnostic;
using Diagnostics = slang::Diagnostics;
using DiagnosticEngine = slang::DiagnosticEngine;
using DiagnosticSeverity = slang::DiagnosticSeverity;
using SourceRange = slang::SourceRange;
using SourceLocation = slang::SourceLocation;

Diagnostic& DiagnosticIssuer::add_diag(DiagCode code, SourceLocation location)
{
	issued_diagnostics.emplace_back(code, location);
	return issued_diagnostics.back();
}

Diagnostic& DiagnosticIssuer::add_diag(DiagCode code, SourceRange sourceRange)
{
	Diagnostic &diag = add_diag(code, sourceRange.start());
	diag << sourceRange;
	return diag;
}

void DiagnosticIssuer::add_diag(Diagnostic diag)
{
	issued_diagnostics.push_back(diag);
}

void DiagnosticIssuer::add_diagnostics(const Diagnostics& diagnostics)
{
	for (const Diagnostic& diag : diagnostics)
		add_diag(diag);
}

void DiagnosticIssuer::report_into(DiagnosticEngine &engine)
{
	for (auto& diag : issued_diagnostics)
		engine.issue(diag);
}

namespace diag {
	DiagCode IffUnsupported(DiagSubsystem::Netlist, 1000);
	DiagCode SignalSensitivityAmbiguous(DiagSubsystem::Netlist, 1001);
	DiagCode EdgeImplicitMixing(DiagSubsystem::Netlist, 1002);
	DiagCode GenericTimingUnsyn(DiagSubsystem::Netlist, 1003);
	DiagCode BothEdgesUnsupported(DiagSubsystem::Netlist, 1004);
	DiagCode NoteSignalEvent(DiagSubsystem::Netlist, 1005);
	DiagCode ExpectingIfElseAload(DiagSubsystem::Netlist, 1006);
	DiagCode NoteDuplicateEdgeSense(DiagSubsystem::Netlist, 1007);
	DiagCode IfElseAloadPolarity(DiagSubsystem::Netlist, 1008);
	DiagCode IfElseAloadMismatch(DiagSubsystem::Netlist, 1009);
	DiagCode LatchNotInferred(DiagSubsystem::Netlist, 1010);
	DiagCode MissingAload(DiagSubsystem::Netlist, 1012);
	DiagCode NoteProcessDriver(DiagSubsystem::Netlist, 1013);
	DiagCode AlwaysFFBadTiming(DiagSubsystem::Netlist, 1014);

	DiagCode MissingStopCondition(DiagSubsystem::Netlist, 1017);

	DiagCode BadMemoryExpr(DiagSubsystem::Netlist, 1019);
	DiagCode MemoryNotInferred(DiagSubsystem::Netlist, 1020);
	DiagCode NoteUsageBlame(DiagSubsystem::Netlist, 1021);

	DiagCode UnrollLimitExhausted(DiagSubsystem::Netlist, 1022);
	DiagCode NoteLoopContributes(DiagSubsystem::Netlist, 1023);

	DiagCode NonconstWildcardEq(DiagSubsystem::Netlist, 1024);

	DiagCode AssertionUnsupported(DiagSubsystem::Netlist, 1025);
	DiagCode LangFeatureUnsupported(DiagSubsystem::Netlist, 1026);
	DiagCode UnsupportedLhs(DiagSubsystem::Netlist, 1027);
	DiagCode ArgumentTypeUnsupported(DiagSubsystem::Netlist, 1028);
	DiagCode MultiportUnsupported(DiagSubsystem::Netlist, 1029);
	DiagCode UnsupportedBlackboxConnection(DiagSubsystem::Netlist, 1030);
	DiagCode UnsupportedPortDirection(DiagSubsystem::Netlist, 1031);
	DiagCode ModportRequired(DiagSubsystem::Netlist, 1032);
	DiagCode FixedSizeRequired(DiagSubsystem::Netlist, 1033);
	DiagCode AloadOne(DiagSubsystem::Netlist, 1034);
	DiagCode BadInlinedPortConnection(DiagSubsystem::Netlist, 1035);
	DiagCode NoParamsOnUnkBboxes(DiagSubsystem::Netlist, 1037);
	DiagCode ConnNameRequiredOnUnkBboxes(DiagSubsystem::Netlist, 1038);
	DiagCode BboxTypeParameter(DiagSubsystem::Netlist, 1039);
	DiagCode BboxExportPortWidths(DiagSubsystem::Netlist, 1040);
	DiagCode NoteIgnoreInitial(DiagSubsystem::Netlist, 1041);
	DiagCode PortCorrespondence(DiagSubsystem::Netlist, 1042);
	DiagCode UnsynthesizableFeature(DiagSubsystem::Netlist, 1043);
	DiagCode SVAUnsupported(DiagSubsystem::Netlist, 1044);
	DiagCode ForbiddenDemotion(DiagSubsystem::Netlist, 1045);
	DiagCode UdpUnsupported(DiagSubsystem::Netlist, 1046);
	DiagCode PrimTypeUnsupported(DiagSubsystem::Netlist, 1047);
	DiagCode ReferenceAcrossKeptHierBoundary(DiagSubsystem::Netlist, 1048);
	DiagCode NoteModuleBlackboxBecauseAttribute(DiagSubsystem::Netlist, 1049);
	DiagCode NoteModuleBlackboxBecauseEmpty(DiagSubsystem::Netlist, 1050);
	DiagCode NoteModuleNotDissolvedBecauseBlackbox(DiagSubsystem::Netlist, 1051);
	DiagCode NoteModuleNotDissolvedBecauseKeepHierarchy(DiagSubsystem::Netlist, 1052);

	DiagGroup unsynthesizable("unsynthesizable", {IffUnsupported, GenericTimingUnsyn, BothEdgesUnsupported, ExpectingIfElseAload,
														 IfElseAloadPolarity, IfElseAloadMismatch, UnsynthesizableFeature});
	DiagGroup sanity("sanity", {EdgeImplicitMixing});

	void setup_messages(slang::DiagnosticEngine &engine)
	{
		engine.setMessage(IffUnsupported, "iff qualifier will not be synthesized");
		engine.setMessage(SignalSensitivityAmbiguous, "non-edge sensitivity on a signal will be synthesized as @* sensitivity");
		engine.setSeverity(SignalSensitivityAmbiguous, DiagnosticSeverity::Warning);
		engine.setMessage(EdgeImplicitMixing, "mixing of implicit and edge sensitivity");
		engine.setMessage(GenericTimingUnsyn, "unsynthesizable timing control (ignore with '--ignore-timing')");
		engine.setMessage(BothEdgesUnsupported, "'edge' sensitivity will not be synthesized");
		engine.setMessage(NoteSignalEvent, "signal event specified here");
		engine.setSeverity(NoteSignalEvent, DiagnosticSeverity::Note);

		engine.setMessage(ExpectingIfElseAload, "simple if-else pattern expected in modeling an asynchronous load on a flip-flop");
		engine.setMessage(NoteDuplicateEdgeSense, "asynchronous load pattern implied by edge sensitivity on multiple signals");
		engine.setSeverity(NoteDuplicateEdgeSense, DiagnosticSeverity::Note);

		engine.setMessage(IfElseAloadPolarity, "polarity of condition doesn't match edge sensitivity");
		engine.setMessage(IfElseAloadMismatch, "condition cannot be matched to any signal from the event list");

		engine.setMessage(LatchNotInferred, "latch not inferred for variable '{}' driven from always_latch procedure");
		engine.setSeverity(LatchNotInferred, DiagnosticSeverity::Warning);

		engine.setMessage(MissingAload, "asynchronous load value missing for variable '{}'");
		engine.setSeverity(MissingAload, DiagnosticSeverity::Warning);
		engine.setMessage(NoteProcessDriver, "variable driven from this procedure");
		engine.setSeverity(NoteProcessDriver, DiagnosticSeverity::Note);

		engine.setMessage(AlwaysFFBadTiming, "timing control does not model a flip-flop");
		engine.setSeverity(AlwaysFFBadTiming, DiagnosticSeverity::Error);

		engine.setMessage(MissingStopCondition, "stop condition is missing; loop cannot be unrolled");
		engine.setSeverity(MissingStopCondition, DiagnosticSeverity::Error);

		engine.setMessage(BadMemoryExpr, "unsupported operation on a memory variable");
		engine.setSeverity(BadMemoryExpr, DiagnosticSeverity::Error);

		engine.setMessage(MemoryNotInferred, "cannot infer memory from a variable despite '{}' attribute");
		engine.setSeverity(MemoryNotInferred, DiagnosticSeverity::Error);
		engine.setMessage(NoteUsageBlame, "inference prevented by variable usage here");
		engine.setSeverity(NoteUsageBlame, DiagnosticSeverity::Note);

		for (auto code : unsynthesizable.getDiags())
			engine.setSeverity(code, DiagnosticSeverity::Error);
		for (auto code : sanity.getDiags())
			engine.setSeverity(code, DiagnosticSeverity::Error);

		engine.setMessage(UnrollLimitExhausted, "unroll limit of {} exhausted [--unroll-limit=]");
		engine.setSeverity(UnrollLimitExhausted, DiagnosticSeverity::Error);

		engine.setMessage(NoteLoopContributes, "loop contributes to unroll tally");
		engine.setSeverity(NoteLoopContributes, DiagnosticSeverity::Note);

		engine.setMessage(NonconstWildcardEq, "wildcard equality unsynthesizable with non-constant right-hand operand");
		engine.setSeverity(NonconstWildcardEq, DiagnosticSeverity::Error);

		engine.setMessage(AssertionUnsupported, "unsupported assertion statement");
		engine.setSeverity(AssertionUnsupported, DiagnosticSeverity::Error);

		engine.setMessage(LangFeatureUnsupported, "unsupported language feature");
		engine.setSeverity(LangFeatureUnsupported, DiagnosticSeverity::Error);

		engine.setMessage(UnsupportedLhs, "unsupported assignment target expression");
		engine.setSeverity(UnsupportedLhs, DiagnosticSeverity::Error);

		engine.setMessage(ArgumentTypeUnsupported, "unsupported argument type: {}");
		engine.setSeverity(ArgumentTypeUnsupported, DiagnosticSeverity::Error);

		engine.setMessage(MultiportUnsupported, "multiports unsupported on kept module boundary");
		engine.setSeverity(MultiportUnsupported, DiagnosticSeverity::Error);

		engine.setMessage(UnsupportedBlackboxConnection, "{} port on blackbox instance unsupported");
		engine.setSeverity(UnsupportedBlackboxConnection, DiagnosticSeverity::Error);

		engine.setMessage(UnsupportedPortDirection, "port direction '{}' on kept module boundary unsupported");
		engine.setSeverity(UnsupportedPortDirection, DiagnosticSeverity::Error);

		engine.setMessage(ModportRequired, "interface port on kept module boundary must be a modport");
		engine.setSeverity(ModportRequired, DiagnosticSeverity::Error);

		engine.setMessage(FixedSizeRequired, "expression of type {} with dynamic size unsupported for synthesis");
		engine.setSeverity(FixedSizeRequired, DiagnosticSeverity::Error);

		engine.setMessage(AloadOne, "multiple asynchronous loads unsupported");
		engine.setSeverity(AloadOne, DiagnosticSeverity::Error);

		engine.setMessage(BadInlinedPortConnection, "direction '{}' on inlined port connection unsupported");
		engine.setSeverity(BadInlinedPortConnection, DiagnosticSeverity::Error);

		engine.setMessage(NoParamsOnUnkBboxes, "parameters on unknown blackboxes unsupported");
		engine.setSeverity(NoParamsOnUnkBboxes, DiagnosticSeverity::Error);

		engine.setMessage(ConnNameRequiredOnUnkBboxes, "port name required in connections on unknown blackboxes");
		engine.setSeverity(ConnNameRequiredOnUnkBboxes, DiagnosticSeverity::Error);

		engine.setMessage(BboxTypeParameter, "blackbox cannot have a type parameter");
		engine.setSeverity(BboxTypeParameter, DiagnosticSeverity::Error);

		engine.setMessage(BboxExportPortWidths, "cannot export a blackbox definition with non-constant port widths");
		engine.setSeverity(BboxExportPortWidths, DiagnosticSeverity::Error);

		engine.setMessage(NoteIgnoreInitial, "use option '--ignore-initial' to ignore initial procedures");
		engine.setSeverity(NoteIgnoreInitial, DiagnosticSeverity::Note);

		engine.setMessage(PortCorrespondence, "ports without direct correspondence to an internal net/variable unsupported");
		engine.setSeverity(PortCorrespondence, DiagnosticSeverity::Error);

		engine.setMessage(UnsynthesizableFeature, "unsynthesizable feature");

		engine.setMessage(SVAUnsupported, "SVA unsupported (ignore all assertions with '--ignore-assertions')");
		engine.setSeverity(SVAUnsupported, DiagnosticSeverity::Error);

		engine.setMessage(ForbiddenDemotion, "disabling error '{}' is unsupported");
		engine.setSeverity(ForbiddenDemotion, DiagnosticSeverity::Error);

		engine.setMessage(UdpUnsupported, "user-defined primitives unsupported");
		engine.setSeverity(UdpUnsupported, DiagnosticSeverity::Error);

		engine.setMessage(PrimTypeUnsupported, "primitives of type '{}' unsupported");
		engine.setSeverity(PrimTypeUnsupported, DiagnosticSeverity::Error);

		engine.setMessage(ReferenceAcrossKeptHierBoundary, "hierarchical reference across preserved module boundary");
		engine.setSeverity(ReferenceAcrossKeptHierBoundary, DiagnosticSeverity::Error);
		engine.setMessage(NoteModuleBlackboxBecauseAttribute, "module '{}' is a blackbox because of attribute");
		engine.setSeverity(NoteModuleBlackboxBecauseAttribute, DiagnosticSeverity::Note);
		engine.setMessage(NoteModuleBlackboxBecauseEmpty, "module '{}'' is a blackbox because of empty body");
		engine.setSeverity(NoteModuleBlackboxBecauseEmpty, DiagnosticSeverity::Note);
		engine.setMessage(NoteModuleNotDissolvedBecauseBlackbox, "instance of module '{}' will not dissolve because the module is a blackbox");
		engine.setSeverity(NoteModuleNotDissolvedBecauseBlackbox, DiagnosticSeverity::Note);
		engine.setMessage(NoteModuleNotDissolvedBecauseKeepHierarchy, "instance of module '{}' will not dissolve because of '--keep-hierarchy' option");
		engine.setSeverity(NoteModuleNotDissolvedBecauseKeepHierarchy, DiagnosticSeverity::Note);
	}
};
};

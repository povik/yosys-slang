//
// Yosys slang frontend
//
// Copyright 2024 Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
#include "diag.h"

namespace slang_frontend {
namespace diag {
	slang::DiagCode IffUnsupported(slang::DiagSubsystem::Netlist, 1000);
	slang::DiagCode SignalSensitivityAmbiguous(slang::DiagSubsystem::Netlist, 1001);
	slang::DiagCode EdgeImplicitMixing(slang::DiagSubsystem::Netlist, 1002);
	slang::DiagCode GenericTimingUnsyn(slang::DiagSubsystem::Netlist, 1003);
	slang::DiagCode BothEdgesUnsupported(slang::DiagSubsystem::Netlist, 1004);
	slang::DiagCode NoteSignalEvent(slang::DiagSubsystem::Netlist, 1005);
	slang::DiagCode ExpectingIfElseAload(slang::DiagSubsystem::Netlist, 1006);
	slang::DiagCode NoteDuplicateEdgeSense(slang::DiagSubsystem::Netlist, 1007);
	slang::DiagCode IfElseAloadPolarity(slang::DiagSubsystem::Netlist, 1008);
	slang::DiagCode IfElseAloadMismatch(slang::DiagSubsystem::Netlist, 1009);
	slang::DiagCode LatchNotInferred(slang::DiagSubsystem::Netlist, 1010);
	slang::DiagCode MissingAload(slang::DiagSubsystem::Netlist, 1012);
	slang::DiagCode NoteProcessDriver(slang::DiagSubsystem::Netlist, 1013);
	slang::DiagCode AlwaysFFBadTiming(slang::DiagSubsystem::Netlist, 1014);

	slang::DiagCode MissingStopCondition(slang::DiagSubsystem::Netlist, 1017);

	slang::DiagCode ComplexLatchLHS(slang::DiagSubsystem::Netlist, 1018);

	slang::DiagCode BadMemoryExpr(slang::DiagSubsystem::Netlist, 1019);
	slang::DiagCode MemoryNotInferred(slang::DiagSubsystem::Netlist, 1020);
	slang::DiagCode NoteUsageBlame(slang::DiagSubsystem::Netlist, 1021);

	slang::DiagCode UnrollLimitExhausted(slang::DiagSubsystem::Netlist, 1022);
	slang::DiagCode NoteLoopContributes(slang::DiagSubsystem::Netlist, 1023);

	slang::DiagCode NonconstWildcardEq(slang::DiagSubsystem::Netlist, 1024);

	slang::DiagCode AssertionUnsupported(slang::DiagSubsystem::Netlist, 1025);
	slang::DiagCode LangFeatureUnsupported(slang::DiagSubsystem::Netlist, 1026);
	slang::DiagCode UnsupportedLhs(slang::DiagSubsystem::Netlist, 1027);
	slang::DiagCode ArgumentTypeUnsupported(slang::DiagSubsystem::Netlist, 1028);
	slang::DiagCode MultiportUnsupported(slang::DiagSubsystem::Netlist, 1029);
	slang::DiagCode UnsupportedBlackboxConnection(slang::DiagSubsystem::Netlist, 1030);
	slang::DiagCode UnsupportedPortDirection(slang::DiagSubsystem::Netlist, 1031);
	slang::DiagCode ModportRequired(slang::DiagSubsystem::Netlist, 1032);
	slang::DiagCode FixedSizeRequired(slang::DiagSubsystem::Netlist, 1033);
	slang::DiagCode AloadOne(slang::DiagSubsystem::Netlist, 1034);
	slang::DiagCode BadInlinedPortConnection(slang::DiagSubsystem::Netlist, 1035);
	slang::DiagCode NoParamsOnUnkBboxes(slang::DiagSubsystem::Netlist, 1037);
	slang::DiagCode ConnNameRequiredOnUnkBboxes(slang::DiagSubsystem::Netlist, 1038);
	slang::DiagCode BboxTypeParameter(slang::DiagSubsystem::Netlist, 1039);
	slang::DiagCode BboxExportPortWidths(slang::DiagSubsystem::Netlist, 1040);
	slang::DiagCode NoteIgnoreInitial(slang::DiagSubsystem::Netlist, 1041);
	slang::DiagCode PortCorrespondence(slang::DiagSubsystem::Netlist, 1042);

	slang::DiagGroup unsynthesizable("unsynthesizable", {IffUnsupported, GenericTimingUnsyn, BothEdgesUnsupported, ExpectingIfElseAload,
														 IfElseAloadPolarity, IfElseAloadMismatch});
	slang::DiagGroup sanity("sanity", {EdgeImplicitMixing});

	void setup_messages(slang::DiagnosticEngine &engine)
	{
		engine.setMessage(IffUnsupported, "iff qualifier will not be synthesized");
		engine.setMessage(SignalSensitivityAmbiguous, "non-edge sensitivity on a signal will be synthesized as @* sensitivity");
		engine.setSeverity(SignalSensitivityAmbiguous, slang::DiagnosticSeverity::Warning);
		engine.setMessage(EdgeImplicitMixing, "mixing of implicit and edge sensitivity");
		engine.setMessage(GenericTimingUnsyn, "unsynthesizable timing control (ignore with '--ignore-timing')");
		engine.setMessage(BothEdgesUnsupported, "'edge' sensitivity will not be synthesized");
		engine.setMessage(NoteSignalEvent, "signal event specified here");
		engine.setSeverity(NoteSignalEvent, slang::DiagnosticSeverity::Note);

		engine.setMessage(ExpectingIfElseAload, "simple if-else pattern expected in modeling an asynchronous load on a flip-flop");
		engine.setMessage(NoteDuplicateEdgeSense, "asynchronous load pattern implied by edge sensitivity on multiple signals");
		engine.setSeverity(NoteDuplicateEdgeSense, slang::DiagnosticSeverity::Note);

		engine.setMessage(IfElseAloadPolarity, "polarity of the condition doesn't match the edge sensitivity");
		engine.setMessage(IfElseAloadMismatch, "condition cannot be matched to any signal from the event list");

		engine.setMessage(LatchNotInferred, "latch not inferred for variable '{}' driven from always_latch procedure");
		engine.setSeverity(LatchNotInferred, slang::DiagnosticSeverity::Warning);

		engine.setMessage(MissingAload, "asynchronous load value missing for variable '{}'");
		engine.setSeverity(MissingAload, slang::DiagnosticSeverity::Warning);
		engine.setMessage(NoteProcessDriver, "variable driven from this procedure");
		engine.setSeverity(NoteProcessDriver, slang::DiagnosticSeverity::Note);

		engine.setMessage(AlwaysFFBadTiming, "timing control does not model a flip-flop");
		engine.setSeverity(AlwaysFFBadTiming, slang::DiagnosticSeverity::Error);

		engine.setMessage(MissingStopCondition, "stop condition is missing; loop cannot be unrolled");
		engine.setSeverity(MissingStopCondition, slang::DiagnosticSeverity::Error);

		engine.setMessage(ComplexLatchLHS, "complex lhs in assignment to latched variable '{}' unsupported");
		engine.setSeverity(ComplexLatchLHS, slang::DiagnosticSeverity::Error);

		engine.setMessage(BadMemoryExpr, "unsupported operation on a memory variable");
		engine.setSeverity(BadMemoryExpr, slang::DiagnosticSeverity::Error);

		engine.setMessage(MemoryNotInferred, "cannot infer memory from a variable despite '{}' attribute");
		engine.setSeverity(MemoryNotInferred, slang::DiagnosticSeverity::Error);
		engine.setMessage(NoteUsageBlame, "inference prevented by variable usage here");
		engine.setSeverity(NoteUsageBlame, slang::DiagnosticSeverity::Note);

		engine.setSeverity(unsynthesizable, slang::DiagnosticSeverity::Error);
		engine.setSeverity(sanity, slang::DiagnosticSeverity::Error);

		engine.setMessage(UnrollLimitExhausted, "unroll limit of {} exhausted [--unroll-limit=]");
		engine.setSeverity(UnrollLimitExhausted, slang::DiagnosticSeverity::Error);

		engine.setMessage(NoteLoopContributes, "loop contributes to unroll tally");
		engine.setSeverity(NoteLoopContributes, slang::DiagnosticSeverity::Note);

		engine.setMessage(NonconstWildcardEq, "wildcard equality unsynthesizable with non-constant right-hand operand");
		engine.setSeverity(NonconstWildcardEq, slang::DiagnosticSeverity::Error);

		engine.setMessage(AssertionUnsupported, "unsupported assertion statement");
		engine.setSeverity(AssertionUnsupported, slang::DiagnosticSeverity::Error);

		engine.setMessage(LangFeatureUnsupported, "unsupported language feature");
		engine.setSeverity(LangFeatureUnsupported, slang::DiagnosticSeverity::Error);

		engine.setMessage(UnsupportedLhs, "unsupported assignment target expression");
		engine.setSeverity(UnsupportedLhs, slang::DiagnosticSeverity::Error);

		engine.setMessage(ArgumentTypeUnsupported, "unsupported argument type: {}");
		engine.setSeverity(ArgumentTypeUnsupported, slang::DiagnosticSeverity::Error);

		engine.setMessage(MultiportUnsupported, "multiports unsupported on kept module boundary");
		engine.setSeverity(MultiportUnsupported, slang::DiagnosticSeverity::Error);

		engine.setMessage(UnsupportedBlackboxConnection, "{} port on blackbox instance unsupported");
		engine.setSeverity(UnsupportedBlackboxConnection, slang::DiagnosticSeverity::Error);

		engine.setMessage(UnsupportedPortDirection, "port direction '{}' on kept module boundary unsupported");
		engine.setSeverity(UnsupportedPortDirection, slang::DiagnosticSeverity::Error);

		engine.setMessage(ModportRequired, "interface port on kept module boundary must be a modport");
		engine.setSeverity(ModportRequired, slang::DiagnosticSeverity::Error);

		engine.setMessage(FixedSizeRequired, "expression of type {} with dynamic size unsupported for synthesis");
		engine.setSeverity(FixedSizeRequired, slang::DiagnosticSeverity::Error);

		engine.setMessage(AloadOne, "multiple asynchronous loads unsupported");
		engine.setSeverity(AloadOne, slang::DiagnosticSeverity::Error);

		engine.setMessage(BadInlinedPortConnection, "direction '{}' on inlined port connection unsupported");
		engine.setSeverity(BadInlinedPortConnection, slang::DiagnosticSeverity::Error);

		engine.setMessage(NoParamsOnUnkBboxes, "parameters on unknown blackboxes unsupported");
		engine.setSeverity(NoParamsOnUnkBboxes, slang::DiagnosticSeverity::Error);

		engine.setMessage(ConnNameRequiredOnUnkBboxes, "port name required in connections on unknown blackboxes");
		engine.setSeverity(ConnNameRequiredOnUnkBboxes, slang::DiagnosticSeverity::Error);

		engine.setMessage(BboxTypeParameter, "blackbox cannot have a type parameter");
		engine.setSeverity(BboxTypeParameter, slang::DiagnosticSeverity::Error);

		engine.setMessage(BboxExportPortWidths, "cannot export a blackbox definition with non-constant port widths");
		engine.setSeverity(BboxExportPortWidths, slang::DiagnosticSeverity::Error);

		engine.setMessage(NoteIgnoreInitial, "use option '--ignore-initial' to ignore initial blocks");
		engine.setSeverity(NoteIgnoreInitial, slang::DiagnosticSeverity::Note);

		engine.setMessage(PortCorrespondence, "ports without direct correspondence to an internal net/variable unsupported");
		engine.setSeverity(PortCorrespondence, slang::DiagnosticSeverity::Error);
	}
};
};

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
	slang::DiagCode LatchInferred(slang::DiagSubsystem::Netlist, 1011);
	slang::DiagCode MissingAload(slang::DiagSubsystem::Netlist, 1012);
	slang::DiagCode NoteProcessDriver(slang::DiagSubsystem::Netlist, 1013);
	slang::DiagCode AlwaysFFBadTiming(slang::DiagSubsystem::Netlist, 1014);

	slang::DiagGroup unsynthesizable("unsynthesizable", {IffUnsupported, SignalSensitivityAmbiguous, GenericTimingUnsyn, BothEdgesUnsupported, ExpectingIfElseAload,
														 IfElseAloadPolarity, IfElseAloadMismatch});
	slang::DiagGroup sanity("sanity", {EdgeImplicitMixing});

	void setup_messages(slang::DiagnosticEngine &engine)
	{
		engine.setMessage(IffUnsupported, "iff qualifier will not be synthesized");
		engine.setMessage(SignalSensitivityAmbiguous, "non-edge sensitivity on a signal will be synthesized as @* sensitivity");
		engine.setMessage(EdgeImplicitMixing, "mixing of implicit and edge sensitivity");
		engine.setMessage(GenericTimingUnsyn, "unsynthesizable timing control");
		engine.setMessage(BothEdgesUnsupported, "'edge' sensitivity will not be synthesized");
		engine.setMessage(NoteSignalEvent, "signal event specified here");
		engine.setSeverity(NoteSignalEvent, slang::DiagnosticSeverity::Note);

		engine.setMessage(ExpectingIfElseAload, "a simple if-else pattern is expected in modeling an asynchronous load on a flip-flop");
		engine.setMessage(NoteDuplicateEdgeSense, "asynchronous load pattern implied by edge sensitivity on multiple signals");
		engine.setSeverity(NoteDuplicateEdgeSense, slang::DiagnosticSeverity::Note);

		engine.setMessage(IfElseAloadPolarity, "polarity of the condition doesn't match the edge sensitivity");
		engine.setMessage(IfElseAloadMismatch, "condition cannot be matched to any signal from the event list");
		engine.setSeverity(LatchInferred, slang::DiagnosticSeverity::Error);

		engine.setMessage(LatchNotInferred, "latch not inferred for variable '{}' driven from always_latch procedure");
		engine.setSeverity(LatchNotInferred, slang::DiagnosticSeverity::Error);
		engine.setMessage(LatchInferred, "latch inferred for variable '{}' driven from always_comb procedure");
		engine.setSeverity(LatchInferred, slang::DiagnosticSeverity::Error);

		engine.setMessage(MissingAload, "asynchronous load value missing for variable '{}'");
		engine.setSeverity(MissingAload, slang::DiagnosticSeverity::Error);
		engine.setMessage(NoteProcessDriver, "variable driven from this procedure");
		engine.setSeverity(NoteProcessDriver, slang::DiagnosticSeverity::Note);

		engine.setMessage(AlwaysFFBadTiming, "timing control does not model a flip-flop");
		engine.setSeverity(AlwaysFFBadTiming, slang::DiagnosticSeverity::Error);

		engine.setSeverity(unsynthesizable, slang::DiagnosticSeverity::Error);
		engine.setSeverity(sanity, slang::DiagnosticSeverity::Error);
	}
};

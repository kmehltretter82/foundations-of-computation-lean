import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Simulator.PaddedEmitter
import FoC.Computability.Compiler.Core.FiniteScaffolds.ControllerInvocation

set_option doc.verso true

/-!
# Controller output-level simulator bridge

This module isolates the controller-facing bridge from generated exact-fuel
inputs through the padded/equivalence fixed-description simulator boundary and
the normalized simulator-output extractor.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

theorem fixedDescriptionBoundedSimulatorCanonicalOutputTape_bridge
    (attempt : MachineDescription) (L : SimulatorLayout) :
    Tape.Equiv
      (Tape.move Direction.left
        (Tape.move Direction.right
          (FixedDescriptionBoundedSimulatorCanonicalOutputTape attempt L)))
      (Tape.input (FixedDescriptionBoundedSimulatorOutput attempt L)) := by
  simpa [FixedDescriptionBoundedSimulatorCanonicalOutputTape,
    FixedDescriptionBoundedSimulatorOutput, SimulatorLayout.tape] using
    EncodedRewriters.BoundedLayoutRunner.moveLeft_moveRight_equiv_self
      (FixedDescriptionBoundedSimulatorCanonicalOutputTape attempt L)

theorem pairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerForwardClosedConstruction_of_parser_equiv_extractor
    (hparserConstruction :
      PairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodeClosedHandoffConstruction)
    (hsimulatorConstruction :
      FixedDescriptionBoundedSimulatorEquivConstruction)
    (hextractorConstruction :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineConstruction) :
    PairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerForwardClosedConstruction := by
  intro attempt _invoker _hinvoker
  rcases hparserConstruction attempt with ⟨parser, hparser⟩
  rcases hsimulatorConstruction attempt with ⟨simulator, hsimulator⟩
  rcases hextractorConstruction attempt with ⟨extractor, hextractor⟩
  let simExtractor :=
    EncodedRewriters.BoundedLayoutRunner.SeqViaCanonical
      simulator extractor
  let runner :=
    seqSubroutine parser simExtractor tapeCodePrimitiveCodeWordHandoffMove
  have hparserReady : parser.SubroutineReady :=
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_subroutineReady
      hparser
  have hsimulatorReady : simulator.SubroutineReady :=
    hsimulator.left
  have hextractorReady : extractor.SubroutineReady :=
    tapeCodePrimitiveOutputCompiledSubroutineByDescription_subroutineReady
      hextractor
  have hsimExtractorReady : simExtractor.SubroutineReady := by
    simpa [simExtractor] using
      EncodedRewriters.BoundedLayoutRunner.SeqViaCanonical_subroutineReady
        hsimulatorReady hextractorReady
  refine ⟨runner, ?_, ?_, ?_⟩
  · simpa [runner] using
      seqSubroutine_subroutineReady hparserReady hsimExtractorReady
  · intro w limit fuel result hattempt
    let L :=
      PairedRecognizerDovetailControllerStageAttemptFuelSimulatorLayout
        attempt w limit fuel
    have hparserTransform :
        (PairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodePrimitive
          attempt).transform
          (PairedRecognizerDovetailControllerStageAttemptFuelInputCode
            w limit fuel) =
          some (SimulatorLayout.encode L) := by
      simpa [L] using
        pairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodePrimitive_encode
          attempt w limit fuel
    rcases
        tapeCodePrimitiveHandoffCompiledSubroutineByDescription_haltsWithTape_of_transform_eq_some
          (tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_handoffCompiled
            hparser)
          hparserTransform with
      ⟨Tparser, hparserHalt, hparserMove⟩
    have hparserMoveLeft :
        Tape.move Direction.left Tparser =
          Tape.input (encodeCodeWordAsInput L.encode) := by
      simpa [tapeCodePrimitiveCodeWordHandoffMove] using hparserMove
    have hsimForward :
        simulator.HaltsFromTapeEquiv
          (Tape.input (FixedDescriptionBoundedSimulatorInput L))
          (FixedDescriptionBoundedSimulatorCanonicalOutputTape attempt L) := by
      simpa [FixedDescriptionBoundedSimulatorInput,
        SimulatorLayout.tape] using
        FixedDescriptionBoundedSimulatorEquivSpec.haltsFromTapeEquiv
          hsimulator L
    have houtputTransform :
        (PairedRecognizerDovetailControllerStageAttemptFuelOutputCodePrimitive
          attempt).transform
          (SimulatorLayout.encode (SimulatorLayout.run attempt L.stage L)) =
          some (encodeBoolWord result) := by
      simpa [L] using
        (pairedRecognizerDovetailControllerStageAttemptFuelOutputCodePrimitive_run_boolWord_iff
          attempt w result limit fuel).mpr hattempt
    rcases
        tapeCodePrimitiveOutputCompiledSubroutineByDescription_haltsFromTape_equiv_input
          hextractor
          (hin := Tape.Equiv.refl
            (Tape.input
              (encodeCodeWordAsInput
                (SimulatorLayout.encode
                  (SimulatorLayout.run attempt L.stage L)))))
          houtputTransform with
      ⟨Textractor, hextractorHalt, hTextractorOutput⟩
    have hextractorWithTape :
        extractor.HaltsWithTape
          (FixedDescriptionBoundedSimulatorOutput attempt L)
          Textractor := by
      rcases hextractorHalt with ⟨n, hn⟩
      exact
        ⟨n, by
          simpa [HaltsWithTapeIn, HaltsFromTapeIn,
            FixedDescriptionBoundedSimulatorOutput,
            MachineDescription.initial] using hn⟩
    rcases
        EncodedRewriters.BoundedLayoutRunner.SeqViaCanonical_haltsFromTapeEquiv_of_haltsWithTape
          hsimulatorReady hextractorReady
          hsimForward
          (fixedDescriptionBoundedSimulatorCanonicalOutputTape_bridge
            attempt L)
          hextractorWithTape with
      ⟨TsimExtractor, hsimExtractorHalt, hTsimExtractor⟩
    have hsimExtractorFromParser :
        simExtractor.HaltsFromTape
          (Tape.move tapeCodePrimitiveCodeWordHandoffMove Tparser)
          TsimExtractor := by
      rw [tapeCodePrimitiveCodeWordHandoffMove, hparserMoveLeft]
      simpa [simExtractor, FixedDescriptionBoundedSimulatorInput,
        SimulatorLayout.asBoolInput] using
        hsimExtractorHalt
    have hTsimExtractorOutput :
        Tape.normalizedOutput TsimExtractor =
          encodeCodeWordAsInput (encodeBoolWord result) := by
      rw [Tape.Equiv.normalizedOutput_eq hTsimExtractor]
      exact hTextractorOutput
    exact
      seqSubroutine_haltsWithOutput_forward
        hparserReady hsimExtractorReady hparserHalt
        hsimExtractorFromParser hTsimExtractorOutput
  · intro w limit fuel result hrunner
    let L :=
      PairedRecognizerDovetailControllerStageAttemptFuelSimulatorLayout
        attempt w limit fuel
    rcases
        seqSubroutine_haltsWithOutput_closed_exists_mid
          hparserReady hsimExtractorReady hrunner with
      ⟨Tparser, TsimExtractor, hparserHalt,
        hsimExtractorHalt, hTsimExtractorOutput⟩
    rcases
        closedHandoffCompiled_haltsWithTape_inv hparser
          hparserHalt with
      ⟨mid, hparserTransform, _hparserOutput, hparserMove⟩
    have hmid :
        mid = SimulatorLayout.encode L := by
      have hknown :=
        pairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodePrimitive_encode
          attempt w limit fuel
      rw [hknown] at hparserTransform
      cases hparserTransform
      rfl
    subst mid
    have hsimExtractorFromLayout :
        simExtractor.HaltsFromTape
          (Tape.input (FixedDescriptionBoundedSimulatorInput L))
          TsimExtractor := by
      rw [hparserMove] at hsimExtractorHalt
      simpa [simExtractor, FixedDescriptionBoundedSimulatorInput,
        SimulatorLayout.asBoolInput] using
        hsimExtractorHalt
    rcases
        EncodedRewriters.BoundedLayoutRunner.SeqViaCanonical_haltsFromTape_inv
          hsimulatorReady hextractorReady hsimExtractorFromLayout with
      ⟨Tsimulator, hsimulatorHalt, hextractorHalt⟩
    have hsimulatorWithTape :
        simulator.HaltsWithTape
          (FixedDescriptionBoundedSimulatorInput L) Tsimulator := by
      rcases hsimulatorHalt with ⟨n, hn⟩
      exact
        ⟨n, by
          simpa [HaltsWithTapeIn, HaltsFromTapeIn,
            FixedDescriptionBoundedSimulatorInput,
            SimulatorLayout.asBoolInput,
            MachineDescription.initial] using hn⟩
    have hsimulatorClosed :
        Tape.Equiv Tsimulator
          (FixedDescriptionBoundedSimulatorCanonicalOutputTape attempt L) :=
      hsimulator.right.right L Tsimulator hsimulatorWithTape
    have hbridgeActual :
        Tape.Equiv
          (Tape.move Direction.left
            (Tape.move Direction.right Tsimulator))
          (Tape.input (FixedDescriptionBoundedSimulatorOutput attempt L)) := by
      exact
        Tape.Equiv.trans
          (Tape.Equiv.move
            (Tape.Equiv.move hsimulatorClosed Direction.right)
            Direction.left)
          (fixedDescriptionBoundedSimulatorCanonicalOutputTape_bridge
            attempt L)
    have houtputTransform :
        (PairedRecognizerDovetailControllerStageAttemptFuelOutputCodePrimitive
          attempt).transform
          (SimulatorLayout.encode (SimulatorLayout.run attempt L.stage L)) =
          some (encodeBoolWord result) := by
      exact
        tapeCodePrimitiveOutputCompiledSubroutineByDescription_transform_eq_some_of_haltsFromTape_equiv_input
          hextractor
          (hin := by
            simpa [FixedDescriptionBoundedSimulatorOutput] using
              hbridgeActual)
          hextractorHalt
          hTsimExtractorOutput
    exact
      (pairedRecognizerDovetailControllerStageAttemptFuelOutputCodePrimitive_run_boolWord_iff
        attempt w result limit fuel).mp (by
          simpa [L] using houtputTransform)

private theorem pairedRecognizerDovetailControllerStageAttemptFuelSimulatorRightShiftedSpecConstruction_finite_leaf :
    PairedRecognizerDovetailControllerStageAttemptFuelSimulatorRightShiftedSpecConstruction := by
  intro attempt
  -- Remaining finite-table obligation: parse generated `(w, limit, fuel)`
  -- inputs into simulator-layout code and halt one cell right of the emitted
  -- canonical simulator-layout word.
  sorry

private theorem pairedRecognizerDovetailControllerStageAttemptFuelSimulatorGeneratedInputClosedHandoffConstruction_finite_leaf :
    PairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodeClosedHandoffConstruction :=
  pairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodeClosedHandoffConstruction_of_rightShifted
    (pairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodeRightShiftedConstruction_of_spec
      pairedRecognizerDovetailControllerStageAttemptFuelSimulatorRightShiftedSpecConstruction_finite_leaf)

private theorem pairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineSpecConstruction_finite_leaf :
    PairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineSpecConstruction := by
  -- Remaining finite-table obligation: on halted simulator layouts, emit the
  -- exact normalized code-word output tape and reject all other inputs.
  sorry

private theorem pairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineConstruction_finite_leaf :
    PairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineConstruction :=
  pairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineConstruction_of_spec
    pairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineSpecConstruction_finite_leaf

private theorem pairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerForwardClosedConstruction_finite_leaf :
    PairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerForwardClosedConstruction :=
  by
    exact
      pairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerForwardClosedConstruction_of_parser_equiv_extractor
        pairedRecognizerDovetailControllerStageAttemptFuelSimulatorGeneratedInputClosedHandoffConstruction_finite_leaf
        EncodedRewriters.BoundedLayoutRunner.fixedDescriptionBoundedSimulatorEquivConstruction_scaffold_configRunner
        pairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineConstruction_finite_leaf

theorem pairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerConstruction_finite_leaf :
    PairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerConstruction :=
  pairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerConstruction_of_forward_closed
    pairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerForwardClosedConstruction_finite_leaf

end Computability
end FoC

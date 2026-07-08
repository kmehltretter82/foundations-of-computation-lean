import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Simulator.PaddedEmitter
import FoC.Computability.Compiler.Core.FiniteScaffolds.ControllerInvocation
import FoC.Computability.Compiler.Core.CommonGround.SeqComposition
import FoC.Computability.Compiler.Core.StructuredConstructionTargets

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
open StructuredConstructionTargets

theorem fixedDescriptionBoundedSimulatorCanonicalOutputTape_bridge
    (attempt : MachineDescription) (L : SimulatorLayout) :
    Tape.Equiv
      (Tape.move Direction.left
        (Tape.move Direction.right
          (FixedDescriptionBoundedSimulatorCanonicalOutputTape attempt L)))
      (Tape.input (FixedDescriptionBoundedSimulatorOutput attempt L)) := by
  simpa [FixedDescriptionBoundedSimulatorCanonicalOutputTape,
    FixedDescriptionBoundedSimulatorOutput, SimulatorLayout.tape] using
    EncRewriters.BoundedLayoutRunner.moveLeft_moveRight_equiv_self
      (FixedDescriptionBoundedSimulatorCanonicalOutputTape attempt L)

private theorem fuelSimulatorStructuredOutputTape_handoffEquiv
    (attempt : MachineDescription)
    (i : FuelSimulatorStructuredIndex)
    {T : Tape Bool}
    (hT : Tape.Equiv T (fuelSimulatorStructuredOutputTape attempt i)) :
    Tape.Equiv
      (Tape.move tapeCodePrimitiveCodeWordHandoffMove T)
      (Tape.input
        (FixedDescriptionBoundedSimulatorInput
          (PairedRecognizerDovetailControllerStageAttemptFuelSimulatorLayout
            attempt i.w i.limit i.fuel))) := by
  have htransform :
      (PairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodePrimitive
        attempt).transform
        (PairedRecognizerDovetailControllerStageAttemptFuelInputCode
          i.w i.limit i.fuel) =
        some
          (SimulatorLayout.encode
            (PairedRecognizerDovetailControllerStageAttemptFuelSimulatorLayout
              attempt i.w i.limit i.fuel)) := by
    exact
      pairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodePrimitive_encode
        attempt i.w i.limit i.fuel
  rcases
      pairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodePrimitive_transform_eq_some_cons
        htransform with
    ⟨symbol, tail, hcons⟩
  have hmove :
      Tape.move tapeCodePrimitiveCodeWordHandoffMove
          (fuelSimulatorStructuredOutputTape attempt i) =
        Tape.input
          (FixedDescriptionBoundedSimulatorInput
            (PairedRecognizerDovetailControllerStageAttemptFuelSimulatorLayout
              attempt i.w i.limit i.fuel)) := by
    simpa [fuelSimulatorStructuredOutputTape,
      PairedRecognizerDovetailControllerStageAttemptFuelSimulatorOutputTape,
      FixedDescriptionBoundedSimulatorInput, SimulatorLayout.asBoolInput,
      hcons] using
      (EncRewriters.tapeCodePrimitiveCodeWord_handoff_tape
        symbol tail).2
  exact
    Tape.Equiv.trans
      (Tape.Equiv.move hT tapeCodePrimitiveCodeWordHandoffMove)
      (by
        rw [hmove]
        exact
          Tape.Equiv.refl
            (Tape.input
              (FixedDescriptionBoundedSimulatorInput
                (PairedRecognizerDovetailControllerStageAttemptFuelSimulatorLayout
                  attempt i.w i.limit i.fuel))))

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
    EncRewriters.BoundedLayoutRunner.SeqViaCanonical
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
      EncRewriters.BoundedLayoutRunner.SeqViaCanonical_subroutineReady
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
        EncRewriters.BoundedLayoutRunner.SeqViaCanonical_haltsFromTapeEquiv_of_haltsWithTape
          hsimulatorReady hextractorReady
          hsimForward
          (fixedDescriptionBoundedSimulatorCanonicalOutputTape_bridge
            attempt L)
          hextractorWithTape with
      ⟨TsimExtractor, hsimExtractorHalt, hTsimExtractor⟩
    have hTsimExtractorOutput :
        Tape.normalizedOutput TsimExtractor =
          encodeCodeWordAsInput (encodeBoolWord result) := by
      rw [Tape.Equiv.normalizedOutput_eq hTsimExtractor]
      exact hTextractorOutput
    have hparserHandoffEquiv :
        Tape.Equiv
          (Tape.move tapeCodePrimitiveCodeWordHandoffMove Tparser)
          (Tape.input (FixedDescriptionBoundedSimulatorInput L)) := by
      rw [tapeCodePrimitiveCodeWordHandoffMove, hparserMoveLeft]
      exact
        Tape.Equiv.refl
          (Tape.input (FixedDescriptionBoundedSimulatorInput L))
    exact
      CommonGround.SeqComposition.seqSubroutine_haltsWithOutput_forward_of_input_equiv
        hparserReady hsimExtractorReady hparserHalt
        hparserHandoffEquiv
        (by
          simpa [simExtractor, FixedDescriptionBoundedSimulatorInput,
            SimulatorLayout.asBoolInput] using
            hsimExtractorHalt)
        hTsimExtractorOutput
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
        tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_haltsWithTape_output hparser
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
        EncRewriters.BoundedLayoutRunner.SeqViaCanonical_haltsFromTape_inv
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

theorem pairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerForwardClosedConstruction_of_parser_endpointEquiv_extractor
    (hparserConstruction :
      forall attempt : MachineDescription,
        FuelSimulatorStructuredEndpointEquivIndexedConstruction attempt)
    (hsimulatorConstruction :
      FixedDescriptionBoundedSimulatorEquivConstruction)
    (hextractorConstruction :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineConstruction) :
    PairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerForwardClosedConstruction := by
  intro attempt _invoker _hinvoker
  rcases hparserConstruction attempt with
    ⟨Wparser, _initialized, _lowered, hparserEndpoint⟩
  rcases hsimulatorConstruction attempt with ⟨simulator, hsimulator⟩
  rcases hextractorConstruction attempt with ⟨extractor, hextractor⟩
  let parser := Wparser.machine
  let simExtractor :=
    EncRewriters.BoundedLayoutRunner.SeqViaCanonical
      simulator extractor
  let runner :=
    seqSubroutine parser simExtractor tapeCodePrimitiveCodeWordHandoffMove
  have hparserReady : parser.SubroutineReady := by
    simpa [parser] using Wparser.machine_subroutineReady
  have hsimulatorReady : simulator.SubroutineReady :=
    hsimulator.left
  have hextractorReady : extractor.SubroutineReady :=
    tapeCodePrimitiveOutputCompiledSubroutineByDescription_subroutineReady
      hextractor
  have hsimExtractorReady : simExtractor.SubroutineReady := by
    simpa [simExtractor] using
      EncRewriters.BoundedLayoutRunner.SeqViaCanonical_subroutineReady
        hsimulatorReady hextractorReady
  refine ⟨runner, ?_, ?_, ?_⟩
  · simpa [runner] using
      seqSubroutine_subroutineReady hparserReady hsimExtractorReady
  · intro w limit fuel result hattempt
    let L :=
      PairedRecognizerDovetailControllerStageAttemptFuelSimulatorLayout
        attempt w limit fuel
    let i : FuelSimulatorStructuredIndex := ⟨w, limit, fuel⟩
    rcases
        Structured3EndpointEquivIndexedFamilySpec.forward
          hparserEndpoint i with
      ⟨Tparser, hparserFromTape, hTparser⟩
    have hparserHalt :
        parser.HaltsWithTape
          (encodeCodeWordAsInput
            (PairedRecognizerDovetailControllerStageAttemptFuelInputCode
              w limit fuel))
          Tparser := by
      rcases hparserFromTape with ⟨n, hn⟩
      exact
        ⟨n, by
          simpa [parser, HaltsWithTapeIn, HaltsFromTapeIn,
            MachineDescription.initial, fuelSimulatorStructuredInputTape,
            fuelSimulatorStructuredInputCode, i] using hn⟩
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
        EncRewriters.BoundedLayoutRunner.SeqViaCanonical_haltsFromTapeEquiv_of_haltsWithTape
          hsimulatorReady hextractorReady
          hsimForward
          (fixedDescriptionBoundedSimulatorCanonicalOutputTape_bridge
            attempt L)
          hextractorWithTape with
      ⟨TsimExtractor, hsimExtractorHalt, hTsimExtractor⟩
    have hTsimExtractorOutput :
        Tape.normalizedOutput TsimExtractor =
          encodeCodeWordAsInput (encodeBoolWord result) := by
      rw [Tape.Equiv.normalizedOutput_eq hTsimExtractor]
      exact hTextractorOutput
    have hparserHandoffEquiv :
        Tape.Equiv
          (Tape.move tapeCodePrimitiveCodeWordHandoffMove Tparser)
          (Tape.input (FixedDescriptionBoundedSimulatorInput L)) := by
      simpa [L, i] using
        fuelSimulatorStructuredOutputTape_handoffEquiv
          attempt i hTparser
    exact
      CommonGround.SeqComposition.seqSubroutine_haltsWithOutput_forward_of_input_equiv
        hparserReady hsimExtractorReady hparserHalt
        hparserHandoffEquiv
        (by
          simpa [simExtractor, FixedDescriptionBoundedSimulatorInput,
            SimulatorLayout.asBoolInput] using
            hsimExtractorHalt)
        hTsimExtractorOutput
  · intro w limit fuel result hrunner
    let L :=
      PairedRecognizerDovetailControllerStageAttemptFuelSimulatorLayout
        attempt w limit fuel
    rcases
        seqSubroutine_haltsWithOutput_closed_exists_mid
          hparserReady hsimExtractorReady hrunner with
      ⟨Tparser, TsimExtractor, hparserHalt,
        hsimExtractorHalt, hTsimExtractorOutput⟩
    have hparserFromTape :
        parser.HaltsFromTape
          (Tape.input
            (encodeCodeWordAsInput
              (PairedRecognizerDovetailControllerStageAttemptFuelInputCode
                w limit fuel)))
          Tparser := by
      rcases hparserHalt with ⟨n, hn⟩
      exact
        ⟨n, by
          simpa [parser, HaltsWithTapeIn, HaltsFromTapeIn,
            MachineDescription.initial] using hn⟩
    rcases
        Structured3EndpointEquivIndexedFamilySpec.closedIndex
          hparserEndpoint
          (Tape.input
            (encodeCodeWordAsInput
              (PairedRecognizerDovetailControllerStageAttemptFuelInputCode
                w limit fuel)))
          Tparser hparserFromTape with
      ⟨i, hinput, hTparser⟩
    have hcode :
        PairedRecognizerDovetailControllerStageAttemptFuelInputCode
            w limit fuel =
          fuelSimulatorStructuredInputCode i :=
      fuelSimulatorStructuredInputCode_eq_of_inputTape_eq hinput
    rcases i with ⟨wi, limiti, fueli⟩
    simp [fuelSimulatorStructuredInputCode] at hcode
    rcases
        pairedRecognizerDovetailControllerStageAttemptFuelInputCode_injective
          hcode with
      ⟨hw, hlimit, hfuel⟩
    subst wi
    subst limiti
    subst fueli
    have hparserHandoffEquiv :
        Tape.Equiv
          (Tape.move tapeCodePrimitiveCodeWordHandoffMove Tparser)
          (Tape.input (FixedDescriptionBoundedSimulatorInput L)) := by
      simpa [L] using
        fuelSimulatorStructuredOutputTape_handoffEquiv
          attempt ⟨w, limit, fuel⟩
          hTparser
    rcases
        HaltsFromTapeEquiv_of_input_equiv
          (D := simExtractor)
          (Tin := Tape.move tapeCodePrimitiveCodeWordHandoffMove Tparser)
          (Tin' := Tape.input (FixedDescriptionBoundedSimulatorInput L))
          (Tout := TsimExtractor)
          hparserHandoffEquiv
          hsimExtractorHalt with
      ⟨TsimExtractorFromLayout, hsimExtractorFromLayout,
        hTsimExtractorFromLayout⟩
    rcases
        EncRewriters.BoundedLayoutRunner.SeqViaCanonical_haltsFromTape_inv
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
    have hTsimExtractorFromLayoutOutput :
        Tape.normalizedOutput TsimExtractorFromLayout =
          encodeCodeWordAsInput (encodeBoolWord result) := by
      rw [Tape.Equiv.normalizedOutput_eq hTsimExtractorFromLayout]
      exact hTsimExtractorOutput
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
          hTsimExtractorFromLayoutOutput
    exact
      (pairedRecognizerDovetailControllerStageAttemptFuelOutputCodePrimitive_run_boolWord_iff
        attempt w result limit fuel).mp (by
          simpa [L] using houtputTransform)

private theorem pairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineConstruction_finite_leaf :
    PairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineConstruction :=
  pairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineConstruction_of_endpointEquivIndexed
    fuelOutputStructuredEndpointEquivIndexedConstruction_core

private theorem pairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerForwardClosedConstruction_finite_leaf :
    PairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerForwardClosedConstruction :=
  by
    -- Remaining finite-table obligation: build the fuel-simulator parser
    -- endpoint without relying on arbitrary-start closedness for unmarked input
    -- tapes.
    sorry

theorem pairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerConstruction_finite_leaf :
    PairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerConstruction :=
  pairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerConstruction_of_forward_closed
    pairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerForwardClosedConstruction_finite_leaf

end Computability
end FoC

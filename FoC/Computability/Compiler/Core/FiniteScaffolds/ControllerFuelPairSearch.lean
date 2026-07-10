import FoC.Computability.Compiler.Core.FiniteScaffolds.ControllerOutputLevelSimulator
import FoC.Computability.Compiler.Core.StructuredConstructionTargets

set_option doc.verso true

/-!
# Controller fuel-pair search bridge

This module isolates the bounded {lit}`(limit, fuel)` pair enumerator and the
classifier handoff used by the controller search driver.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open StructuredConstructionTargets

private theorem boundedFuelPairEnumeratorRightShiftedOutputTape_handoffEquiv
    {runner : MachineDescription}
    (i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner)
    {T : Tape Bool}
    (hT :
      Tape.Equiv T
        (PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape
          i)) :
    Tape.Equiv
      (Tape.move Direction.left T)
      (Tape.input (encodeCodeWordAsInput (encodeBoolWord i.result))) := by
  have hmove :
      Tape.move Direction.left
          (PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape
            i) =
        Tape.input (encodeCodeWordAsInput (encodeBoolWord i.result)) := by
    simpa [
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape,
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorOutputCode,
      PairedRecognizerDovetailControllerBoolWordRightShiftedOutputTape] using
      pairedRecognizerDovetailControllerBoolWordRightShiftedOutputTape_handoff
        i.result
  exact
    Tape.Equiv.trans
      (Tape.Equiv.move hT Direction.left)
      (by
        rw [hmove]
        exact
          Tape.Equiv.refl
            (Tape.input
              (encodeCodeWordAsInput (encodeBoolWord i.result))))

theorem pairedRecognizerDovetailControllerStageAttemptFuelPairSearchConstruction_of_endpointEquiv_emitter
    (henumerator :
      forall runner : MachineDescription,
        runner.SubroutineReady ->
          BoundedFuelPairEnumeratorStructuredEndpointEquivIndexedConstruction
            runner)
    (hemitter :
      PairedRecognizerDovetailControllerBoolWordRawOutputEmitterConstruction) :
    PairedRecognizerDovetailControllerStageAttemptFuelPairSearchConstruction := by
  intro runner hrunner
  rcases henumerator runner hrunner with
    ⟨W, henumeratorEndpoint⟩
  rcases hemitter with ⟨emitter, hemits⟩
  let enumerator := W.machine
  let classifier := seqSubroutine enumerator emitter Direction.left
  have henumeratorReady : enumerator.SubroutineReady := by
    simpa [enumerator] using W.machine_subroutineReady
  have hclassifierReady : classifier.SubroutineReady := by
    simpa [classifier] using
      seqSubroutine_subroutineReady henumeratorReady hemits.left
  refine ⟨classifier, ?_⟩
  constructor
  · exact hclassifierReady.left
  · intro w b
    constructor
    · intro hhalt
      rcases
          seqSubroutine_haltsWithOutput_closed_exists_mid
            henumeratorReady hemits.left hhalt with
        ⟨Tmid, Tout, henumTape, hemitFrom, hout⟩
      have henumFrom :
          enumerator.HaltsFromTape (Tape.input w) Tmid := by
        rcases henumTape with ⟨n, hn⟩
        exact
          ⟨n, by
            simpa [enumerator, HaltsWithTapeIn, HaltsFromTapeIn,
              MachineDescription.initial] using hn⟩
      rcases
          henumeratorEndpoint.closedIndex w Tmid henumFrom with
        ⟨i, hinput, hTmid⟩
      have hw : w = i.input := by
        simpa [boundedFuelPairEnumeratorStructuredInputBits] using hinput
      have hhandoff :
          Tape.Equiv
            (Tape.move Direction.left Tmid)
            (Tape.input
              (encodeCodeWordAsInput (encodeBoolWord i.result))) :=
        boundedFuelPairEnumeratorRightShiftedOutputTape_handoffEquiv
          i hTmid
      have hemitEquiv :
          emitter.HaltsFromTapeEquiv
            (Tape.input
              (encodeCodeWordAsInput (encodeBoolWord i.result)))
            Tout :=
        HaltsFromTapeEquiv_of_input_equiv
          hhandoff hemitFrom
      have hemitFromOutput :
          emitter.HaltsFromTapeWithOutput
            (Tape.input
              (encodeCodeWordAsInput (encodeBoolWord i.result)))
            [b] := by
        simpa [hout] using
          MachineDescription.haltsFromTapeWithOutput_of_haltsFromTapeEquiv
            hemitEquiv
      have hemitsOutput :
          emitter.HaltsWithOutput
            (encodeCodeWordAsInput (encodeBoolWord i.result))
            [b] := by
        rcases hemitFromOutput with ⟨n, hn⟩
        exact
          ⟨n, by
            simpa [HaltsWithOutputIn, HaltsFromTapeWithOutputIn,
              MachineDescription.initial] using hn⟩
      exact
        ⟨i.limit, i.fuel, i.result,
          by
            simpa [hw] using i.runner_halts,
          (hemits.right i.result b).mp hemitsOutput⟩
    · intro h
      rcases h with ⟨limit, fuel, result, hrun, hraw⟩
      let i :
          PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
            runner :=
        { input := w
          searchLimit := max limit fuel
          limit := limit
          fuel := fuel
          result := result
          limit_le_searchLimit := Nat.le_max_left limit fuel
          fuel_le_searchLimit := Nat.le_max_right limit fuel
          runner_halts := hrun }
      rcases
          henumeratorEndpoint.forward i with
        ⟨Tmid, henumFrom, hTmid⟩
      have henumTape :
          enumerator.HaltsWithTape w Tmid := by
        rcases henumFrom with ⟨n, hn⟩
        exact
          ⟨n, by
            simpa [enumerator, HaltsWithTapeIn, HaltsFromTapeIn,
              MachineDescription.initial,
              boundedFuelPairEnumeratorStructuredInputBits, i] using hn⟩
      have hemitsOutput :
          emitter.HaltsWithOutput
            (encodeCodeWordAsInput (encodeBoolWord result)) [b] :=
        (hemits.right result b).mpr hraw
      rcases hemitsOutput with ⟨nB, hnB⟩
      let Tout : Tape Bool :=
        (emitter.runConfig nB
          (emitter.initial
            (encodeCodeWordAsInput (encodeBoolWord result)))).tape
      have hemitFrom :
          emitter.HaltsFromTape
            (Tape.input
              (encodeCodeWordAsInput (encodeBoolWord result)))
            Tout :=
        ⟨nB, by
          exact ⟨hnB.left, rfl⟩⟩
      have hhandoff :
          Tape.Equiv
            (Tape.move Direction.left Tmid)
            (Tape.input
              (encodeCodeWordAsInput (encodeBoolWord result))) := by
        simpa [i] using
          boundedFuelPairEnumeratorRightShiftedOutputTape_handoffEquiv
            i hTmid
      have hout : Tape.normalizedOutput Tout = [b] := by
        simpa [Tout] using hnB.right
      exact
        CommonGround.SeqComposition.seqSubroutine_haltsWithOutput_forward_of_input_equiv
          henumeratorReady hemits.left henumTape hhandoff hemitFrom hout

theorem pairedRecognizerDovetailControllerStageAttemptFuelPairSearchConstruction_finite_leaf :
    PairedRecognizerDovetailControllerStageAttemptFuelPairSearchConstruction :=
  pairedRecognizerDovetailControllerStageAttemptFuelPairSearchConstruction_of_endpointEquiv_emitter
    boundedFuelPairEnumeratorStructuredEndpointEquivIndexedConstruction_core
    pairedRecognizerDovetailControllerBoolWordRawOutputEmitterConstruction_scaffold

end Computability
end FoC

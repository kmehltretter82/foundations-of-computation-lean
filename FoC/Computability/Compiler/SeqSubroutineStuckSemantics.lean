import FoC.Computability.Compiler.SeqSubroutineSemantics
import FoC.Computability.Compiler.StuckExecution

set_option doc.verso true

/-!
# Stuck execution through sequential subroutines

This module keeps exact rejection-path lifting separate from the already-large
core sequence semantics while reusing its fragment execution lemmas.
-/

namespace FoC
namespace Computability

open Languages

namespace MachineDescription

/-- A stuck run in the left subroutine remains the same exact stuck run after
sequencing. -/
theorem seqSubroutine_stuckFromTape_of_left
    {A B : MachineDescription} {handoffMove : Direction}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {input stuck : Tape Bool}
    (hstuck : A.StuckFromTape input stuck) :
    (seqSubroutine A B handoffMove).StuckFromTape input stuck := by
  rcases hstuck with ⟨steps, state, hrun, hstep, hne⟩
  let source : Configuration := { state := A.start, tape := input }
  have hfinalNe : (A.runConfig steps source).state ≠ A.halt := by
    simpa [source, hrun] using hne
  have hno : forall k : Nat, k < steps ->
      (A.runConfig k source).state ≠ A.halt := by
    intro k hk
    exact runConfig_state_ne_halt_of_later_ne_halt
      hA.2 (Nat.le_of_lt hk) hfinalNe
  have hrunSeq := Fragment.runConfig_seq_left_of_no_exit
    (A := A.asFragment) (B := B.asFragment)
    (handoffMove := handoffMove)
    (asFragment_wellFormed hA) (asFragment_wellFormed hB)
    hA.1.2.1 hno
  have hstateBound : state < A.stateCount := by
    have hbound := runConfig_state_bound hA.1 hA.1.2.1
      (n := steps) (c := source)
    simpa [source, hrun] using hbound
  have hstepSeq := Fragment.stepConfig_seq_left
    (A := A.asFragment) (B := B.asFragment)
    (handoffMove := handoffMove)
    (c := { state := state, tape := stuck })
    (asFragment_wellFormed hB) hstateBound hne
  have hstepA : A.asFragment.toDescription.stepConfig
      { state := state, tape := stuck } = none := by
    rw [asFragment_toDescription]
    exact hstep
  have hrunA : A.asFragment.toDescription.runConfig steps source =
      { state := state, tape := stuck } := by
    rw [asFragment_toDescription]
    exact hrun
  refine ⟨steps, state, ?_, ?_, ?_⟩
  · change (Fragment.seq A.asFragment B.asFragment handoffMove).toDescription.runConfig
        steps { state := A.start, tape := input } = _
    simpa [source] using hrunSeq.trans hrunA
  · change (Fragment.seq A.asFragment B.asFragment handoffMove).toDescription.stepConfig
        { state := state, tape := stuck } = none
    exact hstepSeq.trans hstepA
  · intro heq
    have hBhalt := hB.1.2.2.1
    change state = A.stateCount + B.halt at heq
    lia

/-- After the left subroutine halts, a stuck run in the right subroutine lifts
to its offset state in the sequence. -/
theorem seqSubroutine_stuckFromTape_of_right
    {A B : MachineDescription} {handoffMove : Direction}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {input middle stuck : Tape Bool}
    (hAhalts : A.HaltsFromTape input middle)
    (hBstuck : B.StuckFromTape (Tape.move handoffMove middle) stuck) :
    (seqSubroutine A B handoffMove).StuckFromTape input stuck := by
  rcases runConfig_eq_halt_of_haltsFromTape hAhalts with ⟨nA, hArun⟩
  rcases hBstuck with ⟨nB, state, hBrun, hBstep, hBne⟩
  rcases seqSubroutine_reaches_right_state_of_runConfig_eq
      hA hB hArun ⟨nB, hBrun⟩ with ⟨steps, hrun⟩
  have hstep := Fragment.stepConfig_seq_right
    (A := A.asFragment) (B := B.asFragment)
    (handoffMove := handoffMove) (asFragment_wellFormed hA)
    { state := state, tape := stuck }
  have hBstep' : B.asFragment.toDescription.stepConfig
      { state := state, tape := stuck } = none := by
    rw [asFragment_toDescription]
    exact hBstep
  refine ⟨steps, A.stateCount + state, hrun, ?_, ?_⟩
  · rw [hBstep'] at hstep
    change (Fragment.seq A.asFragment B.asFragment handoffMove).toDescription.stepConfig
        { state := A.stateCount + state, tape := stuck } = none
    change (Fragment.seq A.asFragment B.asFragment handoffMove).toDescription.stepConfig
        { state := A.asFragment.stateCount + state, tape := stuck } = none
    simpa [Fragment.offsetConfiguration] using hstep
  · intro heq
    change A.stateCount + state = A.stateCount + B.halt at heq
    exact hBne (Nat.add_left_cancel heq)

end MachineDescription
end Computability
end FoC

import FoC.Computability.Compiler.SeqSubroutineSemantics

set_option doc.verso true

/-!
# Common sequential subroutine composition helpers

This module contains dependency-light wrappers around sequential subroutine
execution lemmas.  It is safe for low-level compiler construction modules to
import without pulling in the full common-ground wrapper surface.
-/

namespace FoC
namespace Computability

namespace CommonGround
namespace SeqComposition

theorem seqSubroutine_runConfig_exists
    {A B : MachineDescription} {handoffMove : Direction}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {nA : Nat} {Tin Tmid Tout : Tape Bool}
    (hArun :
      A.runConfig nA { state := A.start, tape := Tin } =
        { state := A.halt, tape := Tmid })
    (hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start, tape := Tape.move handoffMove Tmid } =
          { state := B.halt, tape := Tout }) :
    exists steps : Nat,
      (MachineDescription.seqSubroutine A B handoffMove).runConfig steps
          { state := (MachineDescription.seqSubroutine A B handoffMove).start,
            tape := Tin } =
        { state := (MachineDescription.seqSubroutine A B handoffMove).halt,
          tape := Tout } :=
  MachineDescription.seqSubroutine_reaches_of_runConfig_eq
    (A := A) (B := B) (handoffMove := handoffMove)
    hA hB hArun hBReach

theorem runConfig_reaches_from_move_eq
    {B : MachineDescription} {handoffMove : Direction}
    {nB : Nat} {Tmid Tin Tout : Tape Bool}
    (hmove : Tape.move handoffMove Tmid = Tin)
    (hrun :
      B.runConfig nB { state := B.start, tape := Tin } =
        { state := B.halt, tape := Tout }) :
    exists steps : Nat,
      B.runConfig steps
          { state := B.start, tape := Tape.move handoffMove Tmid } =
        { state := B.halt, tape := Tout } :=
  ⟨nB, by simpa [hmove] using hrun⟩

theorem runConfig_state_ne_halt_of_reaches_stuck
    {D : MachineDescription}
    {c stuck : MachineDescription.Configuration} {k n : Nat}
    (hD : D.HaltTransitionFree)
    (hprefix : D.runConfig k c = stuck)
    (hstep : D.stepConfig stuck = none)
    (hstuck : stuck.state ≠ D.halt) :
    (D.runConfig n c).state ≠ D.halt := by
  by_cases hle : k ≤ n
  · intro hhalt
    let rem := n - k
    have hn : n = k + rem := by omega
    have hrun :
        D.runConfig n c = D.runConfig rem stuck := by
      rw [hn, MachineDescription.runConfig_add, hprefix]
    have hstay :=
      MachineDescription.runConfig_of_stepConfig_none hstep rem
    have hstate : stuck.state = D.halt := by
      have hstateEq :
          (D.runConfig n c).state = stuck.state := by
        rw [hrun, hstay]
      exact hstateEq ▸ hhalt
    exact hstuck hstate
  · intro hhalt
    let rem := k - n
    have hk : k = n + rem := by omega
    have hrunHalt :
        D.runConfig n c =
          { state := D.halt, tape := (D.runConfig n c).tape } := by
      cases hcfg : D.runConfig n c with
      | mk state tape =>
          simp [hcfg] at hhalt ⊢
          exact hhalt
    have hstay :
        D.runConfig rem (D.runConfig n c) =
          D.runConfig n c := by
      rw [hrunHalt]
      exact MachineDescription.runConfig_halt hD
        (D.runConfig n c).tape rem
    have hstate : stuck.state = D.halt := by
      have hstuckEq :
          stuck = D.runConfig n c := by
        rw [← hprefix, hk, MachineDescription.runConfig_add, hstay]
      rw [hstuckEq]
      exact hhalt
    exact hstuck hstate

end SeqComposition
end CommonGround

end Computability
end FoC

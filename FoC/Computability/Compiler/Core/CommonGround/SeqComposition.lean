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

end SeqComposition
end CommonGround

end Computability
end FoC

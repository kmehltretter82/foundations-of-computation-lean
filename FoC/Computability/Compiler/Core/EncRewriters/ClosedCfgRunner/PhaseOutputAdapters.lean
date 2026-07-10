import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.PhaseAdapters

set_option doc.verso true

/-!
# Output-level phase adapters

This module adds arbitrary-start-tape output composition lemmas for the
canonical phase sequencer.  The existing phase adapters mostly compose exact
tape endpoints; these lemmas keep the exact intermediate handoff while allowing
the final phase to expose only {lit}`HaltsFromTapeWithOutput`.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner

/-! ## Extracting exact final tapes from output halts -/

theorem runConfig_eq_halt_of_haltsFromTapeWithOutput
    {D : MachineDescription} {Tin : Tape Bool} {out : Word Bool}
    (h : D.HaltsFromTapeWithOutput Tin out) :
    exists n : Nat,
    exists Tout : Tape Bool,
      D.runConfig n { state := D.start, tape := Tin } =
        { state := D.halt, tape := Tout } ∧
      Tape.normalizedOutput Tout = out := by
  rcases h with ⟨n, hn⟩
  refine
    ⟨n, (D.runConfig n { state := D.start, tape := Tin }).tape,
      ?_, ?_⟩
  · cases hfinal :
      D.runConfig n { state := D.start, tape := Tin } with
    | mk state tape =>
        have hstate : state = D.halt := by
          simpa [HaltsFromTapeWithOutputIn, hfinal] using hn.left
        simp [hstate]
  · simpa [HaltsFromTapeWithOutputIn] using hn.right

theorem runConfig_reachesWithOutput_from_move_eq
    {B : MachineDescription} {handoffMove : Direction}
    {Tmid Tin : Tape Bool} {out : Word Bool}
    (hmove : Tape.move handoffMove Tmid = Tin)
    (hBhalts : B.HaltsFromTapeWithOutput Tin out) :
    exists nB : Nat,
    exists Tout : Tape Bool,
      B.runConfig nB
          { state := B.start, tape := Tape.move handoffMove Tmid } =
        { state := B.halt, tape := Tout } ∧
      Tape.normalizedOutput Tout = out := by
  rcases runConfig_eq_halt_of_haltsFromTapeWithOutput hBhalts with
    ⟨nB, Tout, hBRun, hout⟩
  exact ⟨nB, Tout, by simpa [hmove] using hBRun, hout⟩

theorem runConfig_reachesWithOutput_from_move_rfl
    {B : MachineDescription} {handoffMove : Direction}
    {Tmid : Tape Bool} {out : Word Bool}
    (hBhalts :
      B.HaltsFromTapeWithOutput
        (Tape.move handoffMove Tmid) out) :
    exists nB : Nat,
    exists Tout : Tape Bool,
      B.runConfig nB
          { state := B.start, tape := Tape.move handoffMove Tmid } =
        { state := B.halt, tape := Tout } ∧
      Tape.normalizedOutput Tout = out :=
  runConfig_reachesWithOutput_from_move_eq rfl hBhalts

theorem haltsFromTapeWithOutput_of_runConfig_eq_output
    {D : MachineDescription} {n : Nat}
    {Tin Tout : Tape Bool} {out : Word Bool}
    (hrun :
      D.runConfig n { state := D.start, tape := Tin } =
        { state := D.halt, tape := Tout })
    (hout : Tape.normalizedOutput Tout = out) :
    D.HaltsFromTapeWithOutput Tin out := by
  have hhalt :
      D.HaltsFromTapeWithOutput Tin (Tape.normalizedOutput Tout) :=
    MachineDescription.haltsFromTapeWithOutput_of_runConfig_eq hrun
  simpa [hout] using hhalt

/-! ## Sequential subroutine output composition -/

theorem seqSubroutine_haltsFromTapeWithOutput_of_haltsFromTape_eq
    {A B : MachineDescription} {handoffMove : Direction}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {Tin Tmid Tnext : Tape Bool} {out : Word Bool}
    (hAhalts : A.HaltsFromTape Tin Tmid)
    (hmove : Tape.move handoffMove Tmid = Tnext)
    (hBhalts : B.HaltsFromTapeWithOutput Tnext out) :
    (seqSubroutine A B handoffMove).HaltsFromTapeWithOutput
      Tin out := by
  rcases MachineDescription.runConfig_eq_halt_of_haltsFromTape
      hAhalts with
    ⟨nA, hArun⟩
  rcases
      runConfig_reachesWithOutput_from_move_eq
        (B := B) (handoffMove := handoffMove)
        hmove hBhalts with
    ⟨nB, Tout, hBRun, hout⟩
  rcases
      seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := handoffMove)
        hA hB hArun ⟨nB, hBRun⟩ with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  constructor
  · simpa [MachineDescription.HaltsFromTapeWithOutputIn] using
      congrArg MachineDescription.Configuration.state hsteps
  · calc
      Tape.normalizedOutput
          ((seqSubroutine A B handoffMove).runConfig steps
            { state := (seqSubroutine A B handoffMove).start,
              tape := Tin }).tape =
        Tape.normalizedOutput Tout := by
          rw [hsteps]
      _ = out := hout

theorem seqSubroutine_haltsFromTapeWithOutput_of_haltsFromTape
    {A B : MachineDescription} {handoffMove : Direction}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {Tin Tmid : Tape Bool} {out : Word Bool}
    (hAhalts : A.HaltsFromTape Tin Tmid)
    (hBhalts :
      B.HaltsFromTapeWithOutput
        (Tape.move handoffMove Tmid) out) :
    (seqSubroutine A B handoffMove).HaltsFromTapeWithOutput
      Tin out :=
  seqSubroutine_haltsFromTapeWithOutput_of_haltsFromTape_eq
    hA hB hAhalts rfl hBhalts

theorem seqSubroutine_haltsWithOutput_of_haltsWithTape_eq
    {A B : MachineDescription} {handoffMove : Direction}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {input : Word Bool} {Tmid Tnext : Tape Bool} {out : Word Bool}
    (hAhalts : A.HaltsWithTape input Tmid)
    (hmove : Tape.move handoffMove Tmid = Tnext)
    (hBhalts : B.HaltsFromTapeWithOutput Tnext out) :
    (seqSubroutine A B handoffMove).HaltsWithOutput input out := by
  have hAfrom :
      A.HaltsFromTape (Tape.input input) Tmid := by
    rcases hAhalts with ⟨nA, hnA⟩
    exact
      ⟨nA, by
        simpa [HaltsWithTapeIn, HaltsFromTapeIn]
          using! hnA⟩
  have hseq :
      (seqSubroutine A B handoffMove).HaltsFromTapeWithOutput
        (Tape.input input) out :=
    seqSubroutine_haltsFromTapeWithOutput_of_haltsFromTape_eq
      hA hB hAfrom hmove hBhalts
  rcases hseq with ⟨n, hn⟩
  exact
    ⟨n, by
      simpa [HaltsWithOutputIn, HaltsFromTapeWithOutputIn,
        MachineDescription.initial] using hn⟩

theorem seqSubroutine_haltsWithOutput_of_haltsWithTape
    {A B : MachineDescription} {handoffMove : Direction}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {input : Word Bool} {Tmid : Tape Bool} {out : Word Bool}
    (hAhalts : A.HaltsWithTape input Tmid)
    (hBhalts :
      B.HaltsFromTapeWithOutput
        (Tape.move handoffMove Tmid) out) :
    (seqSubroutine A B handoffMove).HaltsWithOutput input out :=
  seqSubroutine_haltsWithOutput_of_haltsWithTape_eq
    hA hB hAhalts rfl hBhalts

theorem seqSubroutine_outputFamilySpec
    {ι : Type} {A B : MachineDescription} {handoffMove : Direction}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    (Tin Tmid Tnext : ι -> Tape Bool) (out : ι -> Word Bool)
    (hAhalts : forall i : ι, A.HaltsFromTape (Tin i) (Tmid i))
    (hmove : forall i : ι, Tape.move handoffMove (Tmid i) = Tnext i)
    (hBhalts :
      forall i : ι, B.HaltsFromTapeWithOutput (Tnext i) (out i)) :
    (seqSubroutine A B handoffMove).SubroutineReady ∧
      forall i : ι,
        (seqSubroutine A B handoffMove).HaltsFromTapeWithOutput
          (Tin i) (out i) := by
  constructor
  · exact seqSubroutine_subroutineReady hA hB
  · intro i
    exact
      seqSubroutine_haltsFromTapeWithOutput_of_haltsFromTape_eq
        hA hB (hAhalts i) (hmove i) (hBhalts i)

/-! ## Canonical sequencer output composition -/

theorem SeqViaCanonical_haltsFromTapeWithOutput_of_haltsFromTape_eq
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {Tin Tmid Tnext : Tape Bool} {out : Word Bool}
    (hAmid : A.HaltsFromTape Tin Tmid)
    (hbridge :
      Tape.move Direction.left (Tape.move Direction.right Tmid) = Tnext)
    (hBout : B.HaltsFromTapeWithOutput Tnext out) :
    (SeqViaCanonical A B).HaltsFromTapeWithOutput Tin out := by
  let identity := ExactIdentityDescription
  have hid : identity.SubroutineReady :=
    CommonGround.Identity.exactIdentityDescription_subroutineReady
  have hAid :
      (seqSubroutine A identity Direction.right).HaltsFromTape
        Tin (Tape.move Direction.right Tmid) := by
    exact
      seqSubroutine_haltsFromTape_of_haltsFromTape
        (A := A) (B := identity) (handoffMove := Direction.right)
        hA hid hAmid
        (CommonGround.Identity.exactIdentityDescription_run_from_start
          (Tape.move Direction.right Tmid))
  simpa [SeqViaCanonical, identity] using
    seqSubroutine_haltsFromTapeWithOutput_of_haltsFromTape_eq
      (A := seqSubroutine A identity Direction.right)
      (B := B) (handoffMove := Direction.left)
      (seqSubroutine_subroutineReady hA hid)
      hB hAid hbridge hBout

theorem SeqViaCanonical_haltsFromTapeWithOutput_of_haltsFromTape
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {Tin Tmid : Tape Bool} {out : Word Bool}
    (hAmid : A.HaltsFromTape Tin Tmid)
    (hBout :
      B.HaltsFromTapeWithOutput
        (Tape.move Direction.left (Tape.move Direction.right Tmid))
        out) :
    (SeqViaCanonical A B).HaltsFromTapeWithOutput Tin out :=
  SeqViaCanonical_haltsFromTapeWithOutput_of_haltsFromTape_eq
    hA hB hAmid rfl hBout

theorem SeqViaCanonical_haltsFromTapeWithOutput_of_haltsFromTapeEquiv
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {Tin Tmid Tnext : Tape Bool} {out : Word Bool}
    (hAmid : A.HaltsFromTapeEquiv Tin Tmid)
    (hbridge :
      Tape.Equiv
        (Tape.move Direction.left (Tape.move Direction.right Tmid))
        Tnext)
    (hBout : B.HaltsFromTapeWithOutput Tnext out) :
    (SeqViaCanonical A B).HaltsFromTapeWithOutput Tin out := by
  rcases hAmid with ⟨Tactual, hAactual, hactual⟩
  have hactualBridge :
      Tape.Equiv
        (Tape.move Direction.left (Tape.move Direction.right Tactual))
        Tnext :=
    Tape.Equiv.trans
      (Tape.Equiv.move
        (Tape.Equiv.move hactual Direction.right) Direction.left)
      hbridge
  have hBactual :
      B.HaltsFromTapeWithOutput
        (Tape.move Direction.left (Tape.move Direction.right Tactual))
        out :=
    MachineDescription.haltsFromTapeWithOutput_of_input_equiv
      (Tape.Equiv.symm hactualBridge) hBout
  exact
    SeqViaCanonical_haltsFromTapeWithOutput_of_haltsFromTape
      hA hB hAactual hBactual

theorem SeqViaCanonical_haltsWithOutput_of_haltsWithTape_eq
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {input : Word Bool} {Tmid Tnext : Tape Bool} {out : Word Bool}
    (hAmid : A.HaltsWithTape input Tmid)
    (hbridge :
      Tape.move Direction.left (Tape.move Direction.right Tmid) = Tnext)
    (hBout : B.HaltsFromTapeWithOutput Tnext out) :
    (SeqViaCanonical A B).HaltsWithOutput input out := by
  let identity := ExactIdentityDescription
  have hid : identity.SubroutineReady :=
    CommonGround.Identity.exactIdentityDescription_subroutineReady
  have hAid :
      (seqSubroutine A identity Direction.right).HaltsWithTape
        input (Tape.move Direction.right Tmid) := by
    exact
      seqSubroutine_haltsWithTape_of_haltsWithTape
        (A := A) (B := identity) (handoffMove := Direction.right)
        hA hid hAmid
        (CommonGround.Identity.exactIdentityDescription_run_from_start
          (Tape.move Direction.right Tmid))
  simpa [SeqViaCanonical, identity] using
    seqSubroutine_haltsWithOutput_of_haltsWithTape_eq
      (A := seqSubroutine A identity Direction.right)
      (B := B) (handoffMove := Direction.left)
      (seqSubroutine_subroutineReady hA hid)
      hB hAid hbridge hBout

theorem SeqViaCanonical_haltsWithOutput_of_haltsWithTape
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {input : Word Bool} {Tmid : Tape Bool} {out : Word Bool}
    (hAmid : A.HaltsWithTape input Tmid)
    (hBout :
      B.HaltsFromTapeWithOutput
        (Tape.move Direction.left (Tape.move Direction.right Tmid))
        out) :
    (SeqViaCanonical A B).HaltsWithOutput input out :=
  SeqViaCanonical_haltsWithOutput_of_haltsWithTape_eq
    hA hB hAmid rfl hBout

theorem SeqViaCanonical_outputFamilySpec
    {ι : Type} {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    (Tin Tmid Tnext : ι -> Tape Bool) (out : ι -> Word Bool)
    (hAhalts : forall i : ι, A.HaltsFromTape (Tin i) (Tmid i))
    (hbridge :
      forall i : ι,
        Tape.move Direction.left (Tape.move Direction.right (Tmid i)) =
          Tnext i)
    (hBhalts :
      forall i : ι, B.HaltsFromTapeWithOutput (Tnext i) (out i)) :
    (SeqViaCanonical A B).SubroutineReady ∧
      forall i : ι,
        (SeqViaCanonical A B).HaltsFromTapeWithOutput
          (Tin i) (out i) := by
  constructor
  · exact SeqViaCanonical_subroutineReady hA hB
  · intro i
    exact
      SeqViaCanonical_haltsFromTapeWithOutput_of_haltsFromTape_eq
        hA hB (hAhalts i) (hbridge i) (hBhalts i)

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC

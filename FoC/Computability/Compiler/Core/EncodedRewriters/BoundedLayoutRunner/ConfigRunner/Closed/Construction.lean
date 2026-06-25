import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Closed.Primitives
import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.Emitters
import FoC.Computability.Compiler.Core.FixedDescriptionBoundedSimulator.CodeRightShifted

set_option doc.verso true

/-!
# Bounded recognizer-configuration runner phase construction

This module contains the finite-machine phase contracts and the sequencing
adapters for the bounded recognizer-configuration runner.
-/

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters
namespace BoundedLayoutRunner

def SeqViaCanonical
    (A B : MachineDescription) : MachineDescription :=
  MachineDescription.seqSubroutine
    (MachineDescription.seqSubroutine A
      MachineDescription.ExactIdentityDescription Direction.right)
    B Direction.left

theorem SeqViaCanonical_subroutineReady
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady) :
    (SeqViaCanonical A B).SubroutineReady := by
  have hid : MachineDescription.ExactIdentityDescription.SubroutineReady :=
    ⟨MachineDescription.exactIdentityDescription_wellFormed,
      MachineDescription.exactIdentityDescription_haltTransitionFree⟩
  exact
    MachineDescription.seqSubroutine_subroutineReady
      (MachineDescription.seqSubroutine_subroutineReady hA hid)
      hB

theorem SeqViaCanonical_haltsWithTape_of_haltsWithTape
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {input midInput : Word Bool} {Tmid Tout : Tape Bool}
    (hAmid : A.HaltsWithTape input Tmid)
    (hbridge :
      Tape.move Direction.left (Tape.move Direction.right Tmid) =
        Tape.input midInput)
    (hBout : B.HaltsWithTape midInput Tout) :
    (SeqViaCanonical A B).HaltsWithTape input Tout := by
  let identity := MachineDescription.ExactIdentityDescription
  have hid : identity.SubroutineReady :=
    ⟨MachineDescription.exactIdentityDescription_wellFormed,
      MachineDescription.exactIdentityDescription_haltTransitionFree⟩
  have hAid :
      (MachineDescription.seqSubroutine A identity Direction.right).HaltsWithTape
        input (Tape.move Direction.right Tmid) := by
    exact
      MachineDescription.seqSubroutine_haltsWithTape_of_haltsWithTape
        (A := A) (B := identity) (handoffMove := Direction.right)
        hA hid hAmid
        ⟨0, rfl⟩
  have hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start
              tape :=
                Tape.move Direction.left
                  (Tape.move Direction.right Tmid) } =
          { state := B.halt
            tape := Tout } := by
    rcases
        MachineDescription.runConfig_eq_halt_of_haltsWithTape
          hBout with
      ⟨nB, hBRun⟩
    refine ⟨nB, ?_⟩
    simpa [hbridge] using hBRun
  simpa [SeqViaCanonical, identity] using
    MachineDescription.seqSubroutine_haltsWithTape_of_haltsWithTape
      (A := MachineDescription.seqSubroutine A identity Direction.right)
      (B := B) (handoffMove := Direction.left)
      (MachineDescription.seqSubroutine_subroutineReady hA hid)
      hB hAid hBReach

theorem SeqViaCanonical_haltsFromTape_of_haltsWithTape
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {Tin : Tape Bool} {midInput : Word Bool} {Tmid Tout : Tape Bool}
    (hAmid : A.HaltsFromTape Tin Tmid)
    (hbridge :
      Tape.move Direction.left (Tape.move Direction.right Tmid) =
        Tape.input midInput)
    (hBout : B.HaltsWithTape midInput Tout) :
    (SeqViaCanonical A B).HaltsFromTape Tin Tout := by
  let identity := MachineDescription.ExactIdentityDescription
  have hid : identity.SubroutineReady :=
    ⟨MachineDescription.exactIdentityDescription_wellFormed,
      MachineDescription.exactIdentityDescription_haltTransitionFree⟩
  have hAid :
      (MachineDescription.seqSubroutine A identity Direction.right).HaltsFromTape
        Tin (Tape.move Direction.right Tmid) := by
    exact
      MachineDescription.seqSubroutine_haltsFromTape_of_haltsFromTape
        (A := A) (B := identity) (handoffMove := Direction.right)
        hA hid hAmid
        ⟨0, rfl⟩
  have hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start
              tape :=
                Tape.move Direction.left
                  (Tape.move Direction.right Tmid) } =
          { state := B.halt
            tape := Tout } := by
    rcases
        MachineDescription.runConfig_eq_halt_of_haltsWithTape
          hBout with
      ⟨nB, hBRun⟩
    refine ⟨nB, ?_⟩
    simpa [hbridge] using hBRun
  simpa [SeqViaCanonical, identity] using
    MachineDescription.seqSubroutine_haltsFromTape_of_haltsFromTape
      (A := MachineDescription.seqSubroutine A identity Direction.right)
      (B := B) (handoffMove := Direction.left)
      (MachineDescription.seqSubroutine_subroutineReady hA hid)
      hB hAid hBReach

theorem SeqViaCanonical_haltsFromTape_of_haltsFromTape
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {Tin : Tape Bool} {Tin2 Tmid Tout : Tape Bool}
    (hAmid : A.HaltsFromTape Tin Tmid)
    (hbridge :
      Tape.move Direction.left (Tape.move Direction.right Tmid) = Tin2)
    (hBout : B.HaltsFromTape Tin2 Tout) :
    (SeqViaCanonical A B).HaltsFromTape Tin Tout := by
  let identity := MachineDescription.ExactIdentityDescription
  have hid : identity.SubroutineReady :=
    ⟨MachineDescription.exactIdentityDescription_wellFormed,
      MachineDescription.exactIdentityDescription_haltTransitionFree⟩
  have hAid :
      (MachineDescription.seqSubroutine A identity Direction.right).HaltsFromTape
        Tin (Tape.move Direction.right Tmid) := by
    exact
      MachineDescription.seqSubroutine_haltsFromTape_of_haltsFromTape
        (A := A) (B := identity) (handoffMove := Direction.right)
        hA hid hAmid
        ⟨0, rfl⟩
  have hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start
              tape :=
                Tape.move Direction.left
                  (Tape.move Direction.right Tmid) } =
          { state := B.halt
            tape := Tout } := by
    rcases
        MachineDescription.runConfig_eq_halt_of_haltsFromTape
          hBout with
      ⟨nB, hBRun⟩
    refine ⟨nB, ?_⟩
    simpa [hbridge] using hBRun
  simpa [SeqViaCanonical, identity] using
    MachineDescription.seqSubroutine_haltsFromTape_of_haltsFromTape
      (A := MachineDescription.seqSubroutine A identity Direction.right)
      (B := B) (handoffMove := Direction.left)
      (MachineDescription.seqSubroutine_subroutineReady hA hid)
      hB hAid hBReach

theorem SeqViaCanonical_haltsFromTape_of_haltsWithTape_equiv
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {Tin : Tape Bool} {midInput : Word Bool} {Tmid Tout : Tape Bool}
    (hAmid : A.HaltsFromTape Tin Tmid)
    (hbridge :
      Tape.Equiv
        (Tape.move Direction.left (Tape.move Direction.right Tmid))
        (Tape.input midInput))
    (hBout : B.HaltsWithTape midInput Tout) :
    MachineDescription.HaltsFromTapeEquiv (SeqViaCanonical A B) Tin Tout := by
  let identity := MachineDescription.ExactIdentityDescription
  have hid : identity.SubroutineReady :=
    ⟨MachineDescription.exactIdentityDescription_wellFormed,
      MachineDescription.exactIdentityDescription_haltTransitionFree⟩
  have hAid :
      (MachineDescription.seqSubroutine A identity Direction.right).HaltsFromTape
        Tin (Tape.move Direction.right Tmid) := by
    exact
      MachineDescription.seqSubroutine_haltsFromTape_of_haltsFromTape
        (A := A) (B := identity) (handoffMove := Direction.right)
        hA hid hAmid
        ⟨0, rfl⟩
  rcases hBout with ⟨nB, hnB⟩
  have hB_equiv := MachineDescription.HaltsFromTapeEquiv_of_input_equiv (D := B)
    (Tin := Tape.input midInput)
    (Tin' := Tape.move Direction.left (Tape.move Direction.right Tmid))
    (Tout := Tout)
    (Tape.Equiv.symm hbridge)
    ⟨nB, by simpa [MachineDescription.HaltsWithTapeIn, MachineDescription.HaltsFromTapeIn] using hnB⟩
  rcases hB_equiv with ⟨Tactual, hB_actual_halt, hB_actual_equiv⟩
  
  have hseq_actual := MachineDescription.seqSubroutine_haltsFromTape_of_haltsFromTape
    (A := MachineDescription.seqSubroutine A identity Direction.right)
    (B := B) (handoffMove := Direction.left)
    (MachineDescription.seqSubroutine_subroutineReady hA hid)
    hB hAid (MachineDescription.runConfig_eq_halt_of_haltsFromTape hB_actual_halt)
  exact ⟨Tactual, by simpa [SeqViaCanonical, identity] using hseq_actual, hB_actual_equiv⟩

theorem exactIdentityDescription_runConfig
    (n : Nat) (T : Tape Bool) :
    MachineDescription.ExactIdentityDescription.runConfig n
        { state := MachineDescription.ExactIdentityDescription.start, tape := T } =
      { state := MachineDescription.ExactIdentityDescription.halt, tape := T } := by
  cases n <;>
    simp [MachineDescription.runConfig, MachineDescription.stepConfig, MachineDescription.lookupTransition, MachineDescription.ExactIdentityDescription]

theorem SeqViaCanonical_haltsFromTapeEquiv_of_haltsWithTape
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {Tin : Tape Bool} {midInput : Word Bool} {Tmid Tout : Tape Bool}
    (hAmid : A.HaltsFromTapeEquiv Tin Tmid)
    (hbridge :
      Tape.Equiv
        (Tape.move Direction.left (Tape.move Direction.right Tmid))
        (Tape.input midInput))
    (hBout : B.HaltsWithTape midInput Tout) :
    MachineDescription.HaltsFromTapeEquiv (SeqViaCanonical A B) Tin Tout := by
  rcases hAmid with ⟨Tactual, hhalt, hequiv⟩
  have hequiv2 := Tape.Equiv.moveRight hequiv
  have hequiv3 := Tape.Equiv.moveLeft hequiv2
  have hbridge_actual := Tape.Equiv.trans hequiv3 hbridge
  exact SeqViaCanonical_haltsFromTape_of_haltsWithTape_equiv hA hB hhalt hbridge_actual hBout

theorem SeqViaCanonical_haltsFromTape_inv
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {Tin Tout : Tape Bool}
    (hseq :
      (SeqViaCanonical A B).HaltsFromTape Tin Tout) :
    exists Tmid : Tape Bool,
      A.HaltsFromTape Tin Tmid ∧
      B.HaltsFromTape (Tape.move Direction.left (Tape.move Direction.right Tmid)) Tout := by
  let identity := MachineDescription.ExactIdentityDescription
  have hid : identity.SubroutineReady :=
    ⟨MachineDescription.exactIdentityDescription_wellFormed,
      MachineDescription.exactIdentityDescription_haltTransitionFree⟩
  have hseq' : (MachineDescription.seqSubroutine (MachineDescription.seqSubroutine A identity Direction.right) B Direction.left).HaltsFromTape Tin Tout := by
    simpa [SeqViaCanonical, identity] using hseq
  rcases MachineDescription.seqSubroutine_haltsFromTape_inv
    (MachineDescription.seqSubroutine_subroutineReady hA hid) hB hseq' with ⟨Tmid_seq, hA_seq, ⟨nB, hBRun⟩⟩
  rcases MachineDescription.seqSubroutine_haltsFromTape_inv hA hid hA_seq with ⟨Tmid, hA_halt, ⟨nId, hIdRun⟩⟩
  have hTmid_seq_eq : Tmid_seq = Tape.move Direction.right Tmid := by
    have h_final := exactIdentityDescription_runConfig nId (Tape.move Direction.right Tmid)
    rw [h_final] at hIdRun
    exact (congrArg MachineDescription.Configuration.tape hIdRun).symm
  subst hTmid_seq_eq
  exact ⟨Tmid, hA_halt, ⟨nB, by
    constructor
    · simpa [MachineDescription.HaltsFromTapeIn] using congrArg MachineDescription.Configuration.state hBRun
    · simpa [MachineDescription.HaltsFromTapeIn] using congrArg MachineDescription.Configuration.tape hBRun⟩⟩

theorem moveLeft_moveRight_equiv_self (T : Tape Bool) :
    Tape.Equiv (Tape.move Direction.left (Tape.move Direction.right T)) T := by
  cases T with
  | mk left head right =>
    simp [Tape.Equiv, Tape.move, Tape.moveLeft, Tape.moveRight]
    cases right with
    | nil => simp [Tape.dropTrailingNone]
    | cons x xs => simp [Tape.dropTrailingNone]

theorem SeqViaCanonical_closed_equiv
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {Tin : Tape Bool} {midInput : Word Bool} {Tout : Tape Bool}
    (hA_closed : MachineDescription.ClosedFromTapeEquiv A Tin (Tape.move Direction.left (Tape.input midInput)))
    (hB_closed : MachineDescription.ClosedFromTapeEquiv B (Tape.input midInput) Tout)
    (hmid_bridge : Tape.move Direction.left (Tape.move Direction.right (Tape.move Direction.left (Tape.input midInput))) = Tape.input midInput) :
    MachineDescription.ClosedFromTapeEquiv (SeqViaCanonical A B) Tin Tout := by
  intro T hT
  rcases SeqViaCanonical_haltsFromTape_inv hA hB hT with ⟨Tmid, hA_run, hB_run⟩
  have hA_eq := hA_closed Tmid hA_run
  have hA_eq_moved := Tape.Equiv.move (Tape.Equiv.move hA_eq Direction.right) Direction.left
  rw [hmid_bridge] at hA_eq_moved
  
  have hB_equiv := MachineDescription.HaltsFromTapeEquiv_of_input_equiv (D := B)
    (Tin := Tape.move Direction.left (Tape.move Direction.right Tmid))
    (Tin' := Tape.input midInput)
    (Tout := T)
    hA_eq_moved
    hB_run
  rcases hB_equiv with ⟨Tactual, hB_actual_halt, hB_actual_equiv⟩
  have hB_eq := hB_closed Tactual hB_actual_halt
  exact Tape.Equiv.trans (Tape.Equiv.symm hB_actual_equiv) hB_eq

theorem rightShiftedOutputCompiled_haltsWithTape_of_transform
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (hD : RightShiftedOutputCompiledSubroutineByDescription P D)
    {code out : Word MachineCodeSymbol}
    (htransform : P.transform code = some out) :
    D.HaltsWithTape
      (MachineDescription.encodeCodeWordAsInput code)
      (Tape.move Direction.right
        (Tape.input
          (MachineDescription.encodeCodeWordAsInput out))) := by
  have houtput :
      D.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out) :=
    (hD.right.right.left code out).mpr htransform
  rcases houtput with ⟨n, hn⟩
  let T : Tape Bool :=
    (D.runConfig n
      (D.initial
        (MachineDescription.encodeCodeWordAsInput code))).tape
  have hhalt :
      D.HaltsWithTape
        (MachineDescription.encodeCodeWordAsInput code) T := by
    exact ⟨n, ⟨hn.left, rfl⟩⟩
  rcases hD.right.right.right code T hhalt with
    ⟨actual, hactual, hT⟩
  have hactualOut : actual = out := by
    rw [htransform] at hactual
    cases hactual
    rfl
  rw [hT] at hhalt
  simpa [hactualOut] using hhalt

theorem rightShiftedOutputCompiledSubroutineByDescription_congr
    {P Q : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (hPQ : forall code : Word MachineCodeSymbol,
      P.transform code = Q.transform code)
    (hD : RightShiftedOutputCompiledSubroutineByDescription P D) :
    RightShiftedOutputCompiledSubroutineByDescription Q D := by
  constructor
  · exact hD.left
  constructor
  · exact hD.right.left
  constructor
  · intro code out
    rw [← hPQ code]
    exact hD.right.right.left code out
  · intro code T hhalt
    rcases hD.right.right.right code T hhalt with
      ⟨out, htransform, hT⟩
    exact ⟨out, by simpa [hPQ code] using htransform, hT⟩

def TapeCodeExactPhaseFromClosedHandoff
    (closed : MachineDescription) : MachineDescription :=
  MachineDescription.seqSubroutine closed
    MachineDescription.ExactIdentityDescription
    tapeCodePrimitiveCodeWordHandoffMove

theorem TapeCodeExactPhaseFromClosedHandoff_subroutineReady
    {P : MachineDescription.TapeCodePrimitive}
    {closed : MachineDescription}
    (hclosed :
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        P closed tapeCodePrimitiveCodeWordHandoffMove) :
    (TapeCodeExactPhaseFromClosedHandoff closed).SubroutineReady := by
  have hclosedReady : closed.SubroutineReady :=
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_subroutineReady
      hclosed
  have hid : MachineDescription.ExactIdentityDescription.SubroutineReady :=
    ⟨MachineDescription.exactIdentityDescription_wellFormed,
      MachineDescription.exactIdentityDescription_haltTransitionFree⟩
  exact
    MachineDescription.seqSubroutine_subroutineReady
      hclosedReady hid

theorem TapeCodeExactPhaseFromClosedHandoff_forward
    {P : MachineDescription.TapeCodePrimitive}
    {closed : MachineDescription}
    (hclosed :
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        P closed tapeCodePrimitiveCodeWordHandoffMove)
    {code out : Word MachineCodeSymbol}
    (htransform : P.transform code = some out) :
    (TapeCodeExactPhaseFromClosedHandoff closed).HaltsWithTape
      (MachineDescription.encodeCodeWordAsInput code)
      (Tape.input (MachineDescription.encodeCodeWordAsInput out)) := by
  let identity := MachineDescription.ExactIdentityDescription
  have hclosedReady : closed.SubroutineReady :=
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_subroutineReady
      hclosed
  have hid : identity.SubroutineReady :=
    ⟨MachineDescription.exactIdentityDescription_wellFormed,
      MachineDescription.exactIdentityDescription_haltTransitionFree⟩
  rcases
      (tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_handoffRealized
        hclosed).right code out htransform with
    ⟨Tmid, hclosedHalt, hhandoff⟩
  have hidentityReach :
      exists nB : Nat,
        identity.runConfig nB
            { state := identity.start
              tape := Tape.move tapeCodePrimitiveCodeWordHandoffMove Tmid } =
          { state := identity.halt
            tape := Tape.input (MachineDescription.encodeCodeWordAsInput out) } := by
    refine ⟨0, ?_⟩
    rw [hhandoff]
    rfl
  simpa [TapeCodeExactPhaseFromClosedHandoff, identity,
    tapeCodePrimitiveCodeWordHandoffMove] using
    MachineDescription.seqSubroutine_haltsWithTape_of_haltsWithTape
      (A := closed) (B := identity)
      (handoffMove := tapeCodePrimitiveCodeWordHandoffMove)
      hclosedReady hid hclosedHalt hidentityReach

theorem TapeCodeExactPhaseFromClosedHandoff_closed_eq
    {P : MachineDescription.TapeCodePrimitive}
    {closed : MachineDescription}
    (hclosed :
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        P closed tapeCodePrimitiveCodeWordHandoffMove)
    {code out : Word MachineCodeSymbol}
    (htransform : P.transform code = some out)
    {T : Tape Bool}
    (hhalt :
      (TapeCodeExactPhaseFromClosedHandoff closed).HaltsWithTape
        (MachineDescription.encodeCodeWordAsInput code) T) :
    T = Tape.input (MachineDescription.encodeCodeWordAsInput out) := by
  let identity := MachineDescription.ExactIdentityDescription
  have hclosedReady : closed.SubroutineReady :=
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_subroutineReady
      hclosed
  have hid : identity.SubroutineReady :=
    ⟨MachineDescription.exactIdentityDescription_wellFormed,
      MachineDescription.exactIdentityDescription_haltTransitionFree⟩
  rcases
      MachineDescription.seqSubroutine_haltsWithTape_inv
        (A := closed) (B := identity)
        (handoffMove := tapeCodePrimitiveCodeWordHandoffMove)
        hclosedReady hid
        (by
          simpa [TapeCodeExactPhaseFromClosedHandoff, identity] using hhalt) with
    ⟨Tmid, hclosedHalt, hidentityReach⟩
  rcases hclosed.right code Tmid hclosedHalt with
    ⟨actual, hactual, _hnormalized, hhandoff⟩
  have hactualOut : actual = out := by
    rw [htransform] at hactual
    cases hactual
    rfl
  rcases hidentityReach with ⟨nB, hidentityRun⟩
  have hT :
      T = Tape.move tapeCodePrimitiveCodeWordHandoffMove Tmid := by
    have hidentityStart :
        identity.runConfig nB
            { state := identity.start
              tape := Tape.move tapeCodePrimitiveCodeWordHandoffMove Tmid } =
          { state := identity.halt
            tape := Tape.move tapeCodePrimitiveCodeWordHandoffMove Tmid } := by
      cases nB <;>
        simp [identity, MachineDescription.ExactIdentityDescription,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition]
    have hcfg :
        ({ state := identity.halt
           tape := Tape.move tapeCodePrimitiveCodeWordHandoffMove Tmid } :
          MachineDescription.Configuration) =
        { state := identity.halt, tape := T } := by
      simpa [identity] using
        (hidentityStart.symm.trans hidentityRun)
    exact (congrArg MachineDescription.Configuration.tape hcfg).symm
  rw [hT]
  simpa [hactualOut] using hhandoff

def TapeCodeCheckedPhaseFromClosedHandoff
    (closed : MachineDescription) : MachineDescription :=
  MachineDescription.seqSubroutine closed
    MachineDescription.ExactIdentityDescription
    tapeCodePrimitiveCodeWordHandoffMove

theorem TapeCodeCheckedPhaseFromClosedHandoff_subroutineReady
    {P : MachineDescription.TapeCodePrimitive}
    {closed : MachineDescription}
    (hclosed :
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        P closed tapeCodePrimitiveCodeWordHandoffMove) :
    (TapeCodeCheckedPhaseFromClosedHandoff closed).SubroutineReady := by
  have hclosedReady : closed.SubroutineReady :=
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_subroutineReady
      hclosed
  have hid : MachineDescription.ExactIdentityDescription.SubroutineReady :=
    ⟨MachineDescription.exactIdentityDescription_wellFormed,
      MachineDescription.exactIdentityDescription_haltTransitionFree⟩
  exact
    MachineDescription.seqSubroutine_subroutineReady
      hclosedReady hid

/--
**Checked Handoff Equivalence Bridge**

This theorem bridges a known topological mismatch between {name}`checkedInputTape` (which has a trailing {lean}`[none]`)
and {name}`Tape.input` (which does not). The hypothesis {name}`hclosed` asserts that the machine runs correctly on
{name}`Tape.input`.

Exact canonicalization is impossible because the finite machine cannot erase the trailing {lit}`none` back to an infinite
blank tape. Instead, the theorem intentionally returns {name}`Tape.Equiv` between the actual output tape and
the canonical expected output tape.

This equivalence is enough to preserve the normalized encoded output required by the runner.
-/
theorem TapeCodeCheckedPhaseFromClosedHandoff_forward
    {P : MachineDescription.TapeCodePrimitive}
    {closed : MachineDescription}
    (hclosed :
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        P closed tapeCodePrimitiveCodeWordHandoffMove)
    {code out : Word MachineCodeSymbol}
    (htransform : P.transform code = some out) :
    (TapeCodeCheckedPhaseFromClosedHandoff closed).HaltsFromTapeEquiv
      (checkedInputTape (MachineDescription.encodeCodeWordAsInput code))
      (Tape.input (MachineDescription.encodeCodeWordAsInput out)) := by
  have h_outputCompiled := hclosed.1
  have h_exactOutput := hclosed.2
  have h_outputCompiledByDesc := h_outputCompiled.1
  have h_haltsWithOutput : closed.HaltsWithOutput (MachineDescription.encodeCodeWordAsInput code) (MachineDescription.encodeCodeWordAsInput out) :=
    (h_outputCompiledByDesc.2 code out).mpr htransform
  rcases h_haltsWithOutput with ⟨n, hn⟩
  let T_canonical := (closed.runConfig n (closed.initial (MachineDescription.encodeCodeWordAsInput code))).tape
  have h_haltsWithTape : closed.HaltsWithTape (MachineDescription.encodeCodeWordAsInput code) T_canonical :=
    ⟨n, hn.1, rfl⟩
  have h_exact := h_exactOutput code T_canonical h_haltsWithTape
  rcases h_exact with ⟨out', h_transform', _, h_move⟩
  have h_out_eq : out' = out := by
    rw [htransform] at h_transform'
    injection h_transform' with h_eq
    exact h_eq.symm
  rw [h_out_eq] at h_move
  have hid : MachineDescription.ExactIdentityDescription.SubroutineReady :=
    ⟨MachineDescription.exactIdentityDescription_wellFormed,
      MachineDescription.exactIdentityDescription_haltTransitionFree⟩
  have hclosedReady : closed.SubroutineReady :=
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_subroutineReady hclosed
  have hseq_halts : (TapeCodeCheckedPhaseFromClosedHandoff closed).HaltsFromTape
      (Tape.input (MachineDescription.encodeCodeWordAsInput code))
      (Tape.move tapeCodePrimitiveCodeWordHandoffMove T_canonical) := by
    exact
      MachineDescription.seqSubroutine_haltsFromTape_of_haltsFromTape
        (A := closed) (B := MachineDescription.ExactIdentityDescription)
        (handoffMove := tapeCodePrimitiveCodeWordHandoffMove)
        hclosedReady hid h_haltsWithTape
        ⟨0, rfl⟩
  have hseq_halts' : (TapeCodeCheckedPhaseFromClosedHandoff closed).HaltsFromTape
      (Tape.input (MachineDescription.encodeCodeWordAsInput code))
      (Tape.input (MachineDescription.encodeCodeWordAsInput out)) := by
    rwa [h_move] at hseq_halts
  have h_equiv_in := checkedInputTape_equiv_input (MachineDescription.encodeCodeWordAsInput code)
  exact MachineDescription.HaltsFromTapeEquiv_of_input_equiv (Tape.Equiv.symm h_equiv_in) hseq_halts'

theorem TapeCodeCheckedPhaseFromClosedHandoff_closed_equiv
    {P : MachineDescription.TapeCodePrimitive}
    {closed : MachineDescription}
    (hclosed :
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        P closed tapeCodePrimitiveCodeWordHandoffMove)
    {code out : Word MachineCodeSymbol}
    (htransform : P.transform code = some out)
    {T : Tape Bool}
    (hhalt :
      (TapeCodeCheckedPhaseFromClosedHandoff closed).HaltsFromTape
        (checkedInputTape (MachineDescription.encodeCodeWordAsInput code)) T) :
    Tape.Equiv T (Tape.input (MachineDescription.encodeCodeWordAsInput out)) := by
  have h_forward := TapeCodeCheckedPhaseFromClosedHandoff_forward hclosed htransform
  rcases h_forward with ⟨Tactual, h_halt_actual, h_equiv_actual⟩
  have hid : MachineDescription.ExactIdentityDescription.SubroutineReady :=
    ⟨MachineDescription.exactIdentityDescription_wellFormed,
      MachineDescription.exactIdentityDescription_haltTransitionFree⟩
  have hclosedReady : closed.SubroutineReady :=
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_subroutineReady hclosed
  have h_ready := MachineDescription.seqSubroutine_subroutineReady (handoffMove := tapeCodePrimitiveCodeWordHandoffMove) hclosedReady hid
  have h_T_eq := MachineDescription.haltsFromTape_functional_of_haltTransitionFree h_ready.2 hhalt h_halt_actual
  subst h_T_eq
  exact h_equiv_actual

def AcceptProjectionSpec
    (projector : MachineDescription) : Prop :=
  projector.SubroutineReady ∧
    (forall L : MachineDescription.DovetailLayout,
      projector.HaltsFromTapeEquiv
        (ParsedLayoutCheckedTape L)
        (MachineDescription.SimulatorLayout.tape
          (AcceptSimulatorLayout L))) ∧
    (forall L : MachineDescription.DovetailLayout,
      projector.ClosedFromTapeEquiv
        (ParsedLayoutCheckedTape L)
        (MachineDescription.SimulatorLayout.tape
          (AcceptSimulatorLayout L)))

def RejectProjectionSpec
    (projector : MachineDescription) : Prop :=
  projector.SubroutineReady ∧
    (forall L : MachineDescription.DovetailLayout,
      projector.HaltsWithTape
        (ParsedLayoutBits L)
        (MachineDescription.SimulatorLayout.tape
          (RejectSimulatorLayout L))) ∧
    (forall L : MachineDescription.DovetailLayout,
     forall T : Tape Bool,
      projector.HaltsWithTape (ParsedLayoutBits L) T ->
        T =
          MachineDescription.SimulatorLayout.tape
            (RejectSimulatorLayout L))

def AcceptMergeSpec
    (accept merger : MachineDescription) : Prop :=
  merger.SubroutineReady ∧
    (forall L : MachineDescription.DovetailLayout,
      merger.HaltsWithTape
        (MachineDescription.SimulatorLayout.asBoolInput
          (MachineDescription.SimulatorLayout.run
            accept L.stage (AcceptSimulatorLayout L)))
        (ParsedLayoutTape (ConfigRunnerAfterAccept accept L))) ∧
    (forall L : MachineDescription.DovetailLayout,
     forall T : Tape Bool,
      merger.HaltsWithTape
        (MachineDescription.SimulatorLayout.asBoolInput
          (MachineDescription.SimulatorLayout.run
            accept L.stage (AcceptSimulatorLayout L))) T ->
        T = ParsedLayoutTape (ConfigRunnerAfterAccept accept L))

def RejectMergeSpec
    (reject merger : MachineDescription) : Prop :=
  merger.SubroutineReady ∧
    (forall L : MachineDescription.DovetailLayout,
      merger.HaltsWithTape
        (MachineDescription.SimulatorLayout.asBoolInput
          (MachineDescription.SimulatorLayout.run
            reject L.stage (RejectSimulatorLayout L)))
        (ParsedLayoutTape (ConfigRunnerAfterReject reject L))) ∧
    (forall L : MachineDescription.DovetailLayout,
     forall T : Tape Bool,
      merger.HaltsWithTape
        (MachineDescription.SimulatorLayout.asBoolInput
          (MachineDescription.SimulatorLayout.run
            reject L.stage (RejectSimulatorLayout L))) T ->
        T = ParsedLayoutTape (ConfigRunnerAfterReject reject L))

def ConfigRunnerPhaseConstructionData
    (accept reject : MachineDescription) : Prop :=
  exists acceptProject acceptSim acceptMerge
    rejectProject rejectSim rejectMerge : MachineDescription,
    AcceptProjectionSpec acceptProject ∧
      FixedDescriptionBoundedSimulatorCanonicalSpec accept acceptSim ∧
      AcceptMergeSpec accept acceptMerge ∧
      RejectProjectionSpec rejectProject ∧
      FixedDescriptionBoundedSimulatorCanonicalSpec reject rejectSim ∧
      RejectMergeSpec reject rejectMerge

def ConfigRunnerPhaseConstruction : Prop :=
  forall accept reject : MachineDescription,
    ConfigRunnerPhaseConstructionData accept reject

def ConfigRunnerPrimitiveClosedHandoffConstruction : Prop :=
  exists acceptProject acceptMerge
    rejectProject rejectMerge : MachineDescription,
    TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      AcceptProjectionPrimitive
      acceptProject tapeCodePrimitiveCodeWordHandoffMove ∧
    TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      AcceptMergePrimitive
      acceptMerge tapeCodePrimitiveCodeWordHandoffMove ∧
    TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      RejectProjectionPrimitive
      rejectProject tapeCodePrimitiveCodeWordHandoffMove ∧
    TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      RejectMergePrimitive
      rejectMerge tapeCodePrimitiveCodeWordHandoffMove

def AcceptProjectionPrimitiveClosedHandoffConstruction : Prop :=
  exists closed : MachineDescription,
    TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      AcceptProjectionPrimitive
      closed tapeCodePrimitiveCodeWordHandoffMove

def AcceptMergePrimitiveClosedHandoffConstruction : Prop :=
  exists closed : MachineDescription,
    TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      AcceptMergePrimitive
      closed tapeCodePrimitiveCodeWordHandoffMove

def RejectProjectionPrimitiveClosedHandoffConstruction : Prop :=
  exists closed : MachineDescription,
    TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      RejectProjectionPrimitive
      closed tapeCodePrimitiveCodeWordHandoffMove

def RejectMergePrimitiveClosedHandoffConstruction : Prop :=
  exists closed : MachineDescription,
    TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      RejectMergePrimitive
      closed tapeCodePrimitiveCodeWordHandoffMove

def SelectedProjectionPrimitiveClosedHandoffConstruction : Prop :=
  forall useAccept : Bool,
    exists closed : MachineDescription,
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        (SelectedProjectionPrimitive useAccept)
        closed tapeCodePrimitiveCodeWordHandoffMove

def SelectedMergePrimitiveClosedHandoffConstruction : Prop :=
  forall useAccept : Bool,
    exists closed : MachineDescription,
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        (SelectedMergePrimitive useAccept)
        closed tapeCodePrimitiveCodeWordHandoffMove

theorem acceptProjectionPrimitiveClosedHandoffConstruction_of_selected
    (h : SelectedProjectionPrimitiveClosedHandoffConstruction) :
    AcceptProjectionPrimitiveClosedHandoffConstruction := by
  rcases h true with ⟨closed, hclosed⟩
  refine ⟨closed, ?_⟩
  exact
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_congr
      (P := SelectedProjectionPrimitive true)
      (Q := AcceptProjectionPrimitive)
      (D := closed)
      (handoffMove := tapeCodePrimitiveCodeWordHandoffMove)
      (by
        intro code
        rfl)
      hclosed

theorem rejectProjectionPrimitiveClosedHandoffConstruction_of_selected
    (h : SelectedProjectionPrimitiveClosedHandoffConstruction) :
    RejectProjectionPrimitiveClosedHandoffConstruction := by
  rcases h false with ⟨closed, hclosed⟩
  refine ⟨closed, ?_⟩
  exact
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_congr
      (P := SelectedProjectionPrimitive false)
      (Q := RejectProjectionPrimitive)
      (D := closed)
      (handoffMove := tapeCodePrimitiveCodeWordHandoffMove)
      (by
        intro code
        rfl)
      hclosed

theorem acceptMergePrimitiveClosedHandoffConstruction_of_selected
    (h : SelectedMergePrimitiveClosedHandoffConstruction) :
    AcceptMergePrimitiveClosedHandoffConstruction := by
  rcases h true with ⟨closed, hclosed⟩
  refine ⟨closed, ?_⟩
  exact
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_congr
      (P := SelectedMergePrimitive true)
      (Q := AcceptMergePrimitive)
      (D := closed)
      (handoffMove := tapeCodePrimitiveCodeWordHandoffMove)
      (by
        intro code
        rfl)
      hclosed

theorem rejectMergePrimitiveClosedHandoffConstruction_of_selected
    (h : SelectedMergePrimitiveClosedHandoffConstruction) :
    RejectMergePrimitiveClosedHandoffConstruction := by
  rcases h false with ⟨closed, hclosed⟩
  refine ⟨closed, ?_⟩
  exact
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_congr
      (P := SelectedMergePrimitive false)
      (Q := RejectMergePrimitive)
      (D := closed)
      (handoffMove := tapeCodePrimitiveCodeWordHandoffMove)
      (by
        intro code
        rfl)
      hclosed

theorem configRunnerPrimitiveClosedHandoffConstruction_of_parts
    (hacceptProject : AcceptProjectionPrimitiveClosedHandoffConstruction)
    (hacceptMerge : AcceptMergePrimitiveClosedHandoffConstruction)
    (hrejectProject : RejectProjectionPrimitiveClosedHandoffConstruction)
    (hrejectMerge : RejectMergePrimitiveClosedHandoffConstruction) :
    ConfigRunnerPrimitiveClosedHandoffConstruction := by
  rcases hacceptProject with ⟨acceptProject, hacceptProject⟩
  rcases hacceptMerge with ⟨acceptMerge, hacceptMerge⟩
  rcases hrejectProject with ⟨rejectProject, hrejectProject⟩
  rcases hrejectMerge with ⟨rejectMerge, hrejectMerge⟩
  exact
    ⟨acceptProject, acceptMerge, rejectProject, rejectMerge,
      hacceptProject, hacceptMerge, hrejectProject, hrejectMerge⟩

theorem AcceptProjectionSpec_of_closedHandoff
    {closed : MachineDescription}
    (hclosed :
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        AcceptProjectionPrimitive
        closed tapeCodePrimitiveCodeWordHandoffMove) :
    AcceptProjectionSpec
      (TapeCodeCheckedPhaseFromClosedHandoff closed) := by
  constructor
  · exact TapeCodeCheckedPhaseFromClosedHandoff_subroutineReady hclosed
  constructor
  · intro L
    simpa [ParsedLayoutCheckedTape,
      MachineDescription.SimulatorLayout.tape,
      MachineDescription.SimulatorLayout.asBoolInput] using
      TapeCodeCheckedPhaseFromClosedHandoff_forward
        hclosed (AcceptProjectionPrimitive_encode L)
  · intro L T hhalt
    have hhalt' :
        (TapeCodeCheckedPhaseFromClosedHandoff closed).HaltsFromTape
          (checkedInputTape (MachineDescription.encodeCodeWordAsInput
            (MachineDescription.DovetailLayout.encode L))) T := by
      simpa [ParsedLayoutCheckedTape] using hhalt
    have hT :=
      TapeCodeCheckedPhaseFromClosedHandoff_closed_equiv
        hclosed (AcceptProjectionPrimitive_encode L) hhalt'
    simpa [MachineDescription.SimulatorLayout.tape,
      MachineDescription.SimulatorLayout.asBoolInput] using hT

theorem RejectProjectionSpec_of_closedHandoff
    {closed : MachineDescription}
    (hclosed :
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        RejectProjectionPrimitive
        closed tapeCodePrimitiveCodeWordHandoffMove) :
    RejectProjectionSpec
      (TapeCodeExactPhaseFromClosedHandoff closed) := by
  constructor
  · exact TapeCodeExactPhaseFromClosedHandoff_subroutineReady hclosed
  constructor
  · intro L
    simpa [ParsedLayoutBits,
      MachineDescription.SimulatorLayout.tape,
      MachineDescription.SimulatorLayout.asBoolInput] using
      TapeCodeExactPhaseFromClosedHandoff_forward
        hclosed (RejectProjectionPrimitive_encode L)
  · intro L T hhalt
    have hhalt' :
        (TapeCodeExactPhaseFromClosedHandoff closed).HaltsWithTape
          (MachineDescription.encodeCodeWordAsInput
            (MachineDescription.DovetailLayout.encode L)) T := by
      simpa [ParsedLayoutBits] using hhalt
    have hT :=
      TapeCodeExactPhaseFromClosedHandoff_closed_eq
        hclosed (RejectProjectionPrimitive_encode L) hhalt'
    simpa [MachineDescription.SimulatorLayout.tape,
      MachineDescription.SimulatorLayout.asBoolInput] using hT

theorem AcceptMergeSpec_of_closedHandoff
    (accept : MachineDescription)
    {closed : MachineDescription}
    (hclosed :
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        AcceptMergePrimitive
        closed tapeCodePrimitiveCodeWordHandoffMove) :
    AcceptMergeSpec accept
      (TapeCodeExactPhaseFromClosedHandoff closed) := by
  constructor
  · exact TapeCodeExactPhaseFromClosedHandoff_subroutineReady hclosed
  constructor
  · intro L
    simpa [MachineDescription.SimulatorLayout.asBoolInput,
      ParsedLayoutTape, ParsedLayoutBits] using
      TapeCodeExactPhaseFromClosedHandoff_forward
        hclosed (AcceptMergePrimitive_encode_run accept L)
  · intro L T hhalt
    have hhalt' :
        (TapeCodeExactPhaseFromClosedHandoff closed).HaltsWithTape
          (MachineDescription.encodeCodeWordAsInput
            (MachineDescription.SimulatorLayout.encode
              (MachineDescription.SimulatorLayout.run
                accept L.stage (AcceptSimulatorLayout L)))) T := by
      simpa [MachineDescription.SimulatorLayout.asBoolInput] using hhalt
    have hT :=
      TapeCodeExactPhaseFromClosedHandoff_closed_eq
        hclosed (AcceptMergePrimitive_encode_run accept L) hhalt'
    simpa [ParsedLayoutTape, ParsedLayoutBits] using hT

theorem RejectMergeSpec_of_closedHandoff
    (reject : MachineDescription)
    {closed : MachineDescription}
    (hclosed :
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        RejectMergePrimitive
        closed tapeCodePrimitiveCodeWordHandoffMove) :
    RejectMergeSpec reject
      (TapeCodeExactPhaseFromClosedHandoff closed) := by
  constructor
  · exact TapeCodeExactPhaseFromClosedHandoff_subroutineReady hclosed
  constructor
  · intro L
    simpa [MachineDescription.SimulatorLayout.asBoolInput,
      ParsedLayoutTape, ParsedLayoutBits] using
      TapeCodeExactPhaseFromClosedHandoff_forward
        hclosed (RejectMergePrimitive_encode_run reject L)
  · intro L T hhalt
    have hhalt' :
        (TapeCodeExactPhaseFromClosedHandoff closed).HaltsWithTape
          (MachineDescription.encodeCodeWordAsInput
            (MachineDescription.SimulatorLayout.encode
              (MachineDescription.SimulatorLayout.run
                reject L.stage (RejectSimulatorLayout L)))) T := by
      simpa [MachineDescription.SimulatorLayout.asBoolInput] using hhalt
    have hT :=
      TapeCodeExactPhaseFromClosedHandoff_closed_eq
        hclosed (RejectMergePrimitive_encode_run reject L) hhalt'
    simpa [ParsedLayoutTape, ParsedLayoutBits] using hT

theorem configRunnerPhaseConstruction_of_primitiveClosedHandoff
    (hsim : FixedDescriptionBoundedSimulatorCanonicalConstruction)
    (hprimitive : ConfigRunnerPrimitiveClosedHandoffConstruction) :
    ConfigRunnerPhaseConstruction := by
  intro accept reject
  rcases hprimitive with
    ⟨acceptProject, acceptMerge, rejectProject, rejectMerge,
      hacceptProject, hacceptMerge, hrejectProject, hrejectMerge⟩
  rcases hsim accept with ⟨acceptSim, hacceptSim⟩
  rcases hsim reject with ⟨rejectSim, hrejectSim⟩
  exact
    ⟨TapeCodeExactPhaseFromClosedHandoff acceptProject,
      acceptSim,
      TapeCodeExactPhaseFromClosedHandoff acceptMerge,
      TapeCodeExactPhaseFromClosedHandoff rejectProject,
      rejectSim,
      TapeCodeExactPhaseFromClosedHandoff rejectMerge,
      AcceptProjectionSpec_of_closedHandoff hacceptProject,
      hacceptSim,
      AcceptMergeSpec_of_closedHandoff accept hacceptMerge,
      RejectProjectionSpec_of_closedHandoff hrejectProject,
      hrejectSim,
      RejectMergeSpec_of_closedHandoff reject hrejectMerge⟩

def ConfigRunnerPhaseRunner
    (acceptProject acceptSim acceptMerge
      rejectProject rejectSim rejectMerge : MachineDescription) :
    MachineDescription :=
  SeqViaCanonical
    (SeqViaCanonical
      (SeqViaCanonical
        (SeqViaCanonical
          (SeqViaCanonical acceptProject acceptSim)
          acceptMerge)
        rejectProject)
      rejectSim)
    rejectMerge

theorem configRunnerPhaseRunner_spec
    {accept reject : MachineDescription}
    {acceptProject acceptSim acceptMerge
      rejectProject rejectSim rejectMerge : MachineDescription}
    (hacceptProject : AcceptProjectionSpec acceptProject)
    (hacceptSim :
      FixedDescriptionBoundedSimulatorCanonicalSpec accept acceptSim)
    (hacceptMerge : AcceptMergeSpec accept acceptMerge)
    (hrejectProject : RejectProjectionSpec rejectProject)
    (hrejectSim :
      FixedDescriptionBoundedSimulatorCanonicalSpec reject rejectSim)
    (hrejectMerge : RejectMergeSpec reject rejectMerge) :
    AcceptRejectConfigRunnerSpec accept reject
      (ConfigRunnerPhaseRunner
        acceptProject acceptSim acceptMerge
        rejectProject rejectSim rejectMerge) := by
  let APAS := SeqViaCanonical acceptProject acceptSim
  let APASM := SeqViaCanonical APAS acceptMerge
  let APASMRP := SeqViaCanonical APASM rejectProject
  let APASMRPRS := SeqViaCanonical APASMRP rejectSim
  let runner := SeqViaCanonical APASMRPRS rejectMerge
  have hAcceptProjectReady : acceptProject.SubroutineReady :=
    hacceptProject.left
  have hAcceptSimReady : acceptSim.SubroutineReady :=
    hacceptSim.left
  have hAcceptMergeReady : acceptMerge.SubroutineReady :=
    hacceptMerge.left
  have hRejectProjectReady : rejectProject.SubroutineReady :=
    hrejectProject.left
  have hRejectSimReady : rejectSim.SubroutineReady :=
    hrejectSim.left
  have hRejectMergeReady : rejectMerge.SubroutineReady :=
    hrejectMerge.left
  have hAPASReady : APAS.SubroutineReady := by
    exact SeqViaCanonical_subroutineReady
      hAcceptProjectReady hAcceptSimReady
  have hAPASMReady : APASM.SubroutineReady := by
    exact SeqViaCanonical_subroutineReady
      hAPASReady hAcceptMergeReady
  have hAPASMRPReady : APASMRP.SubroutineReady := by
    exact SeqViaCanonical_subroutineReady
      hAPASMReady hRejectProjectReady
  have hAPASMRPRSReady : APASMRPRS.SubroutineReady := by
    exact SeqViaCanonical_subroutineReady
      hAPASMRPReady hRejectSimReady
  have hrunnerReady : runner.SubroutineReady := by
    exact SeqViaCanonical_subroutineReady
      hAPASMRPRSReady hRejectMergeReady
  have hforward :
      AcceptRejectConfigRunnerForwardSpec accept reject runner := by
    intro L
    have hAcceptProjectRun :
        acceptProject.HaltsFromTapeEquiv
          (ParsedLayoutCheckedTape L)
          (MachineDescription.SimulatorLayout.tape
            (AcceptSimulatorLayout L)) :=
      hacceptProject.right.left L
    have hAcceptSimRun :
        acceptSim.HaltsWithTape
          (MachineDescription.SimulatorLayout.asBoolInput
            (AcceptSimulatorLayout L))
          (MachineDescription.SimulatorLayout.tape
            (MachineDescription.SimulatorLayout.run
              accept L.stage (AcceptSimulatorLayout L))) := by
      simpa [FixedDescriptionBoundedSimulatorInput,
        FixedDescriptionBoundedSimulatorCanonicalOutputTape,
        AcceptSimulatorLayout] using
        hacceptSim.right.left (AcceptSimulatorLayout L)
    have hAPASRun :
        APAS.HaltsFromTapeEquiv
          (ParsedLayoutCheckedTape L)
          (MachineDescription.SimulatorLayout.tape
            (MachineDescription.SimulatorLayout.run
              accept L.stage (AcceptSimulatorLayout L))) := by
      exact
        SeqViaCanonical_haltsFromTapeEquiv_of_haltsWithTape
          hAcceptProjectReady hAcceptSimReady
          hAcceptProjectRun
          (by
            have heq := simulatorLayoutTape_move_left_move_right
                (AcceptSimulatorLayout L)
            rw [heq]
            exact Tape.Equiv.refl _)
          hAcceptSimRun
    have hAcceptMergeRun :
        acceptMerge.HaltsWithTape
          (MachineDescription.SimulatorLayout.asBoolInput
            (MachineDescription.SimulatorLayout.run
              accept L.stage (AcceptSimulatorLayout L)))
          (ParsedLayoutTape (ConfigRunnerAfterAccept accept L)) :=
      hacceptMerge.right.left L
    have hAPASMRun :
        APASM.HaltsFromTapeEquiv
          (ParsedLayoutCheckedTape L)
          (ParsedLayoutTape (ConfigRunnerAfterAccept accept L)) := by
      exact
        SeqViaCanonical_haltsFromTapeEquiv_of_haltsWithTape
          hAPASReady hAcceptMergeReady
          hAPASRun
          (by
            have heq := simulatorLayoutTape_move_left_move_right
                (MachineDescription.SimulatorLayout.run
                  accept L.stage (AcceptSimulatorLayout L))
            rw [heq]
            exact Tape.Equiv.refl _)
          hAcceptMergeRun
    have hRejectProjectRun :
        rejectProject.HaltsWithTape
          (ParsedLayoutBits (ConfigRunnerAfterAccept accept L))
          (MachineDescription.SimulatorLayout.tape
            (RejectSimulatorLayout
              (ConfigRunnerAfterAccept accept L))) :=
      hrejectProject.right.left (ConfigRunnerAfterAccept accept L)
    have hAPASMRPRun :
        APASMRP.HaltsFromTapeEquiv
          (ParsedLayoutCheckedTape L)
          (MachineDescription.SimulatorLayout.tape
            (RejectSimulatorLayout
              (ConfigRunnerAfterAccept accept L))) := by
      exact
        SeqViaCanonical_haltsFromTapeEquiv_of_haltsWithTape
          hAPASMReady hRejectProjectReady
          hAPASMRun
          (by
            have heq := parsedLayoutTape_move_left_move_right_configRunner
                (ConfigRunnerAfterAccept accept L)
            rw [heq]
            exact Tape.Equiv.refl _)
          hRejectProjectRun
    have hRejectSimRun :
        rejectSim.HaltsWithTape
          (MachineDescription.SimulatorLayout.asBoolInput
            (RejectSimulatorLayout
              (ConfigRunnerAfterAccept accept L)))
          (MachineDescription.SimulatorLayout.tape
            (MachineDescription.SimulatorLayout.run
              reject (ConfigRunnerAfterAccept accept L).stage
              (RejectSimulatorLayout
                (ConfigRunnerAfterAccept accept L)))) := by
      simpa [FixedDescriptionBoundedSimulatorInput,
        FixedDescriptionBoundedSimulatorCanonicalOutputTape] using
        hrejectSim.right.left
          (RejectSimulatorLayout (ConfigRunnerAfterAccept accept L))
    have hAPASMRPRSRun :
        APASMRPRS.HaltsFromTapeEquiv
          (ParsedLayoutCheckedTape L)
          (MachineDescription.SimulatorLayout.tape
            (MachineDescription.SimulatorLayout.run
              reject (ConfigRunnerAfterAccept accept L).stage
              (RejectSimulatorLayout
                (ConfigRunnerAfterAccept accept L)))) := by
      exact
        SeqViaCanonical_haltsFromTapeEquiv_of_haltsWithTape
          hAPASMRPReady hRejectSimReady
          hAPASMRPRun
          (by
            have heq := simulatorLayoutTape_move_left_move_right
                (RejectSimulatorLayout
                  (ConfigRunnerAfterAccept accept L))
            rw [heq]
            exact Tape.Equiv.refl _)
          hRejectSimRun
    have hRejectMergeRun :
        rejectMerge.HaltsWithTape
          (MachineDescription.SimulatorLayout.asBoolInput
            (MachineDescription.SimulatorLayout.run
              reject (ConfigRunnerAfterAccept accept L).stage
              (RejectSimulatorLayout
                (ConfigRunnerAfterAccept accept L))))
          (ParsedLayoutTape
            (ConfigRunnerAfterReject reject
              (ConfigRunnerAfterAccept accept L))) :=
      hrejectMerge.right.left (ConfigRunnerAfterAccept accept L)
    have hRunner :
        runner.HaltsFromTapeEquiv
          (ParsedLayoutCheckedTape L)
          (ParsedLayoutTape
            (ConfigRunnerAfterReject reject
              (ConfigRunnerAfterAccept accept L))) := by
      exact
        SeqViaCanonical_haltsFromTapeEquiv_of_haltsWithTape
          hAPASMRPRSReady hRejectMergeReady
          hAPASMRPRSRun
          (by
            have heq := simulatorLayoutTape_move_left_move_right
                (MachineDescription.SimulatorLayout.run
                  reject (ConfigRunnerAfterAccept accept L).stage
                  (RejectSimulatorLayout
                    (ConfigRunnerAfterAccept accept L)))
            rw [heq]
            exact Tape.Equiv.refl _)
          hRejectMergeRun
    have hOutput :
        ParsedLayoutTape
            (ConfigRunnerAfterReject reject
              (ConfigRunnerAfterAccept accept L)) =
          ConfigRunnerOutputTape accept reject L := by
      rw [ConfigRunnerAfterReject_afterAccept]
      rfl
    rw [hOutput] at hRunner
    exact hRunner
  have hrunnerReady' :
      (ConfigRunnerPhaseRunner
        acceptProject acceptSim acceptMerge
        rejectProject rejectSim rejectMerge).SubroutineReady := by
    simpa [ConfigRunnerPhaseRunner, runner, APAS, APASM,
      APASMRP, APASMRPRS] using hrunnerReady
  have hforward' :
      AcceptRejectConfigRunnerForwardSpec accept reject
        (ConfigRunnerPhaseRunner
          acceptProject acceptSim acceptMerge
          rejectProject rejectSim rejectMerge) := by
    simpa [ConfigRunnerPhaseRunner, runner, APAS, APASM,
      APASMRP, APASMRPRS] using hforward
  constructor
  · exact hrunnerReady'
  constructor
  · exact hforward'
  · intro L T hhalt
    rcases hforward' L with ⟨Tactual, hactual, hequiv⟩
    have hT_eq_Tactual : T = Tactual :=
      MachineDescription.haltsFromTape_functional_of_haltTransitionFree
        hrunnerReady'.right hhalt hactual
    rw [hT_eq_Tactual]
    exact hequiv

theorem acceptRejectConfigRunnerConstruction_of_phaseConstruction
    (h : ConfigRunnerPhaseConstruction) :
    AcceptRejectConfigRunnerConstruction := by
  intro accept reject
  rcases h accept reject with
    ⟨acceptProject, acceptSim, acceptMerge,
      rejectProject, rejectSim, rejectMerge,
      hacceptProject, hacceptSim, hacceptMerge,
      hrejectProject, hrejectSim, hrejectMerge⟩
  exact
    ⟨ConfigRunnerPhaseRunner
        acceptProject acceptSim acceptMerge
        rejectProject rejectSim rejectMerge,
      configRunnerPhaseRunner_spec
        hacceptProject hacceptSim hacceptMerge
        hrejectProject hrejectSim hrejectMerge⟩

def SelectedProjectionPrimitiveRightShiftedConstruction : Prop :=
  forall useAccept : Bool,
    exists runner : MachineDescription,
      RightShiftedOutputCompiledSubroutineByDescription
        (SelectedProjectionPrimitive useAccept)
        runner

def AcceptProjectionPrimitiveRightShiftedConstruction : Prop :=
  exists runner : MachineDescription,
    RightShiftedOutputCompiledSubroutineByDescription
      AcceptProjectionPrimitive
      runner

def RejectProjectionPrimitiveRightShiftedConstruction : Prop :=
  exists runner : MachineDescription,
    RightShiftedOutputCompiledSubroutineByDescription
      RejectProjectionPrimitive
      runner

def SelectedMergePrimitiveRightShiftedConstruction : Prop :=
  forall useAccept : Bool,
    exists runner : MachineDescription,
      RightShiftedOutputCompiledSubroutineByDescription
        (SelectedMergePrimitive useAccept)
        runner

def AcceptMergePrimitiveRightShiftedConstruction : Prop :=
  exists runner : MachineDescription,
    RightShiftedOutputCompiledSubroutineByDescription
      AcceptMergePrimitive
      runner

def RejectMergePrimitiveRightShiftedConstruction : Prop :=
  exists runner : MachineDescription,
    RightShiftedOutputCompiledSubroutineByDescription
      RejectMergePrimitive
      runner

theorem selectedProjectionFiniteDescriptionConstruction_of_rightShifted
    (h : SelectedProjectionPrimitiveRightShiftedConstruction) :
    SelectedProjectionFiniteDescriptionConstruction := by
  intro useAccept
  rcases h useAccept with ⟨runner, hrunner⟩
  refine ⟨runner, ?_⟩
  constructor
  · exact ⟨hrunner.left, hrunner.right.left⟩
  constructor
  · intro L
    have htransform :
        (SelectedProjectionPrimitive useAccept).transform
            (MachineDescription.DovetailLayout.encode L) =
          some (SelectedProjectionOutputCode useAccept L) :=
      (SelectedProjectionPrimitive_transform_eq_some_iff
        useAccept
        (MachineDescription.DovetailLayout.encode L)
        (SelectedProjectionOutputCode useAccept L)).mpr
        ⟨L, rfl, by simp [SelectedProjectionOutputCode]⟩
    have hexact := rightShiftedOutputCompiled_haltsWithTape_of_transform hrunner htransform
    have hequiv := MachineDescription.HaltsFromTape.toEquiv hexact
    simpa [ParsedLayoutBits, SelectedProjectionOutputTape] using hequiv
  · intro code T hhalt
    rcases hrunner.right.right.right code T hhalt with
      ⟨out, htransform, hT⟩
    rcases
        (SelectedProjectionPrimitive_transform_eq_some_iff
          useAccept code out).mp htransform with
      ⟨L, hcode, hout⟩
    refine ⟨L, hcode, ?_⟩
    rw [hT]
    simpa [SelectedProjectionOutputTape, SelectedProjectionOutputCode,
      hout] using Tape.Equiv.refl _

theorem selectedMergeFiniteDescriptionConstruction_of_rightShifted
    (h : SelectedMergePrimitiveRightShiftedConstruction) :
    SelectedMergeFiniteDescriptionConstruction := by
  intro useAccept
  rcases h useAccept with ⟨runner, hrunner⟩
  refine ⟨runner, ?_⟩
  constructor
  · exact ⟨hrunner.left, hrunner.right.left⟩
  constructor
  · intro S L hinput
    have htransform :
        (SelectedMergePrimitive useAccept).transform
            (MachineDescription.SimulatorLayout.encode S) =
          some (SelectedMergeOutputCode useAccept S L) :=
      (SelectedMergePrimitive_transform_eq_some_iff
        useAccept
        (MachineDescription.SimulatorLayout.encode S)
        (SelectedMergeOutputCode useAccept S L)).mpr
        ⟨S, L, rfl, hinput, rfl⟩
    simpa [MachineDescription.SimulatorLayout.asBoolInput,
      SelectedMergeOutputTape] using
      rightShiftedOutputCompiled_haltsWithTape_of_transform
        hrunner htransform
  · intro code T hhalt
    rcases hrunner.right.right.right code T hhalt with
      ⟨out, htransform, hT⟩
    rcases
        (SelectedMergePrimitive_transform_eq_some_iff
          useAccept code out).mp htransform with
      ⟨S, L, hcode, hinput, hout⟩
    refine ⟨S, L, hcode, hinput, ?_⟩
    simpa [SelectedMergeOutputTape, hout] using hT

def SelectedProjectionPrimitiveExactSpec
    (useAccept : Bool)
    (runner : MachineDescription) : Prop :=
  ReadySpec runner ∧
    (forall L : MachineDescription.DovetailLayout,
      runner.HaltsWithTape
        (ParsedLayoutBits L)
        (SelectedProjectionOutputTape useAccept L)) ∧
      forall code : Word MachineCodeSymbol,
      forall T : Tape Bool,
        runner.HaltsWithTape
            (MachineDescription.encodeCodeWordAsInput code) T ->
          exists L : MachineDescription.DovetailLayout,
            code = MachineDescription.DovetailLayout.encode L ∧
              T = SelectedProjectionOutputTape useAccept L

def SelectedProjectionPrimitiveExactConstruction : Prop :=
  forall useAccept : Bool,
    exists runner : MachineDescription,
      SelectedProjectionPrimitiveExactSpec useAccept runner

def SelectedProjectionEmitterSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  ReadySpec emitter ∧
    (forall L : MachineDescription.DovetailLayout,
      emitter.HaltsWithTape
        (ParsedLayoutBits L)
        (SelectedProjectionOutputTape useAccept L)) ∧
      forall L : MachineDescription.DovetailLayout,
      forall T : Tape Bool,
        emitter.HaltsWithTape (ParsedLayoutBits L) T ->
          T = SelectedProjectionOutputTape useAccept L

def SelectedProjectionCanonicalEmitterSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  CanonicalLayouts.EmitterSpec
    ParsedLayoutBits
    (SelectedProjectionOutputCode useAccept)
    emitter

theorem selectedProjectionEmitterSpec_iff_canonical
    (useAccept : Bool) (emitter : MachineDescription) :
    SelectedProjectionEmitterSpec useAccept emitter ↔
      SelectedProjectionCanonicalEmitterSpec useAccept emitter := by
  rfl

def SelectedProjectionEmitterConstruction : Prop :=
  forall useAccept : Bool,
    exists emitter : MachineDescription,
      SelectedProjectionEmitterSpec useAccept emitter

def SelectedProjectionCheckedEmitterSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  ReadySpec emitter ∧
    forall L : MachineDescription.DovetailLayout,
      emitter.HaltsFromTape
        (ParsedLayoutCheckedTape L)
        (SelectedProjectionOutputTape useAccept L)

def SelectedProjectionCheckedEmitterConstruction : Prop :=
  forall useAccept : Bool,
    exists emitter : MachineDescription,
      SelectedProjectionCheckedEmitterSpec useAccept emitter

theorem selectedProjectionOutputCode_true
    (L : MachineDescription.DovetailLayout) :
    SelectedProjectionOutputCode true L =
      MachineDescription.SimulatorLayout.encode
        (AcceptSimulatorLayout L) := by
  rfl

theorem selectedProjectionOutputCode_false
    (L : MachineDescription.DovetailLayout) :
    SelectedProjectionOutputCode false L =
      MachineDescription.SimulatorLayout.encode
        (RejectSimulatorLayout L) := by
  rfl

theorem selectedProjectionOutputTape_true
    (L : MachineDescription.DovetailLayout) :
    SelectedProjectionOutputTape true L =
      Tape.move Direction.right
        (MachineDescription.SimulatorLayout.tape
          (AcceptSimulatorLayout L)) := by
  rfl

theorem selectedProjectionOutputTape_false
    (L : MachineDescription.DovetailLayout) :
    SelectedProjectionOutputTape false L =
      Tape.move Direction.right
        (MachineDescription.SimulatorLayout.tape
          (RejectSimulatorLayout L)) := by
  rfl

def AcceptProjectionCheckedEmitterConstruction : Prop :=
  exists emitter : MachineDescription,
    SelectedProjectionCheckedEmitterSpec true emitter

def RejectProjectionCheckedEmitterConstruction : Prop :=
  exists emitter : MachineDescription,
    SelectedProjectionCheckedEmitterSpec false emitter

def SelectedProjectionCheckedEmitterSideConstruction : Prop :=
  AcceptProjectionCheckedEmitterConstruction ∧
    RejectProjectionCheckedEmitterConstruction

theorem selectedProjectionCheckedEmitterConstruction_of_sides
    (h : SelectedProjectionCheckedEmitterSideConstruction) :
    SelectedProjectionCheckedEmitterConstruction := by
  intro useAccept
  cases useAccept
  · exact h.right
  · exact h.left

theorem selectedProjectionPrimitiveRightShiftedConstruction_of_exact
    (h : SelectedProjectionPrimitiveExactConstruction) :
    SelectedProjectionPrimitiveRightShiftedConstruction := by
  intro useAccept
  rcases h useAccept with ⟨runner, hrunner⟩
  refine ⟨runner, ?_⟩
  constructor
  · exact hrunner.left.left
  constructor
  · exact hrunner.left.right
  constructor
  · intro code out
    constructor
    · intro hhalt
      rcases hhalt with ⟨n, hn⟩
      let T : Tape Bool :=
        (runner.runConfig n
          (runner.initial
            (MachineDescription.encodeCodeWordAsInput code))).tape
      have hTape :
          runner.HaltsWithTape
              (MachineDescription.encodeCodeWordAsInput code) T := by
        exact ⟨n, ⟨hn.left, rfl⟩⟩
      rcases hrunner.right.right code T hTape with
        ⟨L, hcode, hT⟩
      have hactual :
          Tape.normalizedOutput T =
            MachineDescription.encodeCodeWordAsInput out := by
        simpa [T] using hn.right
      have hexpected :
          Tape.normalizedOutput T =
            MachineDescription.encodeCodeWordAsInput
              (SelectedProjectionOutputCode useAccept L) := by
        rw [hT]
        exact
          EncodedRewriters.tape_normalizedOutput_move_right_input
            (MachineDescription.encodeCodeWordAsInput
              (SelectedProjectionOutputCode useAccept L))
      have houtBits :
          MachineDescription.encodeCodeWordAsInput out =
            MachineDescription.encodeCodeWordAsInput
              (SelectedProjectionOutputCode useAccept L) :=
        hactual.symm.trans hexpected
      have hout : out = SelectedProjectionOutputCode useAccept L :=
        MachineDescription.encodeCodeWordAsInput_injective houtBits
      exact
        (SelectedProjectionPrimitive_transform_eq_some_iff
          useAccept code out).mpr
          ⟨L, hcode, by simpa [SelectedProjectionOutputCode] using hout⟩
    · intro htransform
      rcases
          (SelectedProjectionPrimitive_transform_eq_some_iff
            useAccept code out).mp htransform with
        ⟨L, hcode, hout⟩
      subst code
      subst out
      simpa [ParsedLayoutBits, SelectedProjectionOutputTape,
        SelectedProjectionOutputCode,
        EncodedRewriters.tape_normalizedOutput_move_right_input] using
        MachineDescription.haltsWithOutput_of_haltsWithTape
          (hrunner.right.left L)
  · intro code T hhalt
    rcases hrunner.right.right code T hhalt with
      ⟨L, hcode, hT⟩
    refine ⟨SelectedProjectionOutputCode useAccept L, ?_, ?_⟩
    · exact
        (SelectedProjectionPrimitive_transform_eq_some_iff
          useAccept code (SelectedProjectionOutputCode useAccept L)).mpr
          ⟨L, hcode, by simp [SelectedProjectionOutputCode]⟩
    · simpa [SelectedProjectionOutputTape] using hT

theorem selectedProjectionPrimitiveExactSpec_of_checkedParser_checkedEmitter
    {useAccept : Bool} {parser emitter : MachineDescription}
    (hparser : LayoutCheckedParserSpec parser)
    (hemitter : SelectedProjectionCheckedEmitterSpec useAccept emitter) :
    SelectedProjectionPrimitiveExactSpec useAccept
      (SeqViaCanonical parser emitter) := by
  have hrunnerReady :
      (SeqViaCanonical parser emitter).SubroutineReady :=
    SeqViaCanonical_subroutineReady hparser.left hemitter.left
  constructor
  · exact hrunnerReady
  constructor
  · intro L
    have hparserFrom :
        parser.HaltsFromTape
          (Tape.input (ParsedLayoutBits L))
          (ParsedLayoutCheckedTape L) := by
      simpa [MachineDescription.HaltsWithTape,
        MachineDescription.HaltsWithTapeIn,
        MachineDescription.HaltsFromTape,
        MachineDescription.HaltsFromTapeIn,
        MachineDescription.initial] using hparser.right.left L
    have hseq :
        (SeqViaCanonical parser emitter).HaltsFromTape
          (Tape.input (ParsedLayoutBits L))
          (SelectedProjectionOutputTape useAccept L) :=
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        hparser.left hemitter.left
        hparserFrom
        (parsedLayoutCheckedTape_move_left_move_right L)
        (hemitter.right L)
    simpa [MachineDescription.HaltsWithTape,
      MachineDescription.HaltsWithTapeIn,
      MachineDescription.HaltsFromTape,
      MachineDescription.HaltsFromTapeIn,
      MachineDescription.initial] using hseq
  · intro code T hhalt
    have hhaltFrom :
        (SeqViaCanonical parser emitter).HaltsFromTape
          (Tape.input (MachineDescription.encodeCodeWordAsInput code)) T := by
      simpa [MachineDescription.HaltsWithTape,
        MachineDescription.HaltsWithTapeIn,
        MachineDescription.HaltsFromTape,
        MachineDescription.HaltsFromTapeIn,
        MachineDescription.initial] using hhalt
    rcases
        SeqViaCanonical_haltsFromTape_inv
          hparser.left hemitter.left hhaltFrom with
      ⟨Tmid, hparserRun, hemitterRun⟩
    have hparserWith :
        parser.HaltsWithTape
          (MachineDescription.encodeCodeWordAsInput code) Tmid := by
      simpa [MachineDescription.HaltsWithTape,
        MachineDescription.HaltsWithTapeIn,
        MachineDescription.HaltsFromTape,
        MachineDescription.HaltsFromTapeIn,
        MachineDescription.initial] using hparserRun
    rcases hparser.right.right code Tmid hparserWith with
      ⟨L, hdecode, hTmid⟩
    have hemitterRun' :
        emitter.HaltsFromTape
          (ParsedLayoutCheckedTape L) T := by
      rw [hTmid] at hemitterRun
      simpa [parsedLayoutCheckedTape_move_left_move_right L]
        using hemitterRun
    have hT :
        T = SelectedProjectionOutputTape useAccept L :=
      MachineDescription.haltsFromTape_functional_of_haltTransitionFree
        hemitter.left.right hemitterRun' (hemitter.right L)
    refine ⟨L, ?_, hT⟩
    exact MachineDescription.DovetailLayout.decodeComplete_eq_some_encode hdecode

theorem selectedProjectionPrimitiveExactConstruction_of_checkedParser_checkedEmitter
    (hparser : LayoutCheckedParserConstruction)
    (hemitter : SelectedProjectionCheckedEmitterConstruction) :
    SelectedProjectionPrimitiveExactConstruction := by
  intro useAccept
  rcases hparser with ⟨parser, hparser⟩
  rcases hemitter useAccept with ⟨emitter, hemits⟩
  exact
    ⟨SeqViaCanonical parser emitter,
      selectedProjectionPrimitiveExactSpec_of_checkedParser_checkedEmitter
        hparser hemits⟩

theorem selectedProjectionCheckedEmitterSideConstruction_scaffold :
    SelectedProjectionCheckedEmitterSideConstruction := by
  sorry

theorem selectedProjectionCheckedEmitterConstruction_scaffold :
    SelectedProjectionCheckedEmitterConstruction := by
  exact
    selectedProjectionCheckedEmitterConstruction_of_sides
      selectedProjectionCheckedEmitterSideConstruction_scaffold

theorem selectedProjectionPrimitiveExactConstruction_scaffold :
    SelectedProjectionPrimitiveExactConstruction := by
  exact
    selectedProjectionPrimitiveExactConstruction_of_checkedParser_checkedEmitter
      layoutCheckedParserConstruction_scaffold
      selectedProjectionCheckedEmitterConstruction_scaffold

theorem selectedProjectionPrimitiveRightShiftedConstruction_core :
    SelectedProjectionPrimitiveRightShiftedConstruction := by
  exact
    selectedProjectionPrimitiveRightShiftedConstruction_of_exact
      selectedProjectionPrimitiveExactConstruction_scaffold

theorem acceptProjectionPrimitiveRightShiftedConstruction_scaffold :
    AcceptProjectionPrimitiveRightShiftedConstruction := by
  rcases selectedProjectionPrimitiveRightShiftedConstruction_core true with
    ⟨runner, hrunner⟩
  refine ⟨runner, ?_⟩
  exact
    rightShiftedOutputCompiledSubroutineByDescription_congr
      (P := SelectedProjectionPrimitive true)
      (Q := AcceptProjectionPrimitive)
      (D := runner)
      (by
        intro code
        rfl)
      hrunner

theorem rejectProjectionPrimitiveRightShiftedConstruction_scaffold :
    RejectProjectionPrimitiveRightShiftedConstruction := by
  rcases selectedProjectionPrimitiveRightShiftedConstruction_core false with
    ⟨runner, hrunner⟩
  refine ⟨runner, ?_⟩
  exact
    rightShiftedOutputCompiledSubroutineByDescription_congr
      (P := SelectedProjectionPrimitive false)
      (Q := RejectProjectionPrimitive)
      (D := runner)
      (by
        intro code
        rfl)
      hrunner

theorem selectedProjectionPrimitiveRightShiftedConstruction_scaffold :
    SelectedProjectionPrimitiveRightShiftedConstruction := by
  exact selectedProjectionPrimitiveRightShiftedConstruction_core

theorem selectedProjectionFiniteDescriptionConstruction_scaffold :
    SelectedProjectionFiniteDescriptionConstruction :=
    selectedProjectionFiniteDescriptionConstruction_of_rightShifted
    selectedProjectionPrimitiveRightShiftedConstruction_scaffold

theorem selectedMergePrimitiveRightShiftedConstruction_core :
    SelectedMergePrimitiveRightShiftedConstruction := by
  sorry

theorem acceptMergePrimitiveRightShiftedConstruction_scaffold :
    AcceptMergePrimitiveRightShiftedConstruction := by
  rcases selectedMergePrimitiveRightShiftedConstruction_core true with
    ⟨runner, hrunner⟩
  refine ⟨runner, ?_⟩
  exact
    rightShiftedOutputCompiledSubroutineByDescription_congr
      (P := SelectedMergePrimitive true)
      (Q := AcceptMergePrimitive)
      (D := runner)
      (by
        intro code
        rfl)
      hrunner

theorem rejectMergePrimitiveRightShiftedConstruction_scaffold :
    RejectMergePrimitiveRightShiftedConstruction := by
  rcases selectedMergePrimitiveRightShiftedConstruction_core false with
    ⟨runner, hrunner⟩
  refine ⟨runner, ?_⟩
  exact
    rightShiftedOutputCompiledSubroutineByDescription_congr
      (P := SelectedMergePrimitive false)
      (Q := RejectMergePrimitive)
      (D := runner)
      (by
        intro code
        rfl)
      hrunner

theorem selectedMergePrimitiveRightShiftedConstruction_scaffold :
    SelectedMergePrimitiveRightShiftedConstruction := by
  exact selectedMergePrimitiveRightShiftedConstruction_core

theorem selectedMergeFiniteDescriptionConstruction_scaffold :
    SelectedMergeFiniteDescriptionConstruction :=
  selectedMergeFiniteDescriptionConstruction_of_rightShifted
    selectedMergePrimitiveRightShiftedConstruction_scaffold

theorem selectedProjectionSpec_of_parser_emitter
    {useAccept : Bool} {parser emitter : MachineDescription}
    (hparser : LayoutCheckedParserSpec parser)
    (hemitter : SelectedProjectionEmitterSpec useAccept emitter) :
    SelectedProjectionSpec useAccept
      (SeqViaCanonical parser emitter) := by
  have hrunnerReady :
      (SeqViaCanonical parser emitter).SubroutineReady :=
    SeqViaCanonical_subroutineReady hparser.left hemitter.left
  constructor
  · exact hrunnerReady
  constructor
  · intro L
    have hbridge :
        Tape.Equiv
          (Tape.move Direction.left
            (Tape.move Direction.right (ParsedLayoutCheckedTape L)))
          (Tape.input (ParsedLayoutBits L)) := by
      rw [parsedLayoutCheckedTape_move_left_move_right L]
      exact checkedInputTape_equiv_input _
    exact
      SeqViaCanonical_haltsFromTapeEquiv_of_haltsWithTape
        hparser.left hemitter.left
        (MachineDescription.HaltsFromTape.toEquiv (hparser.right.left L))
        hbridge
        (hemitter.right.left L)
  · intro code T hhalt
    rcases
        SeqViaCanonical_haltsFromTape_inv hparser.left hemitter.left hhalt with
      ⟨Tmid, hparser_run, hemitter_run⟩
    rcases hparser.right.right code Tmid hparser_run with
      ⟨L, hcode, hTmid_equiv⟩
    refine ⟨L, MachineDescription.DovetailLayout.decodeComplete_eq_some_encode hcode, ?_⟩
    have hemitter_exact := hemitter.right.left L
    have h_in_equiv :
        Tape.Equiv (Tape.input (ParsedLayoutBits L))
          (Tape.move Direction.left (Tape.move Direction.right Tmid)) := by
      rw [hTmid_equiv]
      rw [parsedLayoutCheckedTape_move_left_move_right L]
      exact Tape.Equiv.symm (checkedInputTape_equiv_input _)
    have h_emitter_equiv_out :=
      MachineDescription.HaltsFromTapeEquiv_of_input_equiv h_in_equiv hemitter_exact
    rcases h_emitter_equiv_out with ⟨Tactual_equiv, h_actual_equiv, h_equiv_out⟩
    have h_eq :=
      MachineDescription.haltsFromTape_functional_of_haltTransitionFree
        hemitter.left.right hemitter_run h_actual_equiv
    subst h_eq
    exact h_equiv_out

theorem selectedProjectionFiniteDescriptionConstruction_of_emitter
    (hemitter : SelectedProjectionEmitterConstruction) :
    SelectedProjectionFiniteDescriptionConstruction := by
  intro useAccept
  rcases layoutCheckedParserConstruction_scaffold with ⟨parser, hparser⟩
  rcases hemitter useAccept with ⟨emitter, hemits⟩
  exact
    ⟨SeqViaCanonical parser emitter,
      selectedProjectionSpec_of_parser_emitter hparser hemits⟩

def SelectedMergeParserSpec
    (parser : MachineDescription) : Prop :=
  ReadySpec parser ∧
    (forall S : MachineDescription.SimulatorLayout,
     forall L : MachineDescription.DovetailLayout,
      MachineDescription.decodeCodeWordAsInput S.input =
        some (MachineDescription.DovetailLayout.encode L) ->
      parser.HaltsWithTape
        (MachineDescription.SimulatorLayout.asBoolInput S)
        (MachineDescription.SimulatorLayout.tape S)) ∧
      forall code : Word MachineCodeSymbol,
      forall T : Tape Bool,
        parser.HaltsWithTape
            (MachineDescription.encodeCodeWordAsInput code) T ->
          exists S : MachineDescription.SimulatorLayout,
          exists L : MachineDescription.DovetailLayout,
            code = MachineDescription.SimulatorLayout.encode S ∧
              MachineDescription.decodeCodeWordAsInput S.input =
                some (MachineDescription.DovetailLayout.encode L) ∧
              T = MachineDescription.SimulatorLayout.tape S

def SelectedMergeParserConstruction : Prop :=
  exists parser : MachineDescription,
    SelectedMergeParserSpec parser

def SelectedMergeEmitterSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  ReadySpec emitter ∧
    (forall S : MachineDescription.SimulatorLayout,
     forall L : MachineDescription.DovetailLayout,
      MachineDescription.decodeCodeWordAsInput S.input =
        some (MachineDescription.DovetailLayout.encode L) ->
      emitter.HaltsWithTape
        (MachineDescription.SimulatorLayout.asBoolInput S)
        (SelectedMergeOutputTape useAccept S L)) ∧
      forall S : MachineDescription.SimulatorLayout,
      forall L : MachineDescription.DovetailLayout,
      forall T : Tape Bool,
        MachineDescription.decodeCodeWordAsInput S.input =
          some (MachineDescription.DovetailLayout.encode L) ->
        emitter.HaltsWithTape
            (MachineDescription.SimulatorLayout.asBoolInput S) T ->
          T = SelectedMergeOutputTape useAccept S L

structure SelectedMergeEmitterPayload where
  S : MachineDescription.SimulatorLayout
  L : MachineDescription.DovetailLayout
  input :
    MachineDescription.decodeCodeWordAsInput S.input =
      some (MachineDescription.DovetailLayout.encode L)

def SelectedMergeEmitterInputBits
    (p : SelectedMergeEmitterPayload) : Word Bool :=
  MachineDescription.SimulatorLayout.asBoolInput p.S

def SelectedMergeEmitterOutputCode
    (useAccept : Bool)
    (p : SelectedMergeEmitterPayload) : Word MachineCodeSymbol :=
  SelectedMergeOutputCode useAccept p.S p.L

def SelectedMergeCanonicalEmitterSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  CanonicalLayouts.EmitterSpec
    SelectedMergeEmitterInputBits
    (SelectedMergeEmitterOutputCode useAccept)
    emitter

theorem selectedMergeEmitterSpec_iff_canonical
    (useAccept : Bool) (emitter : MachineDescription) :
    SelectedMergeEmitterSpec useAccept emitter ↔
      SelectedMergeCanonicalEmitterSpec useAccept emitter := by
  constructor
  · intro h
    constructor
    · exact h.left
    constructor
    · intro p
      simpa [SelectedMergeCanonicalEmitterSpec,
        SelectedMergeEmitterInputBits, SelectedMergeEmitterOutputCode,
        CanonicalLayouts.OutputTape, SelectedMergeOutputTape] using
        h.right.left p.S p.L p.input
    · intro p T hhalt
      simpa [SelectedMergeCanonicalEmitterSpec,
        SelectedMergeEmitterInputBits, SelectedMergeEmitterOutputCode,
        CanonicalLayouts.OutputTape, SelectedMergeOutputTape] using
        h.right.right p.S p.L T p.input hhalt
  · intro h
    constructor
    · exact h.left
    constructor
    · intro S L hinput
      exact
        h.right.left
          { S := S, L := L, input := hinput }
    · intro S L T hinput hhalt
      exact
        h.right.right
          { S := S, L := L, input := hinput } T hhalt

def SelectedMergeEmitterConstruction : Prop :=
  forall useAccept : Bool,
    exists emitter : MachineDescription,
      SelectedMergeEmitterSpec useAccept emitter

theorem selectedMergeSpec_of_parser_emitter
    {useAccept : Bool} {parser emitter : MachineDescription}
    (hparser : SelectedMergeParserSpec parser)
    (hemitter : SelectedMergeEmitterSpec useAccept emitter) :
    SelectedMergeSpec useAccept
      (SeqViaCanonical parser emitter) := by
  have hrunnerReady :
      (SeqViaCanonical parser emitter).SubroutineReady :=
    SeqViaCanonical_subroutineReady hparser.left hemitter.left
  constructor
  · exact hrunnerReady
  constructor
  · intro S L hinput
    exact
      SeqViaCanonical_haltsWithTape_of_haltsWithTape
        hparser.left hemitter.left
        (hparser.right.left S L hinput)
        (simulatorLayoutTape_move_left_move_right S)
        (hemitter.right.left S L hinput)
  · intro code T hhalt
    let identity := MachineDescription.ExactIdentityDescription
    have hid : identity.SubroutineReady :=
      ⟨MachineDescription.exactIdentityDescription_wellFormed,
        MachineDescription.exactIdentityDescription_haltTransitionFree⟩
    rcases
        MachineDescription.seqSubroutine_haltsWithTape_inv
          (A := MachineDescription.seqSubroutine
            parser identity Direction.right)
          (B := emitter)
          (handoffMove := Direction.left)
          (MachineDescription.seqSubroutine_subroutineReady
            hparser.left hid)
          hemitter.left
          (by simpa [SeqViaCanonical, identity] using hhalt) with
      ⟨Tmid, hparserIdHalt, _hemitterReach⟩
    rcases
        MachineDescription.seqSubroutine_haltsWithTape_inv
          (A := parser) (B := identity)
          (handoffMove := Direction.right)
          hparser.left hid
          (by simpa [identity] using hparserIdHalt) with
      ⟨Tparser, hparserHalt, _hidentityReach⟩
    rcases hparser.right.right code Tparser hparserHalt with
      ⟨S, L, hcode, hinput, _hTparser⟩
    refine ⟨S, L, hcode, hinput, ?_⟩
    have hhalt' :
        (SeqViaCanonical parser emitter).HaltsWithTape
          (MachineDescription.SimulatorLayout.asBoolInput S) T := by
      simpa [MachineDescription.SimulatorLayout.asBoolInput, hcode] using
        hhalt
    have hforward :
        (SeqViaCanonical parser emitter).HaltsWithTape
          (MachineDescription.SimulatorLayout.asBoolInput S)
          (SelectedMergeOutputTape useAccept S L) :=
      SeqViaCanonical_haltsWithTape_of_haltsWithTape
        hparser.left hemitter.left
        (hparser.right.left S L hinput)
        (simulatorLayoutTape_move_left_move_right S)
        (hemitter.right.left S L hinput)
    exact
      MachineDescription.haltsWithTape_functional_of_haltTransitionFree
        hrunnerReady.right hhalt' hforward

theorem selectedMergeFiniteDescriptionConstruction_of_parser_emitter
    (hparser : SelectedMergeParserConstruction)
    (hemitter : SelectedMergeEmitterConstruction) :
    SelectedMergeFiniteDescriptionConstruction := by
  intro useAccept
  rcases hparser with ⟨parser, hparser⟩
  rcases hemitter useAccept with ⟨emitter, hemits⟩
  exact
    ⟨SeqViaCanonical parser emitter,
      selectedMergeSpec_of_parser_emitter hparser hemits⟩

def FixedDescriptionBoundedSimulatorStepPhaseConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists simulateStep : MachineDescription.Fragment,
      FixedDescriptionBoundedSimulatorPhaseRealizes
        (FixedDescriptionBoundedSimulatorHandoffTape Direction.right)
        FixedDescriptionBoundedSimulatorLayoutTape
        (fun L => MachineDescription.SimulatorLayout.run D L.stage L)
        simulateStep

theorem fixedDescriptionBoundedSimulatorReturnFromRightPhaseRealizes_configRunner :
    FixedDescriptionBoundedSimulatorPhaseRealizes
      (FixedDescriptionBoundedSimulatorHandoffTape Direction.right)
      FixedDescriptionBoundedSimulatorLayoutTape
      id
      (MachineDescription.Fragment.handoff Direction.left) := by
  constructor
  · exact MachineDescription.Fragment.handoff_wellFormed Direction.left
  · intro L
    rcases
        MachineDescription.Fragment.handoff_firstReaches Direction.left
          (FixedDescriptionBoundedSimulatorHandoffTape Direction.right L) with
      ⟨n, hn, hminimal⟩
    refine ⟨n, ?_, hminimal⟩
    simpa [FixedDescriptionBoundedSimulatorHandoffTape,
      FixedDescriptionBoundedSimulatorLayoutTape] using hn

theorem fixedDescriptionBoundedSimulatorRightShiftedRunCodePhaseRealizes_configRunner
    {D runner : MachineDescription}
    (hrunner :
      RightShiftedOutputCompiledSubroutineByDescription
        (FixedDescriptionBoundedSimulatorCode D) runner) :
    FixedDescriptionBoundedSimulatorPhaseRealizes
      FixedDescriptionBoundedSimulatorLayoutTape
      (FixedDescriptionBoundedSimulatorHandoffTape Direction.right)
      (fun L => MachineDescription.SimulatorLayout.run D L.stage L)
      runner.asFragment := by
  constructor
  · exact
      MachineDescription.asFragment_wellFormed
        ⟨hrunner.left, hrunner.right.left⟩
  · intro L
    have hhalt :
        runner.HaltsWithTape
          (FixedDescriptionBoundedSimulatorInput L)
          (FixedDescriptionBoundedSimulatorHandoffTape Direction.right
            (MachineDescription.SimulatorLayout.run D L.stage L)) := by
      have htransform :
          (FixedDescriptionBoundedSimulatorCode D).transform
              (MachineDescription.SimulatorLayout.encode L) =
            some
              (MachineDescription.SimulatorLayout.encode
                (MachineDescription.SimulatorLayout.run D L.stage L)) :=
        fixedDescriptionBoundedSimulatorCode_encode D L
      simpa [FixedDescriptionBoundedSimulatorInput,
        FixedDescriptionBoundedSimulatorHandoffTape,
        FixedDescriptionBoundedSimulatorLayoutTape,
        MachineDescription.SimulatorLayout.tape,
        MachineDescription.SimulatorLayout.asBoolInput] using
        rightShiftedOutputCompiled_haltsWithTape_of_transform
          hrunner htransform
    rcases MachineDescription.runConfig_eq_halt_of_haltsWithTape hhalt with
      ⟨n, hn⟩
    rcases
        MachineDescription.firstReaches_halt_of_runConfig_eq
          hrunner.right.left hn with
      ⟨m, _hmle, hm, hminimal⟩
    refine ⟨m, ?_, ?_⟩
    · simpa [MachineDescription.asFragment_toDescription,
        MachineDescription.asFragment] using hm
    · intro k hk
      simpa [MachineDescription.asFragment_toDescription,
        MachineDescription.asFragment] using hminimal k hk

theorem fixedDescriptionBoundedSimulatorStepPhaseConstruction_of_rightShifted_configRunner
    (hcode :
      FoC.Computability.FixedDescriptionBoundedSimulatorCodeRightShiftedConstruction) :
    FixedDescriptionBoundedSimulatorStepPhaseConstruction_configRunner := by
  intro D
  rcases hcode D with ⟨runner, hrunner⟩
  let leftReturn : MachineDescription.Fragment :=
    MachineDescription.Fragment.handoff Direction.left
  let rightPause : MachineDescription.Fragment :=
    MachineDescription.Fragment.halt
  let runCode : MachineDescription.Fragment :=
    runner.asFragment
  let finalPause : MachineDescription.Fragment :=
    MachineDescription.Fragment.halt
  let enterRun : MachineDescription.Fragment :=
    MachineDescription.Fragment.seq leftReturn rightPause Direction.right
  let runAndReturn : MachineDescription.Fragment :=
    MachineDescription.Fragment.seq runCode finalPause Direction.left
  let simulateStep : MachineDescription.Fragment :=
    MachineDescription.Fragment.seq enterRun runAndReturn Direction.left
  refine ⟨simulateStep, ?_⟩
  have hEnterRun :
      FixedDescriptionBoundedSimulatorPhaseRealizes
        (FixedDescriptionBoundedSimulatorHandoffTape Direction.right)
        (FixedDescriptionBoundedSimulatorHandoffTape Direction.right)
        id enterRun := by
    have hLeft :=
      fixedDescriptionBoundedSimulatorReturnFromRightPhaseRealizes_configRunner
    have hPause :
        FixedDescriptionBoundedSimulatorPhaseRealizes
          (FixedDescriptionBoundedSimulatorHandoffTape Direction.right)
          (FixedDescriptionBoundedSimulatorHandoffTape Direction.right)
          id rightPause := by
      simpa [rightPause] using
        fixedDescriptionBoundedSimulatorHaltPhaseRealizes
          (FixedDescriptionBoundedSimulatorHandoffTape Direction.right)
    simpa [enterRun, leftReturn] using
      fixedDescriptionBoundedSimulatorPhaseRealizes_seq
        (entryTape := FixedDescriptionBoundedSimulatorHandoffTape
          Direction.right)
        (midTape := FixedDescriptionBoundedSimulatorLayoutTape)
        (exitTape := FixedDescriptionBoundedSimulatorHandoffTape
          Direction.right)
        (phaseA := id)
        (phaseB := id)
        (A := leftReturn)
        (B := rightPause)
        (handoffMove := Direction.right)
        hLeft hPause
  have hRunAndReturn :
      FixedDescriptionBoundedSimulatorPhaseRealizes
        FixedDescriptionBoundedSimulatorLayoutTape
        FixedDescriptionBoundedSimulatorLayoutTape
        (fun L => MachineDescription.SimulatorLayout.run D L.stage L)
        runAndReturn := by
    have hRun :=
      fixedDescriptionBoundedSimulatorRightShiftedRunCodePhaseRealizes_configRunner
        hrunner
    have hPause :
        FixedDescriptionBoundedSimulatorPhaseRealizes
          FixedDescriptionBoundedSimulatorLayoutTape
          FixedDescriptionBoundedSimulatorLayoutTape
          id finalPause := by
      simpa [finalPause] using
        fixedDescriptionBoundedSimulatorHaltPhaseRealizes
          FixedDescriptionBoundedSimulatorLayoutTape
    simpa [runAndReturn, runCode, finalPause] using
      fixedDescriptionBoundedSimulatorPhaseRealizes_seq
        (entryTape := FixedDescriptionBoundedSimulatorLayoutTape)
        (midTape := FixedDescriptionBoundedSimulatorHandoffTape
          Direction.right)
        (exitTape := FixedDescriptionBoundedSimulatorLayoutTape)
        (phaseA := fun L =>
          MachineDescription.SimulatorLayout.run D L.stage L)
        (phaseB := id)
        (A := runCode)
        (B := finalPause)
        (handoffMove := Direction.left)
        hRun hPause
  simpa [simulateStep, enterRun, runAndReturn] using
    fixedDescriptionBoundedSimulatorPhaseRealizes_seq
      (entryTape := FixedDescriptionBoundedSimulatorHandoffTape
        Direction.right)
      (midTape := FixedDescriptionBoundedSimulatorHandoffTape
        Direction.right)
      (exitTape := FixedDescriptionBoundedSimulatorLayoutTape)
      (phaseA := id)
      (phaseB := fun L =>
        MachineDescription.SimulatorLayout.run D L.stage L)
      (A := enterRun)
      (B := runAndReturn)
      (handoffMove := Direction.left)
      hEnterRun hRunAndReturn

theorem fixedDescriptionBoundedSimulatorSkeletonPhaseConstruction_of_stepPhase_configRunner
    (hstep :
      FixedDescriptionBoundedSimulatorStepPhaseConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorSkeletonPhaseConstruction := by
  intro D
  rcases hstep D with ⟨simulateStep, hsimulateStep⟩
  let S : MachineDescription.FixedSimulatorTableSkeleton :=
    { decodeLayout := MachineDescription.Fragment.halt
      simulateStep := simulateStep
      repeatControl := MachineDescription.Fragment.handoff Direction.left
      emitLayout := MachineDescription.Fragment.handoff Direction.left
      decodeLayout_wellFormed :=
        MachineDescription.Fragment.halt_wellFormed
      simulateStep_wellFormed := hsimulateStep.left
      repeatControl_wellFormed :=
        MachineDescription.Fragment.handoff_wellFormed Direction.left
      emitLayout_wellFormed :=
        MachineDescription.Fragment.handoff_wellFormed Direction.left }
  refine
    ⟨S, Direction.right,
      FixedDescriptionBoundedSimulatorPhaseTargets.canonical D, ?_⟩
  refine
    { decodeLayout := ?_
      simulateStep := ?_
      repeatControl := ?_
      emitLayout := ?_ }
  · simpa [S, FixedDescriptionBoundedSimulatorPhaseTargets.canonical] using
      fixedDescriptionBoundedSimulatorHaltPhaseRealizes
        FixedDescriptionBoundedSimulatorLayoutTape
  · simpa [S, FixedDescriptionBoundedSimulatorPhaseTargets.canonical] using
      hsimulateStep
  · simpa [S, FixedDescriptionBoundedSimulatorPhaseTargets.canonical] using
      fixedDescriptionBoundedSimulatorReturnFromRightPhaseRealizes_configRunner
  · simpa [S, FixedDescriptionBoundedSimulatorPhaseTargets.canonical] using
      fixedDescriptionBoundedSimulatorReturnFromRightPhaseRealizes_configRunner

theorem fixedDescriptionBoundedSimulatorCodeRightShiftedConstruction_scaffold_configRunner :
    FoC.Computability.FixedDescriptionBoundedSimulatorCodeRightShiftedConstruction :=
  FoC.Computability.fixedDescriptionBoundedSimulatorCodeRightShiftedConstruction_scaffold

theorem fixedDescriptionBoundedSimulatorStepPhaseConstruction_scaffold_configRunner :
    FixedDescriptionBoundedSimulatorStepPhaseConstruction_configRunner :=
  fixedDescriptionBoundedSimulatorStepPhaseConstruction_of_rightShifted_configRunner
    fixedDescriptionBoundedSimulatorCodeRightShiftedConstruction_scaffold_configRunner

theorem fixedDescriptionBoundedSimulatorSkeletonPhaseConstruction_scaffold_configRunner :
    FixedDescriptionBoundedSimulatorSkeletonPhaseConstruction :=
  fixedDescriptionBoundedSimulatorSkeletonPhaseConstruction_of_stepPhase_configRunner
    fixedDescriptionBoundedSimulatorStepPhaseConstruction_scaffold_configRunner

theorem fixedDescriptionBoundedSimulatorCanonicalConstruction_scaffold_configRunner :
    FixedDescriptionBoundedSimulatorCanonicalConstruction :=
  fixedDescriptionBoundedSimulatorCanonicalConstruction_of_phaseConstruction
    fixedDescriptionBoundedSimulatorSkeletonPhaseConstruction_scaffold_configRunner

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC

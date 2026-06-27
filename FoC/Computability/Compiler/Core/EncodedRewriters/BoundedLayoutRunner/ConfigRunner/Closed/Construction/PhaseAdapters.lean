import FoC.Computability.Compiler.Core.CommonGround.Identity
import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Closed.Primitives
import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.Emitters

set_option doc.verso true

/-!
# Bounded runner phase adapters
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

def SeqViaCanonical
    (A B : MachineDescription) : MachineDescription :=
  seqSubroutine
    (seqSubroutine A
      ExactIdentityDescription Direction.right)
    B Direction.left

theorem SeqViaCanonical_subroutineReady
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady) :
    (SeqViaCanonical A B).SubroutineReady := by
  have hid : ExactIdentityDescription.SubroutineReady :=
    CommonGround.Identity.exactIdentityDescription_subroutineReady
  exact
    seqSubroutine_subroutineReady
      (seqSubroutine_subroutineReady hA hid)
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
        runConfig_eq_halt_of_haltsWithTape
          hBout with
      ⟨nB, hBRun⟩
    refine ⟨nB, ?_⟩
    simpa [hbridge] using hBRun
  simpa [SeqViaCanonical, identity] using
    seqSubroutine_haltsWithTape_of_haltsWithTape
      (A := seqSubroutine A identity Direction.right)
      (B := B) (handoffMove := Direction.left)
      (seqSubroutine_subroutineReady hA hid)
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
        runConfig_eq_halt_of_haltsWithTape
          hBout with
      ⟨nB, hBRun⟩
    refine ⟨nB, ?_⟩
    simpa [hbridge] using hBRun
  simpa [SeqViaCanonical, identity] using
    seqSubroutine_haltsFromTape_of_haltsFromTape
      (A := seqSubroutine A identity Direction.right)
      (B := B) (handoffMove := Direction.left)
      (seqSubroutine_subroutineReady hA hid)
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
        runConfig_eq_halt_of_haltsFromTape
          hBout with
      ⟨nB, hBRun⟩
    refine ⟨nB, ?_⟩
    simpa [hbridge] using hBRun
  simpa [SeqViaCanonical, identity] using
    seqSubroutine_haltsFromTape_of_haltsFromTape
      (A := seqSubroutine A identity Direction.right)
      (B := B) (handoffMove := Direction.left)
      (seqSubroutine_subroutineReady hA hid)
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
    HaltsFromTapeEquiv (SeqViaCanonical A B) Tin Tout := by
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
  rcases hBout with ⟨nB, hnB⟩
  have hB_equiv := HaltsFromTapeEquiv_of_input_equiv (D := B)
    (Tin := Tape.input midInput)
    (Tin' := Tape.move Direction.left (Tape.move Direction.right Tmid))
    (Tout := Tout)
    (Tape.Equiv.symm hbridge)
    ⟨nB, by simpa [HaltsWithTapeIn, HaltsFromTapeIn] using hnB⟩
  rcases hB_equiv with ⟨Tactual, hB_actual_halt, hB_actual_equiv⟩
  
  have hseq_actual := seqSubroutine_haltsFromTape_of_haltsFromTape
    (A := seqSubroutine A identity Direction.right)
    (B := B) (handoffMove := Direction.left)
    (seqSubroutine_subroutineReady hA hid)
    hB hAid (runConfig_eq_halt_of_haltsFromTape hB_actual_halt)
  exact ⟨Tactual, by simpa [SeqViaCanonical, identity] using hseq_actual, hB_actual_equiv⟩

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
    HaltsFromTapeEquiv (SeqViaCanonical A B) Tin Tout := by
  rcases hAmid with ⟨Tactual, hhalt, hequiv⟩
  have hequiv2 := Tape.Equiv.moveRight hequiv
  have hequiv3 := Tape.Equiv.moveLeft hequiv2
  have hbridge_actual := Tape.Equiv.trans hequiv3 hbridge
  exact SeqViaCanonical_haltsFromTape_of_haltsWithTape_equiv hA hB hhalt hbridge_actual hBout

theorem SeqViaCanonical_haltsFromTapeEquiv_of_equiv
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {Tin : Tape Bool} {midInput : Word Bool} {Tmid Tout : Tape Bool}
    (hAmid : A.HaltsFromTapeEquiv Tin Tmid)
    (hbridge :
      Tape.Equiv
        (Tape.move Direction.left (Tape.move Direction.right Tmid))
        (Tape.input midInput))
    (hBout : B.HaltsFromTapeEquiv (Tape.input midInput) Tout) :
    HaltsFromTapeEquiv (SeqViaCanonical A B) Tin Tout := by
  rcases hBout with ⟨Tactual, hBactual, hequivB⟩
  have hBwith : B.HaltsWithTape midInput Tactual := by
    rcases hBactual with ⟨n, hn⟩
    exact
      ⟨n, by
        simpa [HaltsWithTapeIn,
          HaltsFromTapeIn,
          initial] using hn⟩
  rcases
      SeqViaCanonical_haltsFromTapeEquiv_of_haltsWithTape
        hA hB hAmid hbridge hBwith with
    ⟨Tseq, hseq, hequivSeq⟩
  exact ⟨Tseq, hseq, Tape.Equiv.trans hequivSeq hequivB⟩

def PaddedEquivEmitterSpec
    {ι : Type}
    (inputTape paddedOutputTape canonicalOutputTape : ι -> Tape Bool)
    (emitter : MachineDescription) : Prop :=
  ReadySpec emitter ∧
    (forall i : ι,
      emitter.HaltsFromTape (inputTape i) (paddedOutputTape i)) ∧
      forall i : ι,
        Tape.Equiv (paddedOutputTape i) (canonicalOutputTape i)

theorem PaddedEquivEmitterSpec.of_haltsFromTape_equiv
    {ι : Type}
    {inputTape paddedOutputTape canonicalOutputTape : ι -> Tape Bool}
    {emitter : MachineDescription}
    (hready : ReadySpec emitter)
    (hforward :
      forall i : ι,
        emitter.HaltsFromTape (inputTape i) (paddedOutputTape i))
    (hequiv :
      forall i : ι,
        Tape.Equiv (paddedOutputTape i) (canonicalOutputTape i)) :
    PaddedEquivEmitterSpec inputTape paddedOutputTape
      canonicalOutputTape emitter :=
  ⟨hready, hforward, hequiv⟩

theorem PaddedEquivEmitterSpec.haltsFromTapeEquiv
    {ι : Type}
    {inputTape paddedOutputTape canonicalOutputTape : ι -> Tape Bool}
    {emitter : MachineDescription}
    (hemits :
      PaddedEquivEmitterSpec inputTape paddedOutputTape
        canonicalOutputTape emitter)
    (i : ι) :
    emitter.HaltsFromTapeEquiv (inputTape i) (canonicalOutputTape i) :=
  ⟨paddedOutputTape i, hemits.right.left i, hemits.right.right i⟩

theorem PaddedEquivEmitterSpec.closedFromTapeEquiv
    {ι : Type}
    {inputTape paddedOutputTape canonicalOutputTape : ι -> Tape Bool}
    {emitter : MachineDescription}
    (hemits :
      PaddedEquivEmitterSpec inputTape paddedOutputTape
        canonicalOutputTape emitter)
    (i : ι) :
    emitter.ClosedFromTapeEquiv (inputTape i) (canonicalOutputTape i) := by
  intro T hhalt
  have hT : T = paddedOutputTape i :=
    haltsFromTape_functional_of_haltTransitionFree
      hemits.left.right hhalt (hemits.right.left i)
  rw [hT]
  exact hemits.right.right i

theorem SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {Tin TinB Tmid Tout : Tape Bool}
    (hAmid : A.HaltsFromTapeEquiv Tin Tmid)
    (hbridge :
      Tape.Equiv
        (Tape.move Direction.left (Tape.move Direction.right Tmid))
        TinB)
    (hBout : B.HaltsFromTapeEquiv TinB Tout) :
    HaltsFromTapeEquiv (SeqViaCanonical A B) Tin Tout := by
  rcases hAmid with ⟨Tactual, hAactual, hTactual⟩
  have hbridgeActual :
      Tape.Equiv
        (Tape.move Direction.left (Tape.move Direction.right Tactual))
        TinB := by
    exact
      Tape.Equiv.trans
        (Tape.Equiv.move
          (Tape.Equiv.move hTactual Direction.right) Direction.left)
        hbridge
  rcases hBout with ⟨TactualB, hBactual, hBactualEquiv⟩
  rcases
      HaltsFromTapeEquiv_of_input_equiv
        (Tape.Equiv.symm hbridgeActual) hBactual with
    ⟨TseqOut, hBfromActual, hTseqOut⟩
  have hseq :
      (SeqViaCanonical A B).HaltsFromTape Tin TseqOut :=
    SeqViaCanonical_haltsFromTape_of_haltsFromTape
      hA hB hAactual rfl hBfromActual
  exact
    ⟨TseqOut, hseq, Tape.Equiv.trans hTseqOut hBactualEquiv⟩

theorem SeqViaCanonical_haltsFromTapeEquiv_of_paddedEmitter
    {ι : Type}
    {inputTape paddedOutputTape canonicalOutputTape : ι -> Tape Bool}
    {A B : MachineDescription}
    (hA : A.SubroutineReady)
    (hB :
      PaddedEquivEmitterSpec inputTape paddedOutputTape
        canonicalOutputTape B)
    {Tin Tmid : Tape Bool} (i : ι)
    (hAmid : A.HaltsFromTapeEquiv Tin Tmid)
    (hbridge :
      Tape.Equiv
        (Tape.move Direction.left (Tape.move Direction.right Tmid))
        (inputTape i)) :
    HaltsFromTapeEquiv
      (SeqViaCanonical A B) Tin (canonicalOutputTape i) :=
  SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
    hA hB.left hAmid hbridge
    (PaddedEquivEmitterSpec.haltsFromTapeEquiv hB i)

theorem SeqViaCanonical_haltsFromTape_inv
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {Tin Tout : Tape Bool}
    (hseq :
      (SeqViaCanonical A B).HaltsFromTape Tin Tout) :
    exists Tmid : Tape Bool,
      A.HaltsFromTape Tin Tmid ∧
      B.HaltsFromTape (Tape.move Direction.left (Tape.move Direction.right Tmid)) Tout := by
  let identity := ExactIdentityDescription
  have hid : identity.SubroutineReady :=
    CommonGround.Identity.exactIdentityDescription_subroutineReady
  have hseq' : (seqSubroutine (seqSubroutine A identity Direction.right) B Direction.left).HaltsFromTape Tin Tout := by
    simpa [SeqViaCanonical, identity] using hseq
  rcases seqSubroutine_haltsFromTape_inv
    (seqSubroutine_subroutineReady hA hid) hB hseq' with ⟨Tmid_seq, hA_seq, ⟨nB, hBRun⟩⟩
  rcases seqSubroutine_haltsFromTape_inv hA hid hA_seq with ⟨Tmid, hA_halt, ⟨nId, hIdRun⟩⟩
  have hTmid_seq_eq : Tmid_seq = Tape.move Direction.right Tmid := by
    have h_final :=
      CommonGround.Identity.exactIdentityDescription_runConfig_from_start
        nId (Tape.move Direction.right Tmid)
    rw [h_final] at hIdRun
    exact (congrArg Configuration.tape hIdRun).symm
  subst hTmid_seq_eq
  exact ⟨Tmid, hA_halt, ⟨nB, by
    constructor
    · simpa [HaltsFromTapeIn] using congrArg Configuration.state hBRun
    · simpa [HaltsFromTapeIn] using congrArg Configuration.tape hBRun⟩⟩

theorem moveLeft_moveRight_equiv_self (T : Tape Bool) :
    Tape.Equiv (Tape.move Direction.left (Tape.move Direction.right T)) T := by
  cases T with
  | mk left head right =>
    simp [Tape.Equiv, Tape.move, Tape.moveLeft, Tape.moveRight]
    cases right with
    | nil => simp [Tape.dropTrailingNone]
    | cons x xs => simp

theorem SeqViaCanonical_closed_equiv
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {Tin : Tape Bool} {midInput : Word Bool} {Tout : Tape Bool}
    (hA_closed : ClosedFromTapeEquiv A Tin (Tape.move Direction.left (Tape.input midInput)))
    (hB_closed : ClosedFromTapeEquiv B (Tape.input midInput) Tout)
    (hmid_bridge : Tape.move Direction.left (Tape.move Direction.right (Tape.move Direction.left (Tape.input midInput))) = Tape.input midInput) :
    ClosedFromTapeEquiv (SeqViaCanonical A B) Tin Tout := by
  intro T hT
  rcases SeqViaCanonical_haltsFromTape_inv hA hB hT with ⟨Tmid, hA_run, hB_run⟩
  have hA_eq := hA_closed Tmid hA_run
  have hA_eq_moved := Tape.Equiv.move (Tape.Equiv.move hA_eq Direction.right) Direction.left
  rw [hmid_bridge] at hA_eq_moved
  
  have hB_equiv := HaltsFromTapeEquiv_of_input_equiv (D := B)
    (Tin := Tape.move Direction.left (Tape.move Direction.right Tmid))
    (Tin' := Tape.input midInput)
    (Tout := T)
    hA_eq_moved
    hB_run
  rcases hB_equiv with ⟨Tactual, hB_actual_halt, hB_actual_equiv⟩
  have hB_eq := hB_closed Tactual hB_actual_halt
  exact Tape.Equiv.trans (Tape.Equiv.symm hB_actual_equiv) hB_eq

theorem rightShiftedOutputCompiled_haltsWithTape_of_transform
    {P : TapeCodePrimitive}
    {D : MachineDescription}
    (hD : RightShiftedOutputCompiledSubroutineByDescription P D)
    {code out : Word MachineCodeSymbol}
    (htransform : P.transform code = some out) :
    D.HaltsWithTape
      (encodeCodeWordAsInput code)
      (Tape.move Direction.right
        (Tape.input
          (encodeCodeWordAsInput out))) := by
  have houtput :
      D.HaltsWithOutput
        (encodeCodeWordAsInput code)
        (encodeCodeWordAsInput out) :=
    (hD.right.right.left code out).mpr htransform
  rcases houtput with ⟨n, hn⟩
  let T : Tape Bool :=
    (D.runConfig n
      (D.initial
        (encodeCodeWordAsInput code))).tape
  have hhalt :
      D.HaltsWithTape
        (encodeCodeWordAsInput code) T := by
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
    {P Q : TapeCodePrimitive}
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
  seqSubroutine closed
    ExactIdentityDescription
    tapeCodePrimitiveCodeWordHandoffMove

theorem TapeCodeExactPhaseFromClosedHandoff_subroutineReady
    {P : TapeCodePrimitive}
    {closed : MachineDescription}
    (hclosed :
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        P closed tapeCodePrimitiveCodeWordHandoffMove) :
    (TapeCodeExactPhaseFromClosedHandoff closed).SubroutineReady := by
  have hclosedReady : closed.SubroutineReady :=
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_subroutineReady
      hclosed
  have hid : ExactIdentityDescription.SubroutineReady :=
    CommonGround.Identity.exactIdentityDescription_subroutineReady
  exact
    seqSubroutine_subroutineReady
      hclosedReady hid

theorem TapeCodeExactPhaseFromClosedHandoff_forward
    {P : TapeCodePrimitive}
    {closed : MachineDescription}
    (hclosed :
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        P closed tapeCodePrimitiveCodeWordHandoffMove)
    {code out : Word MachineCodeSymbol}
    (htransform : P.transform code = some out) :
    (TapeCodeExactPhaseFromClosedHandoff closed).HaltsWithTape
      (encodeCodeWordAsInput code)
      (Tape.input (encodeCodeWordAsInput out)) := by
  let identity := ExactIdentityDescription
  have hclosedReady : closed.SubroutineReady :=
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_subroutineReady
      hclosed
  have hid : identity.SubroutineReady :=
    CommonGround.Identity.exactIdentityDescription_subroutineReady
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
            tape := Tape.input (encodeCodeWordAsInput out) } := by
    refine ⟨0, ?_⟩
    rw [hhandoff]
    rfl
  simpa [TapeCodeExactPhaseFromClosedHandoff, identity,
    tapeCodePrimitiveCodeWordHandoffMove] using
    seqSubroutine_haltsWithTape_of_haltsWithTape
      (A := closed) (B := identity)
      (handoffMove := tapeCodePrimitiveCodeWordHandoffMove)
      hclosedReady hid hclosedHalt hidentityReach

theorem TapeCodeExactPhaseFromClosedHandoff_closed_eq
    {P : TapeCodePrimitive}
    {closed : MachineDescription}
    (hclosed :
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        P closed tapeCodePrimitiveCodeWordHandoffMove)
    {code out : Word MachineCodeSymbol}
    (htransform : P.transform code = some out)
    {T : Tape Bool}
    (hhalt :
      (TapeCodeExactPhaseFromClosedHandoff closed).HaltsWithTape
        (encodeCodeWordAsInput code) T) :
    T = Tape.input (encodeCodeWordAsInput out) := by
  let identity := ExactIdentityDescription
  have hclosedReady : closed.SubroutineReady :=
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_subroutineReady
      hclosed
  have hid : identity.SubroutineReady :=
    CommonGround.Identity.exactIdentityDescription_subroutineReady
  rcases
      seqSubroutine_haltsWithTape_inv
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
      simpa [identity] using
        CommonGround.Identity.exactIdentityDescription_runConfig_from_start
          nB (Tape.move tapeCodePrimitiveCodeWordHandoffMove Tmid)
    have hcfg :
        ({ state := identity.halt
           tape := Tape.move tapeCodePrimitiveCodeWordHandoffMove Tmid } :
          Configuration) =
        { state := identity.halt, tape := T } := by
      simpa [identity] using
        (hidentityStart.symm.trans hidentityRun)
    exact (congrArg Configuration.tape hcfg).symm
  rw [hT]
  simpa [hactualOut] using hhandoff

def TapeCodeCheckedPhaseFromClosedHandoff
    (closed : MachineDescription) : MachineDescription :=
  seqSubroutine closed
    ExactIdentityDescription
    tapeCodePrimitiveCodeWordHandoffMove

theorem TapeCodeCheckedPhaseFromClosedHandoff_subroutineReady
    {P : TapeCodePrimitive}
    {closed : MachineDescription}
    (hclosed :
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        P closed tapeCodePrimitiveCodeWordHandoffMove) :
    (TapeCodeCheckedPhaseFromClosedHandoff closed).SubroutineReady := by
  have hclosedReady : closed.SubroutineReady :=
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_subroutineReady
      hclosed
  have hid : ExactIdentityDescription.SubroutineReady :=
    CommonGround.Identity.exactIdentityDescription_subroutineReady
  exact
    seqSubroutine_subroutineReady
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
    {P : TapeCodePrimitive}
    {closed : MachineDescription}
    (hclosed :
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        P closed tapeCodePrimitiveCodeWordHandoffMove)
    {code out : Word MachineCodeSymbol}
    (htransform : P.transform code = some out) :
    (TapeCodeCheckedPhaseFromClosedHandoff closed).HaltsFromTapeEquiv
      (checkedInputTape (encodeCodeWordAsInput code))
      (Tape.input (encodeCodeWordAsInput out)) := by
  have h_outputCompiled := hclosed.1
  have h_exactOutput := hclosed.2
  have h_outputCompiledByDesc := h_outputCompiled.1
  have h_haltsWithOutput : closed.HaltsWithOutput (encodeCodeWordAsInput code) (encodeCodeWordAsInput out) :=
    (h_outputCompiledByDesc.2 code out).mpr htransform
  rcases h_haltsWithOutput with ⟨n, hn⟩
  let T_canonical := (closed.runConfig n (closed.initial (encodeCodeWordAsInput code))).tape
  have h_haltsWithTape : closed.HaltsWithTape (encodeCodeWordAsInput code) T_canonical :=
    ⟨n, hn.1, rfl⟩
  have h_exact := h_exactOutput code T_canonical h_haltsWithTape
  rcases h_exact with ⟨out', h_transform', _, h_move⟩
  have h_out_eq : out' = out := by
    rw [htransform] at h_transform'
    injection h_transform' with h_eq
    exact h_eq.symm
  rw [h_out_eq] at h_move
  have hid : ExactIdentityDescription.SubroutineReady :=
    CommonGround.Identity.exactIdentityDescription_subroutineReady
  have hclosedReady : closed.SubroutineReady :=
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_subroutineReady hclosed
  have hseq_halts : (TapeCodeCheckedPhaseFromClosedHandoff closed).HaltsFromTape
      (Tape.input (encodeCodeWordAsInput code))
      (Tape.move tapeCodePrimitiveCodeWordHandoffMove T_canonical) := by
    exact
      seqSubroutine_haltsFromTape_of_haltsFromTape
        (A := closed) (B := ExactIdentityDescription)
        (handoffMove := tapeCodePrimitiveCodeWordHandoffMove)
        hclosedReady hid h_haltsWithTape
        (CommonGround.Identity.exactIdentityDescription_run_from_start
          (Tape.move tapeCodePrimitiveCodeWordHandoffMove T_canonical))
  have hseq_halts' : (TapeCodeCheckedPhaseFromClosedHandoff closed).HaltsFromTape
      (Tape.input (encodeCodeWordAsInput code))
      (Tape.input (encodeCodeWordAsInput out)) := by
    rwa [h_move] at hseq_halts
  have h_equiv_in := checkedInputTape_equiv_input (encodeCodeWordAsInput code)
  exact HaltsFromTapeEquiv_of_input_equiv (Tape.Equiv.symm h_equiv_in) hseq_halts'

theorem TapeCodeCheckedPhaseFromClosedHandoff_closed_equiv
    {P : TapeCodePrimitive}
    {closed : MachineDescription}
    (hclosed :
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        P closed tapeCodePrimitiveCodeWordHandoffMove)
    {code out : Word MachineCodeSymbol}
    (htransform : P.transform code = some out)
    {T : Tape Bool}
    (hhalt :
      (TapeCodeCheckedPhaseFromClosedHandoff closed).HaltsFromTape
        (checkedInputTape (encodeCodeWordAsInput code)) T) :
    Tape.Equiv T (Tape.input (encodeCodeWordAsInput out)) := by
  have h_forward := TapeCodeCheckedPhaseFromClosedHandoff_forward hclosed htransform
  rcases h_forward with ⟨Tactual, h_halt_actual, h_equiv_actual⟩
  have hid : ExactIdentityDescription.SubroutineReady :=
    CommonGround.Identity.exactIdentityDescription_subroutineReady
  have hclosedReady : closed.SubroutineReady :=
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_subroutineReady hclosed
  have h_ready := seqSubroutine_subroutineReady (handoffMove := tapeCodePrimitiveCodeWordHandoffMove) hclosedReady hid
  have h_T_eq := haltsFromTape_functional_of_haltTransitionFree h_ready.2 hhalt h_halt_actual
  subst h_T_eq
  exact h_equiv_actual


end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC

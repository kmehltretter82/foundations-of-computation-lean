import FoC.Computability.Compiler.SeqSubroutineSemantics
import FoC.Computability.Compiler.Core.ConstructionTargets
import FoC.Computability.Compiler.Core.FixedDescriptionBoundedSimulator.Skeleton
import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Basic

set_option doc.verso true

/-!
# Bounded recognizer-configuration runner construction

The bridge below remains useful once a closed handoff implementation of
{name (full := FoC.Computability.PairedRecognizerDovetailLayoutCode)}`PairedRecognizerDovetailLayoutCode`
is available without importing this bounded-runner assembly.  The finite
construction leaf is kept here to avoid circular imports.
-/

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters
namespace BoundedLayoutRunner

def AcceptSimulatorLayout
    (L : MachineDescription.DovetailLayout) :
    MachineDescription.SimulatorLayout where
  input := ParsedLayoutBits L
  stage := L.stage
  config := L.acceptConfig
  hit := L.acceptHit

def RejectSimulatorLayout
    (L : MachineDescription.DovetailLayout) :
    MachineDescription.SimulatorLayout where
  input := ParsedLayoutBits L
  stage := L.stage
  config := L.rejectConfig
  hit := L.rejectHit

def MergeAcceptSimulatorResult
    (S : MachineDescription.SimulatorLayout) :
    Option MachineDescription.DovetailLayout :=
  match MachineDescription.decodeCodeWordAsInput S.input with
  | none => none
  | some code =>
      match MachineDescription.DovetailLayout.decodeComplete code with
      | none => none
      | some L =>
          some { L with
            acceptConfig := S.config
            acceptHit := S.hit }

def MergeRejectSimulatorResult
    (S : MachineDescription.SimulatorLayout) :
    Option MachineDescription.DovetailLayout :=
  match MachineDescription.decodeCodeWordAsInput S.input with
  | none => none
  | some code =>
      match MachineDescription.DovetailLayout.decodeComplete code with
      | none => none
      | some L =>
          some { L with
            rejectConfig := S.config
            rejectHit := S.hit }

def AcceptProjectionPrimitive :
    MachineDescription.TapeCodePrimitive where
  transform := fun code =>
    match MachineDescription.DovetailLayout.decodeComplete code with
    | none => none
    | some L =>
        some
          (MachineDescription.SimulatorLayout.encode
            (AcceptSimulatorLayout L))

def RejectProjectionPrimitive :
    MachineDescription.TapeCodePrimitive where
  transform := fun code =>
    match MachineDescription.DovetailLayout.decodeComplete code with
    | none => none
    | some L =>
        some
          (MachineDescription.SimulatorLayout.encode
            (RejectSimulatorLayout L))

def AcceptMergePrimitive :
    MachineDescription.TapeCodePrimitive where
  transform := fun code =>
    match MachineDescription.SimulatorLayout.decodeComplete code with
    | none => none
    | some S =>
        Option.map MachineDescription.DovetailLayout.encode
          (MergeAcceptSimulatorResult S)

def RejectMergePrimitive :
    MachineDescription.TapeCodePrimitive where
  transform := fun code =>
    match MachineDescription.SimulatorLayout.decodeComplete code with
    | none => none
    | some S =>
        Option.map MachineDescription.DovetailLayout.encode
          (MergeRejectSimulatorResult S)

def SelectedProjectionSimulatorLayout
    (useAccept : Bool)
    (L : MachineDescription.DovetailLayout) :
    MachineDescription.SimulatorLayout :=
  if useAccept then
    AcceptSimulatorLayout L
  else
    RejectSimulatorLayout L

def SelectedProjectionPrimitive
    (useAccept : Bool) :
    MachineDescription.TapeCodePrimitive where
  transform := fun code =>
    match MachineDescription.DovetailLayout.decodeComplete code with
    | none => none
    | some L =>
        some
          (MachineDescription.SimulatorLayout.encode
            (SelectedProjectionSimulatorLayout useAccept L))

def SelectedMergeSimulatorResult
    (useAccept : Bool)
    (S : MachineDescription.SimulatorLayout) :
    Option MachineDescription.DovetailLayout :=
  if useAccept then
    MergeAcceptSimulatorResult S
  else
    MergeRejectSimulatorResult S

def SelectedMergePrimitive
    (useAccept : Bool) :
    MachineDescription.TapeCodePrimitive where
  transform := fun code =>
    match MachineDescription.SimulatorLayout.decodeComplete code with
    | none => none
    | some S =>
        Option.map MachineDescription.DovetailLayout.encode
          (SelectedMergeSimulatorResult useAccept S)

def ConfigRunnerAfterAccept
    (accept : MachineDescription)
    (L : MachineDescription.DovetailLayout) :
    MachineDescription.DovetailLayout :=
  { L with
    acceptConfig :=
      accept.runConfig L.stage L.acceptConfig
    acceptHit :=
      L.acceptHit ||
        MachineDescription.SimulatorLayout.hitsFromConfigByBool
          accept L.acceptConfig L.stage }

def ConfigRunnerAfterReject
    (reject : MachineDescription)
    (L : MachineDescription.DovetailLayout) :
    MachineDescription.DovetailLayout :=
  { L with
    rejectConfig :=
      reject.runConfig L.stage L.rejectConfig
    rejectHit :=
      L.rejectHit ||
        MachineDescription.SimulatorLayout.hitsFromConfigByBool
          reject L.rejectConfig L.stage }

theorem decodeCodeWordAsInput_parsedLayoutBits
    (L : MachineDescription.DovetailLayout) :
    MachineDescription.decodeCodeWordAsInput (ParsedLayoutBits L) =
      some (MachineDescription.DovetailLayout.encode L) := by
  simpa [ParsedLayoutBits] using
    MachineDescription.decodeCodeWordAsInput_encodeCodeWordAsInput
      (MachineDescription.DovetailLayout.encode L)

theorem MergeAcceptSimulatorResult_run
    (accept : MachineDescription)
    (L : MachineDescription.DovetailLayout) :
    MergeAcceptSimulatorResult
        (MachineDescription.SimulatorLayout.run
          accept L.stage (AcceptSimulatorLayout L)) =
      some (ConfigRunnerAfterAccept accept L) := by
  simp [MergeAcceptSimulatorResult, ConfigRunnerAfterAccept,
    AcceptSimulatorLayout, decodeCodeWordAsInput_parsedLayoutBits,
    MachineDescription.DovetailLayout.decodeComplete_encode,
    MachineDescription.SimulatorLayout.run]

theorem MergeRejectSimulatorResult_run
    (reject : MachineDescription)
    (L : MachineDescription.DovetailLayout) :
    MergeRejectSimulatorResult
        (MachineDescription.SimulatorLayout.run
          reject L.stage (RejectSimulatorLayout L)) =
      some (ConfigRunnerAfterReject reject L) := by
  simp [MergeRejectSimulatorResult, ConfigRunnerAfterReject,
    RejectSimulatorLayout, decodeCodeWordAsInput_parsedLayoutBits,
    MachineDescription.DovetailLayout.decodeComplete_encode,
    MachineDescription.SimulatorLayout.run]

theorem AcceptProjectionPrimitive_encode
    (L : MachineDescription.DovetailLayout) :
    AcceptProjectionPrimitive.transform
        (MachineDescription.DovetailLayout.encode L) =
      some
        (MachineDescription.SimulatorLayout.encode
          (AcceptSimulatorLayout L)) := by
  simp [AcceptProjectionPrimitive,
    MachineDescription.DovetailLayout.decodeComplete_encode]

theorem RejectProjectionPrimitive_encode
    (L : MachineDescription.DovetailLayout) :
    RejectProjectionPrimitive.transform
        (MachineDescription.DovetailLayout.encode L) =
      some
        (MachineDescription.SimulatorLayout.encode
          (RejectSimulatorLayout L)) := by
  simp [RejectProjectionPrimitive,
    MachineDescription.DovetailLayout.decodeComplete_encode]

theorem SelectedProjectionPrimitive_transform_eq_some_iff
    (useAccept : Bool) (code out : Word MachineCodeSymbol) :
    (SelectedProjectionPrimitive useAccept).transform code = some out ↔
      exists L : MachineDescription.DovetailLayout,
        code = MachineDescription.DovetailLayout.encode L ∧
          out =
            MachineDescription.SimulatorLayout.encode
              (SelectedProjectionSimulatorLayout useAccept L) := by
  constructor
  · intro h
    unfold SelectedProjectionPrimitive at h
    cases hdecode :
        MachineDescription.DovetailLayout.decodeComplete code with
    | none =>
        simp [hdecode] at h
    | some L =>
        simp [hdecode] at h
        cases h
        refine ⟨L, ?_, rfl⟩
        exact
          MachineDescription.DovetailLayout.decodeComplete_eq_some_encode
            hdecode
  · intro h
    rcases h with ⟨L, rfl, rfl⟩
    simp [SelectedProjectionPrimitive,
      MachineDescription.DovetailLayout.decodeComplete_encode]

theorem AcceptMergePrimitive_encode_run
    (accept : MachineDescription)
    (L : MachineDescription.DovetailLayout) :
    AcceptMergePrimitive.transform
        (MachineDescription.SimulatorLayout.encode
          (MachineDescription.SimulatorLayout.run
            accept L.stage (AcceptSimulatorLayout L))) =
      some
        (MachineDescription.DovetailLayout.encode
          (ConfigRunnerAfterAccept accept L)) := by
  simp [AcceptMergePrimitive,
    MachineDescription.SimulatorLayout.decodeComplete_encode,
    MergeAcceptSimulatorResult_run]

theorem RejectMergePrimitive_encode_run
    (reject : MachineDescription)
    (L : MachineDescription.DovetailLayout) :
    RejectMergePrimitive.transform
        (MachineDescription.SimulatorLayout.encode
          (MachineDescription.SimulatorLayout.run
            reject L.stage (RejectSimulatorLayout L))) =
      some
        (MachineDescription.DovetailLayout.encode
          (ConfigRunnerAfterReject reject L)) := by
  simp [RejectMergePrimitive,
    MachineDescription.SimulatorLayout.decodeComplete_encode,
    MergeRejectSimulatorResult_run]

theorem AcceptMergePrimitive_transform_eq_some_iff
    (code out : Word MachineCodeSymbol) :
    AcceptMergePrimitive.transform code = some out ↔
      exists S : MachineDescription.SimulatorLayout,
        exists L : MachineDescription.DovetailLayout,
          code = MachineDescription.SimulatorLayout.encode S ∧
          MachineDescription.decodeCodeWordAsInput S.input =
            some (MachineDescription.DovetailLayout.encode L) ∧
          out =
            MachineDescription.DovetailLayout.encode
              { L with
                acceptConfig := S.config
                acceptHit := S.hit } := by
  constructor
  · intro h
    unfold AcceptMergePrimitive at h
    cases hS : MachineDescription.SimulatorLayout.decodeComplete code with
    | none =>
        simp [hS] at h
    | some S =>
        simp [hS] at h
        unfold MergeAcceptSimulatorResult at h
        cases hinput : MachineDescription.decodeCodeWordAsInput S.input with
        | none =>
            simp [hinput] at h
        | some innerCode =>
            cases hL :
                MachineDescription.DovetailLayout.decodeComplete innerCode with
            | none =>
                simp [hinput, hL] at h
            | some L =>
                simp [hinput, hL] at h
                cases h
                refine ⟨S, L, ?_, ?_, rfl⟩
                · exact
                    MachineDescription.SimulatorLayout.decodeComplete_eq_some_encode
                      hS
                · rw [
                    MachineDescription.DovetailLayout.decodeComplete_eq_some_encode
                      hL] at hinput
                  exact hinput
  · intro h
    rcases h with ⟨S, L, rfl, hinput, rfl⟩
    simp [AcceptMergePrimitive,
      MachineDescription.SimulatorLayout.decodeComplete_encode,
      MergeAcceptSimulatorResult, hinput,
      MachineDescription.DovetailLayout.decodeComplete_encode]

theorem RejectMergePrimitive_transform_eq_some_iff
    (code out : Word MachineCodeSymbol) :
    RejectMergePrimitive.transform code = some out ↔
      exists S : MachineDescription.SimulatorLayout,
        exists L : MachineDescription.DovetailLayout,
          code = MachineDescription.SimulatorLayout.encode S ∧
          MachineDescription.decodeCodeWordAsInput S.input =
            some (MachineDescription.DovetailLayout.encode L) ∧
          out =
            MachineDescription.DovetailLayout.encode
              { L with
                rejectConfig := S.config
                rejectHit := S.hit } := by
  constructor
  · intro h
    unfold RejectMergePrimitive at h
    cases hS : MachineDescription.SimulatorLayout.decodeComplete code with
    | none =>
        simp [hS] at h
    | some S =>
        simp [hS] at h
        unfold MergeRejectSimulatorResult at h
        cases hinput : MachineDescription.decodeCodeWordAsInput S.input with
        | none =>
            simp [hinput] at h
        | some innerCode =>
            cases hL :
                MachineDescription.DovetailLayout.decodeComplete innerCode with
            | none =>
                simp [hinput, hL] at h
            | some L =>
                simp [hinput, hL] at h
                cases h
                refine ⟨S, L, ?_, ?_, rfl⟩
                · exact
                    MachineDescription.SimulatorLayout.decodeComplete_eq_some_encode
                      hS
                · rw [
                    MachineDescription.DovetailLayout.decodeComplete_eq_some_encode
                      hL] at hinput
                  exact hinput
  · intro h
    rcases h with ⟨S, L, rfl, hinput, rfl⟩
    simp [RejectMergePrimitive,
      MachineDescription.SimulatorLayout.decodeComplete_encode,
      MergeRejectSimulatorResult, hinput,
      MachineDescription.DovetailLayout.decodeComplete_encode]

theorem AcceptMergePrimitive_transform_eq_some_cons
    {code out : Word MachineCodeSymbol}
    (h : AcceptMergePrimitive.transform code = some out) :
    exists tail : Word MachineCodeSymbol,
      out = MachineCodeSymbol.transition :: tail := by
  rcases
      (AcceptMergePrimitive_transform_eq_some_iff code out).mp h with
    ⟨S, L, _hcode, _hinput, hout⟩
  rcases
      EncodedRewriters.dovetailLayout_encode_cons
        { L with
          acceptConfig := S.config
          acceptHit := S.hit } with
    ⟨tail, htail⟩
  exact ⟨tail, by rw [hout, htail]⟩

theorem RejectMergePrimitive_transform_eq_some_cons
    {code out : Word MachineCodeSymbol}
    (h : RejectMergePrimitive.transform code = some out) :
    exists tail : Word MachineCodeSymbol,
      out = MachineCodeSymbol.transition :: tail := by
  rcases
      (RejectMergePrimitive_transform_eq_some_iff code out).mp h with
    ⟨S, L, _hcode, _hinput, hout⟩
  rcases
      EncodedRewriters.dovetailLayout_encode_cons
        { L with
          rejectConfig := S.config
          rejectHit := S.hit } with
    ⟨tail, htail⟩
  exact ⟨tail, by rw [hout, htail]⟩

theorem ConfigRunnerAfterReject_afterAccept
    (accept reject : MachineDescription)
    (L : MachineDescription.DovetailLayout) :
    ConfigRunnerAfterReject reject
        (ConfigRunnerAfterAccept accept L) =
      BoundedRunLayout accept reject L := by
  cases L
  simp [ConfigRunnerAfterReject, ConfigRunnerAfterAccept,
    BoundedRunLayout, MachineDescription.DovetailLayout.run]

theorem MergeRejectSimulatorResult_run_afterAccept
    (accept reject : MachineDescription)
    (L : MachineDescription.DovetailLayout) :
    MergeRejectSimulatorResult
        (MachineDescription.SimulatorLayout.run
          reject (ConfigRunnerAfterAccept accept L).stage
          (RejectSimulatorLayout (ConfigRunnerAfterAccept accept L))) =
      some (BoundedRunLayout accept reject L) := by
  rw [MergeRejectSimulatorResult_run]
  exact congrArg some
    (ConfigRunnerAfterReject_afterAccept accept reject L)

theorem ConfigRunnerSemanticPipeline
    (accept reject : MachineDescription)
    (L : MachineDescription.DovetailLayout) :
    (do
      let acceptResult :=
        MachineDescription.SimulatorLayout.run
          accept L.stage (AcceptSimulatorLayout L)
      let Laccept ← MergeAcceptSimulatorResult acceptResult
      let rejectResult :=
        MachineDescription.SimulatorLayout.run
          reject Laccept.stage (RejectSimulatorLayout Laccept)
      MergeRejectSimulatorResult rejectResult) =
        some (BoundedRunLayout accept reject L) := by
  simp [MergeAcceptSimulatorResult_run,
    MergeRejectSimulatorResult_run_afterAccept]

theorem simulatorLayout_encode_cons
    (S : MachineDescription.SimulatorLayout) :
    exists tail : Word MachineCodeSymbol,
      MachineDescription.SimulatorLayout.encode S =
        MachineCodeSymbol.header :: tail := by
  cases S
  exact ⟨_, rfl⟩

theorem SelectedProjectionPrimitive_transform_eq_some_cons
    {useAccept : Bool} {code out : Word MachineCodeSymbol}
    (h : (SelectedProjectionPrimitive useAccept).transform code = some out) :
    exists tail : Word MachineCodeSymbol,
      out = MachineCodeSymbol.header :: tail := by
  rcases
      (SelectedProjectionPrimitive_transform_eq_some_iff useAccept code out).mp
        h with
    ⟨L, _hcode, hout⟩
  rcases simulatorLayout_encode_cons
      (SelectedProjectionSimulatorLayout useAccept L) with
    ⟨tail, htail⟩
  exact ⟨tail, by rw [hout, htail]⟩

theorem simulatorLayoutTape_move_left_move_right
    (S : MachineDescription.SimulatorLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (MachineDescription.SimulatorLayout.tape S)) =
      MachineDescription.SimulatorLayout.tape S := by
  rcases simulatorLayout_encode_cons S with ⟨tail, htail⟩
  unfold MachineDescription.SimulatorLayout.tape
    MachineDescription.SimulatorLayout.asBoolInput
  rw [htail]
  exact
    EncodedRewriters.tape_move_left_move_right_input_encodeCodeWordAsInput_cons
      MachineCodeSymbol.header tail

theorem parsedLayoutTape_move_left_move_right_configRunner
    (L : MachineDescription.DovetailLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right (ParsedLayoutTape L)) =
      ParsedLayoutTape L := by
  rcases EncodedRewriters.dovetailLayout_encode_cons L with
    ⟨tail, htail⟩
  unfold ParsedLayoutTape ParsedLayoutBits
  rw [htail]
  exact
    EncodedRewriters.tape_move_left_move_right_input_encodeCodeWordAsInput_cons
      MachineCodeSymbol.transition tail

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

def AcceptProjectionSpec
    (projector : MachineDescription) : Prop :=
  projector.SubroutineReady ∧
    (forall L : MachineDescription.DovetailLayout,
      projector.HaltsWithTape
        (ParsedLayoutBits L)
        (MachineDescription.SimulatorLayout.tape
          (AcceptSimulatorLayout L))) ∧
    (forall L : MachineDescription.DovetailLayout,
     forall T : Tape Bool,
      projector.HaltsWithTape (ParsedLayoutBits L) T ->
        T =
          MachineDescription.SimulatorLayout.tape
            (AcceptSimulatorLayout L))

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
      (TapeCodeExactPhaseFromClosedHandoff closed) := by
  constructor
  · exact TapeCodeExactPhaseFromClosedHandoff_subroutineReady hclosed
  constructor
  · intro L
    simpa [ParsedLayoutBits,
      MachineDescription.SimulatorLayout.tape,
      MachineDescription.SimulatorLayout.asBoolInput] using
      TapeCodeExactPhaseFromClosedHandoff_forward
        hclosed (AcceptProjectionPrimitive_encode L)
  · intro L T hhalt
    have hhalt' :
        (TapeCodeExactPhaseFromClosedHandoff closed).HaltsWithTape
          (MachineDescription.encodeCodeWordAsInput
            (MachineDescription.DovetailLayout.encode L)) T := by
      simpa [ParsedLayoutBits] using hhalt
    have hT :=
      TapeCodeExactPhaseFromClosedHandoff_closed_eq
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
        acceptProject.HaltsWithTape
          (ParsedLayoutBits L)
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
        APAS.HaltsWithTape
          (ParsedLayoutBits L)
          (MachineDescription.SimulatorLayout.tape
            (MachineDescription.SimulatorLayout.run
              accept L.stage (AcceptSimulatorLayout L))) := by
      exact
        SeqViaCanonical_haltsWithTape_of_haltsWithTape
          hAcceptProjectReady hAcceptSimReady
          hAcceptProjectRun
          (by
            simpa [MachineDescription.SimulatorLayout.tape] using
              simulatorLayoutTape_move_left_move_right
                (AcceptSimulatorLayout L))
          hAcceptSimRun
    have hAcceptMergeRun :
        acceptMerge.HaltsWithTape
          (MachineDescription.SimulatorLayout.asBoolInput
            (MachineDescription.SimulatorLayout.run
              accept L.stage (AcceptSimulatorLayout L)))
          (ParsedLayoutTape (ConfigRunnerAfterAccept accept L)) :=
      hacceptMerge.right.left L
    have hAPASMRun :
        APASM.HaltsWithTape
          (ParsedLayoutBits L)
          (ParsedLayoutTape (ConfigRunnerAfterAccept accept L)) := by
      exact
        SeqViaCanonical_haltsWithTape_of_haltsWithTape
          hAPASReady hAcceptMergeReady
          hAPASRun
          (by
            simpa [MachineDescription.SimulatorLayout.tape] using
              simulatorLayoutTape_move_left_move_right
                (MachineDescription.SimulatorLayout.run
                  accept L.stage (AcceptSimulatorLayout L)))
          hAcceptMergeRun
    have hRejectProjectRun :
        rejectProject.HaltsWithTape
          (ParsedLayoutBits (ConfigRunnerAfterAccept accept L))
          (MachineDescription.SimulatorLayout.tape
            (RejectSimulatorLayout
              (ConfigRunnerAfterAccept accept L))) :=
      hrejectProject.right.left (ConfigRunnerAfterAccept accept L)
    have hAPASMRPRun :
        APASMRP.HaltsWithTape
          (ParsedLayoutBits L)
          (MachineDescription.SimulatorLayout.tape
            (RejectSimulatorLayout
              (ConfigRunnerAfterAccept accept L))) := by
      exact
        SeqViaCanonical_haltsWithTape_of_haltsWithTape
          hAPASMReady hRejectProjectReady
          hAPASMRun
          (by
            simpa [ParsedLayoutTape] using
              parsedLayoutTape_move_left_move_right_configRunner
                (ConfigRunnerAfterAccept accept L))
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
        APASMRPRS.HaltsWithTape
          (ParsedLayoutBits L)
          (MachineDescription.SimulatorLayout.tape
            (MachineDescription.SimulatorLayout.run
              reject (ConfigRunnerAfterAccept accept L).stage
              (RejectSimulatorLayout
                (ConfigRunnerAfterAccept accept L)))) := by
      exact
        SeqViaCanonical_haltsWithTape_of_haltsWithTape
          hAPASMRPReady hRejectSimReady
          hAPASMRPRun
          (by
            simpa [MachineDescription.SimulatorLayout.tape] using
              simulatorLayoutTape_move_left_move_right
                (RejectSimulatorLayout
                  (ConfigRunnerAfterAccept accept L)))
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
        runner.HaltsWithTape
          (ParsedLayoutBits L)
          (ParsedLayoutTape
            (ConfigRunnerAfterReject reject
              (ConfigRunnerAfterAccept accept L))) := by
      exact
        SeqViaCanonical_haltsWithTape_of_haltsWithTape
          hAPASMRPRSReady hRejectMergeReady
          hAPASMRPRSRun
          (by
            simpa [MachineDescription.SimulatorLayout.tape] using
              simulatorLayoutTape_move_left_move_right
                (MachineDescription.SimulatorLayout.run
                  reject (ConfigRunnerAfterAccept accept L).stage
                  (RejectSimulatorLayout
                    (ConfigRunnerAfterAccept accept L))))
          hRejectMergeRun
    have hOutput :
        ParsedLayoutTape
            (ConfigRunnerAfterReject reject
              (ConfigRunnerAfterAccept accept L)) =
          ConfigRunnerOutputTape accept reject L := by
      rw [ConfigRunnerAfterReject_afterAccept]
      rfl
    simpa [hOutput] using hRunner
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
    exact
      MachineDescription.haltsWithTape_functional_of_haltTransitionFree
        hrunnerReady'.right hhalt (hforward' L)

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

theorem fixedDescriptionBoundedSimulatorCanonicalConstruction_scaffold_configRunner :
    FixedDescriptionBoundedSimulatorCanonicalConstruction := by
  sorry

theorem selectedProjectionRejectPrimitiveClosedHandoffConstruction_scaffold :
    exists closed : MachineDescription,
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        (SelectedProjectionPrimitive false)
        closed tapeCodePrimitiveCodeWordHandoffMove := by
  sorry

theorem selectedProjectionAcceptPrimitiveClosedHandoffConstruction_scaffold :
    exists closed : MachineDescription,
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        (SelectedProjectionPrimitive true)
        closed tapeCodePrimitiveCodeWordHandoffMove := by
  sorry

theorem selectedProjectionPrimitiveClosedHandoffConstruction_scaffold :
    SelectedProjectionPrimitiveClosedHandoffConstruction := by
  intro useAccept
  cases useAccept
  · exact selectedProjectionRejectPrimitiveClosedHandoffConstruction_scaffold
  · exact selectedProjectionAcceptPrimitiveClosedHandoffConstruction_scaffold

theorem rejectMergePrimitiveClosedHandoffConstruction_finite_scaffold :
    RejectMergePrimitiveClosedHandoffConstruction := by
  sorry

def AcceptMergePrimitiveClosedHandoffFiniteMachineConstruction : Prop :=
  exists closed : MachineDescription,
    TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      AcceptMergePrimitive
      closed tapeCodePrimitiveCodeWordHandoffMove

theorem acceptMergePrimitiveClosedHandoffConstruction_of_finiteMachine
    (h : AcceptMergePrimitiveClosedHandoffFiniteMachineConstruction) :
    AcceptMergePrimitiveClosedHandoffConstruction :=
  h

-- Actual finite parser/emitter table for the accept-side merge rewriter.
theorem acceptMergePrimitiveClosedHandoffFiniteMachineConstruction_scaffold :
    AcceptMergePrimitiveClosedHandoffFiniteMachineConstruction := by
  sorry

theorem acceptMergePrimitiveClosedHandoffConstruction_finite_scaffold :
    AcceptMergePrimitiveClosedHandoffConstruction := by
  exact
    acceptMergePrimitiveClosedHandoffConstruction_of_finiteMachine
      acceptMergePrimitiveClosedHandoffFiniteMachineConstruction_scaffold

theorem selectedMergeRejectPrimitiveClosedHandoffConstruction_scaffold :
    exists closed : MachineDescription,
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        (SelectedMergePrimitive false)
        closed tapeCodePrimitiveCodeWordHandoffMove := by
  rcases rejectMergePrimitiveClosedHandoffConstruction_finite_scaffold with
    ⟨closed, hclosed⟩
  refine ⟨closed, ?_⟩
  exact
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_congr
      (P := RejectMergePrimitive)
      (Q := SelectedMergePrimitive false)
      (D := closed)
      (handoffMove := tapeCodePrimitiveCodeWordHandoffMove)
      (by
        intro code
        rfl)
      hclosed

theorem selectedMergeAcceptPrimitiveClosedHandoffConstruction_scaffold :
    exists closed : MachineDescription,
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        (SelectedMergePrimitive true)
        closed tapeCodePrimitiveCodeWordHandoffMove := by
  rcases acceptMergePrimitiveClosedHandoffConstruction_finite_scaffold with
    ⟨closed, hclosed⟩
  refine ⟨closed, ?_⟩
  exact
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_congr
      (P := AcceptMergePrimitive)
      (Q := SelectedMergePrimitive true)
      (D := closed)
      (handoffMove := tapeCodePrimitiveCodeWordHandoffMove)
      (by
        intro code
        rfl)
      hclosed

theorem selectedMergePrimitiveClosedHandoffConstruction_scaffold :
    SelectedMergePrimitiveClosedHandoffConstruction := by
  intro useAccept
  cases useAccept
  · exact selectedMergeRejectPrimitiveClosedHandoffConstruction_scaffold
  · exact selectedMergeAcceptPrimitiveClosedHandoffConstruction_scaffold

theorem acceptProjectionPrimitiveClosedHandoffConstruction_scaffold :
    AcceptProjectionPrimitiveClosedHandoffConstruction := by
  exact
    acceptProjectionPrimitiveClosedHandoffConstruction_of_selected
      selectedProjectionPrimitiveClosedHandoffConstruction_scaffold

theorem acceptMergePrimitiveClosedHandoffConstruction_scaffold :
    AcceptMergePrimitiveClosedHandoffConstruction := by
  exact acceptMergePrimitiveClosedHandoffConstruction_finite_scaffold

theorem rejectProjectionPrimitiveClosedHandoffConstruction_scaffold :
    RejectProjectionPrimitiveClosedHandoffConstruction := by
  exact
    rejectProjectionPrimitiveClosedHandoffConstruction_of_selected
      selectedProjectionPrimitiveClosedHandoffConstruction_scaffold

theorem rejectMergePrimitiveClosedHandoffConstruction_scaffold :
    RejectMergePrimitiveClosedHandoffConstruction := by
  exact rejectMergePrimitiveClosedHandoffConstruction_finite_scaffold

theorem configRunnerPrimitiveClosedHandoffConstruction_scaffold :
    ConfigRunnerPrimitiveClosedHandoffConstruction := by
  exact
    configRunnerPrimitiveClosedHandoffConstruction_of_parts
      acceptProjectionPrimitiveClosedHandoffConstruction_scaffold
      acceptMergePrimitiveClosedHandoffConstruction_scaffold
      rejectProjectionPrimitiveClosedHandoffConstruction_scaffold
      rejectMergePrimitiveClosedHandoffConstruction_scaffold

theorem configRunnerPhaseConstruction_scaffold :
    ConfigRunnerPhaseConstruction :=
  configRunnerPhaseConstruction_of_primitiveClosedHandoff
    fixedDescriptionBoundedSimulatorCanonicalConstruction_scaffold_configRunner
    configRunnerPrimitiveClosedHandoffConstruction_scaffold

def ConfigRunnerFromClosedHandoff
    (closed : MachineDescription) : MachineDescription :=
  MachineDescription.seqSubroutine closed
    MachineDescription.ExactIdentityDescription
    tapeCodePrimitiveCodeWordHandoffMove

theorem exactIdentityDescription_reaches_configRunner
    (T : Tape Bool) :
    exists n : Nat,
      MachineDescription.ExactIdentityDescription.runConfig n
          { state := MachineDescription.ExactIdentityDescription.start
            tape := T } =
        { state := MachineDescription.ExactIdentityDescription.halt
          tape := T } :=
  ⟨0, rfl⟩

theorem exactIdentityDescription_runConfig_from_start_configRunner
    (n : Nat) (T : Tape Bool) :
    MachineDescription.ExactIdentityDescription.runConfig n
        { state := MachineDescription.ExactIdentityDescription.start
          tape := T } =
      { state := MachineDescription.ExactIdentityDescription.halt
        tape := T } := by
  cases n <;>
    simp [MachineDescription.ExactIdentityDescription,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition]

theorem configRunnerFromClosedHandoff_spec
    {accept reject closed : MachineDescription}
    (hclosed :
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        (PairedRecognizerDovetailLayoutCode accept reject)
        closed tapeCodePrimitiveCodeWordHandoffMove) :
    AcceptRejectConfigRunnerSpec accept reject
      (ConfigRunnerFromClosedHandoff closed) := by
  let identity := MachineDescription.ExactIdentityDescription
  have hclosedReady : closed.SubroutineReady :=
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_subroutineReady
      hclosed
  have hidentityReady : identity.SubroutineReady :=
    ⟨MachineDescription.exactIdentityDescription_wellFormed,
      MachineDescription.exactIdentityDescription_haltTransitionFree⟩
  constructor
  · exact
      MachineDescription.seqSubroutine_subroutineReady
        hclosedReady hidentityReady
  constructor
  · intro L
    have htransform :
        (PairedRecognizerDovetailLayoutCode accept reject).transform
            (MachineDescription.DovetailLayout.encode L) =
          some
            (MachineDescription.DovetailLayout.encode
              (BoundedRunLayout accept reject L)) := by
      simpa [PairedRecognizerDovetailLayoutCode,
        BoundedRunLayout] using
        MachineDescription.DovetailLayout.runCodePrimitive_encode
          accept reject L
    rcases
        (tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_handoffRealized
          hclosed).right
          (MachineDescription.DovetailLayout.encode L)
          (MachineDescription.DovetailLayout.encode
            (BoundedRunLayout accept reject L))
          htransform with
      ⟨Tmid, hclosedHalt, hhandoff⟩
    have hidentityReach :
        exists nB : Nat,
          identity.runConfig nB
              { state := identity.start
                tape := Tape.move tapeCodePrimitiveCodeWordHandoffMove Tmid } =
            { state := identity.halt
              tape := ConfigRunnerOutputTape accept reject L } := by
      refine ⟨0, ?_⟩
      have hinput :
          Tape.move tapeCodePrimitiveCodeWordHandoffMove Tmid =
            ConfigRunnerOutputTape accept reject L := by
        simpa [ConfigRunnerOutputTape, ParsedLayoutTape,
          ParsedLayoutBits, ConfigRunnerOutputBits] using hhandoff
      rw [hinput]
      rfl
    simpa [ConfigRunnerFromClosedHandoff, identity,
      tapeCodePrimitiveCodeWordHandoffMove] using
      MachineDescription.seqSubroutine_haltsWithTape_of_haltsWithTape
        (A := closed) (B := identity)
        (handoffMove := tapeCodePrimitiveCodeWordHandoffMove)
        hclosedReady hidentityReady hclosedHalt hidentityReach
  · intro L T hhalt
    rcases
        MachineDescription.seqSubroutine_haltsWithTape_inv
          (A := closed) (B := identity)
          (handoffMove := tapeCodePrimitiveCodeWordHandoffMove)
          hclosedReady hidentityReady
          (by simpa [ConfigRunnerFromClosedHandoff, identity] using hhalt) with
      ⟨Tmid, hclosedHalt, hidentityReach⟩
    rcases
        hclosed.right
          (MachineDescription.DovetailLayout.encode L)
          Tmid hclosedHalt with
      ⟨out, htransform, _hnormalized, hhandoff⟩
    have htransformExpected :
        (PairedRecognizerDovetailLayoutCode accept reject).transform
            (MachineDescription.DovetailLayout.encode L) =
          some
            (MachineDescription.DovetailLayout.encode
              (BoundedRunLayout accept reject L)) := by
      simpa [PairedRecognizerDovetailLayoutCode,
        BoundedRunLayout] using
        MachineDescription.DovetailLayout.runCodePrimitive_encode
          accept reject L
    have hout :
        out =
          MachineDescription.DovetailLayout.encode
            (BoundedRunLayout accept reject L) := by
      rw [htransformExpected] at htransform
      cases htransform
      rfl
    rcases hidentityReach with ⟨nB, hidentityRun⟩
    have hT :
        T = Tape.move tapeCodePrimitiveCodeWordHandoffMove Tmid := by
      have hcfg :
          ({ state := identity.halt
             tape := Tape.move tapeCodePrimitiveCodeWordHandoffMove Tmid } :
            MachineDescription.Configuration) =
          { state := identity.halt, tape := T } := by
        simpa [identity] using
          ((exactIdentityDescription_runConfig_from_start_configRunner
              nB (Tape.move tapeCodePrimitiveCodeWordHandoffMove Tmid)).symm.trans
            hidentityRun)
      exact (congrArg MachineDescription.Configuration.tape hcfg).symm
    rw [hT]
    simpa [hout, ConfigRunnerOutputTape, ParsedLayoutTape,
      ParsedLayoutBits, ConfigRunnerOutputBits] using hhandoff

theorem acceptRejectConfigRunnerConstruction_of_closedHandoffConstruction
    (h :
      PairedRecognizerDovetailBoundedLayoutRunnerClosedHandoffCompiledSubroutineConstruction) :
    AcceptRejectConfigRunnerConstruction := by
  intro accept reject
  rcases h accept reject with ⟨closed, hclosed⟩
  exact
    ⟨ConfigRunnerFromClosedHandoff closed,
      configRunnerFromClosedHandoff_spec hclosed⟩

theorem acceptRejectConfigRunnerConstruction_scaffold :
    AcceptRejectConfigRunnerConstruction := by
  exact
    acceptRejectConfigRunnerConstruction_of_phaseConstruction
      configRunnerPhaseConstruction_scaffold

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC

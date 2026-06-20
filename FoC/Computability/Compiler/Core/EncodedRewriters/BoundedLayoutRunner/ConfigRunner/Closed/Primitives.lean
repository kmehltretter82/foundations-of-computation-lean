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

theorem SelectedMergePrimitive_transform_eq_some_cons
    {useAccept : Bool} {code out : Word MachineCodeSymbol}
    (h : (SelectedMergePrimitive useAccept).transform code = some out) :
    exists tail : Word MachineCodeSymbol,
      out = MachineCodeSymbol.transition :: tail := by
  cases useAccept
  · exact
      RejectMergePrimitive_transform_eq_some_cons
        (by
          simpa [SelectedMergePrimitive, SelectedMergeSimulatorResult,
            RejectMergePrimitive] using h)
  · exact
      AcceptMergePrimitive_transform_eq_some_cons
        (by
          simpa [SelectedMergePrimitive, SelectedMergeSimulatorResult,
            AcceptMergePrimitive] using h)

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

def SelectedProjectionOutputCode
    (useAccept : Bool)
    (L : MachineDescription.DovetailLayout) :
    Word MachineCodeSymbol :=
  MachineDescription.SimulatorLayout.encode
    (SelectedProjectionSimulatorLayout useAccept L)

def SelectedProjectionOutputTape
    (useAccept : Bool)
    (L : MachineDescription.DovetailLayout) :
    Tape Bool :=
  Tape.move Direction.right
    (Tape.input
      (MachineDescription.encodeCodeWordAsInput
        (SelectedProjectionOutputCode useAccept L)))

def SelectedProjectionForwardSpec
    (useAccept : Bool)
    (runner : MachineDescription) : Prop :=
  forall L : MachineDescription.DovetailLayout,
    runner.HaltsWithTape
      (ParsedLayoutBits L)
      (SelectedProjectionOutputTape useAccept L)

def SelectedProjectionClosedSpec
    (useAccept : Bool)
    (runner : MachineDescription) : Prop :=
  forall code : Word MachineCodeSymbol,
  forall T : Tape Bool,
    runner.HaltsWithTape
        (MachineDescription.encodeCodeWordAsInput code) T ->
      exists L : MachineDescription.DovetailLayout,
        code = MachineDescription.DovetailLayout.encode L ∧
          T = SelectedProjectionOutputTape useAccept L

def SelectedProjectionSpec
    (useAccept : Bool)
    (runner : MachineDescription) : Prop :=
  ReadySpec runner ∧
    SelectedProjectionForwardSpec useAccept runner ∧
      SelectedProjectionClosedSpec useAccept runner

def SelectedProjectionFiniteDescriptionConstruction : Prop :=
  forall useAccept : Bool,
    exists runner : MachineDescription,
      SelectedProjectionSpec useAccept runner

theorem selectedProjectionRightShifted_of_spec
    {useAccept : Bool} {runner : MachineDescription}
    (hrunner : SelectedProjectionSpec useAccept runner) :
    RightShiftedOutputCompiledSubroutineByDescription
      (SelectedProjectionPrimitive useAccept) runner := by
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
      have hout :
          out = SelectedProjectionOutputCode useAccept L :=
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
      simpa [SelectedProjectionOutputTape, SelectedProjectionOutputCode,
        EncodedRewriters.tape_normalizedOutput_move_right_input] using
        MachineDescription.haltsWithOutput_of_haltsWithTape
          (hrunner.right.left L)
  · intro code T hhalt
    rcases hrunner.right.right code T hhalt with
      ⟨L, hcode, hT⟩
    refine ⟨SelectedProjectionOutputCode useAccept L, ?_, hT⟩
    exact
      (SelectedProjectionPrimitive_transform_eq_some_iff
        useAccept code (SelectedProjectionOutputCode useAccept L)).mpr
        ⟨L, hcode, by simp [SelectedProjectionOutputCode]⟩

def SelectedMergeOutputCode
    (useAccept : Bool)
    (S : MachineDescription.SimulatorLayout)
    (L : MachineDescription.DovetailLayout) :
    Word MachineCodeSymbol :=
  MachineDescription.DovetailLayout.encode
    (if useAccept then
      { L with
        acceptConfig := S.config
        acceptHit := S.hit }
    else
      { L with
        rejectConfig := S.config
        rejectHit := S.hit })

def SelectedMergeOutputTape
    (useAccept : Bool)
    (S : MachineDescription.SimulatorLayout)
    (L : MachineDescription.DovetailLayout) :
    Tape Bool :=
  Tape.move Direction.right
    (Tape.input
      (MachineDescription.encodeCodeWordAsInput
        (SelectedMergeOutputCode useAccept S L)))

theorem SelectedMergePrimitive_transform_eq_some_iff
    (useAccept : Bool) (code out : Word MachineCodeSymbol) :
    (SelectedMergePrimitive useAccept).transform code = some out ↔
      exists S : MachineDescription.SimulatorLayout,
      exists L : MachineDescription.DovetailLayout,
        code = MachineDescription.SimulatorLayout.encode S ∧
          MachineDescription.decodeCodeWordAsInput S.input =
            some (MachineDescription.DovetailLayout.encode L) ∧
          out = SelectedMergeOutputCode useAccept S L := by
  cases useAccept
  · simpa [SelectedMergePrimitive, SelectedMergeSimulatorResult,
      RejectMergePrimitive, SelectedMergeOutputCode] using
      RejectMergePrimitive_transform_eq_some_iff code out
  · simpa [SelectedMergePrimitive, SelectedMergeSimulatorResult,
      AcceptMergePrimitive, SelectedMergeOutputCode] using
      AcceptMergePrimitive_transform_eq_some_iff code out

def SelectedMergeForwardSpec
    (useAccept : Bool)
    (runner : MachineDescription) : Prop :=
  forall S : MachineDescription.SimulatorLayout,
  forall L : MachineDescription.DovetailLayout,
    MachineDescription.decodeCodeWordAsInput S.input =
      some (MachineDescription.DovetailLayout.encode L) ->
    runner.HaltsWithTape
      (MachineDescription.SimulatorLayout.asBoolInput S)
      (SelectedMergeOutputTape useAccept S L)

def SelectedMergeClosedSpec
    (useAccept : Bool)
    (runner : MachineDescription) : Prop :=
  forall code : Word MachineCodeSymbol,
  forall T : Tape Bool,
    runner.HaltsWithTape
        (MachineDescription.encodeCodeWordAsInput code) T ->
      exists S : MachineDescription.SimulatorLayout,
      exists L : MachineDescription.DovetailLayout,
        code = MachineDescription.SimulatorLayout.encode S ∧
          MachineDescription.decodeCodeWordAsInput S.input =
            some (MachineDescription.DovetailLayout.encode L) ∧
          T = SelectedMergeOutputTape useAccept S L

def SelectedMergeSpec
    (useAccept : Bool)
    (runner : MachineDescription) : Prop :=
  ReadySpec runner ∧
    SelectedMergeForwardSpec useAccept runner ∧
      SelectedMergeClosedSpec useAccept runner

def SelectedMergeFiniteDescriptionConstruction : Prop :=
  forall useAccept : Bool,
    exists runner : MachineDescription,
      SelectedMergeSpec useAccept runner

theorem selectedMergeRightShifted_of_spec
    {useAccept : Bool} {runner : MachineDescription}
    (hrunner : SelectedMergeSpec useAccept runner) :
    RightShiftedOutputCompiledSubroutineByDescription
      (SelectedMergePrimitive useAccept) runner := by
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
        ⟨S, L, hcode, hinput, hT⟩
      have hactual :
          Tape.normalizedOutput T =
            MachineDescription.encodeCodeWordAsInput out := by
        simpa [T] using hn.right
      have hexpected :
          Tape.normalizedOutput T =
            MachineDescription.encodeCodeWordAsInput
              (SelectedMergeOutputCode useAccept S L) := by
        rw [hT]
        exact
          EncodedRewriters.tape_normalizedOutput_move_right_input
            (MachineDescription.encodeCodeWordAsInput
              (SelectedMergeOutputCode useAccept S L))
      have houtBits :
          MachineDescription.encodeCodeWordAsInput out =
            MachineDescription.encodeCodeWordAsInput
              (SelectedMergeOutputCode useAccept S L) :=
        hactual.symm.trans hexpected
      have hout :
          out = SelectedMergeOutputCode useAccept S L :=
        MachineDescription.encodeCodeWordAsInput_injective houtBits
      exact
        (SelectedMergePrimitive_transform_eq_some_iff
          useAccept code out).mpr
          ⟨S, L, hcode, hinput, hout⟩
    · intro htransform
      rcases
          (SelectedMergePrimitive_transform_eq_some_iff
            useAccept code out).mp htransform with
        ⟨S, L, hcode, hinput, hout⟩
      subst code
      subst out
      simpa [SelectedMergeOutputTape,
        EncodedRewriters.tape_normalizedOutput_move_right_input] using
        MachineDescription.haltsWithOutput_of_haltsWithTape
          (hrunner.right.left S L hinput)
  · intro code T hhalt
    rcases hrunner.right.right code T hhalt with
      ⟨S, L, hcode, hinput, hT⟩
    refine ⟨SelectedMergeOutputCode useAccept S L, ?_, hT⟩
    exact
      (SelectedMergePrimitive_transform_eq_some_iff
        useAccept code (SelectedMergeOutputCode useAccept S L)).mpr
        ⟨S, L, hcode, hinput, rfl⟩


end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC

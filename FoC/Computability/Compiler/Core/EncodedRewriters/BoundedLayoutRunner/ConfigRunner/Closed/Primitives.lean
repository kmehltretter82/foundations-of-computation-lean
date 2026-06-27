import FoC.Computability.Compiler.SeqSubroutineSemantics
import FoC.Computability.Compiler.Core.ConstructionTargets
import FoC.Computability.Compiler.Core.CommonGround.CodeWordEmitters
import FoC.Computability.Compiler.Core.FixedDescriptionBoundedSimulator.Skeleton
import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Basic

set_option doc.verso true

/-!
# Bounded config-runner primitive rewrites

Projection extracts one recognizer configuration from a dovetail layout; merge
writes the simulated result back into that layout.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

def AcceptSimulatorLayout
    (L : DovetailLayout) :
    SimulatorLayout where
  input := ParsedLayoutBits L
  stage := L.stage
  config := L.acceptConfig
  hit := L.acceptHit

def RejectSimulatorLayout
    (L : DovetailLayout) :
    SimulatorLayout where
  input := ParsedLayoutBits L
  stage := L.stage
  config := L.rejectConfig
  hit := L.rejectHit

def MergeAcceptSimulatorResult
    (S : SimulatorLayout) :
    Option DovetailLayout :=
  match decodeCodeWordAsInput S.input with
  | none => none
  | some code =>
      match DovetailLayout.decodeComplete code with
      | none => none
      | some L =>
          some { L with
            acceptConfig := S.config
            acceptHit := S.hit }

def MergeRejectSimulatorResult
    (S : SimulatorLayout) :
    Option DovetailLayout :=
  match decodeCodeWordAsInput S.input with
  | none => none
  | some code =>
      match DovetailLayout.decodeComplete code with
      | none => none
      | some L =>
          some { L with
            rejectConfig := S.config
            rejectHit := S.hit }

def AcceptProjectionPrimitive :
    TapeCodePrimitive where
  transform := fun code =>
    match DovetailLayout.decodeComplete code with
    | none => none
    | some L =>
        some
          (SimulatorLayout.encode
            (AcceptSimulatorLayout L))

def RejectProjectionPrimitive :
    TapeCodePrimitive where
  transform := fun code =>
    match DovetailLayout.decodeComplete code with
    | none => none
    | some L =>
        some
          (SimulatorLayout.encode
            (RejectSimulatorLayout L))

def AcceptMergePrimitive :
    TapeCodePrimitive where
  transform := fun code =>
    match SimulatorLayout.decodeComplete code with
    | none => none
    | some S =>
        Option.map DovetailLayout.encode
          (MergeAcceptSimulatorResult S)

def RejectMergePrimitive :
    TapeCodePrimitive where
  transform := fun code =>
    match SimulatorLayout.decodeComplete code with
    | none => none
    | some S =>
        Option.map DovetailLayout.encode
          (MergeRejectSimulatorResult S)

def SelectedProjectionSimulatorLayout
    (useAccept : Bool)
    (L : DovetailLayout) :
    SimulatorLayout :=
  if useAccept then
    AcceptSimulatorLayout L
  else
    RejectSimulatorLayout L

def SelectedProjectionPrimitive
    (useAccept : Bool) :
    TapeCodePrimitive where
  transform := fun code =>
    match DovetailLayout.decodeComplete code with
    | none => none
    | some L =>
        some
          (SimulatorLayout.encode
            (SelectedProjectionSimulatorLayout useAccept L))

def SelectedMergeSimulatorResult
    (useAccept : Bool)
    (S : SimulatorLayout) :
    Option DovetailLayout :=
  if useAccept then
    MergeAcceptSimulatorResult S
  else
    MergeRejectSimulatorResult S

def SelectedMergePrimitive
    (useAccept : Bool) :
    TapeCodePrimitive where
  transform := fun code =>
    match SimulatorLayout.decodeComplete code with
    | none => none
    | some S =>
        Option.map DovetailLayout.encode
          (SelectedMergeSimulatorResult useAccept S)

def ConfigRunnerAfterAccept
    (accept : MachineDescription)
    (L : DovetailLayout) :
    DovetailLayout :=
  { L with
    acceptConfig :=
      accept.runConfig L.stage L.acceptConfig
    acceptHit :=
      L.acceptHit ||
        SimulatorLayout.hitsFromConfigByBool
          accept L.acceptConfig L.stage }

def ConfigRunnerAfterReject
    (reject : MachineDescription)
    (L : DovetailLayout) :
    DovetailLayout :=
  { L with
    rejectConfig :=
      reject.runConfig L.stage L.rejectConfig
    rejectHit :=
      L.rejectHit ||
        SimulatorLayout.hitsFromConfigByBool
          reject L.rejectConfig L.stage }

theorem decodeCodeWordAsInput_parsedLayoutBits
    (L : DovetailLayout) :
    decodeCodeWordAsInput (ParsedLayoutBits L) =
      some (DovetailLayout.encode L) := by
  simpa [ParsedLayoutBits] using
    decodeCodeWordAsInput_encodeCodeWordAsInput
      (DovetailLayout.encode L)

theorem MergeAcceptSimulatorResult_run
    (accept : MachineDescription)
    (L : DovetailLayout) :
    MergeAcceptSimulatorResult
        (SimulatorLayout.run
          accept L.stage (AcceptSimulatorLayout L)) =
      some (ConfigRunnerAfterAccept accept L) := by
  simp [MergeAcceptSimulatorResult, ConfigRunnerAfterAccept,
    AcceptSimulatorLayout, decodeCodeWordAsInput_parsedLayoutBits,
    DovetailLayout.decodeComplete_encode,
    SimulatorLayout.run]

theorem MergeRejectSimulatorResult_run
    (reject : MachineDescription)
    (L : DovetailLayout) :
    MergeRejectSimulatorResult
        (SimulatorLayout.run
          reject L.stage (RejectSimulatorLayout L)) =
      some (ConfigRunnerAfterReject reject L) := by
  simp [MergeRejectSimulatorResult, ConfigRunnerAfterReject,
    RejectSimulatorLayout, decodeCodeWordAsInput_parsedLayoutBits,
    DovetailLayout.decodeComplete_encode,
    SimulatorLayout.run]

theorem AcceptProjectionPrimitive_encode
    (L : DovetailLayout) :
    AcceptProjectionPrimitive.transform
        (DovetailLayout.encode L) =
      some
        (SimulatorLayout.encode
          (AcceptSimulatorLayout L)) := by
  simp [AcceptProjectionPrimitive,
    DovetailLayout.decodeComplete_encode]

theorem RejectProjectionPrimitive_encode
    (L : DovetailLayout) :
    RejectProjectionPrimitive.transform
        (DovetailLayout.encode L) =
      some
        (SimulatorLayout.encode
          (RejectSimulatorLayout L)) := by
  simp [RejectProjectionPrimitive,
    DovetailLayout.decodeComplete_encode]

theorem SelectedProjectionPrimitive_transform_eq_some_iff
    (useAccept : Bool) (code out : Word MachineCodeSymbol) :
    (SelectedProjectionPrimitive useAccept).transform code = some out ↔
      exists L : DovetailLayout,
        code = DovetailLayout.encode L ∧
          out =
            SimulatorLayout.encode
              (SelectedProjectionSimulatorLayout useAccept L) := by
  constructor
  · intro h
    unfold SelectedProjectionPrimitive at h
    cases hdecode :
        DovetailLayout.decodeComplete code with
    | none =>
        simp [hdecode] at h
    | some L =>
        simp [hdecode] at h
        cases h
        refine ⟨L, ?_, rfl⟩
        exact
          DovetailLayout.decodeComplete_eq_some_encode
            hdecode
  · intro h
    rcases h with ⟨L, rfl, rfl⟩
    simp [SelectedProjectionPrimitive,
      DovetailLayout.decodeComplete_encode]

theorem AcceptMergePrimitive_encode_run
    (accept : MachineDescription)
    (L : DovetailLayout) :
    AcceptMergePrimitive.transform
        (SimulatorLayout.encode
          (SimulatorLayout.run
            accept L.stage (AcceptSimulatorLayout L))) =
      some
        (DovetailLayout.encode
          (ConfigRunnerAfterAccept accept L)) := by
  simp [AcceptMergePrimitive,
    SimulatorLayout.decodeComplete_encode,
    MergeAcceptSimulatorResult_run]

theorem RejectMergePrimitive_encode_run
    (reject : MachineDescription)
    (L : DovetailLayout) :
    RejectMergePrimitive.transform
        (SimulatorLayout.encode
          (SimulatorLayout.run
            reject L.stage (RejectSimulatorLayout L))) =
      some
        (DovetailLayout.encode
          (ConfigRunnerAfterReject reject L)) := by
  simp [RejectMergePrimitive,
    SimulatorLayout.decodeComplete_encode,
    MergeRejectSimulatorResult_run]

theorem AcceptMergePrimitive_transform_eq_some_iff
    (code out : Word MachineCodeSymbol) :
    AcceptMergePrimitive.transform code = some out ↔
      exists S : SimulatorLayout,
        exists L : DovetailLayout,
          code = SimulatorLayout.encode S ∧
          decodeCodeWordAsInput S.input =
            some (DovetailLayout.encode L) ∧
          out =
            DovetailLayout.encode
              { L with
                acceptConfig := S.config
                acceptHit := S.hit } := by
  constructor
  · intro h
    unfold AcceptMergePrimitive at h
    cases hS : SimulatorLayout.decodeComplete code with
    | none =>
        simp [hS] at h
    | some S =>
        simp [hS] at h
        unfold MergeAcceptSimulatorResult at h
        cases hinput : decodeCodeWordAsInput S.input with
        | none =>
            simp [hinput] at h
        | some innerCode =>
            cases hL :
                DovetailLayout.decodeComplete innerCode with
            | none =>
                simp [hinput, hL] at h
            | some L =>
                simp [hinput, hL] at h
                cases h
                refine ⟨S, L, ?_, ?_, rfl⟩
                · exact
                    SimulatorLayout.decodeComplete_eq_some_encode
                      hS
                · rw [
                    DovetailLayout.decodeComplete_eq_some_encode
                      hL] at hinput
                  exact hinput
  · intro h
    rcases h with ⟨S, L, rfl, hinput, rfl⟩
    simp [AcceptMergePrimitive,
      SimulatorLayout.decodeComplete_encode,
      MergeAcceptSimulatorResult, hinput,
      DovetailLayout.decodeComplete_encode]

theorem RejectMergePrimitive_transform_eq_some_iff
    (code out : Word MachineCodeSymbol) :
    RejectMergePrimitive.transform code = some out ↔
      exists S : SimulatorLayout,
        exists L : DovetailLayout,
          code = SimulatorLayout.encode S ∧
          decodeCodeWordAsInput S.input =
            some (DovetailLayout.encode L) ∧
          out =
            DovetailLayout.encode
              { L with
                rejectConfig := S.config
                rejectHit := S.hit } := by
  constructor
  · intro h
    unfold RejectMergePrimitive at h
    cases hS : SimulatorLayout.decodeComplete code with
    | none =>
        simp [hS] at h
    | some S =>
        simp [hS] at h
        unfold MergeRejectSimulatorResult at h
        cases hinput : decodeCodeWordAsInput S.input with
        | none =>
            simp [hinput] at h
        | some innerCode =>
            cases hL :
                DovetailLayout.decodeComplete innerCode with
            | none =>
                simp [hinput, hL] at h
            | some L =>
                simp [hinput, hL] at h
                cases h
                refine ⟨S, L, ?_, ?_, rfl⟩
                · exact
                    SimulatorLayout.decodeComplete_eq_some_encode
                      hS
                · rw [
                    DovetailLayout.decodeComplete_eq_some_encode
                      hL] at hinput
                  exact hinput
  · intro h
    rcases h with ⟨S, L, rfl, hinput, rfl⟩
    simp [RejectMergePrimitive,
      SimulatorLayout.decodeComplete_encode,
      MergeRejectSimulatorResult, hinput,
      DovetailLayout.decodeComplete_encode]

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
    (L : DovetailLayout) :
    ConfigRunnerAfterReject reject
        (ConfigRunnerAfterAccept accept L) =
      BoundedRunLayout accept reject L := by
  cases L
  simp [ConfigRunnerAfterReject, ConfigRunnerAfterAccept,
    BoundedRunLayout, DovetailLayout.run]

theorem MergeRejectSimulatorResult_run_afterAccept
    (accept reject : MachineDescription)
    (L : DovetailLayout) :
    MergeRejectSimulatorResult
        (SimulatorLayout.run
          reject (ConfigRunnerAfterAccept accept L).stage
          (RejectSimulatorLayout (ConfigRunnerAfterAccept accept L))) =
      some (BoundedRunLayout accept reject L) := by
  rw [MergeRejectSimulatorResult_run]
  exact congrArg some
    (ConfigRunnerAfterReject_afterAccept accept reject L)

theorem ConfigRunnerSemanticPipeline
    (accept reject : MachineDescription)
    (L : DovetailLayout) :
    (do
      let acceptResult :=
        SimulatorLayout.run
          accept L.stage (AcceptSimulatorLayout L)
      let Laccept ← MergeAcceptSimulatorResult acceptResult
      let rejectResult :=
        SimulatorLayout.run
          reject Laccept.stage (RejectSimulatorLayout Laccept)
      MergeRejectSimulatorResult rejectResult) =
        some (BoundedRunLayout accept reject L) := by
  simp [MergeAcceptSimulatorResult_run,
    MergeRejectSimulatorResult_run_afterAccept]

theorem simulatorLayout_encode_cons
    (S : SimulatorLayout) :
    exists tail : Word MachineCodeSymbol,
      SimulatorLayout.encode S =
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
    (S : SimulatorLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (SimulatorLayout.tape S)) =
      SimulatorLayout.tape S := by
  rcases simulatorLayout_encode_cons S with ⟨tail, htail⟩
  unfold SimulatorLayout.tape
    SimulatorLayout.asBoolInput
  rw [htail]
  exact
    EncodedRewriters.tape_move_left_move_right_input_encodeCodeWordAsInput_cons
      MachineCodeSymbol.header tail

theorem parsedLayoutTape_move_left_move_right_configRunner
    (L : DovetailLayout) :
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
    (L : DovetailLayout) :
    Word MachineCodeSymbol :=
  SimulatorLayout.encode
    (SelectedProjectionSimulatorLayout useAccept L)

def SelectedProjectionOutputTape
    (useAccept : Bool)
    (L : DovetailLayout) :
    Tape Bool :=
  Tape.move Direction.right
    (Tape.input
      (encodeCodeWordAsInput
        (SelectedProjectionOutputCode useAccept L)))

def SelectedProjectionForwardSpec
    (useAccept : Bool)
    (runner : MachineDescription) : Prop :=
  forall L : DovetailLayout,
    runner.HaltsFromTapeEquiv
      (Tape.input (ParsedLayoutBits L))
      (SelectedProjectionOutputTape useAccept L)

def SelectedProjectionClosedSpec
    (useAccept : Bool)
    (runner : MachineDescription) : Prop :=
  forall code : Word MachineCodeSymbol,
  forall T : Tape Bool,
    runner.HaltsFromTape
        (Tape.input (encodeCodeWordAsInput code)) T ->
      exists L : DovetailLayout,
        code = DovetailLayout.encode L ∧
          Tape.Equiv T (SelectedProjectionOutputTape useAccept L)

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

def SelectedMergeOutputCode
    (useAccept : Bool)
    (S : SimulatorLayout)
    (L : DovetailLayout) :
    Word MachineCodeSymbol :=
  DovetailLayout.encode
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
    (S : SimulatorLayout)
    (L : DovetailLayout) :
    Tape Bool :=
  Tape.move Direction.right
    (Tape.input
      (encodeCodeWordAsInput
        (SelectedMergeOutputCode useAccept S L)))

theorem SelectedMergePrimitive_transform_eq_some_iff
    (useAccept : Bool) (code out : Word MachineCodeSymbol) :
    (SelectedMergePrimitive useAccept).transform code = some out ↔
      exists S : SimulatorLayout,
      exists L : DovetailLayout,
        code = SimulatorLayout.encode S ∧
          decodeCodeWordAsInput S.input =
            some (DovetailLayout.encode L) ∧
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
  forall S : SimulatorLayout,
  forall L : DovetailLayout,
    decodeCodeWordAsInput S.input =
      some (DovetailLayout.encode L) ->
    runner.HaltsWithTape
      (SimulatorLayout.asBoolInput S)
      (SelectedMergeOutputTape useAccept S L)

def SelectedMergeClosedSpec
    (useAccept : Bool)
    (runner : MachineDescription) : Prop :=
  forall code : Word MachineCodeSymbol,
  forall T : Tape Bool,
    runner.HaltsWithTape
        (encodeCodeWordAsInput code) T ->
      exists S : SimulatorLayout,
      exists L : DovetailLayout,
        code = SimulatorLayout.encode S ∧
          decodeCodeWordAsInput S.input =
            some (DovetailLayout.encode L) ∧
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
  let Index : Type :=
    { pair :
        SimulatorLayout ×
          DovetailLayout //
      decodeCodeWordAsInput pair.1.input =
        some (DovetailLayout.encode pair.2) }
  exact
    CommonGround.CodeWordEmitters.rightShiftedOutputCompiled_of_indexed_tape_spec
      (ι := Index)
      hrunner.left.left
      hrunner.left.right
      (fun i => SimulatorLayout.encode i.1.1)
      (fun i => SelectedMergeOutputCode useAccept i.1.1 i.1.2)
      (fun i => SelectedMergeOutputTape useAccept i.1.1 i.1.2)
      (by
        intro i
        simp [SelectedMergeOutputTape])
      (by
        intro i
        rcases i with ⟨⟨S, L⟩, hinput⟩
        exact hrunner.right.left S L hinput)
      (by
        intro code T hhalt
        rcases hrunner.right.right code T hhalt with
          ⟨S, L, hcode, hinput, hT⟩
        exact ⟨⟨⟨S, L⟩, hinput⟩, hcode, hT⟩)
      (by
        intro code out
        constructor
        · intro htransform
          rcases
              (SelectedMergePrimitive_transform_eq_some_iff
                useAccept code out).mp htransform with
            ⟨S, L, hcode, hinput, hout⟩
          exact ⟨⟨⟨S, L⟩, hinput⟩, hcode, hout⟩
        · intro htransform
          rcases htransform with
            ⟨⟨⟨S, L⟩, hinput⟩, hcode, hout⟩
          exact
            (SelectedMergePrimitive_transform_eq_some_iff
              useAccept code out).mpr
              ⟨S, L, hcode, hinput, hout⟩)


end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC

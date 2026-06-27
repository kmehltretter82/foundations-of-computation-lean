import FoC.Computability.Compiler.Core.CommonGround
import FoC.Computability.Compiler.Core.ConstructionTargets

set_option doc.verso true

/-!
# Controller Result Continuation

This module isolates the finite-machine leaf for the controller continuation
subroutine.  The machine recognizes successful
{name (full := FoC.Computability.PairedRecognizerDovetailControllerResultContinueCode)}`PairedRecognizerDovetailControllerResultContinueCode`
transforms over canonical encoded code words.
-/

namespace FoC
namespace Computability

open Languages

/--
Construction data for the controller continuation subroutine, stated directly
against the code-word transform.  Later scaffolds adapt this data to the public
controller-loop contract.
-/
def ControllerResultContinueConstructionData : Prop :=
  exists continuer : MachineDescription,
    continuer.SubroutineReady ∧
      (forall code out : Word MachineCodeSymbol,
        PairedRecognizerDovetailControllerResultContinueCode.transform code =
            some out ->
          continuer.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput code)
            (MachineDescription.encodeCodeWordAsInput out)) ∧
      (forall code out : Word MachineCodeSymbol,
        continuer.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput code)
            (MachineDescription.encodeCodeWordAsInput out) ->
          PairedRecognizerDovetailControllerResultContinueCode.transform code = some out)

def ControllerResultContinueForwardSpec
    (continuer : MachineDescription) : Prop :=
  forall code out : Word MachineCodeSymbol,
    PairedRecognizerDovetailControllerResultContinueCode.transform code =
        some out ->
      continuer.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out)

def ControllerResultContinueClosedSpec
    (continuer : MachineDescription) : Prop :=
  forall code out : Word MachineCodeSymbol,
    continuer.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out) ->
      PairedRecognizerDovetailControllerResultContinueCode.transform code =
        some out

def ControllerResultContinueSpec
    (continuer : MachineDescription) : Prop :=
  continuer.SubroutineReady ∧
    ControllerResultContinueForwardSpec continuer ∧
      ControllerResultContinueClosedSpec continuer

def ControllerResultContinueCanonicalForwardSpec
    (continuer : MachineDescription) : Prop :=
  forall C : MachineDescription.DovetailControllerLayout,
    PairedRecognizerDovetailControllerRawOutput C.result = none ->
      continuer.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.DovetailControllerLayout.encode C))
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.DovetailControllerLayout.encode
            (MachineDescription.DovetailControllerLayout.nextStage C)))

def ControllerResultContinueClosedLayoutSpec
    (continuer : MachineDescription) : Prop :=
  forall code out : Word MachineCodeSymbol,
    continuer.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out) ->
      exists C : MachineDescription.DovetailControllerLayout,
        code = MachineDescription.DovetailControllerLayout.encode C ∧
          PairedRecognizerDovetailControllerRawOutput C.result = none ∧
            out =
              MachineDescription.DovetailControllerLayout.encode
                (MachineDescription.DovetailControllerLayout.nextStage C)

def ControllerResultContinueComponentSpec
    (continuer : MachineDescription) : Prop :=
  continuer.SubroutineReady ∧
    ControllerResultContinueCanonicalForwardSpec continuer ∧
      ControllerResultContinueClosedLayoutSpec continuer

def ControllerResultContinueComponentConstruction : Prop :=
  exists continuer : MachineDescription,
    ControllerResultContinueComponentSpec continuer

namespace ControllerResultContinueConstruction

def ResultNoneGuardPrimitive : MachineDescription.TapeCodePrimitive where
  transform := fun code =>
    match MachineDescription.DovetailControllerLayout.decodeComplete code with
    | none => none
    | some C =>
        match PairedRecognizerDovetailControllerRawOutput C.result with
        | none => some code
        | some _ => none

def StageInputContinuePrimitive : MachineDescription.TapeCodePrimitive where
  transform := fun code =>
    match MachineDescription.DovetailLayout.decodeStageInputComplete code with
    | none => none
    | some (input, stage) =>
        some
          (MachineDescription.DovetailControllerLayout.encode
            { input := input, stage := stage + 1, result := [] })

def DecomposedResultContinuePrimitive : MachineDescription.TapeCodePrimitive :=
  MachineDescription.TapeCodePrimitive.compose
    (MachineDescription.TapeCodePrimitive.compose
      ResultNoneGuardPrimitive
      PairedRecognizerDovetailControllerStageInputCodePrimitive)
    StageInputContinuePrimitive

theorem nextStage_encode_eq_header_input_succ_empty
    (C : MachineDescription.DovetailControllerLayout) :
    MachineDescription.DovetailControllerLayout.encode
        (MachineDescription.DovetailControllerLayout.nextStage C) =
      MachineCodeSymbol.header ::
        MachineDescription.encodeBoolWordAppend C.input
          (MachineDescription.encodeNatAppend (C.stage + 1)
            (MachineDescription.encodeBoolWordAppend [] [])) := by
  cases C
  rfl

theorem rawOutput_eq_none_iff_empty_or_multi
    (result : Word Bool) :
    PairedRecognizerDovetailControllerRawOutput result = none <->
      result = [] ∨
        exists first second rest, result = first :: second :: rest := by
  constructor
  · intro h
    cases result with
    | nil =>
        exact Or.inl rfl
    | cons first tail =>
        cases tail with
        | nil =>
            simp [PairedRecognizerDovetailControllerRawOutput,
              MachineDescription.DovetailControllerLayout.rawOutput?] at h
        | cons second rest =>
            exact Or.inr ⟨first, second, rest, rfl⟩
  · intro h
    rcases h with rfl | ⟨first, second, rest, rfl⟩
    · rfl
    · rfl

theorem resultNoneGuardPrimitive_transform_eq_some_iff
    (code out : Word MachineCodeSymbol) :
    ResultNoneGuardPrimitive.transform code = some out <->
      exists C : MachineDescription.DovetailControllerLayout,
        code = MachineDescription.DovetailControllerLayout.encode C ∧
          PairedRecognizerDovetailControllerRawOutput C.result = none ∧
            out = code := by
  constructor
  · intro h
    unfold ResultNoneGuardPrimitive at h
    cases hdecode :
        MachineDescription.DovetailControllerLayout.decodeComplete code with
    | none =>
        simp [hdecode] at h
    | some C =>
        cases hraw :
            PairedRecognizerDovetailControllerRawOutput C.result with
        | none =>
            simp [hdecode, hraw] at h
            subst out
            exact
              ⟨C,
                MachineDescription.DovetailControllerLayout.decodeComplete_eq_some_encode
                  hdecode,
                hraw,
                rfl⟩
        | some result =>
            simp [hdecode, hraw] at h
  · intro h
    rcases h with ⟨C, rfl, hraw, rfl⟩
    unfold ResultNoneGuardPrimitive
    simp [MachineDescription.DovetailControllerLayout.decodeComplete_encode,
      hraw]

theorem stageInputContinuePrimitive_transform_eq_some_iff
    (code out : Word MachineCodeSymbol) :
    StageInputContinuePrimitive.transform code = some out <->
      exists input : Word Bool,
      exists stage : Nat,
        code = MachineDescription.DovetailLayout.stageInputCode input stage ∧
          out =
            MachineDescription.DovetailControllerLayout.encode
              { input := input, stage := stage + 1, result := [] } := by
  constructor
  · intro h
    unfold StageInputContinuePrimitive at h
    cases hdecode :
        MachineDescription.DovetailLayout.decodeStageInputComplete code with
    | none =>
        simp [hdecode] at h
    | some parsed =>
        rcases parsed with ⟨input, stage⟩
        simp [hdecode] at h
        subst out
        exact
          ⟨input, stage,
            MachineDescription.DovetailLayout.decodeStageInputComplete_eq_some_stageInputCode
              hdecode,
            rfl⟩
  · intro h
    rcases h with ⟨input, stage, rfl, rfl⟩
    unfold StageInputContinuePrimitive
    simp [MachineDescription.DovetailLayout.decodeStageInputComplete_stageInputCode]

theorem stageInputContinuePrimitive_stageInputCode
    (C : MachineDescription.DovetailControllerLayout) :
    StageInputContinuePrimitive.transform
        (PairedRecognizerDovetailControllerStageInputCode C) =
      some
        (MachineDescription.DovetailControllerLayout.encode
          (MachineDescription.DovetailControllerLayout.nextStage C)) := by
  rcases C with ⟨input, stage, result⟩
  change
    StageInputContinuePrimitive.transform
        (MachineDescription.DovetailLayout.stageInputCode input stage) =
      some
        (MachineDescription.DovetailControllerLayout.encode
          { input := input, stage := stage + 1, result := [] })
  simp [StageInputContinuePrimitive,
    MachineDescription.DovetailLayout.decodeStageInputComplete_stageInputCode]

theorem decomposedResultContinuePrimitive_transform_eq
    (code : Word MachineCodeSymbol) :
    DecomposedResultContinuePrimitive.transform code =
      PairedRecognizerDovetailControllerResultContinueCode.transform code := by
  unfold DecomposedResultContinuePrimitive
  unfold MachineDescription.TapeCodePrimitive.compose
  unfold ResultNoneGuardPrimitive
  unfold StageInputContinuePrimitive
  unfold PairedRecognizerDovetailControllerStageInputCodePrimitive
  unfold PairedRecognizerDovetailControllerResultContinueCode
  unfold MachineDescription.DovetailControllerLayout.continueResultCodePrimitive
  unfold MachineDescription.DovetailControllerLayout.continueResultCode
  cases hdecode :
      MachineDescription.DovetailControllerLayout.decodeComplete code with
  | none =>
      simp [hdecode]
  | some C =>
      cases hraw :
          PairedRecognizerDovetailControllerRawOutput C.result with
      | none =>
          have hrawLayout :
              MachineDescription.DovetailControllerLayout.rawOutput?
                  C.result = none := by
            simpa [PairedRecognizerDovetailControllerRawOutput] using hraw
          have hstage :
              MachineDescription.DovetailLayout.decodeStageInputComplete
                  (PairedRecognizerDovetailControllerStageInputCode C) =
                some (C.input, C.stage) := by
            rcases C with ⟨input, stage, result⟩
            change
              MachineDescription.DovetailLayout.decodeStageInputComplete
                  (MachineDescription.DovetailLayout.stageInputCode
                    input stage) =
                some (input, stage)
            exact
              MachineDescription.DovetailLayout.decodeStageInputComplete_stageInputCode
                input stage
          simp [hdecode, hraw, hrawLayout, hstage]
          cases C
          simp [MachineDescription.DovetailControllerLayout.nextStage]
      | some out =>
          have hrawLayout :
              MachineDescription.DovetailControllerLayout.rawOutput?
                  C.result = some out := by
            simpa [PairedRecognizerDovetailControllerRawOutput] using hraw
          simp [hdecode, hraw, hrawLayout]

end ControllerResultContinueConstruction

theorem controllerResultContinueForwardSpec_of_canonical
    {continuer : MachineDescription}
    (hforward :
      ControllerResultContinueCanonicalForwardSpec continuer) :
    ControllerResultContinueForwardSpec continuer := by
  intro code out htransform
  rcases
      (CommonGround.ControllerLayouts.resultContinue_transform_eq_some_iff
        code out).mp htransform with
    ⟨C, rfl, hraw, rfl⟩
  exact hforward C hraw

theorem controllerResultContinueClosedSpec_of_layout
    {continuer : MachineDescription}
    (hclosed :
      ControllerResultContinueClosedLayoutSpec continuer) :
    ControllerResultContinueClosedSpec continuer := by
  intro code out hhalt
  rcases hclosed code out hhalt with
    ⟨C, rfl, hraw, rfl⟩
  exact
    (CommonGround.ControllerLayouts.resultContinue_encode_nextStage_iff
      (C := C)).mpr hraw

theorem controllerResultContinueSpec_of_components
    {continuer : MachineDescription}
    (h : ControllerResultContinueComponentSpec continuer) :
    ControllerResultContinueSpec continuer := by
  rcases h with ⟨hready, hforward, hclosed⟩
  exact
    ⟨hready,
      controllerResultContinueForwardSpec_of_canonical hforward,
      controllerResultContinueClosedSpec_of_layout hclosed⟩

theorem controllerResultContinueConstructionData_of_spec
    {continuer : MachineDescription}
    (h : ControllerResultContinueSpec continuer) :
    ControllerResultContinueConstructionData := by
  rcases h with ⟨hready, hforward, hclosed⟩
  exact ⟨continuer, hready, hforward, hclosed⟩

theorem controllerResultContinueConstructionData_of_components
    (h : ControllerResultContinueComponentConstruction) :
    ControllerResultContinueConstructionData := by
  rcases h with ⟨continuer, hcomponents⟩
  exact
    controllerResultContinueConstructionData_of_spec
      (controllerResultContinueSpec_of_components hcomponents)

theorem controllerResultContinueComponentConstruction_scaffold :
    ControllerResultContinueComponentConstruction := by
  sorry

theorem controllerResultContinueConstruction_scaffold :
    ControllerResultContinueConstructionData := by
  exact
    controllerResultContinueConstructionData_of_components
      controllerResultContinueComponentConstruction_scaffold

end Computability
end FoC

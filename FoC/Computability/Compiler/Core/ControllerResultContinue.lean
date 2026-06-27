import FoC.Computability.Compiler.Core.CommonGround
import FoC.Computability.Compiler.Core.ConstructionTargets
import FoC.Computability.Compiler.Core.ControllerStageInputProjection

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

def GuardProjectionPrimitive : MachineDescription.TapeCodePrimitive :=
  MachineDescription.TapeCodePrimitive.compose
    ResultNoneGuardPrimitive
    PairedRecognizerDovetailControllerStageInputCodePrimitive

def DecomposedResultContinuePrimitive : MachineDescription.TapeCodePrimitive :=
  MachineDescription.TapeCodePrimitive.compose
    GuardProjectionPrimitive
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

theorem guardProjectionPrimitive_transform_eq_some_iff
    (code out : Word MachineCodeSymbol) :
    GuardProjectionPrimitive.transform code = some out <->
      exists C : MachineDescription.DovetailControllerLayout,
        code = MachineDescription.DovetailControllerLayout.encode C ∧
          PairedRecognizerDovetailControllerRawOutput C.result = none ∧
            out = PairedRecognizerDovetailControllerStageInputCode C := by
  constructor
  · intro h
    unfold GuardProjectionPrimitive at h
    unfold MachineDescription.TapeCodePrimitive.compose at h
    cases hguard : ResultNoneGuardPrimitive.transform code with
    | none =>
        simp [hguard] at h
    | some mid =>
        have hstage :
            PairedRecognizerDovetailControllerStageInputCodePrimitive.transform
                mid = some out := by
          simpa [hguard] using h
        rcases
            (resultNoneGuardPrimitive_transform_eq_some_iff
              code mid).mp hguard with
          ⟨C, hcode, hraw, hmid⟩
        subst mid
        subst code
        have hout :
            out = PairedRecognizerDovetailControllerStageInputCode C := by
          rcases
              (pairedRecognizerDovetailControllerStageInputCode_transform_eq_some_iff
                (MachineDescription.DovetailControllerLayout.encode C)
                out).mp hstage with
            ⟨C', hencode, hout⟩
          have hC' : C' = C := by
            have hdecodeC' :
                MachineDescription.DovetailControllerLayout.decodeComplete
                    (MachineDescription.DovetailControllerLayout.encode C) =
                  some C' := by
              rw [hencode]
              exact
                MachineDescription.DovetailControllerLayout.decodeComplete_encode
                  C'
            have htmp : C = C' := by
              simpa [MachineDescription.DovetailControllerLayout.decodeComplete_encode]
                using hdecodeC'
            exact htmp.symm
          subst C'
          exact hout
        exact ⟨C, rfl, hraw, hout⟩
  · intro h
    rcases h with ⟨C, rfl, hraw, rfl⟩
    unfold GuardProjectionPrimitive
    exact
      MachineDescription.TapeCodePrimitive.compose_transform_some
        ((resultNoneGuardPrimitive_transform_eq_some_iff
          (MachineDescription.DovetailControllerLayout.encode C)
          (MachineDescription.DovetailControllerLayout.encode C)).mpr
          ⟨C, rfl, hraw, rfl⟩)
        (pairedRecognizerDovetailControllerStageInputCode_encode C)

theorem decomposedResultContinuePrimitive_transform_eq
    (code : Word MachineCodeSymbol) :
    DecomposedResultContinuePrimitive.transform code =
      PairedRecognizerDovetailControllerResultContinueCode.transform code := by
  unfold DecomposedResultContinuePrimitive
  unfold GuardProjectionPrimitive
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

inductive ResultNoneGuardBoundary where
  | other
  | tick
  | tickDone
  | falseResult
  | trueResult
deriving DecidableEq

namespace ResultNoneGuardBoundary

def toNat : ResultNoneGuardBoundary -> Nat
  | other => 0
  | tick => 1
  | tickDone => 2
  | falseResult => 3
  | trueResult => 4

def fromNat : Nat -> ResultNoneGuardBoundary
  | 1 => tick
  | 2 => tickDone
  | 3 => falseResult
  | 4 => trueResult
  | _ => other

def update
    (boundary : ResultNoneGuardBoundary)
    (symbol : MachineCodeSymbol) :
    ResultNoneGuardBoundary :=
  match symbol with
  | MachineCodeSymbol.tick => tick
  | MachineCodeSymbol.done =>
      match boundary with
      | tick => tickDone
      | _ => other
  | MachineCodeSymbol.zero =>
      match boundary with
      | tickDone => falseResult
      | _ => other
  | MachineCodeSymbol.one =>
      match boundary with
      | tickDone => trueResult
      | _ => other
  | _ => other

def accepts : ResultNoneGuardBoundary -> Prop
  | falseResult => False
  | trueResult => False
  | _ => True

end ResultNoneGuardBoundary

def resultNoneGuardBitValue : Bool -> Nat
  | false => 0
  | true => 1

def resultNoneGuardCodeOfBits
    (bit0 bit1 bit2 bit3 : Bool) : Nat :=
  (((resultNoneGuardBitValue bit0) * 2 +
      resultNoneGuardBitValue bit1) * 2 +
      resultNoneGuardBitValue bit2) * 2 +
    resultNoneGuardBitValue bit3

def resultNoneGuardBoundaryUpdateCode
    (boundary : Nat) (code : Nat) : Nat :=
  match code with
  | 2 => ResultNoneGuardBoundary.tick.toNat
  | 3 =>
      match ResultNoneGuardBoundary.fromNat boundary with
      | ResultNoneGuardBoundary.tick =>
          ResultNoneGuardBoundary.tickDone.toNat
      | _ => ResultNoneGuardBoundary.other.toNat
  | 5 =>
      match ResultNoneGuardBoundary.fromNat boundary with
      | ResultNoneGuardBoundary.tickDone =>
          ResultNoneGuardBoundary.falseResult.toNat
      | _ => ResultNoneGuardBoundary.other.toNat
  | 6 =>
      match ResultNoneGuardBoundary.fromNat boundary with
      | ResultNoneGuardBoundary.tickDone =>
          ResultNoneGuardBoundary.trueResult.toNat
      | _ => ResultNoneGuardBoundary.other.toNat
  | _ => ResultNoneGuardBoundary.other.toNat

def resultNoneGuardState
    (boundary len bits : Nat) : Nat :=
  boundary * 16 + ((2 ^ len) - 1 + bits)

def resultNoneGuardHalt : Nat := 80

def resultNoneGuardPrefixTransitions
    (boundary : Nat) : List TransitionDescription :=
  [ MachineDescription.transition
      (resultNoneGuardState boundary 0 0)
      (some false) (some false) Direction.right
      (resultNoneGuardState boundary 1 0)
  , MachineDescription.transition
      (resultNoneGuardState boundary 0 0)
      (some true) (some true) Direction.right
      (resultNoneGuardState boundary 1 1)
  , MachineDescription.transition
      (resultNoneGuardState boundary 1 0)
      (some false) (some false) Direction.right
      (resultNoneGuardState boundary 2 0)
  , MachineDescription.transition
      (resultNoneGuardState boundary 1 0)
      (some true) (some true) Direction.right
      (resultNoneGuardState boundary 2 1)
  , MachineDescription.transition
      (resultNoneGuardState boundary 1 1)
      (some false) (some false) Direction.right
      (resultNoneGuardState boundary 2 2)
  , MachineDescription.transition
      (resultNoneGuardState boundary 1 1)
      (some true) (some true) Direction.right
      (resultNoneGuardState boundary 2 3)
  , MachineDescription.transition
      (resultNoneGuardState boundary 2 0)
      (some false) (some false) Direction.right
      (resultNoneGuardState boundary 3 0)
  , MachineDescription.transition
      (resultNoneGuardState boundary 2 0)
      (some true) (some true) Direction.right
      (resultNoneGuardState boundary 3 1)
  , MachineDescription.transition
      (resultNoneGuardState boundary 2 1)
      (some false) (some false) Direction.right
      (resultNoneGuardState boundary 3 2)
  , MachineDescription.transition
      (resultNoneGuardState boundary 2 1)
      (some true) (some true) Direction.right
      (resultNoneGuardState boundary 3 3)
  , MachineDescription.transition
      (resultNoneGuardState boundary 2 2)
      (some false) (some false) Direction.right
      (resultNoneGuardState boundary 3 4)
  , MachineDescription.transition
      (resultNoneGuardState boundary 2 2)
      (some true) (some true) Direction.right
      (resultNoneGuardState boundary 3 5)
  , MachineDescription.transition
      (resultNoneGuardState boundary 2 3)
      (some false) (some false) Direction.right
      (resultNoneGuardState boundary 3 6)
  , MachineDescription.transition
      (resultNoneGuardState boundary 2 3)
      (some true) (some true) Direction.right
      (resultNoneGuardState boundary 3 7)
  , MachineDescription.transition
      (resultNoneGuardState boundary 3 0)
      (some false) (some false) Direction.right
      (resultNoneGuardState
        (resultNoneGuardBoundaryUpdateCode boundary 0) 0 0)
  , MachineDescription.transition
      (resultNoneGuardState boundary 3 0)
      (some true) (some true) Direction.right
      (resultNoneGuardState
        (resultNoneGuardBoundaryUpdateCode boundary 1) 0 0)
  , MachineDescription.transition
      (resultNoneGuardState boundary 3 1)
      (some false) (some false) Direction.right
      (resultNoneGuardState
        (resultNoneGuardBoundaryUpdateCode boundary 2) 0 0)
  , MachineDescription.transition
      (resultNoneGuardState boundary 3 1)
      (some true) (some true) Direction.right
      (resultNoneGuardState
        (resultNoneGuardBoundaryUpdateCode boundary 3) 0 0)
  , MachineDescription.transition
      (resultNoneGuardState boundary 3 2)
      (some false) (some false) Direction.right
      (resultNoneGuardState
        (resultNoneGuardBoundaryUpdateCode boundary 4) 0 0)
  , MachineDescription.transition
      (resultNoneGuardState boundary 3 2)
      (some true) (some true) Direction.right
      (resultNoneGuardState
        (resultNoneGuardBoundaryUpdateCode boundary 5) 0 0)
  , MachineDescription.transition
      (resultNoneGuardState boundary 3 3)
      (some false) (some false) Direction.right
      (resultNoneGuardState
        (resultNoneGuardBoundaryUpdateCode boundary 6) 0 0)
  , MachineDescription.transition
      (resultNoneGuardState boundary 3 3)
      (some true) (some true) Direction.right
      (resultNoneGuardState
        (resultNoneGuardBoundaryUpdateCode boundary 7) 0 0)
  , MachineDescription.transition
      (resultNoneGuardState boundary 3 4)
      (some false) (some false) Direction.right
      (resultNoneGuardState
        (resultNoneGuardBoundaryUpdateCode boundary 8) 0 0)
  , MachineDescription.transition
      (resultNoneGuardState boundary 3 4)
      (some true) (some true) Direction.right
      (resultNoneGuardState
        (resultNoneGuardBoundaryUpdateCode boundary 9) 0 0)
  , MachineDescription.transition
      (resultNoneGuardState boundary 3 5)
      (some false) (some false) Direction.right
      (resultNoneGuardState
        (resultNoneGuardBoundaryUpdateCode boundary 10) 0 0)
  , MachineDescription.transition
      (resultNoneGuardState boundary 3 5)
      (some true) (some true) Direction.right
      (resultNoneGuardState
        (resultNoneGuardBoundaryUpdateCode boundary 11) 0 0)
  , MachineDescription.transition
      (resultNoneGuardState boundary 3 6)
      (some false) (some false) Direction.right
      (resultNoneGuardState
        (resultNoneGuardBoundaryUpdateCode boundary 12) 0 0)
  , MachineDescription.transition
      (resultNoneGuardState boundary 3 6)
      (some true) (some true) Direction.right
      (resultNoneGuardState
        (resultNoneGuardBoundaryUpdateCode boundary 13) 0 0)
  , MachineDescription.transition
      (resultNoneGuardState boundary 3 7)
      (some false) (some false) Direction.right
      (resultNoneGuardState
        (resultNoneGuardBoundaryUpdateCode boundary 14) 0 0)
  , MachineDescription.transition
      (resultNoneGuardState boundary 3 7)
      (some true) (some true) Direction.right
      (resultNoneGuardState
        (resultNoneGuardBoundaryUpdateCode boundary 15) 0 0)
  ]

def resultNoneGuardBitTransitions :
    List TransitionDescription :=
  resultNoneGuardPrefixTransitions
      ResultNoneGuardBoundary.other.toNat ++
    resultNoneGuardPrefixTransitions
      ResultNoneGuardBoundary.tick.toNat ++
    resultNoneGuardPrefixTransitions
      ResultNoneGuardBoundary.tickDone.toNat ++
    resultNoneGuardPrefixTransitions
      ResultNoneGuardBoundary.falseResult.toNat ++
    resultNoneGuardPrefixTransitions
      ResultNoneGuardBoundary.trueResult.toNat

def resultNoneGuardBlankTransitions :
    List TransitionDescription :=
  [ MachineDescription.transition
      (resultNoneGuardState ResultNoneGuardBoundary.other.toNat 0 0)
      none none Direction.right resultNoneGuardHalt
  , MachineDescription.transition
      (resultNoneGuardState ResultNoneGuardBoundary.tick.toNat 0 0)
      none none Direction.right resultNoneGuardHalt
  , MachineDescription.transition
      (resultNoneGuardState ResultNoneGuardBoundary.tickDone.toNat 0 0)
      none none Direction.right resultNoneGuardHalt
  ]

def ResultNoneGuardScannerDescription : MachineDescription where
  stateCount := resultNoneGuardHalt + 1
  start := resultNoneGuardState ResultNoneGuardBoundary.other.toNat 0 0
  halt := resultNoneGuardHalt
  transitions :=
    resultNoneGuardBitTransitions ++
      resultNoneGuardBlankTransitions

theorem resultNoneGuardScannerDescription_wellFormed :
    ResultNoneGuardScannerDescription.WellFormed := by
  refine ⟨by native_decide, by native_decide, by native_decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := ResultNoneGuardScannerDescription.transitions)
      (stateCount := ResultNoneGuardScannerDescription.stateCount)
      (by native_decide)
  · exact transition_deterministic_of_all
      (l := ResultNoneGuardScannerDescription.transitions)
      (by native_decide)

theorem resultNoneGuardScannerDescription_haltTransitionFree :
    ResultNoneGuardScannerDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := ResultNoneGuardScannerDescription.transitions)
    (state := ResultNoneGuardScannerDescription.halt)
    (by native_decide)

theorem resultNoneGuardScannerDescription_subroutineReady :
    ResultNoneGuardScannerDescription.SubroutineReady :=
  ⟨resultNoneGuardScannerDescription_wellFormed,
    resultNoneGuardScannerDescription_haltTransitionFree⟩

def resultNoneGuardSymbolCode : MachineCodeSymbol -> Nat
  | MachineCodeSymbol.header => 0
  | MachineCodeSymbol.transition => 1
  | MachineCodeSymbol.tick => 2
  | MachineCodeSymbol.done => 3
  | MachineCodeSymbol.blank => 4
  | MachineCodeSymbol.zero => 5
  | MachineCodeSymbol.one => 6
  | MachineCodeSymbol.moveLeft => 7
  | MachineCodeSymbol.moveRight => 8

theorem resultNoneGuardBoundaryUpdateCode_symbol
    (boundary : ResultNoneGuardBoundary)
    (symbol : MachineCodeSymbol) :
    resultNoneGuardBoundaryUpdateCode boundary.toNat
        (resultNoneGuardSymbolCode symbol) =
      (boundary.update symbol).toNat := by
  cases boundary <;> cases symbol <;> rfl

def resultNoneGuardScanBoundaryFrom
    (boundary : ResultNoneGuardBoundary) :
    Word MachineCodeSymbol -> ResultNoneGuardBoundary
  | [] => boundary
  | symbol :: rest =>
      resultNoneGuardScanBoundaryFrom
        (boundary.update symbol) rest

def resultNoneGuardScanBoundary
    (code : Word MachineCodeSymbol) :
    ResultNoneGuardBoundary :=
  resultNoneGuardScanBoundaryFrom
    ResultNoneGuardBoundary.other code

theorem resultNoneGuardScanBoundaryFrom_append
    (boundary : ResultNoneGuardBoundary)
    (pre suffix : Word MachineCodeSymbol) :
    resultNoneGuardScanBoundaryFrom boundary
        (List.append pre suffix) =
      resultNoneGuardScanBoundaryFrom
        (resultNoneGuardScanBoundaryFrom boundary pre) suffix := by
  induction pre generalizing boundary with
  | nil =>
      rfl
  | cons symbol rest ih =>
      exact ih (boundary.update symbol)

theorem resultNoneGuardScanBoundaryFrom_encodeCells_some_other
    (w : Word Bool) :
    resultNoneGuardScanBoundaryFrom
        ResultNoneGuardBoundary.other
        (MachineDescription.encodeCellsAppend (w.map some) []) =
      ResultNoneGuardBoundary.other := by
  induction w with
  | nil =>
      rfl
  | cons b rest ih =>
      cases b <;>
        simp [MachineDescription.encodeCellsAppend,
          MachineDescription.encodeCellAppend,
          MachineDescription.encodeCell,
          resultNoneGuardScanBoundaryFrom,
          ResultNoneGuardBoundary.update, ih]

theorem resultNoneGuardScanBoundaryFrom_encodeNat_from_tick
    (n : Nat) :
    resultNoneGuardScanBoundaryFrom
        ResultNoneGuardBoundary.tick
        (MachineDescription.encodeNat n) =
      ResultNoneGuardBoundary.tickDone := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simpa [MachineDescription.encodeNat,
        resultNoneGuardScanBoundaryFrom,
        ResultNoneGuardBoundary.update] using ih

theorem resultNoneGuardScanBoundaryFrom_encodeNat_succ
    (boundary : ResultNoneGuardBoundary) (n : Nat) :
    resultNoneGuardScanBoundaryFrom boundary
        (MachineDescription.encodeNat (n + 1)) =
      ResultNoneGuardBoundary.tickDone := by
  simp [MachineDescription.encodeNat,
    resultNoneGuardScanBoundaryFrom,
    ResultNoneGuardBoundary.update,
    resultNoneGuardScanBoundaryFrom_encodeNat_from_tick]

theorem resultNoneGuardScanBoundaryFrom_encodeCells_singleton
    (b : Bool) :
    resultNoneGuardScanBoundaryFrom
        ResultNoneGuardBoundary.tickDone
        (MachineDescription.encodeCellsAppend [some b] []) =
      (if b then ResultNoneGuardBoundary.trueResult
        else ResultNoneGuardBoundary.falseResult) := by
  cases b <;>
    rfl

theorem resultNoneGuardScanBoundaryFrom_encodeCells_cons_cons
    (first second : Bool) (rest : Word Bool) :
    resultNoneGuardScanBoundaryFrom
        ResultNoneGuardBoundary.tickDone
        (MachineDescription.encodeCellsAppend
          ((first :: second :: rest).map some) []) =
      ResultNoneGuardBoundary.other := by
  cases first <;> cases second <;>
    simp [MachineDescription.encodeCellsAppend,
      MachineDescription.encodeCellAppend,
      MachineDescription.encodeCell,
      resultNoneGuardScanBoundaryFrom,
      ResultNoneGuardBoundary.update,
      resultNoneGuardScanBoundaryFrom_encodeCells_some_other]

theorem resultNoneGuardScanBoundaryFrom_encodeBoolWord_singleton
    (boundary : ResultNoneGuardBoundary) (b : Bool) :
    resultNoneGuardScanBoundaryFrom boundary
        (MachineDescription.encodeBoolWord [b]) =
      (if b then ResultNoneGuardBoundary.trueResult
        else ResultNoneGuardBoundary.falseResult) := by
  rw [show
      MachineDescription.encodeBoolWord [b] =
        List.append (MachineDescription.encodeNat 1)
          (MachineDescription.encodeCellsAppend [some b] []) by
    simp [MachineDescription.encodeBoolWord,
      MachineDescription.encodeBoolWordAppend,
      MachineDescription.encodeCellListAppend,
      MachineDescription.encodeNatAppend]]
  rw [resultNoneGuardScanBoundaryFrom_append]
  rw [resultNoneGuardScanBoundaryFrom_encodeNat_succ]
  exact resultNoneGuardScanBoundaryFrom_encodeCells_singleton b

theorem resultNoneGuardScanBoundaryFrom_encodeBoolWord_cons_cons
    (boundary : ResultNoneGuardBoundary)
    (first second : Bool) (rest : Word Bool) :
    resultNoneGuardScanBoundaryFrom boundary
        (MachineDescription.encodeBoolWord (first :: second :: rest)) =
      ResultNoneGuardBoundary.other := by
  rw [show
      MachineDescription.encodeBoolWord (first :: second :: rest) =
        List.append
          (MachineDescription.encodeNat (rest.length + 1 + 1))
          (MachineDescription.encodeCellsAppend
            ((first :: second :: rest).map some) []) by
    simp [MachineDescription.encodeBoolWord,
      MachineDescription.encodeBoolWordAppend,
      MachineDescription.encodeCellListAppend,
      MachineDescription.encodeNatAppend]]
  rw [resultNoneGuardScanBoundaryFrom_append]
  rw [resultNoneGuardScanBoundaryFrom_encodeNat_succ]
  exact resultNoneGuardScanBoundaryFrom_encodeCells_cons_cons
    first second rest

theorem resultNoneGuardScanBoundaryFrom_encodeBoolWord_accepts_iff
    (boundary : ResultNoneGuardBoundary)
    (result : Word Bool) :
    (resultNoneGuardScanBoundaryFrom boundary
        (MachineDescription.encodeBoolWord result)).accepts <->
      PairedRecognizerDovetailControllerRawOutput result = none := by
  cases result with
  | nil =>
      cases boundary <;>
        simp [MachineDescription.encodeBoolWord,
          MachineDescription.encodeBoolWordAppend,
          MachineDescription.encodeCellListAppend,
          MachineDescription.encodeCellsAppend,
          MachineDescription.encodeNatAppend,
          MachineDescription.encodeNat,
          resultNoneGuardScanBoundaryFrom,
          ResultNoneGuardBoundary.update,
          ResultNoneGuardBoundary.accepts,
          PairedRecognizerDovetailControllerRawOutput,
          MachineDescription.DovetailControllerLayout.rawOutput?]
  | cons first tail =>
      cases tail with
      | nil =>
          cases first <;> cases boundary <;>
            simp [resultNoneGuardScanBoundaryFrom_encodeBoolWord_singleton,
              ResultNoneGuardBoundary.accepts,
              PairedRecognizerDovetailControllerRawOutput,
              MachineDescription.DovetailControllerLayout.rawOutput?]
      | cons second rest =>
          cases first <;> cases second <;> cases boundary <;>
            simp [resultNoneGuardScanBoundaryFrom_encodeBoolWord_cons_cons,
              ResultNoneGuardBoundary.accepts,
              PairedRecognizerDovetailControllerRawOutput,
              MachineDescription.DovetailControllerLayout.rawOutput?]

theorem resultNoneGuardScanBoundary_controllerEncode_accepts_iff
    (C : MachineDescription.DovetailControllerLayout) :
    (resultNoneGuardScanBoundary
        (MachineDescription.DovetailControllerLayout.encode C)).accepts <->
      PairedRecognizerDovetailControllerRawOutput C.result = none := by
  unfold resultNoneGuardScanBoundary
  rw [CommonGround.ControllerLayouts.encode_eq_header_stageInput_append_result C]
  simp only [resultNoneGuardScanBoundaryFrom,
    ResultNoneGuardBoundary.update]
  rw [resultNoneGuardScanBoundaryFrom_append]
  simpa [MachineDescription.encodeBoolWord] using
    resultNoneGuardScanBoundaryFrom_encodeBoolWord_accepts_iff
      (resultNoneGuardScanBoundaryFrom
        ResultNoneGuardBoundary.other
        (PairedRecognizerDovetailControllerStageInputCode C))
      C.result

theorem resultNoneGuardScannerDescription_run_first_bit
    (boundary : ResultNoneGuardBoundary)
    (bit : Bool) (leftRev suffix : Word Bool) :
    ResultNoneGuardScannerDescription.runConfig 1
        { state := resultNoneGuardState boundary.toNat 0 0
          tape := MachineDescription.appendRightScanTape leftRev
            (bit :: suffix) } =
      { state :=
          resultNoneGuardState boundary.toNat 1
            (resultNoneGuardBitValue bit)
        tape := MachineDescription.appendRightScanTape
          (bit :: leftRev) suffix } := by
  cases boundary <;> cases bit <;> cases suffix <;> rfl

theorem resultNoneGuardScannerDescription_run_second_bit
    (boundary : ResultNoneGuardBoundary)
    (bit0 bit1 : Bool) (leftRev suffix : Word Bool) :
    ResultNoneGuardScannerDescription.runConfig 1
        { state :=
            resultNoneGuardState boundary.toNat 1
              (resultNoneGuardBitValue bit0)
          tape := MachineDescription.appendRightScanTape leftRev
            (bit1 :: suffix) } =
      { state :=
          resultNoneGuardState boundary.toNat 2
            (resultNoneGuardBitValue bit0 * 2 +
              resultNoneGuardBitValue bit1)
        tape := MachineDescription.appendRightScanTape
          (bit1 :: leftRev) suffix } := by
  cases boundary <;> cases bit0 <;> cases bit1 <;> cases suffix <;> rfl

theorem resultNoneGuardScannerDescription_run_third_bit
    (boundary : ResultNoneGuardBoundary)
    (bit0 bit1 bit2 : Bool) (leftRev suffix : Word Bool) :
    ResultNoneGuardScannerDescription.runConfig 1
        { state :=
            resultNoneGuardState boundary.toNat 2
              (resultNoneGuardBitValue bit0 * 2 +
                resultNoneGuardBitValue bit1)
          tape := MachineDescription.appendRightScanTape leftRev
            (bit2 :: suffix) } =
      { state :=
          resultNoneGuardState boundary.toNat 3
            ((resultNoneGuardBitValue bit0 * 2 +
                resultNoneGuardBitValue bit1) * 2 +
              resultNoneGuardBitValue bit2)
        tape := MachineDescription.appendRightScanTape
          (bit2 :: leftRev) suffix } := by
  cases boundary <;> cases bit0 <;> cases bit1 <;> cases bit2 <;>
    cases suffix <;> rfl

theorem resultNoneGuardScannerDescription_run_fourth_bit
    (boundary : ResultNoneGuardBoundary)
    (bit0 bit1 bit2 bit3 : Bool) (leftRev suffix : Word Bool) :
    ResultNoneGuardScannerDescription.runConfig 1
        { state :=
            resultNoneGuardState boundary.toNat 3
              ((resultNoneGuardBitValue bit0 * 2 +
                  resultNoneGuardBitValue bit1) * 2 +
                resultNoneGuardBitValue bit2)
          tape := MachineDescription.appendRightScanTape leftRev
            (bit3 :: suffix) } =
      { state :=
          resultNoneGuardState
            (resultNoneGuardBoundaryUpdateCode boundary.toNat
              (resultNoneGuardCodeOfBits bit0 bit1 bit2 bit3)) 0 0
        tape := MachineDescription.appendRightScanTape
          (bit3 :: leftRev) suffix } := by
  cases boundary <;> cases bit0 <;> cases bit1 <;> cases bit2 <;>
    cases bit3 <;> cases suffix <;> rfl

theorem resultNoneGuardScannerDescription_run_bits
    (boundary : ResultNoneGuardBoundary)
    (bit0 bit1 bit2 bit3 : Bool)
    (leftRev suffix : Word Bool) :
    ResultNoneGuardScannerDescription.runConfig 4
        { state := resultNoneGuardState boundary.toNat 0 0
          tape :=
            MachineDescription.appendRightScanTape leftRev
              (List.append [bit0, bit1, bit2, bit3] suffix) } =
      { state :=
          resultNoneGuardState
            (resultNoneGuardBoundaryUpdateCode boundary.toNat
              (resultNoneGuardCodeOfBits bit0 bit1 bit2 bit3)) 0 0
        tape := MachineDescription.appendRightScanTape
          (bit3 :: bit2 :: bit1 :: bit0 :: leftRev) suffix } := by
  rw [show 4 = 1 + 3 by decide, MachineDescription.runConfig_add]
  change
    ResultNoneGuardScannerDescription.runConfig 3
        (ResultNoneGuardScannerDescription.runConfig 1
          { state := resultNoneGuardState boundary.toNat 0 0
            tape :=
              MachineDescription.appendRightScanTape leftRev
                (bit0 :: bit1 :: bit2 :: bit3 :: suffix) }) =
      { state :=
          resultNoneGuardState
            (resultNoneGuardBoundaryUpdateCode boundary.toNat
              (resultNoneGuardCodeOfBits bit0 bit1 bit2 bit3)) 0 0
        tape := MachineDescription.appendRightScanTape
          (bit3 :: bit2 :: bit1 :: bit0 :: leftRev) suffix }
  rw [resultNoneGuardScannerDescription_run_first_bit]
  rw [show 3 = 1 + 2 by decide, MachineDescription.runConfig_add]
  change
    ResultNoneGuardScannerDescription.runConfig 2
        (ResultNoneGuardScannerDescription.runConfig 1
          { state :=
              resultNoneGuardState boundary.toNat 1
                (resultNoneGuardBitValue bit0)
            tape :=
              MachineDescription.appendRightScanTape (bit0 :: leftRev)
                (bit1 :: bit2 :: bit3 :: suffix) }) =
      { state :=
          resultNoneGuardState
            (resultNoneGuardBoundaryUpdateCode boundary.toNat
              (resultNoneGuardCodeOfBits bit0 bit1 bit2 bit3)) 0 0
        tape := MachineDescription.appendRightScanTape
          (bit3 :: bit2 :: bit1 :: bit0 :: leftRev) suffix }
  rw [resultNoneGuardScannerDescription_run_second_bit]
  rw [show 2 = 1 + 1 by decide, MachineDescription.runConfig_add]
  change
    ResultNoneGuardScannerDescription.runConfig 1
        (ResultNoneGuardScannerDescription.runConfig 1
          { state :=
              resultNoneGuardState boundary.toNat 2
                (resultNoneGuardBitValue bit0 * 2 +
                  resultNoneGuardBitValue bit1)
            tape :=
              MachineDescription.appendRightScanTape
                (bit1 :: bit0 :: leftRev)
                (bit2 :: bit3 :: suffix) }) =
      { state :=
          resultNoneGuardState
            (resultNoneGuardBoundaryUpdateCode boundary.toNat
              (resultNoneGuardCodeOfBits bit0 bit1 bit2 bit3)) 0 0
        tape := MachineDescription.appendRightScanTape
          (bit3 :: bit2 :: bit1 :: bit0 :: leftRev) suffix }
  rw [resultNoneGuardScannerDescription_run_third_bit]
  rw [resultNoneGuardScannerDescription_run_fourth_bit]

theorem resultNoneGuardScannerDescription_run_encoded_symbol
    (boundary : ResultNoneGuardBoundary)
    (symbol : MachineCodeSymbol)
    (leftRev suffix : Word Bool) :
    ResultNoneGuardScannerDescription.runConfig 4
        { state := resultNoneGuardState boundary.toNat 0 0
          tape :=
            MachineDescription.appendRightScanTape leftRev
              (List.append
                (MachineDescription.encodeCodeSymbolAsInput symbol)
                suffix) } =
      { state :=
          resultNoneGuardState
            (resultNoneGuardBoundaryUpdateCode boundary.toNat
              (resultNoneGuardSymbolCode symbol)) 0 0
        tape :=
          MachineDescription.appendRightScanTape
            (List.append
              (MachineDescription.encodeCodeSymbolAsInput symbol).reverse
              leftRev)
            suffix } := by
  cases symbol
  · simpa [MachineDescription.encodeCodeSymbolAsInput,
      resultNoneGuardCodeOfBits, resultNoneGuardSymbolCode] using
      (resultNoneGuardScannerDescription_run_bits boundary
        false false false false leftRev suffix)
  · simpa [MachineDescription.encodeCodeSymbolAsInput,
      resultNoneGuardCodeOfBits, resultNoneGuardSymbolCode] using
      (resultNoneGuardScannerDescription_run_bits boundary
        false false false true leftRev suffix)
  · simpa [MachineDescription.encodeCodeSymbolAsInput,
      resultNoneGuardCodeOfBits, resultNoneGuardSymbolCode] using
      (resultNoneGuardScannerDescription_run_bits boundary
        false false true false leftRev suffix)
  · simpa [MachineDescription.encodeCodeSymbolAsInput,
      resultNoneGuardCodeOfBits, resultNoneGuardSymbolCode] using
      (resultNoneGuardScannerDescription_run_bits boundary
        false false true true leftRev suffix)
  · simpa [MachineDescription.encodeCodeSymbolAsInput,
      resultNoneGuardCodeOfBits, resultNoneGuardSymbolCode] using
      (resultNoneGuardScannerDescription_run_bits boundary
        false true false false leftRev suffix)
  · simpa [MachineDescription.encodeCodeSymbolAsInput,
      resultNoneGuardCodeOfBits, resultNoneGuardSymbolCode] using
      (resultNoneGuardScannerDescription_run_bits boundary
        false true false true leftRev suffix)
  · simpa [MachineDescription.encodeCodeSymbolAsInput,
      resultNoneGuardCodeOfBits, resultNoneGuardSymbolCode] using
      (resultNoneGuardScannerDescription_run_bits boundary
        false true true false leftRev suffix)
  · simpa [MachineDescription.encodeCodeSymbolAsInput,
      resultNoneGuardCodeOfBits, resultNoneGuardSymbolCode] using
      (resultNoneGuardScannerDescription_run_bits boundary
        false true true true leftRev suffix)
  · simpa [MachineDescription.encodeCodeSymbolAsInput,
      resultNoneGuardCodeOfBits, resultNoneGuardSymbolCode] using
      (resultNoneGuardScannerDescription_run_bits boundary
        true false false false leftRev suffix)

theorem resultNoneGuardScannerDescription_run_symbol
    (boundary : ResultNoneGuardBoundary)
    (symbol : MachineCodeSymbol)
    (leftRev suffix : Word Bool) :
    ResultNoneGuardScannerDescription.runConfig 4
        { state := resultNoneGuardState boundary.toNat 0 0
          tape :=
            MachineDescription.appendRightScanTape leftRev
              (List.append
                (MachineDescription.encodeCodeSymbolAsInput symbol)
                suffix) } =
      { state :=
          resultNoneGuardState (boundary.update symbol).toNat 0 0
        tape :=
          MachineDescription.appendRightScanTape
            (List.append
              (MachineDescription.encodeCodeSymbolAsInput symbol).reverse
              leftRev)
            suffix } := by
  rw [resultNoneGuardScannerDescription_run_encoded_symbol]
  rw [resultNoneGuardBoundaryUpdateCode_symbol]

theorem resultNoneGuardScannerDescription_run_code_from
    (boundary : ResultNoneGuardBoundary)
    (code : Word MachineCodeSymbol)
    (leftRev suffix : Word Bool) :
    ResultNoneGuardScannerDescription.runConfig
        (4 * code.length)
        { state := resultNoneGuardState boundary.toNat 0 0
          tape :=
            MachineDescription.appendRightScanTape leftRev
              (List.append
                (MachineDescription.encodeCodeWordAsInput code) suffix) } =
      { state :=
          resultNoneGuardState
            (resultNoneGuardScanBoundaryFrom boundary code).toNat 0 0
        tape :=
          MachineDescription.appendRightScanTape
            (List.append
              (MachineDescription.encodeCodeWordAsInput code).reverse
              leftRev)
            suffix } := by
  induction code generalizing boundary leftRev with
  | nil =>
      simp [MachineDescription.encodeCodeWordAsInput,
        resultNoneGuardScanBoundaryFrom,
        MachineDescription.runConfig]
  | cons symbol rest ih =>
      rw [show 4 * (symbol :: rest).length = 4 + 4 * rest.length by
        simp
        omega]
      rw [MachineDescription.runConfig_add]
      simp only [MachineDescription.encodeCodeWordAsInput]
      have happ :
          List.append
              (List.append
                (MachineDescription.encodeCodeSymbolAsInput symbol)
                (MachineDescription.encodeCodeWordAsInput rest))
              suffix =
            List.append
              (MachineDescription.encodeCodeSymbolAsInput symbol)
              (List.append
                (MachineDescription.encodeCodeWordAsInput rest)
                suffix) :=
        List.append_assoc
          (MachineDescription.encodeCodeSymbolAsInput symbol)
          (MachineDescription.encodeCodeWordAsInput rest) suffix
      rw [happ]
      change
        ResultNoneGuardScannerDescription.runConfig
            (4 * rest.length)
            (ResultNoneGuardScannerDescription.runConfig 4
              { state := resultNoneGuardState boundary.toNat 0 0
                tape :=
                  MachineDescription.appendRightScanTape leftRev
                    (List.append
                      (MachineDescription.encodeCodeSymbolAsInput symbol)
                      (List.append
                        (MachineDescription.encodeCodeWordAsInput rest)
                        suffix)) }) =
          { state :=
              resultNoneGuardState
                (resultNoneGuardScanBoundaryFrom boundary
                  (symbol :: rest)).toNat 0 0
            tape :=
              MachineDescription.appendRightScanTape
                (List.append
                  (List.append
                    (MachineDescription.encodeCodeSymbolAsInput symbol)
                    (MachineDescription.encodeCodeWordAsInput rest)).reverse
                  leftRev)
                suffix }
      rw [resultNoneGuardScannerDescription_run_symbol]
      rw [ih]
      simp [resultNoneGuardScanBoundaryFrom, List.reverse_append,
        List.append_assoc]

def resultNoneGuardScannedBlankTape
    (leftRev : Word Bool) : Tape Bool :=
  Tape.move Direction.right
    (MachineDescription.appendRightScanTape leftRev [])

theorem resultNoneGuardScannerDescription_run_blank_of_accepts
    (boundary : ResultNoneGuardBoundary)
    (haccept : boundary.accepts)
    (leftRev : Word Bool) :
    ResultNoneGuardScannerDescription.runConfig 1
        { state := resultNoneGuardState boundary.toNat 0 0
          tape := MachineDescription.appendRightScanTape leftRev [] } =
      { state := ResultNoneGuardScannerDescription.halt
        tape := resultNoneGuardScannedBlankTape leftRev } := by
  cases boundary
  · rfl
  · rfl
  · rfl
  · cases haccept
  · cases haccept

theorem resultNoneGuardScannerDescription_run_code_halt_of_accepts
    (code : Word MachineCodeSymbol)
    (haccept : (resultNoneGuardScanBoundary code).accepts) :
    ResultNoneGuardScannerDescription.runConfig
        (4 * code.length + 1)
        (ResultNoneGuardScannerDescription.initial
          (MachineDescription.encodeCodeWordAsInput code)) =
      { state := ResultNoneGuardScannerDescription.halt
        tape :=
          resultNoneGuardScannedBlankTape
            (MachineDescription.encodeCodeWordAsInput code).reverse } := by
  rw [MachineDescription.runConfig_add]
  have hinitial :
      ResultNoneGuardScannerDescription.initial
          (MachineDescription.encodeCodeWordAsInput code) =
        { state :=
            resultNoneGuardState ResultNoneGuardBoundary.other.toNat 0 0
          tape :=
            MachineDescription.appendRightScanTape []
              (List.append
                (MachineDescription.encodeCodeWordAsInput code) []) } := by
    simp [ResultNoneGuardScannerDescription,
      MachineDescription.initial,
      MachineDescription.appendRightScanTape_nil_eq_input]
  rw [hinitial]
  rw [resultNoneGuardScannerDescription_run_code_from]
  simpa [resultNoneGuardScanBoundary] using
    resultNoneGuardScannerDescription_run_blank_of_accepts
      (resultNoneGuardScanBoundary code) haccept
      (MachineDescription.encodeCodeWordAsInput code).reverse

theorem resultNoneGuardScannedBlankTape_normalizedOutput
    (leftRev : Word Bool) :
    Tape.normalizedOutput
        (resultNoneGuardScannedBlankTape leftRev) =
      leftRev.reverse := by
  have hfilter :
      List.filterMap
          ((fun cell : Option Bool => cell) ∘
            (fun b : Bool => some b)) leftRev =
        leftRev := by
    induction leftRev with
    | nil =>
        rfl
    | cons b rest ih =>
        simp [Function.comp, ih]
  simp [resultNoneGuardScannedBlankTape,
    MachineDescription.appendRightScanTape, Tape.move,
    Tape.moveRight, Tape.normalizedOutput, Tape.cells,
    hfilter]

theorem resultNoneGuardScannerDescription_haltsWithOutput_code_of_accepts
    (code : Word MachineCodeSymbol)
    (haccept : (resultNoneGuardScanBoundary code).accepts) :
    ResultNoneGuardScannerDescription.HaltsWithOutput
      (MachineDescription.encodeCodeWordAsInput code)
      (MachineDescription.encodeCodeWordAsInput code) := by
  refine ⟨4 * code.length + 1, ?_⟩
  constructor
  · rw [resultNoneGuardScannerDescription_run_code_halt_of_accepts
      code haccept]
  · rw [resultNoneGuardScannerDescription_run_code_halt_of_accepts
      code haccept]
    simp [resultNoneGuardScannedBlankTape_normalizedOutput]

theorem resultNoneGuardScannerDescription_haltsWithOutput_controllerEncode
    (C : MachineDescription.DovetailControllerLayout)
    (hraw : PairedRecognizerDovetailControllerRawOutput C.result = none) :
    ResultNoneGuardScannerDescription.HaltsWithOutput
      (MachineDescription.encodeCodeWordAsInput
        (MachineDescription.DovetailControllerLayout.encode C))
      (MachineDescription.encodeCodeWordAsInput
        (MachineDescription.DovetailControllerLayout.encode C)) := by
  exact
    resultNoneGuardScannerDescription_haltsWithOutput_code_of_accepts
      (MachineDescription.DovetailControllerLayout.encode C)
      ((resultNoneGuardScanBoundary_controllerEncode_accepts_iff C).mpr
        hraw)

def ResultNoneGuardRewindDescription : MachineDescription where
  stateCount := 5
  start := 0
  halt := 4
  transitions :=
    [ MachineDescription.transition 0 none none Direction.left 1
    , MachineDescription.transition 1 none none Direction.left 2
    , MachineDescription.transition 2 (some false) (some false)
        Direction.left 2
    , MachineDescription.transition 2 (some true) (some true)
        Direction.left 2
    , MachineDescription.transition 2 none none Direction.right 3
    , MachineDescription.transition 3 none none Direction.right 4
    , MachineDescription.transition 3 (some false) (some false)
        Direction.right 4
    , MachineDescription.transition 3 (some true) (some true)
        Direction.right 4
    ]

theorem resultNoneGuardRewindDescription_wellFormed :
    ResultNoneGuardRewindDescription.WellFormed := by
  refine ⟨by native_decide, by native_decide, by native_decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := ResultNoneGuardRewindDescription.transitions)
      (stateCount := ResultNoneGuardRewindDescription.stateCount)
      (by native_decide)
  · exact transition_deterministic_of_all
      (l := ResultNoneGuardRewindDescription.transitions)
      (by native_decide)

theorem resultNoneGuardRewindDescription_haltTransitionFree :
    ResultNoneGuardRewindDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := ResultNoneGuardRewindDescription.transitions)
    (state := ResultNoneGuardRewindDescription.halt)
    (by native_decide)

theorem resultNoneGuardRewindDescription_subroutineReady :
    ResultNoneGuardRewindDescription.SubroutineReady :=
  ⟨resultNoneGuardRewindDescription_wellFormed,
    resultNoneGuardRewindDescription_haltTransitionFree⟩

def resultNoneGuardRewindLeftScanTape
    (leftRev : Word Bool) (right : List (Option Bool)) : Tape Bool :=
  match leftRev with
  | [] =>
      { left := []
        head := none
        right := right }
  | b :: rest =>
      { left := rest.map some
        head := some b
        right := right }

def resultNoneGuardRewindBoundaryTape
    (bits : Word Bool) : Tape Bool :=
  { left := []
    head := none
    right := (bits.map some) ++ [none, none] }

def resultNoneGuardRewindFinalTape
    (bits : Word Bool) : Tape Bool :=
  Tape.move Direction.right
    (Tape.move Direction.right
      (resultNoneGuardRewindBoundaryTape bits))

theorem resultNoneGuardRewindDescription_run_start
    (leftRev : Word Bool) :
    ResultNoneGuardRewindDescription.runConfig 2
        { state := ResultNoneGuardRewindDescription.start
          tape := resultNoneGuardScannedBlankTape leftRev } =
      { state := 2
        tape := resultNoneGuardRewindLeftScanTape
          leftRev [none, none] } := by
  cases leftRev with
  | nil =>
      rfl
  | cons b rest =>
      cases b <;> rfl

theorem resultNoneGuardRewindDescription_run_left_scan
    (leftRev : Word Bool) (right : List (Option Bool)) :
    ResultNoneGuardRewindDescription.runConfig leftRev.length
        { state := 2
          tape := resultNoneGuardRewindLeftScanTape leftRev right } =
      { state := 2
        tape :=
          { left := []
            head := none
            right := (leftRev.reverse.map some) ++ right } } := by
  induction leftRev generalizing right with
  | nil =>
      rfl
  | cons b rest ih =>
      rw [show (b :: rest).length = 1 + rest.length by
        simp
        omega]
      rw [MachineDescription.runConfig_add]
      cases b
      · have hstep :
            ResultNoneGuardRewindDescription.runConfig 1
                { state := 2
                  tape :=
                    resultNoneGuardRewindLeftScanTape
                      (false :: rest) right } =
              { state := 2
                tape :=
                  resultNoneGuardRewindLeftScanTape rest
                    (some false :: right) } := by
          cases rest with
          | nil =>
              rfl
          | cons c tail =>
              cases c <;> rfl
        rw [hstep]
        rw [ih]
        simp [List.append_assoc]
      · have hstep :
            ResultNoneGuardRewindDescription.runConfig 1
                { state := 2
                  tape :=
                    resultNoneGuardRewindLeftScanTape
                      (true :: rest) right } =
              { state := 2
                tape :=
                  resultNoneGuardRewindLeftScanTape rest
                    (some true :: right) } := by
          cases rest with
          | nil =>
              rfl
          | cons c tail =>
              cases c <;> rfl
        rw [hstep]
        rw [ih]
        simp [List.append_assoc]

theorem resultNoneGuardRewindDescription_run_finish
    (bits : Word Bool) :
    ResultNoneGuardRewindDescription.runConfig 2
        { state := 2
          tape := resultNoneGuardRewindBoundaryTape bits } =
      { state := ResultNoneGuardRewindDescription.halt
        tape := resultNoneGuardRewindFinalTape bits } := by
  cases bits with
  | nil =>
      rfl
  | cons b rest =>
      cases b <;> cases rest <;> rfl

theorem resultNoneGuardRewindDescription_run_scanned
    (bits : Word Bool) :
    ResultNoneGuardRewindDescription.runConfig
        (bits.length + 4)
        { state := ResultNoneGuardRewindDescription.start
          tape := resultNoneGuardScannedBlankTape bits.reverse } =
      { state := ResultNoneGuardRewindDescription.halt
        tape := resultNoneGuardRewindFinalTape bits } := by
  rw [show bits.length + 4 = 2 + (bits.length + 2) by omega]
  rw [MachineDescription.runConfig_add]
  rw [resultNoneGuardRewindDescription_run_start]
  rw [show bits.length + 2 = bits.reverse.length + 2 by simp]
  rw [MachineDescription.runConfig_add]
  rw [resultNoneGuardRewindDescription_run_left_scan]
  change
    ResultNoneGuardRewindDescription.runConfig 2
        { state := 2
          tape :=
            { left := []
              head := none
              right := (bits.reverse.reverse.map some) ++ [none, none] } } =
      { state := ResultNoneGuardRewindDescription.halt
        tape := resultNoneGuardRewindFinalTape bits }
  simp only [List.reverse_reverse]
  exact resultNoneGuardRewindDescription_run_finish bits

theorem resultNoneGuardRewind_dropTrailingNone_map_some
    (bits : Word Bool) :
    Tape.dropTrailingNone (bits.map some) = bits.map some := by
  induction bits with
  | nil =>
      rfl
  | cons b rest ih =>
      cases b <;>
        simp [Tape.dropTrailingNone, ih]

theorem resultNoneGuardRewind_dropTrailingNone_map_some_append_blanks
    (bits : Word Bool) :
    Tape.dropTrailingNone (bits.map some ++ [none, none]) =
      bits.map some := by
  induction bits with
  | nil =>
      rfl
  | cons b rest ih =>
      cases b <;>
        simp [Tape.dropTrailingNone, ih]

theorem resultNoneGuardRewindFinalTape_handoff_equiv
    (bits : Word Bool) :
    Tape.Equiv
      (resultNoneGuardRewindFinalTape bits)
      (Tape.move Direction.right (Tape.input bits)) := by
  cases bits with
  | nil =>
      simp [resultNoneGuardRewindFinalTape,
        resultNoneGuardRewindBoundaryTape, Tape.input, Tape.blank,
        Tape.move, Tape.moveRight, Tape.Equiv,
        Tape.dropTrailingNone]
  | cons b rest =>
      cases rest with
      | nil =>
          cases b <;>
            simp [resultNoneGuardRewindFinalTape,
              resultNoneGuardRewindBoundaryTape, Tape.input,
              Tape.move, Tape.moveRight, Tape.Equiv,
              Tape.dropTrailingNone]
      | cons c tail =>
          cases b <;> cases c <;>
            simp [resultNoneGuardRewindFinalTape,
              resultNoneGuardRewindBoundaryTape, Tape.input,
              Tape.move, Tape.moveRight, Tape.Equiv,
              Tape.dropTrailingNone,
              resultNoneGuardRewind_dropTrailingNone_map_some,
              resultNoneGuardRewind_dropTrailingNone_map_some_append_blanks]

def resultNoneGuardOffsetTransition
    (offset : Nat) (t : TransitionDescription) :
    TransitionDescription :=
  { source := offset + t.source
    read := t.read
    write := t.write
    move := t.move
    target := offset + t.target }

def resultNoneGuardRewindOffset : Nat :=
  ResultNoneGuardScannerDescription.stateCount

def resultNoneGuardScanRewindAcceptTransitions :
    List TransitionDescription :=
  [ MachineDescription.transition
      (resultNoneGuardState ResultNoneGuardBoundary.other.toNat 0 0)
      none none Direction.right
      (resultNoneGuardRewindOffset + ResultNoneGuardRewindDescription.start)
  , MachineDescription.transition
      (resultNoneGuardState ResultNoneGuardBoundary.tick.toNat 0 0)
      none none Direction.right
      (resultNoneGuardRewindOffset + ResultNoneGuardRewindDescription.start)
  , MachineDescription.transition
      (resultNoneGuardState ResultNoneGuardBoundary.tickDone.toNat 0 0)
      none none Direction.right
      (resultNoneGuardRewindOffset + ResultNoneGuardRewindDescription.start)
  ]

def ResultNoneGuardScanRewindDescription : MachineDescription where
  stateCount :=
    ResultNoneGuardScannerDescription.stateCount +
      ResultNoneGuardRewindDescription.stateCount
  start := ResultNoneGuardScannerDescription.start
  halt := resultNoneGuardRewindOffset + ResultNoneGuardRewindDescription.halt
  transitions :=
    resultNoneGuardBitTransitions ++
      resultNoneGuardScanRewindAcceptTransitions ++
        (ResultNoneGuardRewindDescription.transitions.map
          (resultNoneGuardOffsetTransition resultNoneGuardRewindOffset))

theorem resultNoneGuardScanRewindDescription_wellFormed :
    ResultNoneGuardScanRewindDescription.WellFormed := by
  refine ⟨by native_decide, by native_decide, by native_decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := ResultNoneGuardScanRewindDescription.transitions)
      (stateCount := ResultNoneGuardScanRewindDescription.stateCount)
      (by native_decide)
  · exact transition_deterministic_of_all
      (l := ResultNoneGuardScanRewindDescription.transitions)
      (by native_decide)

theorem resultNoneGuardScanRewindDescription_haltTransitionFree :
    ResultNoneGuardScanRewindDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := ResultNoneGuardScanRewindDescription.transitions)
    (state := ResultNoneGuardScanRewindDescription.halt)
    (by native_decide)

theorem resultNoneGuardScanRewindDescription_subroutineReady :
    ResultNoneGuardScanRewindDescription.SubroutineReady :=
  ⟨resultNoneGuardScanRewindDescription_wellFormed,
    resultNoneGuardScanRewindDescription_haltTransitionFree⟩

theorem resultNoneGuardScanRewindDescription_run_blank_of_accepts
    (boundary : ResultNoneGuardBoundary)
    (haccept : boundary.accepts)
    (leftRev : Word Bool) :
    ResultNoneGuardScanRewindDescription.runConfig 1
        { state := resultNoneGuardState boundary.toNat 0 0
          tape := MachineDescription.appendRightScanTape leftRev [] } =
      { state :=
          resultNoneGuardRewindOffset +
            ResultNoneGuardRewindDescription.start
        tape := resultNoneGuardScannedBlankTape leftRev } := by
  cases boundary
  · rfl
  · rfl
  · rfl
  · cases haccept
  · cases haccept

theorem resultNoneGuardScanRewindDescription_run_bits
    (boundary : ResultNoneGuardBoundary)
    (bit0 bit1 bit2 bit3 : Bool)
    (leftRev suffix : Word Bool) :
    ResultNoneGuardScanRewindDescription.runConfig 4
        { state := resultNoneGuardState boundary.toNat 0 0
          tape :=
            MachineDescription.appendRightScanTape leftRev
              (List.append [bit0, bit1, bit2, bit3] suffix) } =
      { state :=
          resultNoneGuardState
            (resultNoneGuardBoundaryUpdateCode boundary.toNat
              (resultNoneGuardCodeOfBits bit0 bit1 bit2 bit3)) 0 0
        tape := MachineDescription.appendRightScanTape
          (bit3 :: bit2 :: bit1 :: bit0 :: leftRev) suffix } := by
  cases boundary <;> cases bit0 <;> cases bit1 <;> cases bit2 <;>
    cases bit3 <;> cases suffix <;> rfl

theorem resultNoneGuardScanRewindDescription_run_encoded_symbol
    (boundary : ResultNoneGuardBoundary)
    (symbol : MachineCodeSymbol)
    (leftRev suffix : Word Bool) :
    ResultNoneGuardScanRewindDescription.runConfig 4
        { state := resultNoneGuardState boundary.toNat 0 0
          tape :=
            MachineDescription.appendRightScanTape leftRev
              (List.append
                (MachineDescription.encodeCodeSymbolAsInput symbol)
                suffix) } =
      { state :=
          resultNoneGuardState
            (resultNoneGuardBoundaryUpdateCode boundary.toNat
              (resultNoneGuardSymbolCode symbol)) 0 0
        tape :=
          MachineDescription.appendRightScanTape
            (List.append
              (MachineDescription.encodeCodeSymbolAsInput symbol).reverse
              leftRev)
            suffix } := by
  cases symbol
  · simpa [MachineDescription.encodeCodeSymbolAsInput,
      resultNoneGuardCodeOfBits, resultNoneGuardSymbolCode] using
      (resultNoneGuardScanRewindDescription_run_bits boundary
        false false false false leftRev suffix)
  · simpa [MachineDescription.encodeCodeSymbolAsInput,
      resultNoneGuardCodeOfBits, resultNoneGuardSymbolCode] using
      (resultNoneGuardScanRewindDescription_run_bits boundary
        false false false true leftRev suffix)
  · simpa [MachineDescription.encodeCodeSymbolAsInput,
      resultNoneGuardCodeOfBits, resultNoneGuardSymbolCode] using
      (resultNoneGuardScanRewindDescription_run_bits boundary
        false false true false leftRev suffix)
  · simpa [MachineDescription.encodeCodeSymbolAsInput,
      resultNoneGuardCodeOfBits, resultNoneGuardSymbolCode] using
      (resultNoneGuardScanRewindDescription_run_bits boundary
        false false true true leftRev suffix)
  · simpa [MachineDescription.encodeCodeSymbolAsInput,
      resultNoneGuardCodeOfBits, resultNoneGuardSymbolCode] using
      (resultNoneGuardScanRewindDescription_run_bits boundary
        false true false false leftRev suffix)
  · simpa [MachineDescription.encodeCodeSymbolAsInput,
      resultNoneGuardCodeOfBits, resultNoneGuardSymbolCode] using
      (resultNoneGuardScanRewindDescription_run_bits boundary
        false true false true leftRev suffix)
  · simpa [MachineDescription.encodeCodeSymbolAsInput,
      resultNoneGuardCodeOfBits, resultNoneGuardSymbolCode] using
      (resultNoneGuardScanRewindDescription_run_bits boundary
        false true true false leftRev suffix)
  · simpa [MachineDescription.encodeCodeSymbolAsInput,
      resultNoneGuardCodeOfBits, resultNoneGuardSymbolCode] using
      (resultNoneGuardScanRewindDescription_run_bits boundary
        false true true true leftRev suffix)
  · simpa [MachineDescription.encodeCodeSymbolAsInput,
      resultNoneGuardCodeOfBits, resultNoneGuardSymbolCode] using
      (resultNoneGuardScanRewindDescription_run_bits boundary
        true false false false leftRev suffix)

theorem resultNoneGuardScanRewindDescription_run_symbol
    (boundary : ResultNoneGuardBoundary)
    (symbol : MachineCodeSymbol)
    (leftRev suffix : Word Bool) :
    ResultNoneGuardScanRewindDescription.runConfig 4
        { state := resultNoneGuardState boundary.toNat 0 0
          tape :=
            MachineDescription.appendRightScanTape leftRev
              (List.append
                (MachineDescription.encodeCodeSymbolAsInput symbol)
                suffix) } =
      { state :=
          resultNoneGuardState (boundary.update symbol).toNat 0 0
        tape :=
          MachineDescription.appendRightScanTape
            (List.append
              (MachineDescription.encodeCodeSymbolAsInput symbol).reverse
              leftRev)
            suffix } := by
  rw [resultNoneGuardScanRewindDescription_run_encoded_symbol]
  rw [resultNoneGuardBoundaryUpdateCode_symbol]

theorem resultNoneGuardScanRewindDescription_run_code_from
    (boundary : ResultNoneGuardBoundary)
    (code : Word MachineCodeSymbol)
    (leftRev suffix : Word Bool) :
    ResultNoneGuardScanRewindDescription.runConfig
        (4 * code.length)
        { state := resultNoneGuardState boundary.toNat 0 0
          tape :=
            MachineDescription.appendRightScanTape leftRev
              (List.append
                (MachineDescription.encodeCodeWordAsInput code) suffix) } =
      { state :=
          resultNoneGuardState
            (resultNoneGuardScanBoundaryFrom boundary code).toNat 0 0
        tape :=
          MachineDescription.appendRightScanTape
            (List.append
              (MachineDescription.encodeCodeWordAsInput code).reverse
              leftRev)
            suffix } := by
  induction code generalizing boundary leftRev with
  | nil =>
      simp [MachineDescription.encodeCodeWordAsInput,
        resultNoneGuardScanBoundaryFrom,
        MachineDescription.runConfig]
  | cons symbol rest ih =>
      rw [show 4 * (symbol :: rest).length = 4 + 4 * rest.length by
        simp
        omega]
      rw [MachineDescription.runConfig_add]
      simp only [MachineDescription.encodeCodeWordAsInput]
      have happ :
          List.append
              (List.append
                (MachineDescription.encodeCodeSymbolAsInput symbol)
                (MachineDescription.encodeCodeWordAsInput rest))
              suffix =
            List.append
              (MachineDescription.encodeCodeSymbolAsInput symbol)
              (List.append
                (MachineDescription.encodeCodeWordAsInput rest)
                suffix) :=
        List.append_assoc
          (MachineDescription.encodeCodeSymbolAsInput symbol)
          (MachineDescription.encodeCodeWordAsInput rest) suffix
      rw [happ]
      change
        ResultNoneGuardScanRewindDescription.runConfig
            (4 * rest.length)
            (ResultNoneGuardScanRewindDescription.runConfig 4
              { state := resultNoneGuardState boundary.toNat 0 0
                tape :=
                  MachineDescription.appendRightScanTape leftRev
                    (List.append
                      (MachineDescription.encodeCodeSymbolAsInput symbol)
                      (List.append
                        (MachineDescription.encodeCodeWordAsInput rest)
                        suffix)) }) =
          { state :=
              resultNoneGuardState
                (resultNoneGuardScanBoundaryFrom boundary
                  (symbol :: rest)).toNat 0 0
            tape :=
              MachineDescription.appendRightScanTape
                (List.append
                  (List.append
                    (MachineDescription.encodeCodeSymbolAsInput symbol)
                    (MachineDescription.encodeCodeWordAsInput rest)).reverse
                  leftRev)
                suffix }
      rw [resultNoneGuardScanRewindDescription_run_symbol]
      rw [ih]
      simp [resultNoneGuardScanBoundaryFrom, List.reverse_append,
        List.append_assoc]

theorem resultNoneGuardScanRewindDescription_run_rewind_start
    (leftRev : Word Bool) :
    ResultNoneGuardScanRewindDescription.runConfig 2
        { state :=
            resultNoneGuardRewindOffset +
              ResultNoneGuardRewindDescription.start
          tape := resultNoneGuardScannedBlankTape leftRev } =
      { state := resultNoneGuardRewindOffset + 2
        tape := resultNoneGuardRewindLeftScanTape
          leftRev [none, none] } := by
  cases leftRev with
  | nil =>
      rfl
  | cons b rest =>
      cases b <;> rfl

theorem resultNoneGuardScanRewindDescription_run_rewind_left_scan
    (leftRev : Word Bool) (right : List (Option Bool)) :
    ResultNoneGuardScanRewindDescription.runConfig leftRev.length
        { state := resultNoneGuardRewindOffset + 2
          tape := resultNoneGuardRewindLeftScanTape leftRev right } =
      { state := resultNoneGuardRewindOffset + 2
        tape :=
          { left := []
            head := none
            right := (leftRev.reverse.map some) ++ right } } := by
  induction leftRev generalizing right with
  | nil =>
      rfl
  | cons b rest ih =>
      rw [show (b :: rest).length = 1 + rest.length by
        simp
        omega]
      rw [MachineDescription.runConfig_add]
      cases b
      · have hstep :
            ResultNoneGuardScanRewindDescription.runConfig 1
                { state := resultNoneGuardRewindOffset + 2
                  tape :=
                    resultNoneGuardRewindLeftScanTape
                      (false :: rest) right } =
              { state := resultNoneGuardRewindOffset + 2
                tape :=
                  resultNoneGuardRewindLeftScanTape rest
                    (some false :: right) } := by
          cases rest with
          | nil =>
              rfl
          | cons c tail =>
              cases c <;> rfl
        rw [hstep]
        rw [ih]
        simp [List.append_assoc]
      · have hstep :
            ResultNoneGuardScanRewindDescription.runConfig 1
                { state := resultNoneGuardRewindOffset + 2
                  tape :=
                    resultNoneGuardRewindLeftScanTape
                      (true :: rest) right } =
              { state := resultNoneGuardRewindOffset + 2
                tape :=
                  resultNoneGuardRewindLeftScanTape rest
                    (some true :: right) } := by
          cases rest with
          | nil =>
              rfl
          | cons c tail =>
              cases c <;> rfl
        rw [hstep]
        rw [ih]
        simp [List.append_assoc]

theorem resultNoneGuardScanRewindDescription_run_rewind_finish
    (bits : Word Bool) :
    ResultNoneGuardScanRewindDescription.runConfig 2
        { state := resultNoneGuardRewindOffset + 2
          tape := resultNoneGuardRewindBoundaryTape bits } =
      { state := ResultNoneGuardScanRewindDescription.halt
        tape := resultNoneGuardRewindFinalTape bits } := by
  cases bits with
  | nil =>
      rfl
  | cons b rest =>
      cases b <;> cases rest <;> rfl

theorem resultNoneGuardScanRewindDescription_run_rewind_scanned
    (bits : Word Bool) :
    ResultNoneGuardScanRewindDescription.runConfig
        (bits.length + 4)
        { state :=
            resultNoneGuardRewindOffset +
              ResultNoneGuardRewindDescription.start
          tape := resultNoneGuardScannedBlankTape bits.reverse } =
      { state := ResultNoneGuardScanRewindDescription.halt
        tape := resultNoneGuardRewindFinalTape bits } := by
  rw [show bits.length + 4 = 2 + (bits.length + 2) by omega]
  rw [MachineDescription.runConfig_add]
  rw [resultNoneGuardScanRewindDescription_run_rewind_start]
  rw [show bits.length + 2 = bits.reverse.length + 2 by simp]
  rw [MachineDescription.runConfig_add]
  rw [resultNoneGuardScanRewindDescription_run_rewind_left_scan]
  change
    ResultNoneGuardScanRewindDescription.runConfig 2
        { state := resultNoneGuardRewindOffset + 2
          tape :=
            { left := []
              head := none
              right := (bits.reverse.reverse.map some) ++ [none, none] } } =
      { state := ResultNoneGuardScanRewindDescription.halt
        tape := resultNoneGuardRewindFinalTape bits }
  simp only [List.reverse_reverse]
  exact resultNoneGuardScanRewindDescription_run_rewind_finish bits

theorem resultNoneGuardScanRewindDescription_run_code_halt_of_accepts
    (code : Word MachineCodeSymbol)
    (haccept : (resultNoneGuardScanBoundary code).accepts) :
    ResultNoneGuardScanRewindDescription.runConfig
        (4 * code.length + 1 +
          (MachineDescription.encodeCodeWordAsInput code).length + 4)
        (ResultNoneGuardScanRewindDescription.initial
          (MachineDescription.encodeCodeWordAsInput code)) =
      { state := ResultNoneGuardScanRewindDescription.halt
        tape :=
          resultNoneGuardRewindFinalTape
            (MachineDescription.encodeCodeWordAsInput code) } := by
  rw [show
      4 * code.length + 1 +
          (MachineDescription.encodeCodeWordAsInput code).length + 4 =
        4 * code.length +
          (1 + ((MachineDescription.encodeCodeWordAsInput code).length + 4)) by
    omega]
  rw [MachineDescription.runConfig_add]
  have hinitial :
      ResultNoneGuardScanRewindDescription.initial
          (MachineDescription.encodeCodeWordAsInput code) =
        { state :=
            resultNoneGuardState ResultNoneGuardBoundary.other.toNat 0 0
          tape :=
            MachineDescription.appendRightScanTape []
              (List.append
                (MachineDescription.encodeCodeWordAsInput code) []) } := by
    simp [ResultNoneGuardScanRewindDescription,
      ResultNoneGuardScannerDescription,
      MachineDescription.initial,
      MachineDescription.appendRightScanTape_nil_eq_input]
  rw [hinitial]
  rw [resultNoneGuardScanRewindDescription_run_code_from]
  rw [show
      1 + ((MachineDescription.encodeCodeWordAsInput code).length + 4) =
        1 + ((MachineDescription.encodeCodeWordAsInput code).length + 4) by
    rfl]
  rw [MachineDescription.runConfig_add]
  change
    ResultNoneGuardScanRewindDescription.runConfig
        ((MachineDescription.encodeCodeWordAsInput code).length + 4)
        (ResultNoneGuardScanRewindDescription.runConfig 1
          { state :=
              resultNoneGuardState
                (resultNoneGuardScanBoundaryFrom
                  ResultNoneGuardBoundary.other code).toNat 0 0
            tape :=
              MachineDescription.appendRightScanTape
                ((MachineDescription.encodeCodeWordAsInput code).reverse.append [])
                [] }) =
      { state := ResultNoneGuardScanRewindDescription.halt
        tape :=
          resultNoneGuardRewindFinalTape
            (MachineDescription.encodeCodeWordAsInput code) }
  rw [resultNoneGuardScanRewindDescription_run_blank_of_accepts]
  · simpa using
      resultNoneGuardScanRewindDescription_run_rewind_scanned
        (MachineDescription.encodeCodeWordAsInput code)
  · simpa [resultNoneGuardScanBoundary] using haccept

theorem resultNoneGuardScanRewindDescription_haltsWithTape_code_of_accepts
    (code : Word MachineCodeSymbol)
    (haccept : (resultNoneGuardScanBoundary code).accepts) :
    ResultNoneGuardScanRewindDescription.HaltsWithTape
      (MachineDescription.encodeCodeWordAsInput code)
      (resultNoneGuardRewindFinalTape
        (MachineDescription.encodeCodeWordAsInput code)) := by
  refine
    ⟨4 * code.length + 1 +
        (MachineDescription.encodeCodeWordAsInput code).length + 4, ?_⟩
  change
    (ResultNoneGuardScanRewindDescription.runConfig
          (4 * code.length + 1 +
            (MachineDescription.encodeCodeWordAsInput code).length + 4)
          (ResultNoneGuardScanRewindDescription.initial
            (MachineDescription.encodeCodeWordAsInput code))).state =
        ResultNoneGuardScanRewindDescription.halt ∧
      (ResultNoneGuardScanRewindDescription.runConfig
          (4 * code.length + 1 +
            (MachineDescription.encodeCodeWordAsInput code).length + 4)
          (ResultNoneGuardScanRewindDescription.initial
            (MachineDescription.encodeCodeWordAsInput code))).tape =
        resultNoneGuardRewindFinalTape
          (MachineDescription.encodeCodeWordAsInput code)
  rw [resultNoneGuardScanRewindDescription_run_code_halt_of_accepts
    code haccept]
  exact ⟨rfl, rfl⟩

theorem resultNoneGuard_moveLeft_moveRight_input_equiv
    (bits : Word Bool) :
    Tape.Equiv
      (Tape.move Direction.left
        (Tape.move Direction.right (Tape.input bits)))
      (Tape.input bits) := by
  cases bits with
  | nil =>
      simp [Tape.input, Tape.blank, Tape.move, Tape.moveLeft,
        Tape.moveRight, Tape.Equiv, Tape.dropTrailingNone]
  | cons b rest =>
      cases rest with
      | nil =>
          cases b <;>
            simp [Tape.input, Tape.move, Tape.moveLeft,
              Tape.moveRight, Tape.Equiv, Tape.dropTrailingNone]
      | cons c tail =>
          cases b <;> cases c <;>
            simp [Tape.input, Tape.move, Tape.moveLeft,
              Tape.moveRight, Tape.Equiv, Tape.dropTrailingNone,
              resultNoneGuardRewind_dropTrailingNone_map_some]

theorem resultNoneGuardRewindFinalTape_moveLeft_input_equiv
    (bits : Word Bool) :
    Tape.Equiv
      (Tape.move Direction.left
        (resultNoneGuardRewindFinalTape bits))
      (Tape.input bits) := by
  exact
    Tape.Equiv.trans
      (Tape.Equiv.move
        (resultNoneGuardRewindFinalTape_handoff_equiv bits)
        Direction.left)
      (resultNoneGuard_moveLeft_moveRight_input_equiv bits)

theorem resultNoneGuardScanRewindDescription_handoff_equiv_code_of_accepts
    (code : Word MachineCodeSymbol)
    (haccept : (resultNoneGuardScanBoundary code).accepts) :
    exists T : Tape Bool,
      ResultNoneGuardScanRewindDescription.HaltsWithTape
        (MachineDescription.encodeCodeWordAsInput code) T ∧
        Tape.Equiv
          (Tape.move Direction.left T)
          (Tape.input (MachineDescription.encodeCodeWordAsInput code)) := by
  refine
    ⟨resultNoneGuardRewindFinalTape
        (MachineDescription.encodeCodeWordAsInput code), ?_, ?_⟩
  · exact
      resultNoneGuardScanRewindDescription_haltsWithTape_code_of_accepts
        code haccept
  · exact
      resultNoneGuardRewindFinalTape_moveLeft_input_equiv
        (MachineDescription.encodeCodeWordAsInput code)

def ResultNoneGuardStageInputProjectionDescription : MachineDescription :=
  MachineDescription.seqSubroutine
    ResultNoneGuardScanRewindDescription
    ControllerStageInputProjection.Description
    Direction.left

theorem resultNoneGuardStageInputProjectionDescription_subroutineReady :
    ResultNoneGuardStageInputProjectionDescription.SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    resultNoneGuardScanRewindDescription_subroutineReady
    ⟨ControllerStageInputProjection.wellFormed,
      ControllerStageInputProjection.haltTransitionFree⟩

theorem resultNoneGuardStageInputProjectionDescription_haltsWithOutput_controllerEncode
    (C : MachineDescription.DovetailControllerLayout)
    (hraw : PairedRecognizerDovetailControllerRawOutput C.result = none) :
    ResultNoneGuardStageInputProjectionDescription.HaltsWithOutput
      (MachineDescription.encodeCodeWordAsInput
        (MachineDescription.DovetailControllerLayout.encode C))
      (MachineDescription.encodeCodeWordAsInput
        (MachineDescription.DovetailControllerLayout.stageInputCode C)) := by
  let code := MachineDescription.DovetailControllerLayout.encode C
  let inputBits := MachineDescription.encodeCodeWordAsInput code
  let stageBits :=
    MachineDescription.encodeCodeWordAsInput
      (MachineDescription.DovetailControllerLayout.stageInputCode C)
  have haccept : (resultNoneGuardScanBoundary code).accepts :=
    (resultNoneGuardScanBoundary_controllerEncode_accepts_iff C).mpr hraw
  rcases
      resultNoneGuardScanRewindDescription_handoff_equiv_code_of_accepts
        code haccept with
    ⟨Tguard, hguard, hguardMove⟩
  have hprojReady : ControllerStageInputProjection.Description.SubroutineReady :=
    ⟨ControllerStageInputProjection.wellFormed,
      ControllerStageInputProjection.haltTransitionFree⟩
  have hprojOut :
      ControllerStageInputProjection.Description.HaltsWithOutput
        inputBits stageBits := by
    simpa [code, inputBits, stageBits] using
      ControllerStageInputProjection.haltsWithOutput_encode C
  rcases hprojOut with ⟨nProj, hnProj⟩
  let Tproj : Tape Bool :=
    (ControllerStageInputProjection.Description.runConfig nProj
      (ControllerStageInputProjection.Description.initial inputBits)).tape
  have hprojTape :
      ControllerStageInputProjection.Description.HaltsFromTape
        (Tape.input inputBits) Tproj := by
    refine ⟨nProj, ?_⟩
    change
      (ControllerStageInputProjection.Description.runConfig nProj
        { state := ControllerStageInputProjection.Description.start
          tape := Tape.input inputBits }).state =
          ControllerStageInputProjection.Description.halt ∧
        (ControllerStageInputProjection.Description.runConfig nProj
          { state := ControllerStageInputProjection.Description.start
            tape := Tape.input inputBits }).tape = Tproj
    constructor
    · simpa [Tproj, MachineDescription.HaltsWithOutputIn] using hnProj.left
    · rfl
  rcases
      MachineDescription.HaltsFromTapeEquiv_of_input_equiv
        (Tape.Equiv.symm hguardMove) hprojTape with
    ⟨Tactual, hprojActual, hactualEquiv⟩
  have hprojReach :
      exists nB : Nat,
        ControllerStageInputProjection.Description.runConfig nB
            { state := ControllerStageInputProjection.Description.start
              tape := Tape.move Direction.left Tguard } =
          { state := ControllerStageInputProjection.Description.halt
            tape := Tactual } :=
    MachineDescription.runConfig_eq_halt_of_haltsFromTape hprojActual
  have hseqTape :
      ResultNoneGuardStageInputProjectionDescription.HaltsWithTape
        inputBits Tactual := by
    simpa [ResultNoneGuardStageInputProjectionDescription, inputBits] using
      MachineDescription.seqSubroutine_haltsWithTape_of_haltsWithTape
        resultNoneGuardScanRewindDescription_subroutineReady
        hprojReady hguard hprojReach
  have hTprojNorm : Tape.normalizedOutput Tproj = stageBits := by
    change
      Tape.normalizedOutput
          (ControllerStageInputProjection.Description.runConfig nProj
            (ControllerStageInputProjection.Description.initial inputBits)).tape =
        stageBits
    exact hnProj.right
  have hTactualNorm : Tape.normalizedOutput Tactual = stageBits :=
    (Tape.Equiv.normalizedOutput_eq hactualEquiv).trans hTprojNorm
  simpa [hTactualNorm, code, inputBits, stageBits] using
    MachineDescription.haltsWithOutput_of_haltsWithTape hseqTape

theorem resultNoneGuardStageInputProjectionDescription_haltsWithOutput_of_transform
    {code out : Word MachineCodeSymbol}
    (htransform :
      GuardProjectionPrimitive.transform code = some out) :
    ResultNoneGuardStageInputProjectionDescription.HaltsWithOutput
      (MachineDescription.encodeCodeWordAsInput code)
      (MachineDescription.encodeCodeWordAsInput out) := by
  rcases
      (guardProjectionPrimitive_transform_eq_some_iff code out).mp
        htransform with
    ⟨C, rfl, hraw, rfl⟩
  exact
    resultNoneGuardStageInputProjectionDescription_haltsWithOutput_controllerEncode
      C hraw

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

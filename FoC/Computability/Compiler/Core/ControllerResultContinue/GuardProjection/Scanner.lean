import FoC.Computability.Compiler.Core.CommonGround.SeqComposition
import FoC.Computability.Compiler.Core.ControllerResultContinue.Base
import FoC.Computability.Compiler.Core.ControllerStageInputProjection

set_option doc.verso true

/-!
# Controller result continuation guard/projection prefix
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace ControllerResultContinueConstruction

def ResultNoneGuardPrimitive : TapeCodePrimitive where
  transform := fun code =>
    match DovetailControllerLayout.decodeComplete code with
    | none => none
    | some C =>
        match PairedRecognizerDovetailControllerRawOutput C.result with
        | none => some code
        | some _ => none

def StageInputContinuePrimitive : TapeCodePrimitive where
  transform := fun code =>
    match DovetailLayout.decodeStageInputComplete code with
    | none => none
    | some (input, stage) =>
        some
          (DovetailControllerLayout.encode
            { input := input, stage := stage + 1, result := [] })

def GuardProjectionPrimitive : TapeCodePrimitive :=
  TapeCodePrimitive.compose
    ResultNoneGuardPrimitive
    PairedRecognizerDovetailControllerStageInputCodePrimitive

def DecomposedResultContinuePrimitive : TapeCodePrimitive :=
  TapeCodePrimitive.compose
    GuardProjectionPrimitive
    StageInputContinuePrimitive

theorem nextStage_encode_eq_header_input_succ_empty
    (C : DovetailControllerLayout) :
    DovetailControllerLayout.encode
        (DovetailControllerLayout.nextStage C) =
      MachineCodeSymbol.header ::
        encodeBoolWordAppend C.input
          (encodeNatAppend (C.stage + 1)
            (encodeBoolWordAppend [] [])) := by
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
              DovetailControllerLayout.rawOutput?] at h
        | cons second rest =>
            exact Or.inr ⟨first, second, rest, rfl⟩
  · intro h
    rcases h with rfl | ⟨first, second, rest, rfl⟩
    · rfl
    · rfl

theorem resultNoneGuardPrimitive_transform_eq_some_iff
    (code out : Word MachineCodeSymbol) :
    ResultNoneGuardPrimitive.transform code = some out <->
      exists C : DovetailControllerLayout,
        code = DovetailControllerLayout.encode C ∧
          PairedRecognizerDovetailControllerRawOutput C.result = none ∧
            out = code := by
  constructor
  · intro h
    unfold ResultNoneGuardPrimitive at h
    cases hdecode :
        DovetailControllerLayout.decodeComplete code with
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
                DovetailControllerLayout.decodeComplete_eq_some_encode
                  hdecode,
                hraw,
                rfl⟩
        | some result =>
            simp [hdecode, hraw] at h
  · intro h
    rcases h with ⟨C, rfl, hraw, rfl⟩
    unfold ResultNoneGuardPrimitive
    simp [DovetailControllerLayout.decodeComplete_encode,
      hraw]

theorem stageInputContinuePrimitive_transform_eq_some_iff
    (code out : Word MachineCodeSymbol) :
    StageInputContinuePrimitive.transform code = some out <->
      exists input : Word Bool,
      exists stage : Nat,
        code = DovetailLayout.stageInputCode input stage ∧
          out =
            DovetailControllerLayout.encode
              { input := input, stage := stage + 1, result := [] } := by
  constructor
  · intro h
    unfold StageInputContinuePrimitive at h
    cases hdecode :
        DovetailLayout.decodeStageInputComplete code with
    | none =>
        simp [hdecode] at h
    | some parsed =>
        rcases parsed with ⟨input, stage⟩
        simp [hdecode] at h
        subst out
        exact
          ⟨input, stage,
            DovetailLayout.decodeStageInputComplete_eq_some_stageInputCode
              hdecode,
            rfl⟩
  · intro h
    rcases h with ⟨input, stage, rfl, rfl⟩
    unfold StageInputContinuePrimitive
    simp [DovetailLayout.decodeStageInputComplete_stageInputCode]

theorem stageInputContinuePrimitive_stageInputCode
    (C : DovetailControllerLayout) :
    StageInputContinuePrimitive.transform
        (PairedRecognizerDovetailControllerStageInputCode C) =
      some
        (DovetailControllerLayout.encode
          (DovetailControllerLayout.nextStage C)) := by
  rcases C with ⟨input, stage, result⟩
  change
    StageInputContinuePrimitive.transform
        (DovetailLayout.stageInputCode input stage) =
      some
        (DovetailControllerLayout.encode
          { input := input, stage := stage + 1, result := [] })
  simp [StageInputContinuePrimitive,
    DovetailLayout.decodeStageInputComplete_stageInputCode]

theorem guardProjectionPrimitive_transform_eq_some_iff
    (code out : Word MachineCodeSymbol) :
    GuardProjectionPrimitive.transform code = some out <->
      exists C : DovetailControllerLayout,
        code = DovetailControllerLayout.encode C ∧
          PairedRecognizerDovetailControllerRawOutput C.result = none ∧
            out = PairedRecognizerDovetailControllerStageInputCode C := by
  constructor
  · intro h
    unfold GuardProjectionPrimitive at h
    unfold TapeCodePrimitive.compose at h
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
                (DovetailControllerLayout.encode C)
                out).mp hstage with
            ⟨C', hencode, hout⟩
          have hC' : C' = C := by
            have hdecodeC' :
                DovetailControllerLayout.decodeComplete
                    (DovetailControllerLayout.encode C) =
                  some C' := by
              rw [hencode]
              exact
                DovetailControllerLayout.decodeComplete_encode
                  C'
            have htmp : C = C' := by
              simpa [DovetailControllerLayout.decodeComplete_encode]
                using hdecodeC'
            exact htmp.symm
          subst C'
          exact hout
        exact ⟨C, rfl, hraw, hout⟩
  · intro h
    rcases h with ⟨C, rfl, hraw, rfl⟩
    unfold GuardProjectionPrimitive
    exact
      TapeCodePrimitive.compose_transform_some
        ((resultNoneGuardPrimitive_transform_eq_some_iff
          (DovetailControllerLayout.encode C)
          (DovetailControllerLayout.encode C)).mpr
          ⟨C, rfl, hraw, rfl⟩)
        (pairedRecognizerDovetailControllerStageInputCode_encode C)

theorem decomposedResultContinuePrimitive_transform_eq
    (code : Word MachineCodeSymbol) :
    DecomposedResultContinuePrimitive.transform code =
      PairedRecognizerDovetailControllerResultContinueCode.transform code := by
  unfold DecomposedResultContinuePrimitive
  unfold GuardProjectionPrimitive
  unfold TapeCodePrimitive.compose
  unfold ResultNoneGuardPrimitive
  unfold StageInputContinuePrimitive
  unfold PairedRecognizerDovetailControllerStageInputCodePrimitive
  unfold PairedRecognizerDovetailControllerResultContinueCode
  unfold DovetailControllerLayout.continueResultCodePrimitive
  unfold DovetailControllerLayout.continueResultCode
  cases hdecode :
      DovetailControllerLayout.decodeComplete code with
  | none =>
      simp [hdecode]
  | some C =>
      cases hraw :
          PairedRecognizerDovetailControllerRawOutput C.result with
      | none =>
          have hrawLayout :
              DovetailControllerLayout.rawOutput?
                  C.result = none := by
            simpa [PairedRecognizerDovetailControllerRawOutput] using hraw
          have hstage :
              DovetailLayout.decodeStageInputComplete
                  (PairedRecognizerDovetailControllerStageInputCode C) =
                some (C.input, C.stage) := by
            rcases C with ⟨input, stage, result⟩
            change
              DovetailLayout.decodeStageInputComplete
                  (DovetailLayout.stageInputCode
                    input stage) =
                some (input, stage)
            exact
              DovetailLayout.decodeStageInputComplete_stageInputCode
                input stage
          simp [hdecode, hraw, hrawLayout, hstage]
          cases C
          simp [DovetailControllerLayout.nextStage]
      | some out =>
          have hrawLayout :
              DovetailControllerLayout.rawOutput?
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
  [ transition
      (resultNoneGuardState boundary 0 0)
      (some false) (some false) Direction.right
      (resultNoneGuardState boundary 1 0)
  , transition
      (resultNoneGuardState boundary 0 0)
      (some true) (some true) Direction.right
      (resultNoneGuardState boundary 1 1)
  , transition
      (resultNoneGuardState boundary 1 0)
      (some false) (some false) Direction.right
      (resultNoneGuardState boundary 2 0)
  , transition
      (resultNoneGuardState boundary 1 0)
      (some true) (some true) Direction.right
      (resultNoneGuardState boundary 2 1)
  , transition
      (resultNoneGuardState boundary 1 1)
      (some false) (some false) Direction.right
      (resultNoneGuardState boundary 2 2)
  , transition
      (resultNoneGuardState boundary 1 1)
      (some true) (some true) Direction.right
      (resultNoneGuardState boundary 2 3)
  , transition
      (resultNoneGuardState boundary 2 0)
      (some false) (some false) Direction.right
      (resultNoneGuardState boundary 3 0)
  , transition
      (resultNoneGuardState boundary 2 0)
      (some true) (some true) Direction.right
      (resultNoneGuardState boundary 3 1)
  , transition
      (resultNoneGuardState boundary 2 1)
      (some false) (some false) Direction.right
      (resultNoneGuardState boundary 3 2)
  , transition
      (resultNoneGuardState boundary 2 1)
      (some true) (some true) Direction.right
      (resultNoneGuardState boundary 3 3)
  , transition
      (resultNoneGuardState boundary 2 2)
      (some false) (some false) Direction.right
      (resultNoneGuardState boundary 3 4)
  , transition
      (resultNoneGuardState boundary 2 2)
      (some true) (some true) Direction.right
      (resultNoneGuardState boundary 3 5)
  , transition
      (resultNoneGuardState boundary 2 3)
      (some false) (some false) Direction.right
      (resultNoneGuardState boundary 3 6)
  , transition
      (resultNoneGuardState boundary 2 3)
      (some true) (some true) Direction.right
      (resultNoneGuardState boundary 3 7)
  , transition
      (resultNoneGuardState boundary 3 0)
      (some false) (some false) Direction.right
      (resultNoneGuardState
        (resultNoneGuardBoundaryUpdateCode boundary 0) 0 0)
  , transition
      (resultNoneGuardState boundary 3 0)
      (some true) (some true) Direction.right
      (resultNoneGuardState
        (resultNoneGuardBoundaryUpdateCode boundary 1) 0 0)
  , transition
      (resultNoneGuardState boundary 3 1)
      (some false) (some false) Direction.right
      (resultNoneGuardState
        (resultNoneGuardBoundaryUpdateCode boundary 2) 0 0)
  , transition
      (resultNoneGuardState boundary 3 1)
      (some true) (some true) Direction.right
      (resultNoneGuardState
        (resultNoneGuardBoundaryUpdateCode boundary 3) 0 0)
  , transition
      (resultNoneGuardState boundary 3 2)
      (some false) (some false) Direction.right
      (resultNoneGuardState
        (resultNoneGuardBoundaryUpdateCode boundary 4) 0 0)
  , transition
      (resultNoneGuardState boundary 3 2)
      (some true) (some true) Direction.right
      (resultNoneGuardState
        (resultNoneGuardBoundaryUpdateCode boundary 5) 0 0)
  , transition
      (resultNoneGuardState boundary 3 3)
      (some false) (some false) Direction.right
      (resultNoneGuardState
        (resultNoneGuardBoundaryUpdateCode boundary 6) 0 0)
  , transition
      (resultNoneGuardState boundary 3 3)
      (some true) (some true) Direction.right
      (resultNoneGuardState
        (resultNoneGuardBoundaryUpdateCode boundary 7) 0 0)
  , transition
      (resultNoneGuardState boundary 3 4)
      (some false) (some false) Direction.right
      (resultNoneGuardState
        (resultNoneGuardBoundaryUpdateCode boundary 8) 0 0)
  , transition
      (resultNoneGuardState boundary 3 4)
      (some true) (some true) Direction.right
      (resultNoneGuardState
        (resultNoneGuardBoundaryUpdateCode boundary 9) 0 0)
  , transition
      (resultNoneGuardState boundary 3 5)
      (some false) (some false) Direction.right
      (resultNoneGuardState
        (resultNoneGuardBoundaryUpdateCode boundary 10) 0 0)
  , transition
      (resultNoneGuardState boundary 3 5)
      (some true) (some true) Direction.right
      (resultNoneGuardState
        (resultNoneGuardBoundaryUpdateCode boundary 11) 0 0)
  , transition
      (resultNoneGuardState boundary 3 6)
      (some false) (some false) Direction.right
      (resultNoneGuardState
        (resultNoneGuardBoundaryUpdateCode boundary 12) 0 0)
  , transition
      (resultNoneGuardState boundary 3 6)
      (some true) (some true) Direction.right
      (resultNoneGuardState
        (resultNoneGuardBoundaryUpdateCode boundary 13) 0 0)
  , transition
      (resultNoneGuardState boundary 3 7)
      (some false) (some false) Direction.right
      (resultNoneGuardState
        (resultNoneGuardBoundaryUpdateCode boundary 14) 0 0)
  , transition
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

def resultNoneGuardBitTransitionChunks :
    List (List TransitionDescription) :=
  [ resultNoneGuardPrefixTransitions
      ResultNoneGuardBoundary.other.toNat
  , resultNoneGuardPrefixTransitions
      ResultNoneGuardBoundary.tick.toNat
  , resultNoneGuardPrefixTransitions
      ResultNoneGuardBoundary.tickDone.toNat
  , resultNoneGuardPrefixTransitions
      ResultNoneGuardBoundary.falseResult.toNat
  , resultNoneGuardPrefixTransitions
      ResultNoneGuardBoundary.trueResult.toNat
  ]

def resultNoneGuardBlankTransitions :
    List TransitionDescription :=
  [ transition
      (resultNoneGuardState ResultNoneGuardBoundary.other.toNat 0 0)
      none none Direction.right resultNoneGuardHalt
  , transition
      (resultNoneGuardState ResultNoneGuardBoundary.tick.toNat 0 0)
      none none Direction.right resultNoneGuardHalt
  , transition
      (resultNoneGuardState ResultNoneGuardBoundary.tickDone.toNat 0 0)
      none none Direction.right resultNoneGuardHalt
  ]

def resultNoneGuardScannerTransitionChunks :
    List (List TransitionDescription) :=
  resultNoneGuardBitTransitionChunks ++
    [resultNoneGuardBlankTransitions]

def ResultNoneGuardScannerDescription : MachineDescription where
  stateCount := resultNoneGuardHalt + 1
  start := resultNoneGuardState ResultNoneGuardBoundary.other.toNat 0 0
  halt := resultNoneGuardHalt
  transitions := resultNoneGuardScannerTransitionChunks.flatten

theorem resultNoneGuardScannerDescription_wellFormed :
    ResultNoneGuardScannerDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_chunk_all
      (chunks := resultNoneGuardScannerTransitionChunks)
      (stateCount := ResultNoneGuardScannerDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_chunk_all
      (chunks := resultNoneGuardScannerTransitionChunks)
      (by decide)

theorem resultNoneGuardScannerDescription_haltTransitionFree :
    ResultNoneGuardScannerDescription.HaltTransitionFree :=
  transition_notFrom_of_chunk_all
    (chunks := resultNoneGuardScannerTransitionChunks)
    (state := ResultNoneGuardScannerDescription.halt)
    (by decide)

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
        (encodeCellsAppend (w.map some) []) =
      ResultNoneGuardBoundary.other := by
  induction w with
  | nil =>
      rfl
  | cons b rest ih =>
      cases b <;>
        simp [encodeCellsAppend,
          encodeCellAppend,
          encodeCell,
          resultNoneGuardScanBoundaryFrom,
          ResultNoneGuardBoundary.update, ih]

theorem resultNoneGuardScanBoundaryFrom_encodeNat_from_tick
    (n : Nat) :
    resultNoneGuardScanBoundaryFrom
        ResultNoneGuardBoundary.tick
        (encodeNat n) =
      ResultNoneGuardBoundary.tickDone := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simpa [encodeNat,
        resultNoneGuardScanBoundaryFrom,
        ResultNoneGuardBoundary.update] using ih

theorem resultNoneGuardScanBoundaryFrom_encodeNat_succ
    (boundary : ResultNoneGuardBoundary) (n : Nat) :
    resultNoneGuardScanBoundaryFrom boundary
        (encodeNat (n + 1)) =
      ResultNoneGuardBoundary.tickDone := by
  simp [encodeNat,
    resultNoneGuardScanBoundaryFrom,
    ResultNoneGuardBoundary.update,
    resultNoneGuardScanBoundaryFrom_encodeNat_from_tick]

theorem resultNoneGuardScanBoundaryFrom_encodeCells_singleton
    (b : Bool) :
    resultNoneGuardScanBoundaryFrom
        ResultNoneGuardBoundary.tickDone
        (encodeCellsAppend [some b] []) =
      (if b then ResultNoneGuardBoundary.trueResult
        else ResultNoneGuardBoundary.falseResult) := by
  cases b <;>
    rfl

theorem resultNoneGuardScanBoundaryFrom_encodeCells_cons_cons
    (first second : Bool) (rest : Word Bool) :
    resultNoneGuardScanBoundaryFrom
        ResultNoneGuardBoundary.tickDone
        (encodeCellsAppend
          ((first :: second :: rest).map some) []) =
      ResultNoneGuardBoundary.other := by
  cases first <;> cases second <;>
    simp [encodeCellsAppend,
      encodeCellAppend,
      encodeCell,
      resultNoneGuardScanBoundaryFrom,
      ResultNoneGuardBoundary.update,
      resultNoneGuardScanBoundaryFrom_encodeCells_some_other]

theorem resultNoneGuardScanBoundaryFrom_encodeBoolWord_singleton
    (boundary : ResultNoneGuardBoundary) (b : Bool) :
    resultNoneGuardScanBoundaryFrom boundary
        (encodeBoolWord [b]) =
      (if b then ResultNoneGuardBoundary.trueResult
        else ResultNoneGuardBoundary.falseResult) := by
  rw [show
      encodeBoolWord [b] =
        List.append (encodeNat 1)
          (encodeCellsAppend [some b] []) by
    simp [encodeBoolWord,
      encodeBoolWordAppend,
      encodeCellListAppend,
      encodeNatAppend]]
  rw [resultNoneGuardScanBoundaryFrom_append]
  rw [resultNoneGuardScanBoundaryFrom_encodeNat_succ]
  exact resultNoneGuardScanBoundaryFrom_encodeCells_singleton b

theorem resultNoneGuardScanBoundaryFrom_encodeBoolWord_cons_cons
    (boundary : ResultNoneGuardBoundary)
    (first second : Bool) (rest : Word Bool) :
    resultNoneGuardScanBoundaryFrom boundary
        (encodeBoolWord (first :: second :: rest)) =
      ResultNoneGuardBoundary.other := by
  rw [show
      encodeBoolWord (first :: second :: rest) =
        List.append
          (encodeNat (rest.length + 1 + 1))
          (encodeCellsAppend
            ((first :: second :: rest).map some) []) by
    simp [encodeBoolWord,
      encodeBoolWordAppend,
      encodeCellListAppend,
      encodeNatAppend]]
  rw [resultNoneGuardScanBoundaryFrom_append]
  rw [resultNoneGuardScanBoundaryFrom_encodeNat_succ]
  exact resultNoneGuardScanBoundaryFrom_encodeCells_cons_cons
    first second rest

theorem resultNoneGuardScanBoundaryFrom_encodeBoolWord_accepts_iff
    (boundary : ResultNoneGuardBoundary)
    (result : Word Bool) :
    (resultNoneGuardScanBoundaryFrom boundary
        (encodeBoolWord result)).accepts <->
      PairedRecognizerDovetailControllerRawOutput result = none := by
  cases result with
  | nil =>
      cases boundary <;>
        simp [encodeBoolWord,
          encodeBoolWordAppend,
          encodeCellListAppend,
          encodeCellsAppend,
          encodeNatAppend,
          encodeNat,
          resultNoneGuardScanBoundaryFrom,
          ResultNoneGuardBoundary.update,
          ResultNoneGuardBoundary.accepts,
          PairedRecognizerDovetailControllerRawOutput,
          DovetailControllerLayout.rawOutput?]
  | cons first tail =>
      cases tail with
      | nil =>
          cases first <;> cases boundary <;>
            simp [resultNoneGuardScanBoundaryFrom_encodeBoolWord_singleton,
              ResultNoneGuardBoundary.accepts,
              PairedRecognizerDovetailControllerRawOutput,
              DovetailControllerLayout.rawOutput?]
      | cons second rest =>
          cases first <;> cases second <;> cases boundary <;>
            simp [resultNoneGuardScanBoundaryFrom_encodeBoolWord_cons_cons,
              ResultNoneGuardBoundary.accepts,
              PairedRecognizerDovetailControllerRawOutput,
              DovetailControllerLayout.rawOutput?]

theorem resultNoneGuardScanBoundary_controllerEncode_accepts_iff
    (C : DovetailControllerLayout) :
    (resultNoneGuardScanBoundary
        (DovetailControllerLayout.encode C)).accepts <->
      PairedRecognizerDovetailControllerRawOutput C.result = none := by
  unfold resultNoneGuardScanBoundary
  rw [CommonGround.ControllerLayouts.encode_eq_header_stageInput_append_result C]
  simp only [resultNoneGuardScanBoundaryFrom,
    ResultNoneGuardBoundary.update]
  rw [resultNoneGuardScanBoundaryFrom_append]
  simpa [encodeBoolWord] using
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
          tape := appendRightScanTape leftRev
            (bit :: suffix) } =
      { state :=
          resultNoneGuardState boundary.toNat 1
            (resultNoneGuardBitValue bit)
        tape := appendRightScanTape
          (bit :: leftRev) suffix } := by
  cases boundary <;> cases bit <;> cases suffix <;> rfl

theorem resultNoneGuardScannerDescription_run_second_bit
    (boundary : ResultNoneGuardBoundary)
    (bit0 bit1 : Bool) (leftRev suffix : Word Bool) :
    ResultNoneGuardScannerDescription.runConfig 1
        { state :=
            resultNoneGuardState boundary.toNat 1
              (resultNoneGuardBitValue bit0)
          tape := appendRightScanTape leftRev
            (bit1 :: suffix) } =
      { state :=
          resultNoneGuardState boundary.toNat 2
            (resultNoneGuardBitValue bit0 * 2 +
              resultNoneGuardBitValue bit1)
        tape := appendRightScanTape
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
          tape := appendRightScanTape leftRev
            (bit2 :: suffix) } =
      { state :=
          resultNoneGuardState boundary.toNat 3
            ((resultNoneGuardBitValue bit0 * 2 +
                resultNoneGuardBitValue bit1) * 2 +
              resultNoneGuardBitValue bit2)
        tape := appendRightScanTape
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
          tape := appendRightScanTape leftRev
            (bit3 :: suffix) } =
      { state :=
          resultNoneGuardState
            (resultNoneGuardBoundaryUpdateCode boundary.toNat
              (resultNoneGuardCodeOfBits bit0 bit1 bit2 bit3)) 0 0
        tape := appendRightScanTape
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
            appendRightScanTape leftRev
              (List.append [bit0, bit1, bit2, bit3] suffix) } =
      { state :=
          resultNoneGuardState
            (resultNoneGuardBoundaryUpdateCode boundary.toNat
              (resultNoneGuardCodeOfBits bit0 bit1 bit2 bit3)) 0 0
        tape := appendRightScanTape
          (bit3 :: bit2 :: bit1 :: bit0 :: leftRev) suffix } := by
  rw [show 4 = 1 + 3 by decide, runConfig_add]
  change
    ResultNoneGuardScannerDescription.runConfig 3
        (ResultNoneGuardScannerDescription.runConfig 1
          { state := resultNoneGuardState boundary.toNat 0 0
            tape :=
              appendRightScanTape leftRev
                (bit0 :: bit1 :: bit2 :: bit3 :: suffix) }) =
      { state :=
          resultNoneGuardState
            (resultNoneGuardBoundaryUpdateCode boundary.toNat
              (resultNoneGuardCodeOfBits bit0 bit1 bit2 bit3)) 0 0
        tape := appendRightScanTape
          (bit3 :: bit2 :: bit1 :: bit0 :: leftRev) suffix }
  rw [resultNoneGuardScannerDescription_run_first_bit]
  rw [show 3 = 1 + 2 by decide, runConfig_add]
  change
    ResultNoneGuardScannerDescription.runConfig 2
        (ResultNoneGuardScannerDescription.runConfig 1
          { state :=
              resultNoneGuardState boundary.toNat 1
                (resultNoneGuardBitValue bit0)
            tape :=
              appendRightScanTape (bit0 :: leftRev)
                (bit1 :: bit2 :: bit3 :: suffix) }) =
      { state :=
          resultNoneGuardState
            (resultNoneGuardBoundaryUpdateCode boundary.toNat
              (resultNoneGuardCodeOfBits bit0 bit1 bit2 bit3)) 0 0
        tape := appendRightScanTape
          (bit3 :: bit2 :: bit1 :: bit0 :: leftRev) suffix }
  rw [resultNoneGuardScannerDescription_run_second_bit]
  rw [show 2 = 1 + 1 by decide, runConfig_add]
  change
    ResultNoneGuardScannerDescription.runConfig 1
        (ResultNoneGuardScannerDescription.runConfig 1
          { state :=
              resultNoneGuardState boundary.toNat 2
                (resultNoneGuardBitValue bit0 * 2 +
                  resultNoneGuardBitValue bit1)
            tape :=
              appendRightScanTape
                (bit1 :: bit0 :: leftRev)
                (bit2 :: bit3 :: suffix) }) =
      { state :=
          resultNoneGuardState
            (resultNoneGuardBoundaryUpdateCode boundary.toNat
              (resultNoneGuardCodeOfBits bit0 bit1 bit2 bit3)) 0 0
        tape := appendRightScanTape
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
            appendRightScanTape leftRev
              (List.append
                (encodeCodeSymbolAsInput symbol)
                suffix) } =
      { state :=
          resultNoneGuardState
            (resultNoneGuardBoundaryUpdateCode boundary.toNat
              (resultNoneGuardSymbolCode symbol)) 0 0
        tape :=
          appendRightScanTape
            (List.append
              (encodeCodeSymbolAsInput symbol).reverse
              leftRev)
            suffix } := by
  cases symbol
  · simpa [encodeCodeSymbolAsInput,
      resultNoneGuardCodeOfBits, resultNoneGuardSymbolCode] using
      (resultNoneGuardScannerDescription_run_bits boundary
        false false false false leftRev suffix)
  · simpa [encodeCodeSymbolAsInput,
      resultNoneGuardCodeOfBits, resultNoneGuardSymbolCode] using
      (resultNoneGuardScannerDescription_run_bits boundary
        false false false true leftRev suffix)
  · simpa [encodeCodeSymbolAsInput,
      resultNoneGuardCodeOfBits, resultNoneGuardSymbolCode] using
      (resultNoneGuardScannerDescription_run_bits boundary
        false false true false leftRev suffix)
  · simpa [encodeCodeSymbolAsInput,
      resultNoneGuardCodeOfBits, resultNoneGuardSymbolCode] using
      (resultNoneGuardScannerDescription_run_bits boundary
        false false true true leftRev suffix)
  · simpa [encodeCodeSymbolAsInput,
      resultNoneGuardCodeOfBits, resultNoneGuardSymbolCode] using
      (resultNoneGuardScannerDescription_run_bits boundary
        false true false false leftRev suffix)
  · simpa [encodeCodeSymbolAsInput,
      resultNoneGuardCodeOfBits, resultNoneGuardSymbolCode] using
      (resultNoneGuardScannerDescription_run_bits boundary
        false true false true leftRev suffix)
  · simpa [encodeCodeSymbolAsInput,
      resultNoneGuardCodeOfBits, resultNoneGuardSymbolCode] using
      (resultNoneGuardScannerDescription_run_bits boundary
        false true true false leftRev suffix)
  · simpa [encodeCodeSymbolAsInput,
      resultNoneGuardCodeOfBits, resultNoneGuardSymbolCode] using
      (resultNoneGuardScannerDescription_run_bits boundary
        false true true true leftRev suffix)
  · simpa [encodeCodeSymbolAsInput,
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
            appendRightScanTape leftRev
              (List.append
                (encodeCodeSymbolAsInput symbol)
                suffix) } =
      { state :=
          resultNoneGuardState (boundary.update symbol).toNat 0 0
        tape :=
          appendRightScanTape
            (List.append
              (encodeCodeSymbolAsInput symbol).reverse
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
            appendRightScanTape leftRev
              (List.append
                (encodeCodeWordAsInput code) suffix) } =
      { state :=
          resultNoneGuardState
            (resultNoneGuardScanBoundaryFrom boundary code).toNat 0 0
        tape :=
          appendRightScanTape
            (List.append
              (encodeCodeWordAsInput code).reverse
              leftRev)
            suffix } := by
  induction code generalizing boundary leftRev with
  | nil =>
      simp [encodeCodeWordAsInput,
        resultNoneGuardScanBoundaryFrom,
        runConfig]
  | cons symbol rest ih =>
      rw [show 4 * (symbol :: rest).length = 4 + 4 * rest.length by
        simp
        omega]
      rw [runConfig_add]
      simp only [encodeCodeWordAsInput]
      have happ :
          List.append
              (List.append
                (encodeCodeSymbolAsInput symbol)
                (encodeCodeWordAsInput rest))
              suffix =
            List.append
              (encodeCodeSymbolAsInput symbol)
              (List.append
                (encodeCodeWordAsInput rest)
                suffix) :=
        List.append_assoc
          (encodeCodeSymbolAsInput symbol)
          (encodeCodeWordAsInput rest) suffix
      rw [happ]
      change
        ResultNoneGuardScannerDescription.runConfig
            (4 * rest.length)
            (ResultNoneGuardScannerDescription.runConfig 4
              { state := resultNoneGuardState boundary.toNat 0 0
                tape :=
                  appendRightScanTape leftRev
                    (List.append
                      (encodeCodeSymbolAsInput symbol)
                      (List.append
                        (encodeCodeWordAsInput rest)
                        suffix)) }) =
          { state :=
              resultNoneGuardState
                (resultNoneGuardScanBoundaryFrom boundary
                  (symbol :: rest)).toNat 0 0
            tape :=
              appendRightScanTape
                (List.append
                  (List.append
                    (encodeCodeSymbolAsInput symbol)
                    (encodeCodeWordAsInput rest)).reverse
                  leftRev)
                suffix }
      rw [resultNoneGuardScannerDescription_run_symbol]
      rw [ih]
      simp [resultNoneGuardScanBoundaryFrom, List.reverse_append,
        List.append_assoc]

def resultNoneGuardScannedBlankTape
    (leftRev : Word Bool) : Tape Bool :=
  Tape.move Direction.right
    (appendRightScanTape leftRev [])

theorem resultNoneGuardScannerDescription_run_blank_of_accepts
    (boundary : ResultNoneGuardBoundary)
    (haccept : boundary.accepts)
    (leftRev : Word Bool) :
    ResultNoneGuardScannerDescription.runConfig 1
        { state := resultNoneGuardState boundary.toNat 0 0
          tape := appendRightScanTape leftRev [] } =
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
          (encodeCodeWordAsInput code)) =
      { state := ResultNoneGuardScannerDescription.halt
        tape :=
          resultNoneGuardScannedBlankTape
            (encodeCodeWordAsInput code).reverse } := by
  rw [runConfig_add]
  have hinitial :
      ResultNoneGuardScannerDescription.initial
          (encodeCodeWordAsInput code) =
        { state :=
            resultNoneGuardState ResultNoneGuardBoundary.other.toNat 0 0
          tape :=
            appendRightScanTape []
              (List.append
                (encodeCodeWordAsInput code) []) } := by
    simp [ResultNoneGuardScannerDescription,
      initial,
      appendRightScanTape_nil_eq_input]
  rw [hinitial]
  rw [resultNoneGuardScannerDescription_run_code_from]
  simpa [resultNoneGuardScanBoundary] using
    resultNoneGuardScannerDescription_run_blank_of_accepts
      (resultNoneGuardScanBoundary code) haccept
      (encodeCodeWordAsInput code).reverse

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
    appendRightScanTape, Tape.move,
    Tape.moveRight, Tape.normalizedOutput, Tape.cells,
    hfilter]

theorem resultNoneGuardScannerDescription_haltsWithOutput_code_of_accepts
    (code : Word MachineCodeSymbol)
    (haccept : (resultNoneGuardScanBoundary code).accepts) :
    ResultNoneGuardScannerDescription.HaltsWithOutput
      (encodeCodeWordAsInput code)
      (encodeCodeWordAsInput code) := by
  refine ⟨4 * code.length + 1, ?_⟩
  constructor
  · rw [resultNoneGuardScannerDescription_run_code_halt_of_accepts
      code haccept]
  · rw [resultNoneGuardScannerDescription_run_code_halt_of_accepts
      code haccept]
    simp [resultNoneGuardScannedBlankTape_normalizedOutput]

theorem resultNoneGuardScannerDescription_haltsWithOutput_controllerEncode
    (C : DovetailControllerLayout)
    (hraw : PairedRecognizerDovetailControllerRawOutput C.result = none) :
    ResultNoneGuardScannerDescription.HaltsWithOutput
      (encodeCodeWordAsInput
        (DovetailControllerLayout.encode C))
      (encodeCodeWordAsInput
        (DovetailControllerLayout.encode C)) := by
  exact
    resultNoneGuardScannerDescription_haltsWithOutput_code_of_accepts
      (DovetailControllerLayout.encode C)
      ((resultNoneGuardScanBoundary_controllerEncode_accepts_iff C).mpr
        hraw)


end ControllerResultContinueConstruction

end Computability
end FoC

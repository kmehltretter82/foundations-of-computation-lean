import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.FixedSkips
import FoC.Computability.Compiler.Core.CommonGround.SeqComposition
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.PostPaddingFieldEraser

set_option doc.verso true

/-!
# Post-padding prefix scanners

This module builds the fixed scanner prefix used before deleting an unselected
configuration field.  It validates the selected-projection output prefix
header, the quoted parsed layout Boolean word, and the following stage natural,
then halts just left of the first configuration field.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.SeqComposition
open FoC.Computability.DovetailInitialLayoutInitializer
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner

namespace EncodedRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

open CanonicalLayouts.DovetailLayoutScanner
open CanonicalLayouts.DovetailStagePrefix

def postPaddingOutputPrefixScannerDescription : MachineDescription :=
  SeqViaCanonical
    CommonGround.FiniteTransducers.rightMoveAcrossFourBitsDescription
    BoolWordSuffixScannerDescription

theorem postPaddingOutputPrefixScannerDescription_subroutineReady :
    postPaddingOutputPrefixScannerDescription.SubroutineReady :=
  SeqViaCanonical_subroutineReady
    CommonGround.FiniteTransducers.rightMoveAcrossFourBitsDescription_subroutineReady
    boolWordSuffixScannerDescription_subroutineReady

def postPaddingOutputPrefixStageScannerDescription :
    MachineDescription :=
  seqSubroutine
    postPaddingOutputPrefixScannerDescription
    NonemptyNatSuffixScannerDescription
    Direction.right

theorem postPaddingOutputPrefixStageScannerDescription_subroutineReady :
    postPaddingOutputPrefixStageScannerDescription.SubroutineReady :=
  seqSubroutine_subroutineReady
    postPaddingOutputPrefixScannerDescription_subroutineReady
    nonemptyNatSuffixScannerDescription_subroutineReady

def postPaddingOutputPrefixHeaderBase
    (baseLeft : List (Option Bool)) : List (Option Bool) :=
  List.append
    ((encodeCodeSymbolAsInput MachineCodeSymbol.header).reverse.map some)
    baseLeft

def postPaddingOutputPrefixStageHandoffBase
    (quoted : Word Bool) (baseLeft : List (Option Bool)) :
    List (Option Bool) :=
  cellListCanonicalRestoredLeftWithBase (quoted.map some)
    (postPaddingOutputPrefixHeaderBase baseLeft)

def postPaddingOutputPrefixStageScannerTargetTape
    (quoted : Word Bool) (stage : Nat)
    (baseLeft : List (Option Bool)) (fieldTail : Word Bool) :
    Tape Bool :=
  (nonemptyNatSuffixHandoffConfigWithBase stage
    (postPaddingOutputPrefixStageHandoffBase quoted baseLeft)
    (false :: fieldTail)).tape

def postPaddingOutputPrefixStageScannerTargetTapeWithRight
    (quoted : Word Bool) (stage : Nat)
    (baseLeft : List (Option Bool)) (fieldTail : Word Bool)
    (rightPadding : List (Option Bool)) : Tape Bool :=
  (nonemptyNatSuffixHandoffConfigWithBaseAndRight stage
    (postPaddingOutputPrefixStageHandoffBase quoted baseLeft)
    (false :: fieldTail) rightPadding).tape

def postPaddingOutputPrefixAfterStageBase
    (quoted : Word Bool) (stage : Nat)
    (baseLeft : List (Option Bool)) : List (Option Bool) :=
  List.append ((stageNatBits stage).reverse.map some)
    (postPaddingOutputPrefixStageHandoffBase quoted baseLeft)

theorem postPaddingOutputPrefixStageHandoffBase_eq_bits_reverse
    (quoted : Word Bool) (baseLeft : List (Option Bool)) :
    postPaddingOutputPrefixStageHandoffBase quoted baseLeft =
      List.append
        ((encodeCodeWordAsInput
          (encodeBoolWordAppend quoted [])).reverse.map some)
        (postPaddingOutputPrefixHeaderBase baseLeft) := by
  rw [postPaddingOutputPrefixStageHandoffBase]
  rw [← cellListCanonicalRestoredBitsRev_map_some_withBase
    (quoted.map some) (postPaddingOutputPrefixHeaderBase baseLeft)]
  have hbits :
      cellListFieldBits (quoted.map some) [] =
        encodeCodeWordAsInput (encodeBoolWordAppend quoted []) := by
    simpa [cellListFieldBits, encodeCodeWordAsInput] using
      (boolWordBits_eq_encodeBoolWordAppend quoted []).symm
  rw [← hbits]
  rw [← cellListCanonicalRestoredBitsRev_reverse (quoted.map some)]
  simp

theorem postPaddingOutputPrefixAfterStageBase_eq_bits_reverse
    (quoted : Word Bool) (stage : Nat)
    (baseLeft : List (Option Bool)) :
    postPaddingOutputPrefixAfterStageBase quoted stage baseLeft =
      List.append ((stageNatBits stage).reverse.map some)
        (List.append
          ((encodeCodeWordAsInput
            (encodeBoolWordAppend quoted [])).reverse.map some)
          (postPaddingOutputPrefixHeaderBase baseLeft)) := by
  rw [postPaddingOutputPrefixAfterStageBase,
    postPaddingOutputPrefixStageHandoffBase_eq_bits_reverse]

def postPaddingOutputPrefixStageConfigScannerDescription :
    MachineDescription :=
  seqSubroutine
    postPaddingOutputPrefixStageScannerDescription
    ConfigurationSuffixScannerDescription
    Direction.right

theorem postPaddingOutputPrefixStageConfigScannerDescription_subroutineReady :
    postPaddingOutputPrefixStageConfigScannerDescription.SubroutineReady :=
  seqSubroutine_subroutineReady
    postPaddingOutputPrefixStageScannerDescription_subroutineReady
    configurationSuffixScannerDescription_subroutineReady

def postPaddingOutputPrefixStageConfigScannerTargetTape
    (quoted : Word Bool) (stage : Nat) (cfg : Configuration)
    (baseLeft : List (Option Bool)) (suffixTail : Word Bool) :
    Tape Bool :=
  (cellListCanonicalHandoffConfigWithBase cfg.tape.right
    (List.append ((cellCodeBits cfg.tape.head).reverse.map some)
      (cellListCanonicalRestoredLeftWithBase cfg.tape.left
        (List.append ((stageNatBits cfg.state).reverse.map some)
          (postPaddingOutputPrefixAfterStageBase
            quoted stage baseLeft))))
    (false :: suffixTail)).tape

def postPaddingOutputPrefixStageConfigScannerTargetTapeWithRight
    (quoted : Word Bool) (stage : Nat) (cfg : Configuration)
    (baseLeft : List (Option Bool)) (suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) : Tape Bool :=
  (cellListCanonicalHandoffConfigWithBaseAndRight cfg.tape.right
    (List.append ((cellCodeBits cfg.tape.head).reverse.map some)
      (cellListCanonicalRestoredLeftWithBase cfg.tape.left
        (List.append ((stageNatBits cfg.state).reverse.map some)
          (postPaddingOutputPrefixAfterStageBase
            quoted stage baseLeft))))
    (false :: suffixTail) rightPadding).tape

theorem rightMoveAcrossFourBitsDescription_haltsFrom_header
    (baseLeft right : List (Option Bool)) :
    CommonGround.FiniteTransducers.rightMoveAcrossFourBitsDescription.HaltsFromTape
      (tapeAtCells baseLeft
        (List.append
          ((encodeCodeSymbolAsInput MachineCodeSymbol.header).map some)
          right))
      (tapeAtCells
        (postPaddingOutputPrefixHeaderBase baseLeft)
        right) := by
  simpa [postPaddingOutputPrefixHeaderBase, encodeCodeSymbolAsInput,
    CommonGround.FiniteTransducers.tapeAtCells, tapeAtCells]
    using
      CommonGround.FiniteTransducers.rightMoveAcrossFourBitsDescription_haltsFromTape_bits
        false false false false baseLeft right

theorem postPaddingStageNatBits_cons_cons
    (n : Nat) :
    exists first : Bool,
    exists second : Bool,
    exists rest : Word Bool,
      stageNatBits n = first :: second :: rest := by
  cases n with
  | zero =>
      exact ⟨false, false, [true, true], by simp [stageNatBits_zero]⟩
  | succ n =>
      exact
        ⟨false, false, true :: false :: stageNatBits n,
          by simp [stageNatBits_succ]⟩

theorem postPaddingOutputPrefixHeaderTarget_move_left_move_right
    (quoted stageTail : Word Bool)
    (baseLeft : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (tapeAtCells
            (postPaddingOutputPrefixHeaderBase baseLeft)
            (List.append
              ((encodeCodeWordAsInput
                (encodeBoolWordAppend quoted [])).map some)
              (some false :: stageTail.map some)))) =
      tapeAtCells
        (postPaddingOutputPrefixHeaderBase baseLeft)
        (List.append
          ((encodeCodeWordAsInput
            (encodeBoolWordAppend quoted [])).map some)
          (some false :: stageTail.map some)) := by
  rcases postPaddingStageNatBits_cons_cons quoted.length with
    ⟨first, second, rest, hstage⟩
  rw [boolWordBits_eq_encodeBoolWordAppend]
  rw [hstage]
  simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight,
    List.map_append, List.append_assoc]

theorem postPaddingOutputPrefixHeaderTarget_move_left_move_right_withRight
    (quoted stageTail : Word Bool)
    (baseLeft rightPadding : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (tapeAtCells
            (postPaddingOutputPrefixHeaderBase baseLeft)
            (List.append
              ((encodeCodeWordAsInput
                (encodeBoolWordAppend quoted [])).map some)
              (some false ::
                List.append (stageTail.map some) rightPadding)))) =
      tapeAtCells
        (postPaddingOutputPrefixHeaderBase baseLeft)
        (List.append
          ((encodeCodeWordAsInput
            (encodeBoolWordAppend quoted [])).map some)
          (some false ::
            List.append (stageTail.map some) rightPadding)) := by
  rcases postPaddingStageNatBits_cons_cons quoted.length with
    ⟨first, second, rest, hstage⟩
  rw [boolWordBits_eq_encodeBoolWordAppend]
  rw [hstage]
  simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight,
    List.map_append, List.append_assoc]

theorem boolWordSuffixScannerDescription_haltsFrom_outputPrefixTail
    (quoted stageTail : Word Bool)
    (baseLeft : List (Option Bool)) :
    BoolWordSuffixScannerDescription.HaltsFromTape
      (tapeAtCells
        (postPaddingOutputPrefixHeaderBase baseLeft)
        (List.append
          ((encodeCodeWordAsInput
            (encodeBoolWordAppend quoted [])).map some)
          (some false :: stageTail.map some)))
      (boolWordCanonicalHandoffConfigWithBase quoted
        (postPaddingOutputPrefixHeaderBase baseLeft)
        (false :: stageTail)).tape := by
  rcases
      run_boolWordSuffix_raw_to_canonical_handoff_withBase
        quoted
        (postPaddingOutputPrefixHeaderBase baseLeft)
        stageTail with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  constructor
  · simpa [boolWordBits_eq_encodeBoolWordAppend, List.map_append,
      List.append_assoc] using
      congrArg Configuration.state hsteps
  · simpa [boolWordBits_eq_encodeBoolWordAppend, List.map_append,
      List.append_assoc] using
      congrArg Configuration.tape hsteps

theorem boolWordSuffixScannerDescription_haltsFrom_outputPrefixTail_withRight
    (quoted stageTail : Word Bool)
    (baseLeft rightPadding : List (Option Bool)) :
    BoolWordSuffixScannerDescription.HaltsFromTape
      (tapeAtCells
        (postPaddingOutputPrefixHeaderBase baseLeft)
        (List.append
          ((encodeCodeWordAsInput
            (encodeBoolWordAppend quoted [])).map some)
          (some false ::
            List.append (stageTail.map some) rightPadding)))
      (boolWordCanonicalHandoffConfigWithBaseAndRight quoted
        (postPaddingOutputPrefixHeaderBase baseLeft)
        (false :: stageTail) rightPadding).tape := by
  rcases
      run_boolWordSuffix_raw_to_canonical_handoff_withBaseAndRight
        quoted
        (postPaddingOutputPrefixHeaderBase baseLeft)
        stageTail
        rightPadding with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  constructor
  · simpa [boolWordBits_eq_encodeBoolWordAppend, List.map_append,
      List.append_assoc] using
      congrArg Configuration.state hsteps
  · simpa [boolWordBits_eq_encodeBoolWordAppend, List.map_append,
      List.append_assoc] using
      congrArg Configuration.tape hsteps

theorem postPaddingOutputPrefixScannerDescription_haltsFrom
    (quoted stageTail : Word Bool)
    (baseLeft : List (Option Bool)) :
    postPaddingOutputPrefixScannerDescription.HaltsFromTape
      (tapeAtCells baseLeft
        (List.append
          ((encodeCodeSymbolAsInput MachineCodeSymbol.header).map some)
          (List.append
            ((encodeCodeWordAsInput
              (encodeBoolWordAppend quoted [])).map some)
            (some false :: stageTail.map some))))
      (boolWordCanonicalHandoffConfigWithBase quoted
        (postPaddingOutputPrefixHeaderBase baseLeft)
        (false :: stageTail)).tape := by
  exact
    SeqViaCanonical_haltsFromTape_of_haltsFromTape
      CommonGround.FiniteTransducers.rightMoveAcrossFourBitsDescription_subroutineReady
      boolWordSuffixScannerDescription_subroutineReady
      (rightMoveAcrossFourBitsDescription_haltsFrom_header
        baseLeft
        (List.append
          ((encodeCodeWordAsInput
            (encodeBoolWordAppend quoted [])).map some)
          (some false :: stageTail.map some)))
      (postPaddingOutputPrefixHeaderTarget_move_left_move_right
        quoted stageTail baseLeft)
      (boolWordSuffixScannerDescription_haltsFrom_outputPrefixTail
        quoted stageTail baseLeft)

theorem postPaddingOutputPrefixScannerDescription_haltsFrom_withRight
    (quoted stageTail : Word Bool)
    (baseLeft rightPadding : List (Option Bool)) :
    postPaddingOutputPrefixScannerDescription.HaltsFromTape
      (tapeAtCells baseLeft
        (List.append
          ((encodeCodeSymbolAsInput MachineCodeSymbol.header).map some)
          (List.append
            ((encodeCodeWordAsInput
              (encodeBoolWordAppend quoted [])).map some)
            (some false ::
              List.append (stageTail.map some) rightPadding))))
      (boolWordCanonicalHandoffConfigWithBaseAndRight quoted
        (postPaddingOutputPrefixHeaderBase baseLeft)
        (false :: stageTail) rightPadding).tape := by
  exact
    SeqViaCanonical_haltsFromTape_of_haltsFromTape
      CommonGround.FiniteTransducers.rightMoveAcrossFourBitsDescription_subroutineReady
      boolWordSuffixScannerDescription_subroutineReady
      (rightMoveAcrossFourBitsDescription_haltsFrom_header
        baseLeft
        (List.append
          ((encodeCodeWordAsInput
            (encodeBoolWordAppend quoted [])).map some)
          (some false ::
            List.append (stageTail.map some) rightPadding)))
      (postPaddingOutputPrefixHeaderTarget_move_left_move_right_withRight
        quoted stageTail baseLeft rightPadding)
      (boolWordSuffixScannerDescription_haltsFrom_outputPrefixTail_withRight
        quoted stageTail baseLeft rightPadding)

theorem nonemptyNatSuffixScannerDescription_haltsFrom_outputPrefixStage
    (quoted : Word Bool) (stage : Nat)
    (baseLeft : List (Option Bool)) (fieldTail : Word Bool) :
    NonemptyNatSuffixScannerDescription.HaltsFromTape
      (tapeAtCells
        (postPaddingOutputPrefixStageHandoffBase quoted baseLeft)
        (List.append ((stageNatBits stage).map some)
          (some false :: fieldTail.map some)))
      (postPaddingOutputPrefixStageScannerTargetTape
        quoted stage baseLeft fieldTail) := by
  rcases
      run_nonemptyNatSuffix_raw_to_handoff_withBase
        stage
        (postPaddingOutputPrefixStageHandoffBase quoted baseLeft)
        false fieldTail with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  constructor
  · simpa [postPaddingOutputPrefixStageScannerTargetTape] using
      congrArg Configuration.state hsteps
  · simpa [postPaddingOutputPrefixStageScannerTargetTape] using
      congrArg Configuration.tape hsteps

theorem nonemptyNatSuffixScannerDescription_haltsFrom_outputPrefixStage_withRight
    (quoted : Word Bool) (stage : Nat)
    (baseLeft : List (Option Bool)) (fieldTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    NonemptyNatSuffixScannerDescription.HaltsFromTape
      (tapeAtCells
        (postPaddingOutputPrefixStageHandoffBase quoted baseLeft)
        (List.append ((stageNatBits stage).map some)
          (some false ::
            List.append (fieldTail.map some) rightPadding)))
      (postPaddingOutputPrefixStageScannerTargetTapeWithRight
        quoted stage baseLeft fieldTail rightPadding) := by
  rcases
      run_nonemptyNatSuffix_raw_to_handoff_withBaseAndRight
        stage
        (postPaddingOutputPrefixStageHandoffBase quoted baseLeft)
        false fieldTail rightPadding with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  constructor
  · simpa [postPaddingOutputPrefixStageScannerTargetTapeWithRight] using
      congrArg Configuration.state hsteps
  · simpa [postPaddingOutputPrefixStageScannerTargetTapeWithRight] using
      congrArg Configuration.tape hsteps

theorem postPaddingOutputPrefixScannerTarget_move_right_eq_stageSource
    (quoted : Word Bool) (stage : Nat)
    (baseLeft : List (Option Bool)) (fieldTail stageTail : Word Bool)
    (hstage : stageNatBits stage = false :: stageTail) :
    Tape.move Direction.right
        (boolWordCanonicalHandoffConfigWithBase quoted
          (postPaddingOutputPrefixHeaderBase baseLeft)
          (false :: List.append stageTail (false :: fieldTail))).tape =
      tapeAtCells
        (postPaddingOutputPrefixStageHandoffBase quoted baseLeft)
        (List.append ((stageNatBits stage).map some)
          (some false :: fieldTail.map some)) := by
  rw [boolWordCanonicalHandoffConfigWithBase_move_right_all]
  rw [hstage]
  simp [postPaddingOutputPrefixStageHandoffBase,
    List.map_append]

theorem postPaddingOutputPrefixStageScannerDescription_haltsFrom_raw
    (quoted : Word Bool) (stage : Nat)
    (baseLeft : List (Option Bool)) (fieldTail : Word Bool) :
    postPaddingOutputPrefixStageScannerDescription.HaltsFromTape
      (tapeAtCells baseLeft
        (List.append
          ((encodeCodeSymbolAsInput MachineCodeSymbol.header).map some)
          (List.append
            ((encodeCodeWordAsInput
              (encodeBoolWordAppend quoted [])).map some)
            (List.append ((stageNatBits stage).map some)
              (some false :: fieldTail.map some)))))
      (postPaddingOutputPrefixStageScannerTargetTape
        quoted stage baseLeft fieldTail) := by
  rcases stageNatBits_cons_false stage with
    ⟨stageTail, hstage⟩
  refine
    seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      (A := postPaddingOutputPrefixScannerDescription)
      (B := NonemptyNatSuffixScannerDescription)
      (handoffMove := Direction.right)
      (Tmid :=
        (boolWordCanonicalHandoffConfigWithBase quoted
          (postPaddingOutputPrefixHeaderBase baseLeft)
          (false :: List.append stageTail (false :: fieldTail))).tape)
      (Tnext :=
        tapeAtCells
          (postPaddingOutputPrefixStageHandoffBase quoted baseLeft)
          (List.append ((stageNatBits stage).map some)
            (some false :: fieldTail.map some)))
      postPaddingOutputPrefixScannerDescription_subroutineReady
      nonemptyNatSuffixScannerDescription_subroutineReady
      ?hprefix ?hmove ?hstageRun
  · rw [hstage]
    simpa [List.map_append, List.append_assoc] using
      postPaddingOutputPrefixScannerDescription_haltsFrom
        quoted (List.append stageTail (false :: fieldTail)) baseLeft
  · exact
      postPaddingOutputPrefixScannerTarget_move_right_eq_stageSource
        quoted stage baseLeft fieldTail stageTail hstage
  · exact
      nonemptyNatSuffixScannerDescription_haltsFrom_outputPrefixStage
        quoted stage baseLeft fieldTail

theorem postPaddingOutputPrefixScannerTarget_move_right_eq_stageSource_withRight
    (quoted : Word Bool) (stage : Nat)
    (baseLeft : List (Option Bool)) (fieldTail stageTail : Word Bool)
    (rightPadding : List (Option Bool))
    (hstage : stageNatBits stage = false :: stageTail) :
    Tape.move Direction.right
        (boolWordCanonicalHandoffConfigWithBaseAndRight quoted
          (postPaddingOutputPrefixHeaderBase baseLeft)
          (false :: List.append stageTail (false :: fieldTail))
          rightPadding).tape =
      tapeAtCells
        (postPaddingOutputPrefixStageHandoffBase quoted baseLeft)
        (List.append ((stageNatBits stage).map some)
          (some false ::
            List.append (fieldTail.map some) rightPadding)) := by
  rw [hstage]
  simpa [boolWordCanonicalHandoffConfigWithBaseAndRight,
    postPaddingOutputPrefixStageHandoffBase, List.map_append,
    List.append_assoc] using
    cellListCanonicalHandoffConfigWithBaseAndRight_move_right
      (quoted.map some)
      (postPaddingOutputPrefixHeaderBase baseLeft)
      false (List.append stageTail (false :: fieldTail))
      rightPadding

theorem postPaddingOutputPrefixStageScannerDescription_haltsFrom_raw_withRight
    (quoted : Word Bool) (stage : Nat)
    (baseLeft : List (Option Bool)) (fieldTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    postPaddingOutputPrefixStageScannerDescription.HaltsFromTape
      (tapeAtCells baseLeft
        (List.append
          ((encodeCodeSymbolAsInput MachineCodeSymbol.header).map some)
          (List.append
            ((encodeCodeWordAsInput
              (encodeBoolWordAppend quoted [])).map some)
            (List.append ((stageNatBits stage).map some)
              (some false ::
                List.append (fieldTail.map some) rightPadding)))))
      (postPaddingOutputPrefixStageScannerTargetTapeWithRight
        quoted stage baseLeft fieldTail rightPadding) := by
  rcases stageNatBits_cons_false stage with
    ⟨stageTail, hstage⟩
  refine
    seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      (A := postPaddingOutputPrefixScannerDescription)
      (B := NonemptyNatSuffixScannerDescription)
      (handoffMove := Direction.right)
      (Tmid :=
        (boolWordCanonicalHandoffConfigWithBaseAndRight quoted
          (postPaddingOutputPrefixHeaderBase baseLeft)
          (false :: List.append stageTail (false :: fieldTail))
          rightPadding).tape)
      (Tnext :=
        tapeAtCells
          (postPaddingOutputPrefixStageHandoffBase quoted baseLeft)
          (List.append ((stageNatBits stage).map some)
            (some false ::
              List.append (fieldTail.map some) rightPadding)))
      postPaddingOutputPrefixScannerDescription_subroutineReady
      nonemptyNatSuffixScannerDescription_subroutineReady
      ?hprefix ?hmove ?hstageRun
  · rw [hstage]
    simpa [List.map_append, List.append_assoc] using
      postPaddingOutputPrefixScannerDescription_haltsFrom_withRight
        quoted (List.append stageTail (false :: fieldTail)) baseLeft
        rightPadding
  · exact
      postPaddingOutputPrefixScannerTarget_move_right_eq_stageSource_withRight
        quoted stage baseLeft fieldTail stageTail rightPadding hstage
  · exact
      nonemptyNatSuffixScannerDescription_haltsFrom_outputPrefixStage_withRight
        quoted stage baseLeft fieldTail rightPadding

theorem postPaddingOutputPrefixStageScannerTarget_move_right_eq_configSource
    (quoted : Word Bool) (stage : Nat)
    (baseLeft : List (Option Bool)) (fieldTail : Word Bool) :
    Tape.move Direction.right
        (postPaddingOutputPrefixStageScannerTargetTape
          quoted stage baseLeft fieldTail) =
      tapeAtCells
        (postPaddingOutputPrefixAfterStageBase quoted stage baseLeft)
        ((false :: fieldTail).map some) := by
  simpa [postPaddingOutputPrefixStageScannerTargetTape,
    postPaddingOutputPrefixAfterStageBase] using
    nonemptyNatSuffixHandoffConfigWithBase_move_right
      stage (postPaddingOutputPrefixStageHandoffBase quoted baseLeft)
      false fieldTail

theorem postPaddingOutputPrefixStageScannerTarget_move_right_eq_configSource_withRight
    (quoted : Word Bool) (stage : Nat)
    (baseLeft : List (Option Bool)) (fieldTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    Tape.move Direction.right
        (postPaddingOutputPrefixStageScannerTargetTapeWithRight
          quoted stage baseLeft fieldTail rightPadding) =
      tapeAtCells
        (postPaddingOutputPrefixAfterStageBase quoted stage baseLeft)
        (List.append ((false :: fieldTail).map some) rightPadding) := by
  simpa [postPaddingOutputPrefixStageScannerTargetTapeWithRight,
    postPaddingOutputPrefixAfterStageBase] using
    nonemptyNatSuffixHandoffConfigWithBaseAndRight_move_right
      stage (postPaddingOutputPrefixStageHandoffBase quoted baseLeft)
      false fieldTail rightPadding

theorem postPaddingOutputPrefixStageConfigScannerTarget_move_right_eq_suffixSource
    (quoted : Word Bool) (stage : Nat) (cfg : Configuration)
    (baseLeft : List (Option Bool)) (suffixTail : Word Bool) :
    Tape.move Direction.right
        (postPaddingOutputPrefixStageConfigScannerTargetTape
          quoted stage cfg baseLeft suffixTail) =
      tapeAtCells
        (configurationRestoredLeftWithBase cfg
          (postPaddingOutputPrefixAfterStageBase quoted stage baseLeft))
        ((false :: suffixTail).map some) := by
  simpa [postPaddingOutputPrefixStageConfigScannerTargetTape,
    configurationRestoredLeftWithBase] using
    cellListCanonicalHandoffConfigWithBase_move_right
      cfg.tape.right
      (List.append ((cellCodeBits cfg.tape.head).reverse.map some)
        (cellListCanonicalRestoredLeftWithBase cfg.tape.left
          (List.append ((stageNatBits cfg.state).reverse.map some)
            (postPaddingOutputPrefixAfterStageBase
              quoted stage baseLeft))))
      false suffixTail

theorem postPaddingOutputPrefixStageConfigScannerTarget_move_right_eq_suffixSource_withRight
    (quoted : Word Bool) (stage : Nat) (cfg : Configuration)
    (baseLeft : List (Option Bool)) (suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    Tape.move Direction.right
        (postPaddingOutputPrefixStageConfigScannerTargetTapeWithRight
          quoted stage cfg baseLeft suffixTail rightPadding) =
      tapeAtCells
        (configurationRestoredLeftWithBase cfg
          (postPaddingOutputPrefixAfterStageBase quoted stage baseLeft))
        (List.append ((false :: suffixTail).map some) rightPadding) := by
  simpa [postPaddingOutputPrefixStageConfigScannerTargetTapeWithRight,
    configurationRestoredLeftWithBase] using
    cellListCanonicalHandoffConfigWithBaseAndRight_move_right
      cfg.tape.right
      (List.append ((cellCodeBits cfg.tape.head).reverse.map some)
        (cellListCanonicalRestoredLeftWithBase cfg.tape.left
          (List.append ((stageNatBits cfg.state).reverse.map some)
            (postPaddingOutputPrefixAfterStageBase
              quoted stage baseLeft))))
      false suffixTail rightPadding

theorem configurationSuffixScannerDescription_haltsFrom_afterPrefixStage
    (quoted : Word Bool) (stage : Nat) (cfg : Configuration)
    (baseLeft : List (Option Bool)) (suffixTail : Word Bool) :
    ConfigurationSuffixScannerDescription.HaltsFromTape
      (tapeAtCells
        (postPaddingOutputPrefixAfterStageBase quoted stage baseLeft)
        ((configurationFieldBits cfg
          (false :: suffixTail)).map some))
      (postPaddingOutputPrefixStageConfigScannerTargetTape
        quoted stage cfg baseLeft suffixTail) := by
  rcases
      run_configurationSuffix_raw_to_handoff_withBase
        cfg
        (postPaddingOutputPrefixAfterStageBase
          quoted stage baseLeft)
        suffixTail with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  constructor
  · simpa [postPaddingOutputPrefixStageConfigScannerTargetTape] using
      congrArg Configuration.state hsteps
  · simpa [postPaddingOutputPrefixStageConfigScannerTargetTape] using
      congrArg Configuration.tape hsteps

theorem configurationSuffixScannerDescription_haltsFrom_afterPrefixStage_withRight
    (quoted : Word Bool) (stage : Nat) (cfg : Configuration)
    (baseLeft : List (Option Bool)) (suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    ConfigurationSuffixScannerDescription.HaltsFromTape
      (tapeAtCells
        (postPaddingOutputPrefixAfterStageBase quoted stage baseLeft)
        (List.append
          ((configurationFieldBits cfg
            (false :: suffixTail)).map some)
          rightPadding))
      (postPaddingOutputPrefixStageConfigScannerTargetTapeWithRight
        quoted stage cfg baseLeft suffixTail rightPadding) := by
  rcases
      run_configurationSuffix_raw_to_handoff_withBaseAndRight
        cfg
        (postPaddingOutputPrefixAfterStageBase
          quoted stage baseLeft)
        suffixTail
        rightPadding with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  constructor
  · simpa [postPaddingOutputPrefixStageConfigScannerTargetTapeWithRight] using
      congrArg Configuration.state hsteps
  · simpa [postPaddingOutputPrefixStageConfigScannerTargetTapeWithRight] using
      congrArg Configuration.tape hsteps

theorem postPaddingOutputPrefixStageConfigScannerDescription_haltsFrom_raw
    (quoted : Word Bool) (stage : Nat) (cfg : Configuration)
    (baseLeft : List (Option Bool)) (suffixTail : Word Bool) :
    postPaddingOutputPrefixStageConfigScannerDescription.HaltsFromTape
      (tapeAtCells baseLeft
        (List.append
          ((encodeCodeSymbolAsInput MachineCodeSymbol.header).map some)
          (List.append
            ((encodeCodeWordAsInput
              (encodeBoolWordAppend quoted [])).map some)
            (List.append ((stageNatBits stage).map some)
              ((configurationFieldBits cfg
                (false :: suffixTail)).map some)))))
      (postPaddingOutputPrefixStageConfigScannerTargetTape
        quoted stage cfg baseLeft suffixTail) := by
  rcases configurationFieldBits_cons_false cfg (false :: suffixTail) with
    ⟨fieldTail, hfield⟩
  refine
    seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      (A := postPaddingOutputPrefixStageScannerDescription)
      (B := ConfigurationSuffixScannerDescription)
      (handoffMove := Direction.right)
      (Tmid :=
        postPaddingOutputPrefixStageScannerTargetTape
          quoted stage baseLeft fieldTail)
      (Tnext :=
        tapeAtCells
          (postPaddingOutputPrefixAfterStageBase
            quoted stage baseLeft)
          ((configurationFieldBits cfg
            (false :: suffixTail)).map some))
      postPaddingOutputPrefixStageScannerDescription_subroutineReady
      configurationSuffixScannerDescription_subroutineReady
      ?hprefix ?hmove ?hconfig
  · rw [hfield]
    simpa [List.map_append, List.append_assoc] using
      postPaddingOutputPrefixStageScannerDescription_haltsFrom_raw
        quoted stage baseLeft fieldTail
  · rw [hfield]
    exact
      postPaddingOutputPrefixStageScannerTarget_move_right_eq_configSource
        quoted stage baseLeft fieldTail
  · exact
      configurationSuffixScannerDescription_haltsFrom_afterPrefixStage
        quoted stage cfg baseLeft suffixTail

theorem postPaddingOutputPrefixStageConfigScannerDescription_haltsFrom_raw_withRight
    (quoted : Word Bool) (stage : Nat) (cfg : Configuration)
    (baseLeft : List (Option Bool)) (suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    postPaddingOutputPrefixStageConfigScannerDescription.HaltsFromTape
      (tapeAtCells baseLeft
        (List.append
          ((encodeCodeSymbolAsInput MachineCodeSymbol.header).map some)
          (List.append
            ((encodeCodeWordAsInput
              (encodeBoolWordAppend quoted [])).map some)
            (List.append ((stageNatBits stage).map some)
              (List.append
                ((configurationFieldBits cfg
                  (false :: suffixTail)).map some)
                rightPadding)))))
      (postPaddingOutputPrefixStageConfigScannerTargetTapeWithRight
        quoted stage cfg baseLeft suffixTail rightPadding) := by
  rcases configurationFieldBits_cons_false cfg (false :: suffixTail) with
    ⟨fieldTail, hfield⟩
  refine
    seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      (A := postPaddingOutputPrefixStageScannerDescription)
      (B := ConfigurationSuffixScannerDescription)
      (handoffMove := Direction.right)
      (Tmid :=
        postPaddingOutputPrefixStageScannerTargetTapeWithRight
          quoted stage baseLeft fieldTail rightPadding)
      (Tnext :=
        tapeAtCells
          (postPaddingOutputPrefixAfterStageBase
            quoted stage baseLeft)
          (List.append
            ((configurationFieldBits cfg
              (false :: suffixTail)).map some)
            rightPadding))
      postPaddingOutputPrefixStageScannerDescription_subroutineReady
      configurationSuffixScannerDescription_subroutineReady
      ?hprefix ?hmove ?hconfig
  · rw [hfield]
    simpa [List.map_append, List.append_assoc] using
      postPaddingOutputPrefixStageScannerDescription_haltsFrom_raw_withRight
        quoted stage baseLeft fieldTail rightPadding
  · rw [hfield]
    exact
      postPaddingOutputPrefixStageScannerTarget_move_right_eq_configSource_withRight
        quoted stage baseLeft fieldTail rightPadding
  · exact
      configurationSuffixScannerDescription_haltsFrom_afterPrefixStage_withRight
        quoted stage cfg baseLeft suffixTail rightPadding

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC

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

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC

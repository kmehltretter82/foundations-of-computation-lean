import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.StageInputMarkedScanner.Basic
import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.BoolWordQuoter.ControllerInitial.CellPass
import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.Basic
import FoC.Computability.Compiler.Core.CommonGround.SeqComposition
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.RightEdgeRewind
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.CountedSuffixExtraBlankRestorer

set_option doc.verso true

/-!
# Count-window raw-source encoder

This module packages the reusable finite-machine obligation for re-encoding a
raw split layout window.  The input contains the parsed layout bits directly,
followed by a blank count window, one repaired extra count-window blank, and a
tail.  The output restores the encoded header, layout length, skipped-cell
field, counted-cell field, consumes the repaired blank, and preserves the tail.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers

def countWindowRawSourceEncoderHeaderCells : List (Option Bool) :=
  (encodeCodeSymbolAsInput MachineCodeSymbol.header).map some

def countWindowRawSourceEncoderLayoutLengthCells
    (layout : Word Bool) : List (Option Bool) :=
  (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
    layout.length).map some

def countWindowRawSourceEncoderCellFieldCells
    (cells : List (Option Bool)) : List (Option Bool) :=
  (EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.cellsCodeBits
    cells).map some

def countWindowRawSourceEncoderEncodedLayoutCells
    (layout : Word Bool) : List (Option Bool) :=
  List.append
    countWindowRawSourceEncoderHeaderCells
    (List.append
      (countWindowRawSourceEncoderLayoutLengthCells layout)
      (countWindowRawSourceEncoderCellFieldCells
        (layout.map some)))

def countWindowRawSourceEncoderOutputCells
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    List (Option Bool) :=
  List.append
    (countWindowRawSourceEncoderEncodedLayoutCells
      (List.append skipped count))
    (List.append tail
      (List.replicate count.length (none : Option Bool)))

def countWindowRawSourceEncoderScanPadding
    (count : Word Bool) (tail : List (Option Bool)) :
    List (Option Bool) :=
  none ::
    none ::
    List.append
      (List.replicate count.length (none : Option Bool))
      tail

def countWindowRawSourceEncoderSourceTape
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape Bool :=
  tapeAtCells [none]
    (List.append
      ((List.append skipped count).map some)
      (none ::
        none ::
        none ::
        List.append
          (List.replicate count.length (none : Option Bool))
          tail))

def countWindowRawSourceEncoderTargetTape
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape Bool :=
  tapeAtCells [none]
    (List.append
      countWindowRawSourceEncoderHeaderCells
      (List.append
        (countWindowRawSourceEncoderLayoutLengthCells
          (List.append skipped count))
        (List.append
          (countWindowRawSourceEncoderCellFieldCells
            (skipped.map some))
          (List.append
            (countWindowRawSourceEncoderCellFieldCells
              (count.map some))
            (List.append tail
              (List.replicate count.length
                (none : Option Bool)))))))

def countWindowRawSourceEncoderRightEdgeTape
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape Bool :=
  rightEdgeScanTargetTapeFromLeft [none]
    (List.append skipped count)
    (countWindowRawSourceEncoderScanPadding count tail)

def countWindowRawSourceEncoderCountWindowStartTape
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape Bool :=
  tapeAtCells
    (none ::
      none ::
      none ::
      List.append
        ((List.append skipped count).reverse.map some)
        [none])
    (List.append
      (List.replicate count.length (none : Option Bool))
      tail)

def countWindowRawSourceEncoderBeforeCountWindowTape
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape Bool :=
  tapeAtCells
    (none ::
      none ::
      List.append
        ((List.append skipped count).reverse.map some)
        [none])
    (none ::
      List.append
        (List.replicate count.length (none : Option Bool))
        tail)

def countWindowRawSourceEncoderTailPastFirstTape
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (some tailFirst ::
      List.append
        (List.replicate count.length (none : Option Bool))
        (none ::
          none ::
          none ::
          List.append
            ((List.append skipped count).reverse.map some)
            [none]))
    tail

theorem countWindowRawSourceEncoderCellFieldCells_append
    (left right : List (Option Bool)) :
    countWindowRawSourceEncoderCellFieldCells
        (List.append left right) =
      List.append
        (countWindowRawSourceEncoderCellFieldCells left)
        (countWindowRawSourceEncoderCellFieldCells right) := by
  unfold countWindowRawSourceEncoderCellFieldCells
  rw [
    EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.cellsCodeBits_append]
  simp [List.map_append]

theorem countWindowRawSourceEncoderCellFieldCells_map_append
    (left right : Word Bool) :
    countWindowRawSourceEncoderCellFieldCells
        ((List.append left right).map some) =
      List.append
        (countWindowRawSourceEncoderCellFieldCells (left.map some))
        (countWindowRawSourceEncoderCellFieldCells (right.map some)) := by
  have hmap :
      (List.append left right).map some =
        List.append (left.map some) (right.map some) := by
    induction left with
    | nil =>
        rfl
    | cons bit rest ih =>
        simp [List.append]
  rw [hmap]
  exact countWindowRawSourceEncoderCellFieldCells_append
    (left.map some) (right.map some)

theorem countWindowRawSourceEncoderTargetTape_eq_outputCells
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    countWindowRawSourceEncoderTargetTape skipped count tail =
      tapeAtCells [none]
        (countWindowRawSourceEncoderOutputCells skipped count tail) := by
  unfold countWindowRawSourceEncoderTargetTape
  unfold countWindowRawSourceEncoderOutputCells
  unfold countWindowRawSourceEncoderEncodedLayoutCells
  rw [countWindowRawSourceEncoderCellFieldCells_map_append]
  simp [List.append_assoc]

theorem countWindowRawSourceEncoder_dropTrailingNone_append_none
    (xs : List (Option Bool)) :
    Tape.dropTrailingNone (xs ++ [none]) = Tape.dropTrailingNone xs := by
  induction xs with
  | nil =>
      rfl
  | cons cell xs ih =>
      cases cell <;>
        simp [Tape.dropTrailingNone, ih]

theorem countWindowRawSourceEncoder_dropTrailingNone_append_replicate_none
    (xs : List (Option Bool)) (padding : Nat) :
    Tape.dropTrailingNone
        (xs ++ List.replicate padding (none : Option Bool)) =
      Tape.dropTrailingNone xs := by
  induction padding generalizing xs with
  | zero =>
      simp
  | succ padding ih =>
      calc
        Tape.dropTrailingNone
            (xs ++ List.replicate (padding + 1)
              (none : Option Bool)) =
          Tape.dropTrailingNone
            ((xs ++ [none]) ++
              List.replicate padding (none : Option Bool)) := by
            simp [List.replicate_succ, List.append_assoc]
        _ = Tape.dropTrailingNone (xs ++ [none]) :=
          ih (xs ++ [none])
        _ = Tape.dropTrailingNone xs :=
          countWindowRawSourceEncoder_dropTrailingNone_append_none xs

def countWindowRawSourceEncoderTargetTapeNoCountPadding
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape Bool :=
  tapeAtCells [none]
    (List.append
      countWindowRawSourceEncoderHeaderCells
      (List.append
        (countWindowRawSourceEncoderLayoutLengthCells
          (List.append skipped count))
        (List.append
          (countWindowRawSourceEncoderCellFieldCells
            (skipped.map some))
          (List.append
            (countWindowRawSourceEncoderCellFieldCells
              (count.map some))
            tail))))

theorem
    countWindowRawSourceEncoderTargetTapeNoCountPadding_eq_encodedLayoutCells
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    countWindowRawSourceEncoderTargetTapeNoCountPadding
        skipped count tail =
      tapeAtCells [none]
        (List.append
          (countWindowRawSourceEncoderEncodedLayoutCells
            (List.append skipped count))
          tail) := by
  unfold countWindowRawSourceEncoderTargetTapeNoCountPadding
  unfold countWindowRawSourceEncoderEncodedLayoutCells
  rw [countWindowRawSourceEncoderCellFieldCells_map_append]
  simp [List.append_assoc]

theorem countWindowRawSourceEncoderTargetTape_equiv_noCountPadding
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape.Equiv
      (countWindowRawSourceEncoderTargetTape skipped count tail)
      (countWindowRawSourceEncoderTargetTapeNoCountPadding
        skipped count tail) := by
  unfold countWindowRawSourceEncoderTargetTape
  unfold countWindowRawSourceEncoderTargetTapeNoCountPadding
  simp [countWindowRawSourceEncoderHeaderCells, encodeCodeSymbolAsInput,
    Tape.Equiv, tapeAtCells]
  simpa [List.append_assoc] using
    countWindowRawSourceEncoder_dropTrailingNone_append_replicate_none
      (some false :: some false :: some false ::
        (List.append
          (countWindowRawSourceEncoderLayoutLengthCells
            (List.append skipped count))
          (List.append
            (countWindowRawSourceEncoderCellFieldCells
              (skipped.map some))
            (List.append
              (countWindowRawSourceEncoderCellFieldCells
                (count.map some))
              tail))))
      count.length

theorem countWindowRawSourceEncoderEncodedLayoutCells_eq_headerBoolWord
    (layout : Word Bool) :
    countWindowRawSourceEncoderEncodedLayoutCells layout =
      (encodeCodeWordAsInput
        (MachineCodeSymbol.header ::
          encodeBoolWordAppend layout [])).map some := by
  unfold countWindowRawSourceEncoderEncodedLayoutCells
  unfold countWindowRawSourceEncoderHeaderCells
  unfold countWindowRawSourceEncoderLayoutLengthCells
  unfold countWindowRawSourceEncoderCellFieldCells
  simp [encodeCodeWordAsInput, List.map_append]
  rw [
    EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.boolWordBits_eq_encodeBoolWordAppend
      layout []]
  simp [encodeCodeWordAsInput, List.map_append]

theorem countWindowRawSourceEncoderOutputCells_eq_headerBoolWord
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    countWindowRawSourceEncoderOutputCells skipped count tail =
      List.append
        ((encodeCodeWordAsInput
          (MachineCodeSymbol.header ::
            encodeBoolWordAppend (List.append skipped count) [])).map some)
        (List.append tail
          (List.replicate count.length (none : Option Bool))) := by
  rw [countWindowRawSourceEncoderOutputCells,
    countWindowRawSourceEncoderEncodedLayoutCells_eq_headerBoolWord]

theorem countWindowRawSourceEncoderTargetTapeNoCountPadding_eq_headerBoolWord
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    countWindowRawSourceEncoderTargetTapeNoCountPadding
        skipped count tail =
      tapeAtCells [none]
        (List.append
          ((encodeCodeWordAsInput
            (MachineCodeSymbol.header ::
              encodeBoolWordAppend (List.append skipped count) [])).map
              some)
          tail) := by
  rw [
    countWindowRawSourceEncoderTargetTapeNoCountPadding_eq_encodedLayoutCells]
  rw [countWindowRawSourceEncoderEncodedLayoutCells_eq_headerBoolWord]

def countWindowRawSourceEncoderHeaderGapEmitterDescription :
    MachineDescription :=
  { DovetailInitialLayoutInitializer.ControllerInitialRawBoolWordHeaderEmitterDescription with
    stateCount := 61
    halt := 60
    transitions :=
      DovetailInitialLayoutInitializer.ControllerInitialRawBoolWordHeaderEmitterDescription.transitions.filter
        (fun row => row.source < 60) }

private abbrev CWRSEHeaderGap :=
  countWindowRawSourceEncoderHeaderGapEmitterDescription

theorem countWindowRawSourceEncoderHeaderGapEmitterDescription_wellFormed :
    CWRSEHeaderGap.WellFormed := by
  refine ⟨by native_decide, by native_decide, by native_decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := CWRSEHeaderGap.transitions)
      (stateCount := CWRSEHeaderGap.stateCount)
      (by native_decide)
  · exact transition_deterministic_of_all
      (l := CWRSEHeaderGap.transitions)
      (by native_decide)

theorem countWindowRawSourceEncoderHeaderGapEmitterDescription_haltTransitionFree :
    CWRSEHeaderGap.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := CWRSEHeaderGap.transitions)
    (state := CWRSEHeaderGap.halt)
    (by native_decide)

theorem countWindowRawSourceEncoderHeaderGapEmitterDescription_subroutineReady :
    CWRSEHeaderGap.SubroutineReady :=
  ⟨countWindowRawSourceEncoderHeaderGapEmitterDescription_wellFormed,
    countWindowRawSourceEncoderHeaderGapEmitterDescription_haltTransitionFree⟩

theorem countWindowRawSourceEncoderHeaderGapEmitterDescription_step_finish
    (leftRev : List (Option Bool)) (output : Word Bool)
    (padding : List (Option Bool)) :
    CWRSEHeaderGap.runConfig 1
        (DovetailInitialLayoutInitializer.config 36 leftRev
          (none :: List.append (output.map some) (none :: padding))) =
      { state := CWRSEHeaderGap.halt
        tape :=
          tapeAtCells (none :: leftRev)
            (List.append (output.map some) (none :: padding)) } := by
  cases output <;> cases padding <;>
    simp [CWRSEHeaderGap,
      countWindowRawSourceEncoderHeaderGapEmitterDescription,
      DovetailInitialLayoutInitializer.ControllerInitialRawBoolWordHeaderEmitterDescription,
      DovetailInitialLayoutInitializer.config, tapeAtCells, runConfig,
      DovetailInitialLayoutInitializer.tapeAtCells, stepConfig,
      lookupTransition, Matches, transition, Tape.read, Tape.write,
      Tape.move, Tape.moveRight]

theorem countWindowRawSourceEncoderHeaderGapEmitterOutput_bits_eq
    (layout : Word Bool) :
    List.append
        (List.append
          (List.append [false, false, false, false]
            (DovetailInitialLayoutInitializer.controllerInitialRawBoolWordHeaderEmitterCountTicksBits
              layout))
          [false, false, true, true])
        (DovetailInitialLayoutInitializer.controllerInitialRawBoolWordHeaderEmitterCellBits
          layout) =
      encodeCodeWordAsInput
        (MachineCodeSymbol.header :: encodeBoolWordAppend layout []) := by
  rw [show
      List.append
          (List.append
            (List.append [false, false, false, false]
              (DovetailInitialLayoutInitializer.controllerInitialRawBoolWordHeaderEmitterCountTicksBits
                layout))
            [false, false, true, true])
          (DovetailInitialLayoutInitializer.controllerInitialRawBoolWordHeaderEmitterCellBits
            layout) =
        List.append [false, false, false, false]
          (List.append
            (List.append
              (DovetailInitialLayoutInitializer.controllerInitialRawBoolWordHeaderEmitterCountTicksBits
                layout)
              [false, false, true, true])
            (DovetailInitialLayoutInitializer.controllerInitialRawBoolWordHeaderEmitterCellBits
              layout)) by
    simp [List.append_assoc]]
  rw [
    DovetailInitialLayoutInitializer.controllerInitialRawBoolWordHeaderEmitterCountTicksBits_append_done]
  have hcells :
      DovetailInitialLayoutInitializer.controllerInitialRawBoolWordHeaderEmitterCellBits
          layout =
        encodeCodeWordAsInput (encodeCellsAppend (layout.map some) []) := by
    simpa [encodeCodeWordAsInput] using
      DovetailInitialLayoutInitializer.controllerInitialRawBoolWordHeaderEmitterCellBits_append_suffix
        layout ([] : Word MachineCodeSymbol)
  rw [hcells]
  rw [← encodeCodeWordAsInput_append]
  simp [encodeBoolWordAppend, encodeCellListAppend, encodeNatAppend,
    encodeCodeWordAsInput, encodeCodeSymbolAsInput]

theorem countWindowRawSourceEncoderRightEdgeScan_haltsFromTape
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    rightEdgeScanDescription.HaltsFromTape
      (countWindowRawSourceEncoderSourceTape skipped count tail)
      (countWindowRawSourceEncoderRightEdgeTape skipped count tail) := by
  simpa [countWindowRawSourceEncoderSourceTape,
    countWindowRawSourceEncoderRightEdgeTape,
    countWindowRawSourceEncoderScanPadding,
    rightEdgeScanSourceTapeFromLeft, List.append_assoc] using
    rightEdgeScanDescription_haltsFromTape [none]
      (List.append skipped count)
      (countWindowRawSourceEncoderScanPadding count tail)

theorem countWindowRawSourceEncoder_tapeAtCells_moveRight_cons
    (leftRev : List (Option Bool)) (cell : Option Bool)
    (rest : List (Option Bool)) :
    Tape.move Direction.right (tapeAtCells leftRev (cell :: rest)) =
      tapeAtCells (cell :: leftRev) rest := by
  cases rest <;> rfl

theorem countWindowRawSourceEncoder_tapeAtCells_moveRight_moveLeft_append_none
    (pref right : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (tapeAtCells (List.append pref [none]) right)) =
      tapeAtCells (List.append pref [none]) right := by
  cases pref <;> cases right <;>
    simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem rightEdgeScanTargetTapeFromLeft_moveRight_four_fixedBlanks
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.move Direction.right
      (Tape.move Direction.right
        (Tape.move Direction.right
          (Tape.move Direction.right
            (rightEdgeScanTargetTapeFromLeft [none] bits
              (none :: none :: padding))))) =
      tapeAtCells
        (none ::
          none ::
          none ::
          List.append (bits.reverse.map some) [none])
        padding := by
  rw [rightEdgeScanTargetTapeFromLeft]
  rw [
    countWindowRawSourceEncoder_tapeAtCells_moveRight_moveLeft_append_none]
  rw [countWindowRawSourceEncoder_tapeAtCells_moveRight_cons]
  rw [countWindowRawSourceEncoder_tapeAtCells_moveRight_cons]
  rw [countWindowRawSourceEncoder_tapeAtCells_moveRight_cons]

theorem rightEdgeScanTargetTapeFromLeft_moveRight_threeBlankSource
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.move Direction.right
        (rightEdgeScanTargetTapeFromLeft [none] bits
          (none :: none :: padding)) =
      tapeAtCells
        (List.append (bits.reverse.map some) [none])
        (none :: none :: none :: padding) := by
  rw [rightEdgeScanTargetTapeFromLeft]
  exact
    countWindowRawSourceEncoder_tapeAtCells_moveRight_moveLeft_append_none
      (bits.reverse.map some) (none :: none :: none :: padding)

theorem countWindowRawSourceEncoderRightEdgeTape_moveRight_four
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape.move Direction.right
      (Tape.move Direction.right
        (Tape.move Direction.right
          (Tape.move Direction.right
            (countWindowRawSourceEncoderRightEdgeTape
              skipped count tail)))) =
      countWindowRawSourceEncoderCountWindowStartTape
        skipped count tail := by
  rw [countWindowRawSourceEncoderRightEdgeTape,
    countWindowRawSourceEncoderCountWindowStartTape,
    countWindowRawSourceEncoderScanPadding]
  exact
    rightEdgeScanTargetTapeFromLeft_moveRight_four_fixedBlanks
      (List.append skipped count)
      (List.append
        (List.replicate count.length (none : Option Bool))
        tail)

def rightMoveAcrossThreeBlanksDescription : MachineDescription where
  stateCount := 4
  start := 0
  halt := 3
  transitions :=
    [ transition 0 none none Direction.right 1
    , transition 1 none none Direction.right 2
    , transition 2 none none Direction.right 3 ]

theorem rightMoveAcrossThreeBlanksDescription_wellFormed :
    rightMoveAcrossThreeBlanksDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := rightMoveAcrossThreeBlanksDescription.transitions)
      (stateCount := rightMoveAcrossThreeBlanksDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := rightMoveAcrossThreeBlanksDescription.transitions)
      (by decide)

theorem rightMoveAcrossThreeBlanksDescription_haltTransitionFree :
    rightMoveAcrossThreeBlanksDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := rightMoveAcrossThreeBlanksDescription.transitions)
    (state := rightMoveAcrossThreeBlanksDescription.halt)
    (by decide)

theorem rightMoveAcrossThreeBlanksDescription_subroutineReady :
    rightMoveAcrossThreeBlanksDescription.SubroutineReady :=
  ⟨rightMoveAcrossThreeBlanksDescription_wellFormed,
    rightMoveAcrossThreeBlanksDescription_haltTransitionFree⟩

theorem rightMoveAcrossThreeBlanksDescription_run
    (left right : List (Option Bool)) :
    rightMoveAcrossThreeBlanksDescription.runConfig 3
        { state := rightMoveAcrossThreeBlanksDescription.start
          tape :=
            tapeAtCells left
              (none :: none :: none :: right) } =
      { state := rightMoveAcrossThreeBlanksDescription.halt
        tape :=
          tapeAtCells
            (none :: none :: none :: left)
            right } := by
  cases right <;>
    simp [rightMoveAcrossThreeBlanksDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem rightMoveAcrossThreeBlanksDescription_haltsFromTape
    (left right : List (Option Bool)) :
    rightMoveAcrossThreeBlanksDescription.HaltsFromTape
      (tapeAtCells left
        (none :: none :: none :: right))
      (tapeAtCells
        (none :: none :: none :: left)
        right) := by
  refine ⟨3, ?_⟩
  constructor <;>
    rw [rightMoveAcrossThreeBlanksDescription_run]

def countWindowRawSourceEncoderScanToCountWindowStartDescription :
    MachineDescription :=
  seqSubroutine rightEdgeScanDescription
    rightMoveAcrossThreeBlanksDescription Direction.right

theorem
    countWindowRawSourceEncoderScanToCountWindowStartDescription_subroutineReady :
    countWindowRawSourceEncoderScanToCountWindowStartDescription.SubroutineReady :=
  seqSubroutine_subroutineReady
    rightEdgeScanDescription_subroutineReady
    rightMoveAcrossThreeBlanksDescription_subroutineReady

theorem countWindowRawSourceEncoderRightEdgeTape_moveRight_threeBlankSource
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape.move Direction.right
        (countWindowRawSourceEncoderRightEdgeTape skipped count tail) =
      tapeAtCells
        (List.append
          ((List.append skipped count).reverse.map some)
          [none])
        (none ::
          none ::
          none ::
          List.append
            (List.replicate count.length (none : Option Bool))
            tail) := by
  rw [countWindowRawSourceEncoderRightEdgeTape,
    countWindowRawSourceEncoderScanPadding]
  exact
    rightEdgeScanTargetTapeFromLeft_moveRight_threeBlankSource
      (List.append skipped count)
      (List.append
        (List.replicate count.length (none : Option Bool))
        tail)

theorem
    countWindowRawSourceEncoderRightEdgeTape_moveRight_eq_countedSuffixExtraBlank
    (skipped suffixRest : Word Bool) (suffixFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.move Direction.right
        (countWindowRawSourceEncoderRightEdgeTape
          skipped (suffixFirst :: suffixRest) tail) =
      countedSuffixExtraBlankRightGapSourceTape
        skipped suffixRest suffixFirst tail := by
  simpa [countedSuffixExtraBlankRightGapSourceTape,
    rightEdgeRewindSourceTapeWithBase, List.append_assoc] using
    countWindowRawSourceEncoderRightEdgeTape_moveRight_threeBlankSource
      skipped (suffixFirst :: suffixRest) tail

theorem countWindowRawSourceEncoderSourceTape_eq_countedSuffixRestored
    (skipped suffixRest : Word Bool) (suffixFirst : Bool)
    (tail : List (Option Bool)) :
    countWindowRawSourceEncoderSourceTape
        skipped (suffixFirst :: suffixRest) tail =
      countedSuffixExtraBlankRestoredSourceTape
        skipped suffixRest suffixFirst tail := by
  simp [countedSuffixExtraBlankRestoredSourceTape,
    rightEdgeRewindTargetTapeWithBase,
    countWindowRawSourceEncoderSourceTape, List.replicate_succ,
    List.append_assoc]

theorem
    countWindowRawSourceEncoderScanToCountWindowStartDescription_haltsFromTape
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    countWindowRawSourceEncoderScanToCountWindowStartDescription.HaltsFromTape
      (countWindowRawSourceEncoderSourceTape skipped count tail)
      (countWindowRawSourceEncoderCountWindowStartTape
        skipped count tail) := by
  exact
    CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      rightEdgeScanDescription_subroutineReady
      rightMoveAcrossThreeBlanksDescription_subroutineReady
      (countWindowRawSourceEncoderRightEdgeScan_haltsFromTape
        skipped count tail)
      (countWindowRawSourceEncoderRightEdgeTape_moveRight_threeBlankSource
        skipped count tail)
      (by
        simpa [countWindowRawSourceEncoderCountWindowStartTape] using
          rightMoveAcrossThreeBlanksDescription_haltsFromTape
            (List.append
              ((List.append skipped count).reverse.map some)
              [none])
            (List.append
              (List.replicate count.length (none : Option Bool))
              tail))

def rightMoveAcrossTwoBlanksDescription : MachineDescription where
  stateCount := 3
  start := 0
  halt := 2
  transitions :=
    [ transition 0 none none Direction.right 1
    , transition 1 none none Direction.right 2 ]

theorem rightMoveAcrossTwoBlanksDescription_wellFormed :
    rightMoveAcrossTwoBlanksDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := rightMoveAcrossTwoBlanksDescription.transitions)
      (stateCount := rightMoveAcrossTwoBlanksDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := rightMoveAcrossTwoBlanksDescription.transitions)
      (by decide)

theorem rightMoveAcrossTwoBlanksDescription_haltTransitionFree :
    rightMoveAcrossTwoBlanksDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := rightMoveAcrossTwoBlanksDescription.transitions)
    (state := rightMoveAcrossTwoBlanksDescription.halt)
    (by decide)

theorem rightMoveAcrossTwoBlanksDescription_subroutineReady :
    rightMoveAcrossTwoBlanksDescription.SubroutineReady :=
  ⟨rightMoveAcrossTwoBlanksDescription_wellFormed,
    rightMoveAcrossTwoBlanksDescription_haltTransitionFree⟩

theorem rightMoveAcrossTwoBlanksDescription_run
    (left right : List (Option Bool)) :
    rightMoveAcrossTwoBlanksDescription.runConfig 2
        { state := rightMoveAcrossTwoBlanksDescription.start
          tape := tapeAtCells left (none :: none :: right) } =
      { state := rightMoveAcrossTwoBlanksDescription.halt
        tape := tapeAtCells (none :: none :: left) right } := by
  cases right <;>
    simp [rightMoveAcrossTwoBlanksDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem rightMoveAcrossTwoBlanksDescription_haltsFromTape
    (left right : List (Option Bool)) :
    rightMoveAcrossTwoBlanksDescription.HaltsFromTape
      (tapeAtCells left (none :: none :: right))
      (tapeAtCells (none :: none :: left) right) := by
  refine ⟨2, ?_⟩
  constructor <;>
    rw [rightMoveAcrossTwoBlanksDescription_run]

def countWindowRawSourceEncoderScanToBeforeCountWindowDescription :
    MachineDescription :=
  seqSubroutine rightEdgeScanDescription
    rightMoveAcrossTwoBlanksDescription Direction.right

theorem
    countWindowRawSourceEncoderScanToBeforeCountWindowDescription_subroutineReady :
    countWindowRawSourceEncoderScanToBeforeCountWindowDescription.SubroutineReady :=
  seqSubroutine_subroutineReady
    rightEdgeScanDescription_subroutineReady
    rightMoveAcrossTwoBlanksDescription_subroutineReady

theorem
    countWindowRawSourceEncoderScanToBeforeCountWindowDescription_haltsFromTape
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    countWindowRawSourceEncoderScanToBeforeCountWindowDescription.HaltsFromTape
      (countWindowRawSourceEncoderSourceTape skipped count tail)
      (countWindowRawSourceEncoderBeforeCountWindowTape
        skipped count tail) := by
  exact
    CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      rightEdgeScanDescription_subroutineReady
      rightMoveAcrossTwoBlanksDescription_subroutineReady
      (countWindowRawSourceEncoderRightEdgeScan_haltsFromTape
        skipped count tail)
      (countWindowRawSourceEncoderRightEdgeTape_moveRight_threeBlankSource
        skipped count tail)
      (by
        simpa [countWindowRawSourceEncoderBeforeCountWindowTape] using
          rightMoveAcrossTwoBlanksDescription_haltsFromTape
            (List.append
              ((List.append skipped count).reverse.map some)
              [none])
            (none ::
              List.append
                (List.replicate count.length (none : Option Bool))
                tail))

theorem countWindowRawSourceEncoderBeforeCountWindowTape_moveRight
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape.move Direction.right
        (countWindowRawSourceEncoderBeforeCountWindowTape
          skipped count tail) =
      countWindowRawSourceEncoderCountWindowStartTape
        skipped count tail := by
  rw [countWindowRawSourceEncoderBeforeCountWindowTape,
    countWindowRawSourceEncoderCountWindowStartTape]
  exact
    countWindowRawSourceEncoder_tapeAtCells_moveRight_cons
      (none ::
        none ::
        List.append
          ((List.append skipped count).reverse.map some)
          [none])
      (none : Option Bool)
      (List.append
        (List.replicate count.length (none : Option Bool))
        tail)

def rightBlankRunTailFirstScannerDescription : MachineDescription where
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [ transition 0 none none Direction.right 0
    , transition 0 (some false) (some false) Direction.right 1
    , transition 0 (some true) (some true) Direction.right 1 ]

theorem rightBlankRunTailFirstScannerDescription_wellFormed :
    rightBlankRunTailFirstScannerDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := rightBlankRunTailFirstScannerDescription.transitions)
      (stateCount := rightBlankRunTailFirstScannerDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := rightBlankRunTailFirstScannerDescription.transitions)
      (by decide)

theorem rightBlankRunTailFirstScannerDescription_haltTransitionFree :
    rightBlankRunTailFirstScannerDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := rightBlankRunTailFirstScannerDescription.transitions)
    (state := rightBlankRunTailFirstScannerDescription.halt)
    (by decide)

theorem rightBlankRunTailFirstScannerDescription_subroutineReady :
    rightBlankRunTailFirstScannerDescription.SubroutineReady :=
  ⟨rightBlankRunTailFirstScannerDescription_wellFormed,
    rightBlankRunTailFirstScannerDescription_haltTransitionFree⟩

theorem rightBlankRunTailFirstScannerDescription_step_blank
    (left right : List (Option Bool)) :
    rightBlankRunTailFirstScannerDescription.runConfig 1
        { state := rightBlankRunTailFirstScannerDescription.start
          tape := tapeAtCells left (none :: right) } =
      { state := rightBlankRunTailFirstScannerDescription.start
        tape := tapeAtCells (none :: left) right } := by
  cases right <;>
    simp [rightBlankRunTailFirstScannerDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem rightBlankRunTailFirstScannerDescription_step_tailFirst
    (left tail : List (Option Bool)) (tailFirst : Bool) :
    rightBlankRunTailFirstScannerDescription.runConfig 1
        { state := rightBlankRunTailFirstScannerDescription.start
          tape := tapeAtCells left (some tailFirst :: tail) } =
      { state := rightBlankRunTailFirstScannerDescription.halt
        tape := tapeAtCells (some tailFirst :: left) tail } := by
  cases tailFirst <;> cases tail <;>
    simp [rightBlankRunTailFirstScannerDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem countWindowRawSourceEncoder_replicate_none_append_cons
    (n : Nat) (left : List (Option Bool)) :
    List.append (List.replicate n (none : Option Bool))
        (none :: left) =
      List.append
        (List.replicate (n + 1) (none : Option Bool))
        left := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        none ::
            List.append (List.replicate n (none : Option Bool))
              (none :: left) =
          List.append
            (List.replicate (Nat.succ n + 1)
              (none : Option Bool))
            left
      rw [ih]
      rfl

theorem rightBlankRunTailFirstScannerDescription_run
    (blankCount : Nat) (left tail : List (Option Bool))
    (tailFirst : Bool) :
    rightBlankRunTailFirstScannerDescription.runConfig
        (blankCount + 1)
        { state := rightBlankRunTailFirstScannerDescription.start
          tape :=
            tapeAtCells left
              (List.append
                (List.replicate blankCount (none : Option Bool))
                (some tailFirst :: tail)) } =
      { state := rightBlankRunTailFirstScannerDescription.halt
        tape :=
          tapeAtCells
            (some tailFirst ::
              List.append
                (List.replicate blankCount (none : Option Bool))
                left)
            tail } := by
  induction blankCount generalizing left with
  | zero =>
      simpa using
        rightBlankRunTailFirstScannerDescription_step_tailFirst
          left tail tailFirst
  | succ blankCount ih =>
      rw [show Nat.succ blankCount + 1 =
        1 + (blankCount + 1) by omega]
      rw [runConfig_add]
      change
        rightBlankRunTailFirstScannerDescription.runConfig
            (blankCount + 1)
            (rightBlankRunTailFirstScannerDescription.runConfig 1
              { state := rightBlankRunTailFirstScannerDescription.start
                tape :=
                  tapeAtCells left
                    (none ::
                      List.append
                        (List.replicate blankCount
                          (none : Option Bool))
                        (some tailFirst :: tail)) }) =
          { state := rightBlankRunTailFirstScannerDescription.halt
            tape :=
              tapeAtCells
                (some tailFirst ::
                  List.append
                    (List.replicate (Nat.succ blankCount)
                      (none : Option Bool))
                    left)
                tail }
      rw [rightBlankRunTailFirstScannerDescription_step_blank]
      have hih := ih (none :: left)
      rw [hih]
      simpa [List.replicate] using
        congrArg
          (fun cells =>
            tapeAtCells (some tailFirst :: cells) tail)
          (countWindowRawSourceEncoder_replicate_none_append_cons
            blankCount left)

theorem rightBlankRunTailFirstScannerDescription_haltsFromTape
    (blankCount : Nat) (left tail : List (Option Bool))
    (tailFirst : Bool) :
    rightBlankRunTailFirstScannerDescription.HaltsFromTape
      (tapeAtCells left
        (List.append
          (List.replicate blankCount (none : Option Bool))
          (some tailFirst :: tail)))
      (tapeAtCells
        (some tailFirst ::
          List.append
            (List.replicate blankCount (none : Option Bool))
            left)
        tail) := by
  refine ⟨blankCount + 1, ?_⟩
  constructor <;>
    rw [rightBlankRunTailFirstScannerDescription_run]

theorem rightBlankRunTailFirstScannerDescription_haltsFrom_countWindowStart
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    rightBlankRunTailFirstScannerDescription.HaltsFromTape
      (countWindowRawSourceEncoderCountWindowStartTape
        skipped count (some tailFirst :: tail))
      (countWindowRawSourceEncoderTailPastFirstTape
        skipped count tailFirst tail) := by
  simpa [countWindowRawSourceEncoderCountWindowStartTape,
    countWindowRawSourceEncoderTailPastFirstTape] using
    rightBlankRunTailFirstScannerDescription_haltsFromTape
      count.length
      (none ::
        none ::
        none ::
        List.append
          ((List.append skipped count).reverse.map some)
          [none])
      tail
      tailFirst

def countWindowRawSourceEncoderScanToTailPastFirstDescription :
    MachineDescription :=
  seqSubroutine
    countWindowRawSourceEncoderScanToBeforeCountWindowDescription
    rightBlankRunTailFirstScannerDescription Direction.right

theorem
    countWindowRawSourceEncoderScanToTailPastFirstDescription_subroutineReady :
    countWindowRawSourceEncoderScanToTailPastFirstDescription.SubroutineReady :=
  seqSubroutine_subroutineReady
    countWindowRawSourceEncoderScanToBeforeCountWindowDescription_subroutineReady
    rightBlankRunTailFirstScannerDescription_subroutineReady

theorem
    countWindowRawSourceEncoderScanToTailPastFirstDescription_haltsFromTape
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    countWindowRawSourceEncoderScanToTailPastFirstDescription.HaltsFromTape
      (countWindowRawSourceEncoderSourceTape
        skipped count (some tailFirst :: tail))
      (countWindowRawSourceEncoderTailPastFirstTape
        skipped count tailFirst tail) := by
  exact
    CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      countWindowRawSourceEncoderScanToBeforeCountWindowDescription_subroutineReady
      rightBlankRunTailFirstScannerDescription_subroutineReady
      (countWindowRawSourceEncoderScanToBeforeCountWindowDescription_haltsFromTape
        skipped count (some tailFirst :: tail))
      (countWindowRawSourceEncoderBeforeCountWindowTape_moveRight
        skipped count (some tailFirst :: tail))
      (rightBlankRunTailFirstScannerDescription_haltsFrom_countWindowStart
        skipped count tailFirst tail)

def countWindowRawSourceEncoderLiveTailEmitterSourceTape
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  Tape.move Direction.right
    (countWindowRawSourceEncoderTailPastFirstTape
      skipped count tailFirst tail)

def CountWindowRawSourceEncoderLiveTailEmitterSpec
    (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall (skipped count : Word Bool)
      (tailFirst : Bool) (tail : List (Option Bool)),
      emitter.HaltsFromTape
        (countWindowRawSourceEncoderLiveTailEmitterSourceTape
          skipped count tailFirst tail)
        (countWindowRawSourceEncoderTargetTape
          skipped count (some tailFirst :: tail))

def CountWindowRawSourceEncoderLiveTailEmitterConstruction : Prop :=
  exists emitter : MachineDescription,
    CountWindowRawSourceEncoderLiveTailEmitterSpec emitter

theorem countWindowRawSourceEncoderSourceTape_arbitraryTail_ambiguous :
    countWindowRawSourceEncoderSourceTape
        [false] [true] [none, some true] =
      countWindowRawSourceEncoderSourceTape
        [] [false, true] [some true] := by
  native_decide

theorem countWindowRawSourceEncoderTargetTape_arbitraryTail_ambiguous_ne :
    countWindowRawSourceEncoderTargetTape
        [false] [true] [none, some true] ≠
      countWindowRawSourceEncoderTargetTape
        [] [false, true] [some true] := by
  native_decide

theorem countWindowRawSourceEncoderSourceTape_tailTrailingBlank_equiv :
    Tape.Equiv
      (countWindowRawSourceEncoderSourceTape
        [] [true] [some false])
      (countWindowRawSourceEncoderSourceTape
        [] [true] [some false, none]) := by
  simp [Tape.Equiv, countWindowRawSourceEncoderSourceTape, tapeAtCells,
    Tape.dropTrailingNone]

theorem countWindowRawSourceEncoderTargetTape_tailTrailingBlank_ne :
    countWindowRawSourceEncoderTargetTape
        [] [true] [some false] ≠
      countWindowRawSourceEncoderTargetTape
        [] [true] [some false, none] := by
  native_decide

theorem countWindowRawSourceEncoderTargetTape_tailTrailingBlank_equiv :
    Tape.Equiv
      (countWindowRawSourceEncoderTargetTape
        [] [true] [some false])
      (countWindowRawSourceEncoderTargetTape
        [] [true] [some false, none]) := by
  unfold Tape.Equiv
  constructor
  · native_decide
  constructor
  · native_decide
  · native_decide

theorem countWindowRawSourceEncoderLiveTailEmitterSourceTape_tailTrailingBlank_eq :
    countWindowRawSourceEncoderLiveTailEmitterSourceTape
        [] [true] false [] =
      countWindowRawSourceEncoderLiveTailEmitterSourceTape
        [] [true] false [none] := by
  native_decide

theorem countWindowRawSourceEncoderLiveTailEmitterSpec_impossible
    (emitter : MachineDescription) :
    ¬ CountWindowRawSourceEncoderLiveTailEmitterSpec emitter := by
  intro hem
  have hleft :=
    hem.right [] [true] false []
  have hright :=
    hem.right [] [true] false [none]
  rw [← countWindowRawSourceEncoderLiveTailEmitterSourceTape_tailTrailingBlank_eq]
    at hright
  have htape :=
    MachineDescription.haltsFromTape_functional_of_haltTransitionFree
      hem.left.right hleft hright
  exact countWindowRawSourceEncoderTargetTape_tailTrailingBlank_ne htape

theorem countWindowRawSourceEncoderLiveTailEmitterConstruction_impossible :
    ¬ CountWindowRawSourceEncoderLiveTailEmitterConstruction := by
  intro hconstruction
  rcases hconstruction with ⟨emitter, hem⟩
  exact countWindowRawSourceEncoderLiveTailEmitterSpec_impossible
    emitter hem

def CountWindowRawSourceEncoderLiveTailEmitterEquivSpec
    (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall (skipped count : Word Bool)
      (tailFirst : Bool) (tail : List (Option Bool)),
      emitter.HaltsFromTapeEquiv
        (countWindowRawSourceEncoderLiveTailEmitterSourceTape
          skipped count tailFirst tail)
        (countWindowRawSourceEncoderTargetTape
          skipped count (some tailFirst :: tail))

def CountWindowRawSourceEncoderLiveTailEmitterEquivConstruction :
    Prop :=
  exists emitter : MachineDescription,
    CountWindowRawSourceEncoderLiveTailEmitterEquivSpec emitter

def CountWindowRawSourceEncoderArbitraryTailSpec
    (encoder : MachineDescription) : Prop :=
  encoder.SubroutineReady ∧
    forall (skipped count : Word Bool)
      (tail : List (Option Bool)),
      encoder.HaltsFromTape
        (countWindowRawSourceEncoderSourceTape skipped count tail)
        (countWindowRawSourceEncoderTargetTape skipped count tail)

theorem countWindowRawSourceEncoderArbitraryTailSpec_impossible
    (encoder : MachineDescription) :
    ¬ CountWindowRawSourceEncoderArbitraryTailSpec encoder := by
  intro hencoder
  have hleft :=
    hencoder.right [false] [true] [none, some true]
  have hright :=
    hencoder.right [] [false, true] [some true]
  rw [← countWindowRawSourceEncoderSourceTape_arbitraryTail_ambiguous]
    at hright
  have htape :=
    MachineDescription.haltsFromTape_functional_of_haltTransitionFree
      hencoder.left.right hleft hright
  exact
    countWindowRawSourceEncoderTargetTape_arbitraryTail_ambiguous_ne
      htape

def CountWindowRawSourceEncoderSpec
    (encoder : MachineDescription) : Prop :=
  encoder.SubroutineReady ∧
    forall (skipped count : Word Bool)
      (tailFirst : Bool) (tail : List (Option Bool)),
      encoder.HaltsFromTape
        (countWindowRawSourceEncoderSourceTape
          skipped count (some tailFirst :: tail))
        (countWindowRawSourceEncoderTargetTape
          skipped count (some tailFirst :: tail))

def CountWindowRawSourceEncoderConstruction : Prop :=
  exists encoder : MachineDescription,
    CountWindowRawSourceEncoderSpec encoder

def CountWindowRawSourceEncoderEquivSpec
    (encoder : MachineDescription) : Prop :=
  encoder.SubroutineReady ∧
    forall (skipped count : Word Bool)
      (tailFirst : Bool) (tail : List (Option Bool)),
      encoder.HaltsFromTapeEquiv
        (countWindowRawSourceEncoderSourceTape
          skipped count (some tailFirst :: tail))
        (countWindowRawSourceEncoderTargetTape
          skipped count (some tailFirst :: tail))

def CountWindowRawSourceEncoderEquivConstruction : Prop :=
  exists encoder : MachineDescription,
    CountWindowRawSourceEncoderEquivSpec encoder

def CountWindowRawSourceEncoderNoCountPaddingEquivSpec
    (encoder : MachineDescription) : Prop :=
  encoder.SubroutineReady ∧
    forall (skipped count : Word Bool)
      (tailFirst : Bool) (tail : List (Option Bool)),
      encoder.HaltsFromTapeEquiv
        (countWindowRawSourceEncoderSourceTape
          skipped count (some tailFirst :: tail))
        (countWindowRawSourceEncoderTargetTapeNoCountPadding
          skipped count (some tailFirst :: tail))

def CountWindowRawSourceEncoderNoCountPaddingEquivConstruction :
    Prop :=
  exists encoder : MachineDescription,
    CountWindowRawSourceEncoderNoCountPaddingEquivSpec encoder

def CountWindowRawSourceEncoderCountWindowStartEmitterEquivSpec
    (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall (skipped count : Word Bool)
      (tailFirst : Bool) (tail : List (Option Bool)),
      emitter.HaltsFromTapeEquiv
        (countWindowRawSourceEncoderCountWindowStartTape
          skipped count (some tailFirst :: tail))
        (countWindowRawSourceEncoderTargetTapeNoCountPadding
          skipped count (some tailFirst :: tail))

def CountWindowRawSourceEncoderCountWindowStartEmitterEquivConstruction :
    Prop :=
  exists emitter : MachineDescription,
    CountWindowRawSourceEncoderCountWindowStartEmitterEquivSpec emitter

theorem countWindowRawSourceEncoderNoCountPaddingEquivConstruction_of_countWindowStartEmitter
    (hemitter :
      CountWindowRawSourceEncoderCountWindowStartEmitterEquivConstruction) :
    CountWindowRawSourceEncoderNoCountPaddingEquivConstruction := by
  rcases hemitter with ⟨emitter, hemitterSpec⟩
  refine
    ⟨seqSubroutine
        countWindowRawSourceEncoderScanToBeforeCountWindowDescription
        emitter Direction.right,
      ?_⟩
  constructor
  · exact
      seqSubroutine_subroutineReady
        countWindowRawSourceEncoderScanToBeforeCountWindowDescription_subroutineReady
        hemitterSpec.left
  · intro skipped count tailFirst tail
    exact
      CommonGround.SeqComposition.seqSubroutine_haltsFromTapeEquiv_of_haltsFromTape_eq
        countWindowRawSourceEncoderScanToBeforeCountWindowDescription_subroutineReady
        hemitterSpec.left
        (countWindowRawSourceEncoderScanToBeforeCountWindowDescription_haltsFromTape
          skipped count (some tailFirst :: tail))
        (countWindowRawSourceEncoderBeforeCountWindowTape_moveRight
          skipped count (some tailFirst :: tail))
        (hemitterSpec.right skipped count tailFirst tail)

theorem countWindowRawSourceEncoderEquivConstruction_of_noCountPadding
    (hencoder :
      CountWindowRawSourceEncoderNoCountPaddingEquivConstruction) :
    CountWindowRawSourceEncoderEquivConstruction := by
  rcases hencoder with ⟨encoder, hencoderSpec⟩
  refine ⟨encoder, hencoderSpec.left, ?_⟩
  intro skipped count tailFirst tail
  rcases hencoderSpec.right skipped count tailFirst tail with
    ⟨actual, hhalt, hequiv⟩
  exact
    ⟨actual, hhalt,
      Tape.Equiv.trans hequiv
        (Tape.Equiv.symm
          (countWindowRawSourceEncoderTargetTape_equiv_noCountPadding
            skipped count (some tailFirst :: tail)))⟩

theorem countWindowRawSourceEncoderConstruction_of_liveTailEmitter
    (hemitter : CountWindowRawSourceEncoderLiveTailEmitterConstruction) :
    CountWindowRawSourceEncoderConstruction := by
  rcases hemitter with ⟨emitter, hemitterSpec⟩
  refine
    ⟨seqSubroutine
        countWindowRawSourceEncoderScanToTailPastFirstDescription
        emitter Direction.right,
      ?_⟩
  constructor
  · exact
      seqSubroutine_subroutineReady
        countWindowRawSourceEncoderScanToTailPastFirstDescription_subroutineReady
        hemitterSpec.left
  · intro skipped count tailFirst tail
    exact
      CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
        countWindowRawSourceEncoderScanToTailPastFirstDescription_subroutineReady
        hemitterSpec.left
        (countWindowRawSourceEncoderScanToTailPastFirstDescription_haltsFromTape
          skipped count tailFirst tail)
        rfl
        (hemitterSpec.right skipped count tailFirst tail)

theorem countWindowRawSourceEncoderEquivConstruction_of_liveTailEmitter
    (hemitter :
      CountWindowRawSourceEncoderLiveTailEmitterEquivConstruction) :
    CountWindowRawSourceEncoderEquivConstruction := by
  rcases hemitter with ⟨emitter, hemitterSpec⟩
  refine
    ⟨seqSubroutine
        countWindowRawSourceEncoderScanToTailPastFirstDescription
        emitter Direction.right,
      ?_⟩
  constructor
  · exact
      seqSubroutine_subroutineReady
        countWindowRawSourceEncoderScanToTailPastFirstDescription_subroutineReady
        hemitterSpec.left
  · intro skipped count tailFirst tail
    exact
      CommonGround.SeqComposition.seqSubroutine_haltsFromTapeEquiv_of_haltsFromTape_eq
        countWindowRawSourceEncoderScanToTailPastFirstDescription_subroutineReady
        hemitterSpec.left
        (countWindowRawSourceEncoderScanToTailPastFirstDescription_haltsFromTape
          skipped count tailFirst tail)
        rfl
        (hemitterSpec.right skipped count tailFirst tail)

theorem
    countWindowRawSourceEncoderCountWindowStartEmitterEquivConstruction_core :
    CountWindowRawSourceEncoderCountWindowStartEmitterEquivConstruction := by
  sorry

theorem countWindowRawSourceEncoderNoCountPaddingEquivConstruction_core :
    CountWindowRawSourceEncoderNoCountPaddingEquivConstruction := by
  exact
    countWindowRawSourceEncoderNoCountPaddingEquivConstruction_of_countWindowStartEmitter
      countWindowRawSourceEncoderCountWindowStartEmitterEquivConstruction_core

/--
Direct construction obligation for the raw-source encoder.

This should not be factored through the live-tail emitter handoff: once the
head has crossed the tail-first bit, the empty raw-layout case has no nonblank
left sentinel separating it from an arbitrarily long count-window blank run.
The original source tape still exposes the empty/nonempty raw-layout boundary
at the head, so the real finite-machine proof belongs at this level.
-/
theorem countWindowRawSourceEncoderEquivConstruction_core :
    CountWindowRawSourceEncoderEquivConstruction := by
  exact
    countWindowRawSourceEncoderEquivConstruction_of_noCountPadding
      countWindowRawSourceEncoderNoCountPaddingEquivConstruction_core

end FiniteTransducers
end CommonGround

end Computability
end FoC

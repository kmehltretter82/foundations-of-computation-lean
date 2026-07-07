import FoC.Computability.ListLemmas
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.TapeLemmas
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.FixedSkips
import FoC.Computability.Compiler.Core.DovetailInitLayout.StageInputMarkedScanner.Basic
import FoC.Computability.Compiler.Core.DovetailInitLayout.BoolWordQuoter.ControllerInitial.CellPass
import FoC.Computability.Compiler.Dovetail.Scanner.Basic
import FoC.Computability.Compiler.Core.CommonGround.SeqComposition
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.Mirror
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.RightEdgeRewind
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.CountedSuffixExtraBlankRestorer
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Contracts

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
  (EncRewriters.CanonicalLayouts.DovetailLayoutScanner.cellsCodeBits
    cells).map some

def countWindowRawSourceEncoderEncodedLayoutCells
    (layout : Word Bool) : List (Option Bool) :=
  List.append
    countWindowRawSourceEncoderHeaderCells
    (List.append
      (countWindowRawSourceEncoderLayoutLengthCells layout)
      (countWindowRawSourceEncoderCellFieldCells
        (layout.map some)))

def countWindowRawSourceEncoderEncodedLayoutBits
    (layout : Word Bool) : Word Bool :=
  encodeCodeWordAsInput
    (MachineCodeSymbol.header :: encodeBoolWordAppend layout [])

def countWindowRawSourceEncoderEncodedLayoutRightEdgeTape
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    ((countWindowRawSourceEncoderEncodedLayoutBits
      (List.append skipped count)).reverse.map some)
    (some tailFirst :: tail)

def countWindowRawSourceEncoderEncodedLayoutPreRewindTape
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  Tape.move Direction.left
    (countWindowRawSourceEncoderEncodedLayoutRightEdgeTape
      skipped count tailFirst tail)

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

def countWindowRawSourceEncoderRawBoundaryTape
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape Bool :=
  tapeAtCells
    (List.append ((List.append skipped count).reverse.map some) [none])
    (none ::
      none ::
      none ::
      List.append
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

private theorem countWindowRawSourceEncoderCellFieldCells_append
    (left right : List (Option Bool)) :
    countWindowRawSourceEncoderCellFieldCells
        (List.append left right) =
      List.append
        (countWindowRawSourceEncoderCellFieldCells left)
        (countWindowRawSourceEncoderCellFieldCells right) := by
  unfold countWindowRawSourceEncoderCellFieldCells
  rw [
    EncRewriters.CanonicalLayouts.DovetailLayoutScanner.cellsCodeBits_append]
  simp [List.map_append]

private theorem countWindowRawSourceEncoderCellFieldCells_map_append
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

theorem countWindowRawSourceEncoderTargetTapeNoCountPadding_eq_encodedLayoutCells
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
    FoC.Computability.dropTrailingNone_append_replicate_none
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

private theorem countWindowRawSourceEncoderEncodedLayoutCells_eq_headerBoolWord
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
    EncRewriters.CanonicalLayouts.DovetailLayoutScanner.boolWordBits_eq_encodeBoolWordAppend
      layout []]
  simp [encodeCodeWordAsInput, List.map_append]

private theorem countWindowRawSourceEncoderCellFieldCells_length
    (cells : List (Option Bool)) :
    (countWindowRawSourceEncoderCellFieldCells cells).length =
      4 * cells.length := by
  unfold countWindowRawSourceEncoderCellFieldCells
  induction cells with
  | nil =>
      rfl
  | cons cell rest ih =>
      cases cell with
      | none =>
        simp [EncRewriters.CanonicalLayouts.DovetailLayoutScanner.cellsCodeBits,
          EncRewriters.CanonicalLayouts.DovetailLayoutScanner.cellCodeBits,
          encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
          ih, Nat.mul_add, Nat.add_comm] <;>
        lia
      | some bit =>
          cases bit <;>
            simp [EncRewriters.CanonicalLayouts.DovetailLayoutScanner.cellsCodeBits,
              EncRewriters.CanonicalLayouts.DovetailLayoutScanner.cellCodeBits,
              encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
              ih, Nat.mul_add, Nat.add_comm] <;>
            lia

private theorem countWindowRawSourceEncoderEncodedLayoutCells_length
    (layout : Word Bool) :
    (countWindowRawSourceEncoderEncodedLayoutCells layout).length =
      8 * layout.length + 8 := by
  unfold countWindowRawSourceEncoderEncodedLayoutCells
  unfold countWindowRawSourceEncoderHeaderCells
  unfold countWindowRawSourceEncoderLayoutLengthCells
  simp [countWindowRawSourceEncoderCellFieldCells_length,
    DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_length,
    encodeCodeSymbolAsInput]
  lia

theorem countWindowRawSourceEncoderEncodedLayoutCells_length_gt_sourcePrefix
    (skipped count : Word Bool) :
    (List.append skipped count).length + 3 + count.length <
      (countWindowRawSourceEncoderEncodedLayoutCells
        (List.append skipped count)).length := by
  rw [countWindowRawSourceEncoderEncodedLayoutCells_length]
  simp [List.length_append]
  lia

private theorem countWindowRawSourceEncoderOutputCells_eq_headerBoolWord
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

theorem countWindowRawSourceEncoderTargetTapeNoCountPadding_normalizedOutput
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.normalizedOutput
        (countWindowRawSourceEncoderTargetTapeNoCountPadding
          skipped count (some tailFirst :: tail)) =
      CountWindowRawSourceEncoder.RawBoundaryRightEdgeEmitter.rightEdgeOutputWord
        skipped count tailFirst tail := by
  rw [countWindowRawSourceEncoderTargetTapeNoCountPadding_eq_headerBoolWord]
  rw [tapeAtCells_normalizedOutput]
  simp [
    CountWindowRawSourceEncoder.RawBoundaryRightEdgeEmitter.rightEdgeOutputWord,
    CountWindowRawSourceEncoder.RawBoundaryRightEdgeEmitter.encodedLayoutBits,
    List.filterMap_append,
    Function.comp_def]

theorem countWindowRawSourceEncoder_tapeAtCells_moveRight_moveLeft_append_headerBits
    (pref right : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (tapeAtCells
            (List.append pref
              [some false, some false, some false, some false])
            right)) =
      tapeAtCells
        (List.append pref
          [some false, some false, some false, some false])
        right := by
  cases pref <;> cases right <;>
    simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem countWindowRawSourceEncoderEncodedLayoutRightEdgeTape_rewind_haltsFromTape
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    rightEdgeRewindDescription.HaltsFromTape
      (countWindowRawSourceEncoderEncodedLayoutRightEdgeTape
        skipped count tailFirst tail)
      (countWindowRawSourceEncoderTargetTapeNoCountPadding
        skipped count (some tailFirst :: tail)) := by
  simpa [countWindowRawSourceEncoderEncodedLayoutRightEdgeTape,
    countWindowRawSourceEncoderEncodedLayoutBits,
    countWindowRawSourceEncoderTargetTapeNoCountPadding_eq_headerBoolWord,
    List.append_assoc] using
    rightEdgeRewindDescription_haltsFrom_rightEdge_noDelimiter
      (countWindowRawSourceEncoderEncodedLayoutBits
        (List.append skipped count))
      tailFirst tail

theorem countWindowRawSourceEncoderEncodedLayoutPreRewindTape_moveRight
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.move Direction.right
        (countWindowRawSourceEncoderEncodedLayoutPreRewindTape
          skipped count tailFirst tail) =
      countWindowRawSourceEncoderEncodedLayoutRightEdgeTape
        skipped count tailFirst tail := by
  rw [countWindowRawSourceEncoderEncodedLayoutPreRewindTape,
    countWindowRawSourceEncoderEncodedLayoutRightEdgeTape,
    countWindowRawSourceEncoderEncodedLayoutBits]
  change
    Tape.move Direction.right
        (Tape.move Direction.left
          (tapeAtCells
            ((encodeCodeWordAsInput
              (MachineCodeSymbol.header ::
                encodeBoolWordAppend (List.append skipped count) [])).reverse.map
              some)
            (some tailFirst :: tail))) =
      tapeAtCells
        ((encodeCodeWordAsInput
          (MachineCodeSymbol.header ::
            encodeBoolWordAppend (List.append skipped count) [])).reverse.map
          some)
        (some tailFirst :: tail)
  rw [show
      (encodeCodeWordAsInput
        (MachineCodeSymbol.header ::
          encodeBoolWordAppend (List.append skipped count) [])).reverse.map
          some =
        List.append
          ((encodeCodeWordAsInput
            (encodeBoolWordAppend (List.append skipped count) [])).reverse.map
            some)
          [some false, some false, some false, some false] by
    simp [encodeCodeWordAsInput, encodeCodeSymbolAsInput,
      List.map_append, List.append_assoc]]
  exact
    countWindowRawSourceEncoder_tapeAtCells_moveRight_moveLeft_append_headerBits
      ((encodeCodeWordAsInput
        (encodeBoolWordAppend (List.append skipped count) [])).reverse.map
        some)
      (some tailFirst :: tail)

theorem countWindowRawSourceEncoderTargetTapeNoCountPadding_equiv_leftPadding
    (padding : Nat) (skipped count : Word Bool)
    (tail : List (Option Bool)) :
    Tape.Equiv
      (tapeAtCells
        (List.replicate padding (none : Option Bool))
        (List.append
          (countWindowRawSourceEncoderEncodedLayoutCells
            (List.append skipped count))
          tail))
      (countWindowRawSourceEncoderTargetTapeNoCountPadding
        skipped count tail) := by
  rw [countWindowRawSourceEncoderTargetTapeNoCountPadding_eq_encodedLayoutCells]
  have hpadding :
      Tape.dropTrailingNone
          (List.replicate padding (none : Option Bool)) =
        [] := by
    simpa using
      (FoC.Computability.dropTrailingNone_append_replicate_none
        ([] : List (Option Bool)) padding)
  have hone :
      Tape.dropTrailingNone ([none] : List (Option Bool)) = [] :=
    rfl
  cases hcells :
      List.append
        (countWindowRawSourceEncoderEncodedLayoutCells
          (List.append skipped count))
        tail <;>
    simp [Tape.Equiv, tapeAtCells, hpadding, hone]

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
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := CWRSEHeaderGap.transitions)
      (stateCount := CWRSEHeaderGap.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := CWRSEHeaderGap.transitions)
      (by decide)

theorem countWindowRawSourceEncoderHeaderGapEmitterDescription_haltTransitionFree :
    CWRSEHeaderGap.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := CWRSEHeaderGap.transitions)
    (state := CWRSEHeaderGap.halt)
    (by decide)

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

private theorem countWindowRawSourceEncoderHeaderGapEmitterOutput_bits_eq
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
    tapeAtCells_move_right_move_left_append_singleton]
  rw [tapeAtCells_move_right_cons]
  rw [tapeAtCells_move_right_cons]
  rw [tapeAtCells_move_right_cons]

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
    tapeAtCells_move_right_move_left_append_singleton
      (bits.reverse.map some) (none : Option Bool)
      (none :: none :: none :: padding)

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

def leftMoveToRawBoundaryDescription : MachineDescription where
  stateCount := 4
  start := 0
  halt := 3
  transitions :=
    [ transition 0 none none Direction.left 1
    , transition 0 (some false) (some false) Direction.left 1
    , transition 0 (some true) (some true) Direction.left 1
    , transition 1 none none Direction.left 2
    , transition 2 none none Direction.left 3 ]

theorem leftMoveToRawBoundaryDescription_wellFormed :
    leftMoveToRawBoundaryDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := leftMoveToRawBoundaryDescription.transitions)
      (stateCount := leftMoveToRawBoundaryDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := leftMoveToRawBoundaryDescription.transitions)
      (by decide)

theorem leftMoveToRawBoundaryDescription_haltTransitionFree :
    leftMoveToRawBoundaryDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := leftMoveToRawBoundaryDescription.transitions)
    (state := leftMoveToRawBoundaryDescription.halt)
    (by decide)

theorem leftMoveToRawBoundaryDescription_subroutineReady :
    leftMoveToRawBoundaryDescription.SubroutineReady :=
  ⟨leftMoveToRawBoundaryDescription_wellFormed,
    leftMoveToRawBoundaryDescription_haltTransitionFree⟩

theorem leftMoveToRawBoundaryDescription_run
    (left : List (Option Bool)) (cell : Option Bool)
    (rest : List (Option Bool)) :
    leftMoveToRawBoundaryDescription.runConfig 3
        { state := leftMoveToRawBoundaryDescription.start
          tape := tapeAtCells
            (none :: none :: none :: left) (cell :: rest) } =
      { state := leftMoveToRawBoundaryDescription.halt
        tape := tapeAtCells left (none :: none :: none :: cell :: rest) } := by
  cases cell with
  | none =>
      simp [leftMoveToRawBoundaryDescription, runConfig,
        stepConfig, lookupTransition, Matches, transition,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft, tapeAtCells]
  | some bit =>
      cases bit <;>
        simp [leftMoveToRawBoundaryDescription, runConfig,
          stepConfig, lookupTransition, Matches, transition,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft, tapeAtCells]

theorem leftMoveToRawBoundaryDescription_haltsFromTape
    (left : List (Option Bool)) (cell : Option Bool)
    (rest : List (Option Bool)) :
    leftMoveToRawBoundaryDescription.HaltsFromTape
      (tapeAtCells (none :: none :: none :: left) (cell :: rest))
      (tapeAtCells left (none :: none :: none :: cell :: rest)) := by
  refine ⟨3, ?_⟩
  constructor <;>
    rw [leftMoveToRawBoundaryDescription_run]

private theorem countWindowRawSourceEncoderCountWindowStart_to_rawBoundary
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    leftMoveToRawBoundaryDescription.HaltsFromTape
      (countWindowRawSourceEncoderCountWindowStartTape
        skipped count (some tailFirst :: tail))
      (countWindowRawSourceEncoderRawBoundaryTape
        skipped count (some tailFirst :: tail)) := by
  cases count with
  | nil =>
      simpa [countWindowRawSourceEncoderCountWindowStartTape,
        countWindowRawSourceEncoderRawBoundaryTape] using
        leftMoveToRawBoundaryDescription_haltsFromTape
          (List.append ((List.append skipped ([] : Word Bool)).reverse.map
            some) [none])
          (some tailFirst) tail
  | cons bit rest =>
      simpa [countWindowRawSourceEncoderCountWindowStartTape,
        countWindowRawSourceEncoderRawBoundaryTape,
        List.replicate_succ] using
        leftMoveToRawBoundaryDescription_haltsFromTape
          (List.append
            ((List.append skipped (bit :: rest)).reverse.map some) [none])
          (none : Option Bool)
          (List.append
            (List.replicate rest.length (none : Option Bool))
            (some tailFirst :: tail))

theorem leftMoveToRawBoundaryDescription_haltsFromTape_withEmptyRight
    (left : List (Option Bool)) :
    leftMoveToRawBoundaryDescription.HaltsFromTape
      (tapeAtCells (none :: none :: none :: left) [])
      (tapeAtCells left [none, none, none, none]) := by
  refine ⟨3, ?_⟩
  constructor <;>
    simp [leftMoveToRawBoundaryDescription, runConfig,
            stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft, tapeAtCells]

theorem countWindowRawSourceEncoderRawBoundaryTape_move_left_move_right
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (countWindowRawSourceEncoderRawBoundaryTape
            skipped count tail)) =
      countWindowRawSourceEncoderRawBoundaryTape skipped count tail := by
  simp [countWindowRawSourceEncoderRawBoundaryTape, tapeAtCells,
    Tape.move, Tape.moveLeft, Tape.moveRight]

theorem countWindowRawSourceEncoderRightBoundaryLayout_rewind_haltsFromTape
    (layout : Word Bool) (right : List (Option Bool)) :
    rightEdgeRewindDescription.HaltsFromTape
      (tapeAtCells (List.append (layout.reverse.map some) [none])
        (none :: right))
      (tapeAtCells [none]
        (List.append (layout.map some) (none :: right))) := by
  cases hrev : layout.reverse with
  | nil =>
      have hlayout : layout = [] := by
        have h := congrArg List.reverse hrev
        simpa using h
      simpa [hlayout, List.append_assoc] using
        rightEdgeRewindDescription_haltsFrom_emptyBoundaryBase_noDelimiter
          ([] : List (Option Bool)) right
  | cons current leftBits =>
      have hlayout : layout = List.append leftBits.reverse [current] := by
        have h := congrArg List.reverse hrev
        simpa [List.reverse_cons] using h
      simpa [hlayout, List.map_append, List.append_assoc] using
        rightEdgeRewindDescription_haltsFrom_rightBoundaryBase_noDelimiter
          ([] : List (Option Bool)) leftBits current right

theorem countWindowRawSourceEncoderRawBoundaryTape_rewind_haltsFromTape
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    rightEdgeRewindDescription.HaltsFromTape
      (countWindowRawSourceEncoderRawBoundaryTape skipped count tail)
      (countWindowRawSourceEncoderSourceTape skipped count tail) := by
  simpa [countWindowRawSourceEncoderRawBoundaryTape,
    countWindowRawSourceEncoderSourceTape, List.append_assoc] using
    countWindowRawSourceEncoderRightBoundaryLayout_rewind_haltsFromTape
      (List.append skipped count)
      (none ::
        none ::
        List.append
          (List.replicate count.length (none : Option Bool))
          tail)

def countWindowRawSourceEncoderScanToCountWindowStartDescription :
    MachineDescription :=
  seqSubroutine rightEdgeScanDescription
    rightMoveAcrossThreeBlanksDescription Direction.right

theorem countWindowRawSourceEncoderScanToCountWindowStartDescription_subroutineReady :
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

theorem countWindowRawSourceEncoderRightEdgeTape_moveRight_eq_countedSuffixExtraBlank
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

theorem countWindowRawSourceEncoderScanToCountWindowStartDescription_haltsFromTape
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

def countWindowRawSourceEncoderScanToBeforeCountWindowDescription :
    MachineDescription :=
  seqSubroutine rightEdgeScanDescription
    rightMoveAcrossTwoBlanksDescription Direction.right

theorem countWindowRawSourceEncoderScanToBeforeCountWindowDescription_subroutineReady :
    countWindowRawSourceEncoderScanToBeforeCountWindowDescription.SubroutineReady :=
  seqSubroutine_subroutineReady
    rightEdgeScanDescription_subroutineReady
    rightMoveAcrossTwoBlanksDescription_subroutineReady

theorem countWindowRawSourceEncoderScanToBeforeCountWindowDescription_haltsFromTape
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
    tapeAtCells_move_right_cons
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

private theorem countWindowRawSourceEncoder_replicate_none_append_cons
    (n : Nat) (left : List (Option Bool)) :
    List.append (List.replicate n (none : Option Bool))
        (none :: left) =
      List.append
        (List.replicate (n + 1) (none : Option Bool))
        left := by
  exact list_replicate_append_self (none : Option Bool) n left

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
        1 + (blankCount + 1) by lia]
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

theorem countWindowRawSourceEncoderScanToTailPastFirstDescription_subroutineReady :
    countWindowRawSourceEncoderScanToTailPastFirstDescription.SubroutineReady :=
  seqSubroutine_subroutineReady
    countWindowRawSourceEncoderScanToBeforeCountWindowDescription_subroutineReady
    rightBlankRunTailFirstScannerDescription_subroutineReady

theorem countWindowRawSourceEncoderScanToTailPastFirstDescription_haltsFromTape
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
  decide

theorem countWindowRawSourceEncoderTargetTape_arbitraryTail_ambiguous_ne :
    countWindowRawSourceEncoderTargetTape
        [false] [true] [none, some true] ≠
      countWindowRawSourceEncoderTargetTape
        [] [false, true] [some true] := by
  decide

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
  decide

theorem countWindowRawSourceEncoderTargetTape_tailTrailingBlank_equiv :
    Tape.Equiv
      (countWindowRawSourceEncoderTargetTape
        [] [true] [some false])
      (countWindowRawSourceEncoderTargetTape
        [] [true] [some false, none]) := by
  unfold Tape.Equiv
  constructor
  · decide
  constructor
  · decide
  · decide

theorem countWindowRawSourceEncoderLiveTailEmitterSourceTape_tailTrailingBlank_eq :
    countWindowRawSourceEncoderLiveTailEmitterSourceTape
        [] [true] false [] =
      countWindowRawSourceEncoderLiveTailEmitterSourceTape
        [] [true] false [none] := by
  decide

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

def CountWindowRawSourceEncoderRawBoundaryEmitterEquivSpec
    (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall (skipped count : Word Bool)
      (tailFirst : Bool) (tail : List (Option Bool)),
      emitter.HaltsFromTapeEquiv
        (countWindowRawSourceEncoderRawBoundaryTape
          skipped count (some tailFirst :: tail))
        (countWindowRawSourceEncoderTargetTapeNoCountPadding
          skipped count (some tailFirst :: tail))

def CountWindowRawSourceEncoderRawBoundaryEmitterEquivConstruction :
    Prop :=
  exists emitter : MachineDescription,
    CountWindowRawSourceEncoderRawBoundaryEmitterEquivSpec emitter

def CountWindowRawSourceEncoderRawBoundaryRightEdgeEmitterSpec
    (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall (skipped count : Word Bool)
      (tailFirst : Bool) (tail : List (Option Bool)),
      emitter.HaltsFromTape
        (countWindowRawSourceEncoderRawBoundaryTape
          skipped count (some tailFirst :: tail))
        (countWindowRawSourceEncoderEncodedLayoutPreRewindTape
          skipped count tailFirst tail)

def CountWindowRawSourceEncoderRawBoundaryRightEdgeEmitterConstruction :
    Prop :=
  exists emitter : MachineDescription,
    CountWindowRawSourceEncoderRawBoundaryRightEdgeEmitterSpec emitter

def CountWindowRawSourceEncoderRawBoundaryOutputRouteFamily : Prop :=
  forall (skipped count : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)),
    exists emitter : MachineDescription,
      emitter.SubroutineReady ∧
        emitter.HaltsFromTapeWithOutput
          (countWindowRawSourceEncoderRawBoundaryTape
            skipped count (some tailFirst :: tail))
          (Tape.normalizedOutput
            (countWindowRawSourceEncoderTargetTapeNoCountPadding
              skipped count (some tailFirst :: tail)))

theorem countWindowRawSourceEncoderRawBoundaryOutputRouteFamily_blankSentinel :
    CountWindowRawSourceEncoderRawBoundaryOutputRouteFamily := by
  intro skipped count tailFirst tail
  refine
    ⟨CountWindowRawSourceEncoder.RawBoundaryRightEdgeEmitter.rawBoundaryBlankSentinelRouteDescription
        skipped count tailFirst,
      ?_, ?_⟩
  · exact
      CountWindowRawSourceEncoder.RawBoundaryRightEdgeEmitter.rawBoundaryBlankSentinelRouteDescription_subroutineReady
        skipped count tailFirst
  · have hroute :=
      CountWindowRawSourceEncoder.RawBoundaryRightEdgeEmitter.rawBoundary_blankSentinelEndToEnd_haltsWithOutput
        skipped count tailFirst tail
    simpa [
      countWindowRawSourceEncoderRawBoundaryTape,
      CountWindowRawSourceEncoder.RawBoundaryRightEdgeEmitter.sourceTape,
      countWindowRawSourceEncoderTargetTapeNoCountPadding_normalizedOutput]
      using hroute

def CountWindowRawSourceEncoderRawBoundaryEmitterEquivRouteFamily : Prop :=
  forall (skipped count : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)),
    exists emitter : MachineDescription,
      emitter.SubroutineReady ∧
        emitter.HaltsFromTapeEquiv
          (countWindowRawSourceEncoderRawBoundaryTape
            skipped count (some tailFirst :: tail))
          (countWindowRawSourceEncoderTargetTapeNoCountPadding
            skipped count (some tailFirst :: tail))

theorem countWindowRawSourceEncoderRawBoundaryEmitterEquivRouteFamily_blankSentinel :
    CountWindowRawSourceEncoderRawBoundaryEmitterEquivRouteFamily := by
  intro skipped count tailFirst tail
  let route :=
    CountWindowRawSourceEncoder.RawBoundaryRightEdgeEmitter.rawBoundaryBlankSentinelRouteDescription
      skipped count tailFirst
  refine
    ⟨CommonGround.SameHeadComposition.leftRightSeqDescription
        route rightEdgeRewindDescription,
      ?_, ?_⟩
  · exact
      CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
        (CountWindowRawSourceEncoder.RawBoundaryRightEdgeEmitter.rawBoundaryBlankSentinelRouteDescription_subroutineReady
          skipped count tailFirst)
        rightEdgeRewindDescription_subroutineReady
  · exact
      CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTapeEquiv_of_haltsFromTapeEquiv
        (CountWindowRawSourceEncoder.RawBoundaryRightEdgeEmitter.rawBoundaryBlankSentinelRouteDescription_subroutineReady
          skipped count tailFirst)
        rightEdgeRewindDescription_subroutineReady
        (by
          simpa [route, countWindowRawSourceEncoderRawBoundaryTape,
            CountWindowRawSourceEncoder.RawBoundaryRightEdgeEmitter.sourceTape] using
            CountWindowRawSourceEncoder.RawBoundaryRightEdgeEmitter.rawBoundary_blankSentinelEndToEnd_haltsEquiv
              skipped count tailFirst tail)
        (by
          simpa [countWindowRawSourceEncoderEncodedLayoutRightEdgeTape,
            countWindowRawSourceEncoderEncodedLayoutBits,
            CountWindowRawSourceEncoder.RawBoundaryRightEdgeEmitter.rightEdgeTape,
            CountWindowRawSourceEncoder.RawBoundaryRightEdgeEmitter.preRewindTape,
            CountWindowRawSourceEncoder.RawBoundaryRightEdgeEmitter.encodedLayoutBits] using
            CountWindowRawSourceEncoder.RawBoundaryRightEdgeEmitter.preRewindTape_moveRight
              skipped count tailFirst tail)
        (countWindowRawSourceEncoderEncodedLayoutRightEdgeTape_rewind_haltsFromTape
          skipped count tailFirst tail).toEquiv

theorem countWindowRawSourceEncoderRawBoundaryEmitterEquivConstruction_of_rightEdgeEmitter
    (hemitter :
      CountWindowRawSourceEncoderRawBoundaryRightEdgeEmitterConstruction) :
    CountWindowRawSourceEncoderRawBoundaryEmitterEquivConstruction := by
  rcases hemitter with ⟨emitter, hemitterSpec⟩
  refine
    ⟨seqSubroutine emitter rightEdgeRewindDescription Direction.right,
      ?_⟩
  constructor
  · exact
      seqSubroutine_subroutineReady
        hemitterSpec.left
        rightEdgeRewindDescription_subroutineReady
  · intro skipped count tailFirst tail
    exact
      CommonGround.SeqComposition.seqSubroutine_haltsFromTapeEquiv_of_haltsFromTape_eq
        hemitterSpec.left
        rightEdgeRewindDescription_subroutineReady
        (hemitterSpec.right skipped count tailFirst tail)
        (countWindowRawSourceEncoderEncodedLayoutPreRewindTape_moveRight
          skipped count tailFirst tail)
        (countWindowRawSourceEncoderEncodedLayoutRightEdgeTape_rewind_haltsFromTape
          skipped count tailFirst tail).toEquiv

theorem countWindowRawSourceEncoderCountWindowStartEmitterEquivConstruction_of_rawBoundaryEmitter
    (hemitter :
      CountWindowRawSourceEncoderRawBoundaryEmitterEquivConstruction) :
    CountWindowRawSourceEncoderCountWindowStartEmitterEquivConstruction := by
  rcases hemitter with ⟨emitter, hemitterSpec⟩
  refine
    ⟨canonicalSeqDescription
        leftMoveToRawBoundaryDescription emitter,
      ?_⟩
  constructor
  · exact
      canonicalSeqDescription_subroutineReady
        leftMoveToRawBoundaryDescription_subroutineReady
        hemitterSpec.left
  · intro skipped count tailFirst tail
    exact
      canonicalSeqDescription_haltsFromTapeEquiv_of_haltsFromTape
        leftMoveToRawBoundaryDescription_subroutineReady
        hemitterSpec.left
        (countWindowRawSourceEncoderCountWindowStart_to_rawBoundary
          skipped count tailFirst tail)
        (countWindowRawSourceEncoderRawBoundaryTape_move_left_move_right
          skipped count (some tailFirst :: tail))
        (hemitterSpec.right skipped count tailFirst tail)

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

theorem countWindowRawSourceEncoderRawBoundaryRightEdgeEmitterConstruction_core :
    CountWindowRawSourceEncoderRawBoundaryRightEdgeEmitterConstruction := by
  rcases
      CountWindowRawSourceEncoder.RawBoundaryRightEdgeEmitter.construction_core
    with ⟨emitter, hemitter⟩
  refine ⟨emitter, hemitter.left, ?_⟩
  intro skipped count tailFirst tail
  simpa [CountWindowRawSourceEncoder.RawBoundaryRightEdgeEmitter.Spec,
    CountWindowRawSourceEncoder.RawBoundaryRightEdgeEmitter.sourceTape,
    CountWindowRawSourceEncoder.RawBoundaryRightEdgeEmitter.preRewindTape,
    CountWindowRawSourceEncoder.RawBoundaryRightEdgeEmitter.rightEdgeTape,
    CountWindowRawSourceEncoder.RawBoundaryRightEdgeEmitter.encodedLayoutBits,
    countWindowRawSourceEncoderRawBoundaryTape,
    countWindowRawSourceEncoderEncodedLayoutPreRewindTape,
    countWindowRawSourceEncoderEncodedLayoutRightEdgeTape,
    countWindowRawSourceEncoderEncodedLayoutBits] using
      hemitter.right skipped count tailFirst tail

theorem countWindowRawSourceEncoderRawBoundaryEmitterEquivConstruction_core :
    CountWindowRawSourceEncoderRawBoundaryEmitterEquivConstruction := by
  exact
    countWindowRawSourceEncoderRawBoundaryEmitterEquivConstruction_of_rightEdgeEmitter
      countWindowRawSourceEncoderRawBoundaryRightEdgeEmitterConstruction_core

theorem countWindowRawSourceEncoderCountWindowStartEmitterEquivConstruction_core :
    CountWindowRawSourceEncoderCountWindowStartEmitterEquivConstruction := by
  exact
    countWindowRawSourceEncoderCountWindowStartEmitterEquivConstruction_of_rawBoundaryEmitter
      countWindowRawSourceEncoderRawBoundaryEmitterEquivConstruction_core

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

import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.PairEncodedOptionCellCompactor.Base

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering
namespace PairEncodedOptionCellCompactor

namespace ProjectableFocusMachine

def scanState : Nat := 1

def bitsState : Nat := 2

def haltState : Nat := 99

def markerRewindTape (left passed : Nat) : Tape Bool :=
  { left := List.replicate left markerCell
    head := markerCell
    right := List.replicate passed markerCell ++ [none] }

def markerBlankTape (passed : Nat) : Tape Bool :=
  { left := []
    head := none
    right := List.replicate passed markerCell ++ [none] }

def focusTargetTape
    (bits : Word Bool) (padding : List (Option Bool)) : Tape Bool :=
  tapeAtCells (bits.reverse.map some ++ [none])
    (none :: padding ++ [none])

def leftEdgeTargetTape
    (bits : Word Bool) (padding : List (Option Bool)) : Tape Bool :=
  tapeAtCells [] (none :: splitTargetPayloadCells bits padding ++ [none])

def scanStartTargetTape
    (bits : Word Bool) (padding : List (Option Bool)) : Tape Bool :=
  tapeAtCells [none] (splitTargetPayloadCells bits padding ++ [none])

def rows : List Transition :=
  [ ThreeTape.row 0 none none none
      ThreeTape.keepS ThreeTape.keepL ThreeTape.keepS scanState
  , ThreeTape.row scanState none markerCell none
      ThreeTape.keepS ThreeTape.keepL ThreeTape.keepL scanState
  , ThreeTape.row scanState none markerCell (some false)
      ThreeTape.keepS ThreeTape.keepL ThreeTape.keepL scanState
  , ThreeTape.row scanState none markerCell (some true)
      ThreeTape.keepS ThreeTape.keepL ThreeTape.keepL scanState
  , ThreeTape.row scanState none none none
      ThreeTape.keepS ThreeTape.keepS ThreeTape.keepR bitsState
  , ThreeTape.row bitsState none none (some false)
      ThreeTape.keepS ThreeTape.keepS ThreeTape.keepR bitsState
  , ThreeTape.row bitsState none none (some true)
      ThreeTape.keepS ThreeTape.keepS ThreeTape.keepR bitsState
  , ThreeTape.row bitsState none none none
      ThreeTape.keepS ThreeTape.keepS ThreeTape.keepS haltState ]

def description : Description :=
  ThreeTape.description 100 0 haltState rows

theorem description_wellFormed :
    description.WellFormed := by
  refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
  · exact
      structuredTransition_wellFormed_of_all
        (l := description.transitions)
        (stateCount := description.stateCount)
        (tapeCount := description.tapeCount)
        (by decide)
  · exact
      structuredTransition_deterministic_of_all
        (l := description.transitions)
        (by decide)

theorem description_haltTransitionFree :
    description.HaltTransitionFree :=
  structuredTransition_notFrom_of_all
    (l := description.transitions)
    (state := description.halt)
    (by decide)

theorem description_supportsReadWriteRows3 :
    SupportsReadWriteRows3 description :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)

def initialConfig
    (bits : Word Bool) (padding : List (Option Bool)) :
    Configuration :=
  ThreeTape.config 0
    (splitTargetOutput0 bits padding)
    (splitTargetOutput1 bits padding)
    (splitTargetOutput2 bits padding)

def loopConfig
    (bits : Word Bool) (padding : List (Option Bool))
    (left passed : Nat) (target : Tape Bool) : Configuration :=
  ThreeTape.config scanState
    (splitTargetOutput0 bits padding)
    (markerRewindTape left passed)
    target

def blankConfig
    (bits : Word Bool) (padding : List (Option Bool))
    (passed : Nat) (target : Tape Bool) : Configuration :=
  ThreeTape.config scanState
    (splitTargetOutput0 bits padding)
    (markerBlankTape passed)
    target

def scanConfig
    (bits : Word Bool) (padding : List (Option Bool))
    (target : Tape Bool) : Configuration :=
  ThreeTape.config bitsState
    (splitTargetOutput0 bits padding)
    (markerBlankTape ((splitTargetPayloadCells bits padding).length + 1))
    target

def finalConfig
    (bits : Word Bool) (padding : List (Option Bool)) : Configuration :=
  ThreeTape.config haltState
    (splitTargetOutput0 bits padding)
    (markerBlankTape ((splitTargetPayloadCells bits padding).length + 1))
    (focusTargetTape bits padding)

def focusSteps
    (bits : Word Bool) (padding : List (Option Bool)) : Nat :=
  (((1 + ((splitTargetPayloadCells bits padding).length + 1)) + 1) +
    (bits.length + 1))

def repeatMoveLeft : Nat -> Tape Bool -> Tape Bool
  | 0, T => T
  | n + 1, T => repeatMoveLeft n (Tape.moveLeft T)

theorem splitSourcePayloadCells_length_eq
    (bits : Word Bool) (padding : List (Option Bool)) :
    (splitSourcePayloadCells bits padding).length =
      (splitTargetPayloadCells bits padding).length + 1 := by
  simp [splitSourcePayloadCells, splitTargetPayloadCells]
  lia

theorem enter_run
    (bits : Word Bool) (padding : List (Option Bool)) :
    description.runConfig 1 (initialConfig bits padding) =
      loopConfig bits padding (splitTargetPayloadCells bits padding).length 0
        (splitTargetOutput2 bits padding) := by
  three_tape_step [description, rows, scanState, bitsState, haltState,
    initialConfig, loopConfig,
    splitTargetOutput0, splitTargetOutput1, splitTargetOutput2,
    markerTapeAt, markerRewindTape, outputTape,
    sourceTapeAt, encodedCells, markerCell,
    splitSourcePayloadCells_length_eq]

theorem loop_step_succ
    (bits : Word Bool) (padding : List (Option Bool))
    (left passed : Nat) (target : Tape Bool) :
    description.runConfig 1
      (loopConfig bits padding (left + 1) passed target) =
    loopConfig bits padding left (passed + 1) (Tape.moveLeft target) := by
  cases target with
  | mk targetLeft targetHead targetRight =>
      cases targetHead with
      | none =>
          three_tape_step [description, rows, scanState, bitsState,
            haltState, loopConfig, markerRewindTape,
            splitTargetOutput0, sourceTapeAt, encodedCells, markerCell]
      | some bit =>
          cases bit <;>
            three_tape_step [description, rows, scanState, bitsState,
              haltState, loopConfig, markerRewindTape,
              splitTargetOutput0, sourceTapeAt, encodedCells, markerCell]

theorem loop_step_zero
    (bits : Word Bool) (padding : List (Option Bool))
    (passed : Nat) (target : Tape Bool) :
    description.runConfig 1
      (loopConfig bits padding 0 passed target) =
    blankConfig bits padding (passed + 1) (Tape.moveLeft target) := by
  cases target with
  | mk targetLeft targetHead targetRight =>
      cases targetHead with
      | none =>
          three_tape_step [description, rows, scanState, bitsState,
            haltState, loopConfig, blankConfig,
            markerRewindTape, markerBlankTape,
            splitTargetOutput0, sourceTapeAt, encodedCells, markerCell]
      | some bit =>
          cases bit <;>
            three_tape_step [description, rows, scanState, bitsState,
              haltState, loopConfig, blankConfig,
              markerRewindTape, markerBlankTape,
              splitTargetOutput0, sourceTapeAt, encodedCells, markerCell]

theorem loop_run
    (bits : Word Bool) (padding : List (Option Bool))
    (left passed : Nat) (target : Tape Bool) :
    description.runConfig (left + 1)
      (loopConfig bits padding left passed target) =
    blankConfig bits padding (passed + (left + 1))
      (repeatMoveLeft (left + 1) target) := by
  induction left generalizing passed target with
  | zero =>
      simpa using loop_step_zero bits padding passed target
  | succ left ih =>
      rw [show left + 1 + 1 = 1 + (left + 1) by lia]
      rw [Description.runConfig_add]
      rw [loop_step_succ bits padding left passed target]
      rw [ih (passed + 1) (Tape.moveLeft target)]
      simp [repeatMoveLeft, Nat.add_comm, Nat.add_left_comm]

theorem repeatMoveLeft_all
    (left : List (Option Bool)) (head : Option Bool)
    (right : List (Option Bool)) :
    repeatMoveLeft (left.length + 1)
      { left := left, head := head, right := right } =
    { left := [], head := none, right := left.reverse ++ head :: right } := by
  induction left generalizing head right with
  | nil =>
      simp [repeatMoveLeft, Tape.moveLeft]
  | cons cell rest ih =>
      change repeatMoveLeft (rest.length + 1)
          { left := rest, head := cell, right := head :: right } =
        { left := [], head := none,
          right := (cell :: rest).reverse ++ head :: right }
      simpa [List.append_assoc] using ih cell (head :: right)

theorem repeatMoveLeft_outputTape
    (cells : List (Option Bool)) :
    repeatMoveLeft (cells.length + 1) (outputTape cells) =
      tapeAtCells [] (none :: cells ++ [none]) := by
  simpa [outputTape, tapeAtCells, List.reverse_reverse]
    using repeatMoveLeft_all cells.reverse none ([] : List (Option Bool))

theorem blank_to_scan_run
    (bits : Word Bool) (padding : List (Option Bool)) :
    description.runConfig 1
      (blankConfig bits padding
        ((splitTargetPayloadCells bits padding).length + 1)
        (leftEdgeTargetTape bits padding)) =
    scanConfig bits padding (scanStartTargetTape bits padding) := by
  three_tape_step [description, rows, scanState, bitsState, haltState,
    blankConfig, scanConfig,
    leftEdgeTargetTape, scanStartTargetTape, markerBlankTape,
    splitTargetOutput0, sourceTapeAt, encodedCells, markerCell,
    splitTargetPayloadCells]
  cases bits <;> rfl

theorem scan_step
    (bits : Word Bool) (padding : List (Option Bool))
    (base rest : List (Option Bool)) (bit : Bool) :
    description.runConfig 1
      (scanConfig bits padding (tapeAtCells base (some bit :: rest))) =
    scanConfig bits padding (tapeAtCells (some bit :: base) rest) := by
  cases bit <;>
    three_tape_step [description, rows, scanState, bitsState, haltState,
      scanConfig, markerBlankTape,
      splitTargetOutput0, sourceTapeAt, encodedCells, markerCell,
      tapeAtCells_moveRight_cons] <;>
    cases rest <;> rfl

theorem scan_prefix_run
    (bits : Word Bool) (padding : List (Option Bool))
    (scanBits : Word Bool) (base : List (Option Bool)) :
    description.runConfig scanBits.length
      (scanConfig bits padding
        (tapeAtCells base (scanBits.map some ++ none :: padding ++ [none]))) =
    scanConfig bits padding
      (tapeAtCells (scanBits.reverse.map some ++ base)
        (none :: padding ++ [none])) := by
  induction scanBits generalizing base with
  | nil =>
      rfl
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        change rest.length + 1 = 1 + rest.length
        lia]
      rw [Description.runConfig_add]
      simp only [List.map_cons, List.cons_append]
      rw [scan_step bits padding base
        (rest.map some ++ none :: padding ++ [none]) bit]
      simpa [List.map_append, List.append_assoc] using
        ih (some bit :: base)

theorem scan_halt_final
    (bits : Word Bool) (padding : List (Option Bool)) :
    description.runConfig 1
      (scanConfig bits padding (focusTargetTape bits padding)) =
    finalConfig bits padding := by
  three_tape_step [description, rows, scanState, bitsState, haltState,
    scanConfig, finalConfig,
    focusTargetTape, markerBlankTape,
    splitTargetOutput0, sourceTapeAt, encodedCells, markerCell]

theorem scan_run
    (bits : Word Bool) (padding : List (Option Bool)) :
    description.runConfig (bits.length + 1)
      (scanConfig bits padding (scanStartTargetTape bits padding)) =
    finalConfig bits padding := by
  rw [Description.runConfig_add]
  rw [show scanStartTargetTape bits padding =
      tapeAtCells [none] (bits.map some ++ none :: padding ++ [none]) by
    simp [scanStartTargetTape, splitTargetPayloadCells, List.append_assoc]]
  rw [scan_prefix_run bits padding bits [none]]
  simpa [focusTargetTape] using scan_halt_final bits padding

theorem run
    (bits : Word Bool) (padding : List (Option Bool)) :
    description.runConfig (focusSteps bits padding)
        (initialConfig bits padding) =
      finalConfig bits padding := by
  unfold focusSteps
  refine ThreeTape.runConfig_chain4 (D := description)
    (c := initialConfig bits padding)
    (c1 := loopConfig bits padding
        (splitTargetPayloadCells bits padding).length 0
        (splitTargetOutput2 bits padding))
    (c2 := blankConfig bits padding
        ((splitTargetPayloadCells bits padding).length + 1)
        (leftEdgeTargetTape bits padding))
    (c3 := scanConfig bits padding (scanStartTargetTape bits padding))
    (c4 := finalConfig bits padding) ?_ ?_ ?_ ?_
  · exact enter_run bits padding
  · simpa [leftEdgeTargetTape, splitTargetOutput2,
      repeatMoveLeft_outputTape, Nat.zero_add] using
      loop_run bits padding (splitTargetPayloadCells bits padding).length 0
        (splitTargetOutput2 bits padding)
  · exact blank_to_scan_run bits padding
  · exact scan_run bits padding

theorem focusTargetTape_equiv_rightEdgeRewindSourceTape
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.Equiv (focusTargetTape bits padding)
      (rightEdgeRewindSourceTape bits padding) := by
  simp [focusTargetTape, rightEdgeRewindSourceTape, tapeAtCells,
    Tape.Equiv, dropTrailingNone_append_none]

def loweredDescription : MachineDescription :=
  lowerStructured3Description description

theorem loweredDescription_wellFormed :
    loweredDescription.WellFormed := by
  simpa [loweredDescription] using
    lowerStructured3Description_wellFormed
      description_wellFormed
      description_supportsReadWriteRows3

theorem loweredDescription_subroutineReady :
    loweredDescription.SubroutineReady := by
  simpa [loweredDescription] using
    lowerStructured3Description_subroutineReady
      description_wellFormed
      description_supportsReadWriteRows3

theorem loweredDescription_haltsFromTapeEquiv
    (bits : Word Bool) (padding : List (Option Bool)) :
    loweredDescription.HaltsFromTapeEquiv
      (splitTargetOutputTape bits padding)
      (encodedGuardedStructured3Tapes
        (splitTargetOutput0 bits padding)
        (markerBlankTape ((splitTargetPayloadCells bits padding).length + 1))
        (focusTargetTape bits padding)) := by
  simpa [loweredDescription, initialConfig, finalConfig,
    splitTargetOutputTape, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      description_wellFormed
      description_haltTransitionFree
      description_supportsReadWriteRows3
      (c := initialConfig bits padding)
      (tapes :=
        [ splitTargetOutput0 bits padding
        , markerBlankTape ((splitTargetPayloadCells bits padding).length + 1)
        , focusTargetTape bits padding ])
      rfl
      (by simp [description, initialConfig, ThreeTape.description])
      ⟨focusSteps bits padding, run bits padding⟩

theorem projectableSpec :
    SplitTargetProjectableRightEdgeRewindOutputSpec loweredDescription := by
  refine ⟨loweredDescription_subroutineReady, ?_⟩
  intro bits padding
  refine
    ⟨splitTargetOutput0 bits padding,
      markerBlankTape ((splitTargetPayloadCells bits padding).length + 1),
      focusTargetTape bits padding,
      focusTargetTape_equiv_rightEdgeRewindSourceTape bits padding,
      ?_⟩
  exact loweredDescription_haltsFromTapeEquiv bits padding

theorem construction :
    SplitTargetProjectableRightEdgeRewindOutputSplitPadSymbolCaseConstruction := by
  exact
    ⟨loweredDescription,
      splitTargetProjectableRightEdgeRewindOutputSplitPadSymbolCaseSpec_of_spec
        projectableSpec⟩

end ProjectableFocusMachine

theorem splitTargetProjectableRightEdgeRewindOutputSplitPadSymbolCaseConstruction_core :
    SplitTargetProjectableRightEdgeRewindOutputSplitPadSymbolCaseConstruction := by
  exact ProjectableFocusMachine.construction

theorem splitTargetProjectableRightEdgeRewindOutputConstruction_core :
    SplitTargetProjectableRightEdgeRewindOutputConstruction := by
  exact
    splitTargetProjectableRightEdgeRewindOutputConstruction_of_splitPadSymbolCases
      splitTargetProjectableRightEdgeRewindOutputSplitPadSymbolCaseConstruction_core


end PairEncodedOptionCellCompactor
end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC

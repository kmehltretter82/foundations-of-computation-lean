import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.ChunkExpandLoop

set_option doc.verso true

/-!
# Raw-boundary length cursor loop

This module starts the uniform replacement for the length-field prepender.  The
machine first prepends the done chunk immediately left of the cell-chunk block,
then walks the cell chunks with a temporary cursor blank.  For each four-bit
cell chunk it prepends one tick chunk at the far-left anchor, restores the
cursor cell, advances four cells to the next chunk, and halts when that advance
lands on the separator.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open EncRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf

namespace CommonGround
namespace FiniteTransducers
namespace CountWindowRawSourceEncoder
namespace RawBoundaryRightEdgeEmitter

def rawBoundaryLengthCursorLoopHalt : Nat := 0

def rawBoundaryLengthCursorLoopStart : Nat := 1

def rawBoundaryLengthCursorLoopDoneScanLeft : Nat := 2

def rawBoundaryLengthCursorLoopDoneWrite2 : Nat := 3

def rawBoundaryLengthCursorLoopDoneWrite1 : Nat := 4

def rawBoundaryLengthCursorLoopDoneWrite0 : Nat := 5

def rawBoundaryLengthCursorLoopDoneReturn : Nat := 6

def rawBoundaryLengthCursorLoopDoneBounce : Nat := 7

def rawBoundaryLengthCursorLoopCursorStart : Nat := 8

def rawBoundaryLengthCursorLoopCursorScanLeft : Nat := 9

def rawBoundaryLengthCursorLoopSkipDone0 : Nat := 10

def rawBoundaryLengthCursorLoopSkipDone1 : Nat := 11

def rawBoundaryLengthCursorLoopSkipDone2 : Nat := 12

def rawBoundaryLengthCursorLoopSkipDone3 : Nat := 13

def rawBoundaryLengthCursorLoopCursorCheck : Nat := 14

def rawBoundaryLengthCursorLoopHaltBounce : Nat := 15

def rawBoundaryLengthCursorLoopCarryFalse : Nat := 16

def rawBoundaryLengthCursorLoopTickFalse2 : Nat := 17

def rawBoundaryLengthCursorLoopTickFalse1 : Nat := 18

def rawBoundaryLengthCursorLoopTickFalse0 : Nat := 19

def rawBoundaryLengthCursorLoopReturnFalse : Nat := 20

def rawBoundaryLengthCursorLoopCarryTrue : Nat := 21

def rawBoundaryLengthCursorLoopTickTrue2 : Nat := 22

def rawBoundaryLengthCursorLoopTickTrue1 : Nat := 23

def rawBoundaryLengthCursorLoopTickTrue0 : Nat := 24

def rawBoundaryLengthCursorLoopReturnTrue : Nat := 25

def rawBoundaryLengthCursorLoopAdvance1 : Nat := 26

def rawBoundaryLengthCursorLoopAdvance2 : Nat := 27

def rawBoundaryLengthCursorLoopAdvance3 : Nat := 28

def rawBoundaryLengthCursorLoopDescription : MachineDescription where
  stateCount := 29
  start := rawBoundaryLengthCursorLoopStart
  halt := rawBoundaryLengthCursorLoopHalt
  transitions :=
    [ transition rawBoundaryLengthCursorLoopStart
        none none Direction.left rawBoundaryLengthCursorLoopDoneScanLeft
    , transition rawBoundaryLengthCursorLoopDoneScanLeft
        (some false) (some false) Direction.left
        rawBoundaryLengthCursorLoopDoneScanLeft
    , transition rawBoundaryLengthCursorLoopDoneScanLeft
        (some true) (some true) Direction.left
        rawBoundaryLengthCursorLoopDoneScanLeft
    , transition rawBoundaryLengthCursorLoopDoneScanLeft
        none (some true) Direction.left
        rawBoundaryLengthCursorLoopDoneWrite2
    , transition rawBoundaryLengthCursorLoopDoneWrite2
        none (some true) Direction.left
        rawBoundaryLengthCursorLoopDoneWrite1
    , transition rawBoundaryLengthCursorLoopDoneWrite1
        none (some false) Direction.left
        rawBoundaryLengthCursorLoopDoneWrite0
    , transition rawBoundaryLengthCursorLoopDoneWrite0
        none (some false) Direction.right
        rawBoundaryLengthCursorLoopDoneReturn
    , transition rawBoundaryLengthCursorLoopDoneReturn
        (some false) (some false) Direction.right
        rawBoundaryLengthCursorLoopDoneReturn
    , transition rawBoundaryLengthCursorLoopDoneReturn
        (some true) (some true) Direction.right
        rawBoundaryLengthCursorLoopDoneReturn
    , transition rawBoundaryLengthCursorLoopDoneReturn
        none none Direction.left rawBoundaryLengthCursorLoopDoneBounce
    , transition rawBoundaryLengthCursorLoopDoneBounce
        (some false) (some false) Direction.right
        rawBoundaryLengthCursorLoopCursorStart
    , transition rawBoundaryLengthCursorLoopDoneBounce
        (some true) (some true) Direction.right
        rawBoundaryLengthCursorLoopCursorStart
    , transition rawBoundaryLengthCursorLoopCursorStart
        none none Direction.left rawBoundaryLengthCursorLoopCursorScanLeft
    , transition rawBoundaryLengthCursorLoopCursorScanLeft
        (some false) (some false) Direction.left
        rawBoundaryLengthCursorLoopCursorScanLeft
    , transition rawBoundaryLengthCursorLoopCursorScanLeft
        (some true) (some true) Direction.left
        rawBoundaryLengthCursorLoopCursorScanLeft
    , transition rawBoundaryLengthCursorLoopCursorScanLeft
        none none Direction.right rawBoundaryLengthCursorLoopSkipDone0
    , transition rawBoundaryLengthCursorLoopSkipDone0
        (some false) (some false) Direction.right
        rawBoundaryLengthCursorLoopSkipDone1
    , transition rawBoundaryLengthCursorLoopSkipDone0
        (some true) (some true) Direction.right
        rawBoundaryLengthCursorLoopSkipDone1
    , transition rawBoundaryLengthCursorLoopSkipDone1
        (some false) (some false) Direction.right
        rawBoundaryLengthCursorLoopSkipDone2
    , transition rawBoundaryLengthCursorLoopSkipDone1
        (some true) (some true) Direction.right
        rawBoundaryLengthCursorLoopSkipDone2
    , transition rawBoundaryLengthCursorLoopSkipDone2
        (some false) (some false) Direction.right
        rawBoundaryLengthCursorLoopSkipDone3
    , transition rawBoundaryLengthCursorLoopSkipDone2
        (some true) (some true) Direction.right
        rawBoundaryLengthCursorLoopSkipDone3
    , transition rawBoundaryLengthCursorLoopSkipDone3
        (some false) (some false) Direction.right
        rawBoundaryLengthCursorLoopCursorCheck
    , transition rawBoundaryLengthCursorLoopSkipDone3
        (some true) (some true) Direction.right
        rawBoundaryLengthCursorLoopCursorCheck
    , transition rawBoundaryLengthCursorLoopCursorCheck
        none none Direction.left rawBoundaryLengthCursorLoopHaltBounce
    , transition rawBoundaryLengthCursorLoopHaltBounce
        (some false) (some false) Direction.right
        rawBoundaryLengthCursorLoopHalt
    , transition rawBoundaryLengthCursorLoopHaltBounce
        (some true) (some true) Direction.right
        rawBoundaryLengthCursorLoopHalt
    , transition rawBoundaryLengthCursorLoopCursorCheck
        (some false) none Direction.left
        rawBoundaryLengthCursorLoopCarryFalse
    , transition rawBoundaryLengthCursorLoopCursorCheck
        (some true) none Direction.left
        rawBoundaryLengthCursorLoopCarryTrue
    , transition rawBoundaryLengthCursorLoopCarryFalse
        (some false) (some false) Direction.left
        rawBoundaryLengthCursorLoopCarryFalse
    , transition rawBoundaryLengthCursorLoopCarryFalse
        (some true) (some true) Direction.left
        rawBoundaryLengthCursorLoopCarryFalse
    , transition rawBoundaryLengthCursorLoopCarryFalse
        none (some false) Direction.left
        rawBoundaryLengthCursorLoopTickFalse2
    , transition rawBoundaryLengthCursorLoopTickFalse2
        none (some true) Direction.left
        rawBoundaryLengthCursorLoopTickFalse1
    , transition rawBoundaryLengthCursorLoopTickFalse1
        none (some false) Direction.left
        rawBoundaryLengthCursorLoopTickFalse0
    , transition rawBoundaryLengthCursorLoopTickFalse0
        none (some false) Direction.right
        rawBoundaryLengthCursorLoopReturnFalse
    , transition rawBoundaryLengthCursorLoopReturnFalse
        (some false) (some false) Direction.right
        rawBoundaryLengthCursorLoopReturnFalse
    , transition rawBoundaryLengthCursorLoopReturnFalse
        (some true) (some true) Direction.right
        rawBoundaryLengthCursorLoopReturnFalse
    , transition rawBoundaryLengthCursorLoopReturnFalse
        none (some false) Direction.right
        rawBoundaryLengthCursorLoopAdvance1
    , transition rawBoundaryLengthCursorLoopCarryTrue
        (some false) (some false) Direction.left
        rawBoundaryLengthCursorLoopCarryTrue
    , transition rawBoundaryLengthCursorLoopCarryTrue
        (some true) (some true) Direction.left
        rawBoundaryLengthCursorLoopCarryTrue
    , transition rawBoundaryLengthCursorLoopCarryTrue
        none (some false) Direction.left
        rawBoundaryLengthCursorLoopTickTrue2
    , transition rawBoundaryLengthCursorLoopTickTrue2
        none (some true) Direction.left
        rawBoundaryLengthCursorLoopTickTrue1
    , transition rawBoundaryLengthCursorLoopTickTrue1
        none (some false) Direction.left
        rawBoundaryLengthCursorLoopTickTrue0
    , transition rawBoundaryLengthCursorLoopTickTrue0
        none (some false) Direction.right
        rawBoundaryLengthCursorLoopReturnTrue
    , transition rawBoundaryLengthCursorLoopReturnTrue
        (some false) (some false) Direction.right
        rawBoundaryLengthCursorLoopReturnTrue
    , transition rawBoundaryLengthCursorLoopReturnTrue
        (some true) (some true) Direction.right
        rawBoundaryLengthCursorLoopReturnTrue
    , transition rawBoundaryLengthCursorLoopReturnTrue
        none (some true) Direction.right
        rawBoundaryLengthCursorLoopAdvance1
    , transition rawBoundaryLengthCursorLoopAdvance1
        (some false) (some false) Direction.right
        rawBoundaryLengthCursorLoopAdvance2
    , transition rawBoundaryLengthCursorLoopAdvance1
        (some true) (some true) Direction.right
        rawBoundaryLengthCursorLoopAdvance2
    , transition rawBoundaryLengthCursorLoopAdvance2
        (some false) (some false) Direction.right
        rawBoundaryLengthCursorLoopAdvance3
    , transition rawBoundaryLengthCursorLoopAdvance2
        (some true) (some true) Direction.right
        rawBoundaryLengthCursorLoopAdvance3
    , transition rawBoundaryLengthCursorLoopAdvance3
        (some false) (some false) Direction.right
        rawBoundaryLengthCursorLoopCursorCheck
    , transition rawBoundaryLengthCursorLoopAdvance3
        (some true) (some true) Direction.right
        rawBoundaryLengthCursorLoopCursorCheck ]

theorem rawBoundaryLengthCursorLoopDescription_wellFormed :
    rawBoundaryLengthCursorLoopDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := rawBoundaryLengthCursorLoopDescription.transitions)
      (stateCount := rawBoundaryLengthCursorLoopDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := rawBoundaryLengthCursorLoopDescription.transitions)
      (by decide)

theorem rawBoundaryLengthCursorLoopDescription_haltTransitionFree :
    rawBoundaryLengthCursorLoopDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := rawBoundaryLengthCursorLoopDescription.transitions)
    (state := rawBoundaryLengthCursorLoopDescription.halt)
    (by decide)

theorem rawBoundaryLengthCursorLoopDescription_subroutineReady :
    rawBoundaryLengthCursorLoopDescription.SubroutineReady :=
  ⟨rawBoundaryLengthCursorLoopDescription_wellFormed,
    rawBoundaryLengthCursorLoopDescription_haltTransitionFree⟩

def rawBoundaryLengthCursorTickBits : Word Bool :=
  encodeCodeSymbolAsInput MachineCodeSymbol.tick

def rawBoundaryLengthCursorDoneBits : Word Bool :=
  encodeCodeSymbolAsInput MachineCodeSymbol.done

private abbrev rawBoundaryLengthCursorStageNatBits (n : Nat) : Word Bool :=
  DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits n

def rawBoundaryLengthCursorSeparatorTape
    (emitted : Word Bool) (blankTail : Nat)
    (right : List (Option Bool)) : Tape Bool :=
  tapeAtCells (emitted.reverse.map some)
    (none ::
      List.append
        (List.replicate (blankTail + 1) (none : Option Bool))
        right)

def rawBoundaryLengthCursorOutputBits (layout : Word Bool) : Word Bool :=
  List.append
    (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
      layout.length)
    (preservingCellPassCellBits layout)

def rawBoundaryLengthCursorTargetTape
    (layout : Word Bool) (blankTail : Nat)
    (right : List (Option Bool)) : Tape Bool :=
  rawBoundaryLengthCursorSeparatorTape
    (rawBoundaryLengthCursorOutputBits layout) blankTail right

attribute [local simp]
  rawBoundaryLengthCursorLoopDescription
  rawBoundaryLengthCursorLoopHalt
  rawBoundaryLengthCursorLoopStart
  rawBoundaryLengthCursorLoopDoneScanLeft
  rawBoundaryLengthCursorLoopDoneWrite2
  rawBoundaryLengthCursorLoopDoneWrite1
  rawBoundaryLengthCursorLoopDoneWrite0
  rawBoundaryLengthCursorLoopDoneReturn
  rawBoundaryLengthCursorLoopDoneBounce
  rawBoundaryLengthCursorLoopCursorStart
  rawBoundaryLengthCursorLoopCursorScanLeft
  rawBoundaryLengthCursorLoopSkipDone0
  rawBoundaryLengthCursorLoopSkipDone1
  rawBoundaryLengthCursorLoopSkipDone2
  rawBoundaryLengthCursorLoopSkipDone3
  rawBoundaryLengthCursorLoopCursorCheck
  rawBoundaryLengthCursorLoopHaltBounce
  rawBoundaryLengthCursorLoopCarryFalse
  rawBoundaryLengthCursorLoopTickFalse2
  rawBoundaryLengthCursorLoopTickFalse1
  rawBoundaryLengthCursorLoopTickFalse0
  rawBoundaryLengthCursorLoopReturnFalse
  rawBoundaryLengthCursorLoopCarryTrue
  rawBoundaryLengthCursorLoopTickTrue2
  rawBoundaryLengthCursorLoopTickTrue1
  rawBoundaryLengthCursorLoopTickTrue0
  rawBoundaryLengthCursorLoopReturnTrue
  rawBoundaryLengthCursorLoopAdvance1
  rawBoundaryLengthCursorLoopAdvance2
  rawBoundaryLengthCursorLoopAdvance3

private def rawBoundaryLengthCursorAnchorTape :
    Word Bool -> List (Option Bool) -> Tape Bool
  | [], right => tapeAtCells [] (none :: right)
  | bit :: rest, right => tapeAtCells (rest.map some) (some bit :: right)

private theorem rawBoundaryLengthCursorLoopDescription_step_doneScanLeft_bit
    (bit : Bool) (rest : Word Bool) (right : List (Option Bool)) :
    rawBoundaryLengthCursorLoopDescription.runConfig 1
        { state := rawBoundaryLengthCursorLoopDoneScanLeft
          tape := rawBoundaryLengthCursorAnchorTape (bit :: rest) right } =
      { state := rawBoundaryLengthCursorLoopDoneScanLeft
        tape :=
          rawBoundaryLengthCursorAnchorTape rest (some bit :: right) } := by
  cases bit <;> cases rest <;> cases right <;>
    simp [rawBoundaryLengthCursorAnchorTape, runConfig, stepConfig,
      lookupTransition, Matches, transition, tapeAtCells, Tape.read,
      Tape.write, Tape.move, Tape.moveLeft]

private theorem rawBoundaryLengthCursorLoopDescription_run_doneScanLeft
    (remainingRev : Word Bool) (right : List (Option Bool)) :
    rawBoundaryLengthCursorLoopDescription.runConfig
        remainingRev.length
        { state := rawBoundaryLengthCursorLoopDoneScanLeft
          tape := rawBoundaryLengthCursorAnchorTape remainingRev right } =
      { state := rawBoundaryLengthCursorLoopDoneScanLeft
        tape :=
          tapeAtCells []
            (none ::
              List.append (remainingRev.reverse.map some) right) } := by
  induction remainingRev generalizing right with
  | nil =>
      simp [rawBoundaryLengthCursorAnchorTape, runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        lia]
      rw [MachineDescription.runConfig_add]
      rw [rawBoundaryLengthCursorLoopDescription_step_doneScanLeft_bit]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: right)

private theorem rawBoundaryLengthCursorLoopDescription_run_start_doneScanLeft
    (emitted : Word Bool) (blankTail : Nat)
    (right : List (Option Bool)) :
    rawBoundaryLengthCursorLoopDescription.runConfig 1
        { state := rawBoundaryLengthCursorLoopStart
          tape :=
            rawBoundaryLengthCursorSeparatorTape
              emitted blankTail right } =
      { state := rawBoundaryLengthCursorLoopDoneScanLeft
        tape :=
          rawBoundaryLengthCursorAnchorTape emitted.reverse
            (none ::
              List.append
                (List.replicate (blankTail + 1) (none : Option Bool))
                right) } := by
  cases hrev : emitted.reverse with
  | nil =>
      simp [rawBoundaryLengthCursorSeparatorTape,
        rawBoundaryLengthCursorAnchorTape, runConfig, stepConfig,
        lookupTransition, Matches, transition, tapeAtCells, Tape.read,
        Tape.write, Tape.move, Tape.moveLeft, hrev]
  | cons bit rest =>
      cases bit <;>
        simp [rawBoundaryLengthCursorSeparatorTape,
          rawBoundaryLengthCursorAnchorTape, runConfig, stepConfig,
          lookupTransition, Matches, transition, tapeAtCells, Tape.read,
          Tape.write, Tape.move, Tape.moveLeft, hrev]

private theorem rawBoundaryLengthCursorLoopDescription_run_doneWrite
    (right : List (Option Bool)) :
    rawBoundaryLengthCursorLoopDescription.runConfig 4
        { state := rawBoundaryLengthCursorLoopDoneScanLeft
          tape := tapeAtCells [] (none :: right) } =
      { state := rawBoundaryLengthCursorLoopDoneReturn
        tape :=
          tapeAtCells [some false]
            (some false :: some true :: some true :: right) } := by
  cases right <;>
    simp [runConfig, stepConfig, lookupTransition, Matches, transition,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
      Tape.moveRight]

private theorem rawBoundaryLengthCursorLoopDescription_step_doneReturn_bit
    (bit : Bool) (left right : List (Option Bool)) :
    rawBoundaryLengthCursorLoopDescription.runConfig 1
        { state := rawBoundaryLengthCursorLoopDoneReturn
          tape := tapeAtCells left (some bit :: right) } =
      { state := rawBoundaryLengthCursorLoopDoneReturn
        tape := tapeAtCells (some bit :: left) right } := by
  cases bit <;> cases right <;>
    simp [runConfig, stepConfig, lookupTransition, Matches, transition,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]

private theorem rawBoundaryLengthCursorLoopDescription_run_doneReturn_scanRight
    (bits : Word Bool) (left right : List (Option Bool)) :
    rawBoundaryLengthCursorLoopDescription.runConfig bits.length
        { state := rawBoundaryLengthCursorLoopDoneReturn
          tape := tapeAtCells left
            (List.append (bits.map some) right) } =
      { state := rawBoundaryLengthCursorLoopDoneReturn
        tape :=
          tapeAtCells (List.append (bits.reverse.map some) left)
            right } := by
  induction bits generalizing left with
  | nil =>
      simp [runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        lia]
      rw [MachineDescription.runConfig_add]
      change
        rawBoundaryLengthCursorLoopDescription.runConfig rest.length
            (rawBoundaryLengthCursorLoopDescription.runConfig 1
              { state := rawBoundaryLengthCursorLoopDoneReturn
                tape := tapeAtCells left
                  (some bit ::
                    List.append (rest.map some) right) }) =
          { state := rawBoundaryLengthCursorLoopDoneReturn
            tape :=
              tapeAtCells
                (List.append ((bit :: rest).reverse.map some) left)
                right }
      rw [rawBoundaryLengthCursorLoopDescription_step_doneReturn_bit]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: left)

private theorem rawBoundaryLengthCursorLoopDescription_run_doneReturn_bounce
    (bit : Bool) (left right : List (Option Bool)) :
    rawBoundaryLengthCursorLoopDescription.runConfig 2
        { state := rawBoundaryLengthCursorLoopDoneReturn
          tape := tapeAtCells (some bit :: left) (none :: right) } =
      { state := rawBoundaryLengthCursorLoopCursorStart
        tape := tapeAtCells (some bit :: left) (none :: right) } := by
  cases bit <;> cases left <;> cases right <;>
    simp [runConfig, stepConfig, lookupTransition, Matches, transition,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
      Tape.moveRight]

private theorem rawBoundaryLengthCursorDoneBits_eq :
    rawBoundaryLengthCursorDoneBits = [false, false, true, true] := by
  simp [rawBoundaryLengthCursorDoneBits, encodeCodeSymbolAsInput]

private theorem rawBoundaryLengthCursorTickBits_eq :
    rawBoundaryLengthCursorTickBits = [false, false, true, false] := by
  simp [rawBoundaryLengthCursorTickBits, encodeCodeSymbolAsInput]

private theorem rawBoundaryLengthCursorStageNatBits_ne_nil
    (n : Nat) :
    rawBoundaryLengthCursorStageNatBits n ≠ [] := by
  cases n <;>
    simp [rawBoundaryLengthCursorStageNatBits,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_zero,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_succ]

private theorem rawBoundaryLengthCursorStageNatBits_succ
    (n : Nat) :
    rawBoundaryLengthCursorStageNatBits (n + 1) =
      List.append rawBoundaryLengthCursorTickBits
        (rawBoundaryLengthCursorStageNatBits n) := by
  simp [rawBoundaryLengthCursorStageNatBits,
    rawBoundaryLengthCursorTickBits,
    DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_succ,
    encodeCodeSymbolAsInput]

private theorem rawBoundaryLengthCursorLoopDescription_run_donePrefix
    (emitted : Word Bool) (blankTail : Nat)
    (right : List (Option Bool)) :
    rawBoundaryLengthCursorLoopDescription.runConfig
        (2 * emitted.length + 10)
        { state := rawBoundaryLengthCursorLoopStart
          tape := rawBoundaryLengthCursorSeparatorTape emitted blankTail right } =
      { state := rawBoundaryLengthCursorLoopCursorStart
        tape :=
          rawBoundaryLengthCursorSeparatorTape
            (List.append rawBoundaryLengthCursorDoneBits emitted)
            blankTail right } := by
  rw [show 2 * emitted.length + 10 =
      1 + (emitted.length + (4 + ((3 + emitted.length) + 2))) by
    lia]
  rw [MachineDescription.runConfig_add]
  rw [rawBoundaryLengthCursorLoopDescription_run_start_doneScanLeft]
  rw [show emitted.length = emitted.reverse.length by
    simp]
  rw [MachineDescription.runConfig_add]
  rw [rawBoundaryLengthCursorLoopDescription_run_doneScanLeft]
  rw [MachineDescription.runConfig_add]
  rw [rawBoundaryLengthCursorLoopDescription_run_doneWrite]
  rw [MachineDescription.runConfig_add]
  rw [show 3 + emitted.reverse.length =
      (List.append [false, true, true] emitted.reverse.reverse).length by
    simp
    lia]
  change
    rawBoundaryLengthCursorLoopDescription.runConfig 2
        (rawBoundaryLengthCursorLoopDescription.runConfig
          (List.append [false, true, true] emitted.reverse.reverse).length
          { state := rawBoundaryLengthCursorLoopDoneReturn
            tape :=
              tapeAtCells [some false]
                (List.append
                  ((List.append [false, true, true]
                    emitted.reverse.reverse).map some)
                  (none ::
                    (List.replicate (blankTail + 1) none ++ right))) }) =
      { state := rawBoundaryLengthCursorLoopCursorStart
        tape :=
          rawBoundaryLengthCursorSeparatorTape
            (List.append rawBoundaryLengthCursorDoneBits emitted)
            blankTail right }
  rw [rawBoundaryLengthCursorLoopDescription_run_doneReturn_scanRight]
  cases hrev : emitted.reverse with
  | nil =>
      simp [rawBoundaryLengthCursorSeparatorTape,
        rawBoundaryLengthCursorDoneBits_eq, hrev, runConfig, stepConfig,
        lookupTransition, Matches, transition, tapeAtCells, Tape.read,
        Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons bit rest =>
      cases bit
      · simp [rawBoundaryLengthCursorSeparatorTape,
          rawBoundaryLengthCursorDoneBits_eq, List.map_append,
          List.reverse_append, hrev, runConfig, stepConfig,
          lookupTransition, Matches, transition, tapeAtCells, Tape.read,
          Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
      · simp [rawBoundaryLengthCursorSeparatorTape,
          rawBoundaryLengthCursorDoneBits_eq, List.map_append,
          List.reverse_append, hrev, runConfig, stepConfig,
          lookupTransition, Matches, transition, tapeAtCells, Tape.read,
          Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

private def rawBoundaryLengthCursorCursorTape
    (storedAnchor : Bool) (emittedPrefix remaining : Word Bool)
    (blankTail : Nat) (right : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append (emittedPrefix.reverse.map some)
      (if storedAnchor then [none] else []))
    (List.append (remaining.map some)
      (none ::
        List.append
          (List.replicate (blankTail + 1) (none : Option Bool))
          right))

private theorem rawBoundaryLengthCursorLoopDescription_step_cursorScanLeft_bit
    (bit : Bool) (rest : Word Bool) (right : List (Option Bool)) :
    rawBoundaryLengthCursorLoopDescription.runConfig 1
        { state := rawBoundaryLengthCursorLoopCursorScanLeft
          tape := rawBoundaryLengthCursorAnchorTape (bit :: rest) right } =
      { state := rawBoundaryLengthCursorLoopCursorScanLeft
        tape :=
          rawBoundaryLengthCursorAnchorTape rest (some bit :: right) } := by
  cases bit <;> cases rest <;> cases right <;>
    simp [rawBoundaryLengthCursorAnchorTape, runConfig, stepConfig,
      lookupTransition, Matches, transition, tapeAtCells, Tape.read,
      Tape.write, Tape.move, Tape.moveLeft]

private theorem rawBoundaryLengthCursorLoopDescription_run_cursorScanLeft
    (remainingRev : Word Bool) (right : List (Option Bool)) :
    rawBoundaryLengthCursorLoopDescription.runConfig
        remainingRev.length
        { state := rawBoundaryLengthCursorLoopCursorScanLeft
          tape := rawBoundaryLengthCursorAnchorTape remainingRev right } =
      { state := rawBoundaryLengthCursorLoopCursorScanLeft
        tape :=
          tapeAtCells []
            (none ::
              List.append (remainingRev.reverse.map some) right) } := by
  induction remainingRev generalizing right with
  | nil =>
      simp [rawBoundaryLengthCursorAnchorTape, runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        lia]
      rw [MachineDescription.runConfig_add]
      rw [rawBoundaryLengthCursorLoopDescription_step_cursorScanLeft_bit]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: right)

private theorem rawBoundaryLengthCursorLoopDescription_run_cursorStart_scanLeft
    (block : Word Bool) (blankTail : Nat)
    (right : List (Option Bool)) :
    rawBoundaryLengthCursorLoopDescription.runConfig 1
        { state := rawBoundaryLengthCursorLoopCursorStart
          tape :=
            rawBoundaryLengthCursorSeparatorTape
              block blankTail right } =
      { state := rawBoundaryLengthCursorLoopCursorScanLeft
        tape :=
          rawBoundaryLengthCursorAnchorTape block.reverse
            (none ::
              List.append
                (List.replicate (blankTail + 1) (none : Option Bool))
                right) } := by
  cases hrev : block.reverse with
  | nil =>
      simp [rawBoundaryLengthCursorSeparatorTape,
        rawBoundaryLengthCursorAnchorTape, runConfig, stepConfig,
        lookupTransition, Matches, transition, tapeAtCells, Tape.read,
        Tape.write, Tape.move, Tape.moveLeft, hrev]
  | cons bit rest =>
      cases bit <;>
        simp [rawBoundaryLengthCursorSeparatorTape,
          rawBoundaryLengthCursorAnchorTape, runConfig, stepConfig,
          lookupTransition, Matches, transition, tapeAtCells, Tape.read,
          Tape.write, Tape.move, Tape.moveLeft, hrev]

private theorem rawBoundaryLengthCursorLoopDescription_run_skipDone
    (emitted : Word Bool) (blankTail : Nat)
    (right : List (Option Bool)) :
    rawBoundaryLengthCursorLoopDescription.runConfig 5
        { state := rawBoundaryLengthCursorLoopCursorScanLeft
          tape :=
            tapeAtCells []
              (none ::
                List.append
                  ((List.append rawBoundaryLengthCursorDoneBits
                    emitted).map some)
                  (none ::
                    List.append
                      (List.replicate (blankTail + 1)
                        (none : Option Bool))
                      right)) } =
      { state := rawBoundaryLengthCursorLoopCursorCheck
        tape :=
          rawBoundaryLengthCursorCursorTape true
            rawBoundaryLengthCursorDoneBits emitted blankTail right } := by
  cases emitted with
  | nil =>
      simp [rawBoundaryLengthCursorCursorTape,
        rawBoundaryLengthCursorDoneBits_eq, runConfig, stepConfig,
        lookupTransition, Matches, transition, tapeAtCells, Tape.read,
        Tape.write, Tape.move, Tape.moveRight]
  | cons bit rest =>
      cases bit <;>
        simp [rawBoundaryLengthCursorCursorTape,
          rawBoundaryLengthCursorDoneBits_eq, runConfig, stepConfig,
          lookupTransition, Matches, transition, tapeAtCells, Tape.read,
          Tape.write, Tape.move, Tape.moveRight]

private theorem rawBoundaryLengthCursorLoopDescription_run_cursorBootstrap
    (emitted : Word Bool) (blankTail : Nat)
    (right : List (Option Bool)) :
    rawBoundaryLengthCursorLoopDescription.runConfig
        (emitted.length + 10)
        { state := rawBoundaryLengthCursorLoopCursorStart
          tape :=
            rawBoundaryLengthCursorSeparatorTape
              (List.append rawBoundaryLengthCursorDoneBits emitted)
              blankTail right } =
      { state := rawBoundaryLengthCursorLoopCursorCheck
        tape :=
          rawBoundaryLengthCursorCursorTape true
            rawBoundaryLengthCursorDoneBits emitted blankTail right } := by
  rw [show emitted.length + 10 =
      1 +
        ((List.append rawBoundaryLengthCursorDoneBits emitted).length + 5) by
    simp [rawBoundaryLengthCursorDoneBits_eq]
    lia]
  rw [MachineDescription.runConfig_add]
  rw [rawBoundaryLengthCursorLoopDescription_run_cursorStart_scanLeft]
  rw [show (List.append rawBoundaryLengthCursorDoneBits emitted).length =
      (List.append rawBoundaryLengthCursorDoneBits emitted).reverse.length by
    simp
    lia]
  rw [MachineDescription.runConfig_add]
  rw [rawBoundaryLengthCursorLoopDescription_run_cursorScanLeft]
  simp only [List.reverse_reverse]
  rw [rawBoundaryLengthCursorLoopDescription_run_skipDone]

private def rawBoundaryLengthCursorCellBits (bit : Bool) : Word Bool :=
  rawBoundaryChunkExpandCellBits bit

private theorem rawBoundaryLengthCursorCellBits_false :
    rawBoundaryLengthCursorCellBits false =
      [false, true, false, true] := by
  simp [rawBoundaryLengthCursorCellBits, rawBoundaryChunkExpandCellBits,
    pulledRawBitCellChunkBits, preservingCellPassZeroBits]

private theorem rawBoundaryLengthCursorCellBits_true :
    rawBoundaryLengthCursorCellBits true =
      [false, true, true, false] := by
  simp [rawBoundaryLengthCursorCellBits, rawBoundaryChunkExpandCellBits,
    pulledRawBitCellChunkBits, preservingCellPassOneBits]

private def rawBoundaryLengthCursorCarryTape
    (storedAnchor : Bool) : Word Bool -> List (Option Bool) -> Tape Bool
  | [], right => tapeAtCells [] (none :: right)
  | bit :: rest, right =>
      tapeAtCells
        (List.append (rest.map some)
          (if storedAnchor then [none] else []))
        (some bit :: right)

private theorem rawBoundaryLengthCursorLoopDescription_step_cursorCheck_false
    (storedAnchor : Bool) (last : Bool) (rest : Word Bool)
    (right : List (Option Bool)) :
    rawBoundaryLengthCursorLoopDescription.runConfig 1
        { state := rawBoundaryLengthCursorLoopCursorCheck
          tape :=
            tapeAtCells
              (List.append ((last :: rest).map some)
                (if storedAnchor then [none] else []))
              (some false :: right) } =
      { state := rawBoundaryLengthCursorLoopCarryFalse
        tape :=
          rawBoundaryLengthCursorCarryTape storedAnchor
            (last :: rest) (none :: right) } := by
  cases storedAnchor <;> cases last <;> cases rest <;> cases right <;>
    simp [rawBoundaryLengthCursorCarryTape, runConfig, stepConfig,
      lookupTransition, Matches, transition, tapeAtCells, Tape.read,
      Tape.write, Tape.move, Tape.moveLeft]

private theorem rawBoundaryLengthCursorLoopDescription_step_carryFalse_bit
    (storedAnchor : Bool) (bit : Bool) (rest : Word Bool)
    (right : List (Option Bool)) :
    rawBoundaryLengthCursorLoopDescription.runConfig 1
        { state := rawBoundaryLengthCursorLoopCarryFalse
          tape :=
            rawBoundaryLengthCursorCarryTape storedAnchor
              (bit :: rest) right } =
      { state := rawBoundaryLengthCursorLoopCarryFalse
        tape :=
          rawBoundaryLengthCursorCarryTape storedAnchor
            rest (some bit :: right) } := by
  cases storedAnchor <;> cases bit <;> cases rest <;> cases right <;>
    simp [rawBoundaryLengthCursorCarryTape, runConfig, stepConfig,
      lookupTransition, Matches, transition, tapeAtCells, Tape.read,
      Tape.write, Tape.move, Tape.moveLeft]

private theorem rawBoundaryLengthCursorLoopDescription_run_carryFalse_to_anchor
    (storedAnchor : Bool) (remainingRev : Word Bool)
    (right : List (Option Bool)) :
    rawBoundaryLengthCursorLoopDescription.runConfig
        remainingRev.length
        { state := rawBoundaryLengthCursorLoopCarryFalse
          tape :=
            rawBoundaryLengthCursorCarryTape storedAnchor
              remainingRev right } =
      { state := rawBoundaryLengthCursorLoopCarryFalse
        tape :=
          tapeAtCells []
            (none ::
              List.append (remainingRev.reverse.map some) right) } := by
  induction remainingRev generalizing right with
  | nil =>
      cases storedAnchor <;>
        simp [rawBoundaryLengthCursorCarryTape, runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        lia]
      rw [MachineDescription.runConfig_add]
      rw [rawBoundaryLengthCursorLoopDescription_step_carryFalse_bit]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: right)

private theorem rawBoundaryLengthCursorLoopDescription_run_tickWriteFalse
    (right : List (Option Bool)) :
    rawBoundaryLengthCursorLoopDescription.runConfig 4
        { state := rawBoundaryLengthCursorLoopCarryFalse
          tape := tapeAtCells [] (none :: right) } =
      { state := rawBoundaryLengthCursorLoopReturnFalse
        tape :=
          tapeAtCells [some false]
            (some false :: some true :: some false :: right) } := by
  cases right <;>
    simp [runConfig, stepConfig, lookupTransition, Matches, transition,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
      Tape.moveRight]

private theorem rawBoundaryLengthCursorLoopDescription_step_returnFalse_bit
    (bit : Bool) (left right : List (Option Bool)) :
    rawBoundaryLengthCursorLoopDescription.runConfig 1
        { state := rawBoundaryLengthCursorLoopReturnFalse
          tape := tapeAtCells left (some bit :: right) } =
      { state := rawBoundaryLengthCursorLoopReturnFalse
        tape := tapeAtCells (some bit :: left) right } := by
  cases bit <;> cases right <;>
    simp [runConfig, stepConfig, lookupTransition, Matches, transition,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]

private theorem rawBoundaryLengthCursorLoopDescription_run_returnFalse_scanRight
    (bits : Word Bool) (left right : List (Option Bool)) :
    rawBoundaryLengthCursorLoopDescription.runConfig bits.length
        { state := rawBoundaryLengthCursorLoopReturnFalse
          tape := tapeAtCells left
            (List.append (bits.map some) right) } =
      { state := rawBoundaryLengthCursorLoopReturnFalse
        tape :=
          tapeAtCells (List.append (bits.reverse.map some) left)
            right } := by
  induction bits generalizing left with
  | nil =>
      simp [runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        lia]
      rw [MachineDescription.runConfig_add]
      change
        rawBoundaryLengthCursorLoopDescription.runConfig rest.length
            (rawBoundaryLengthCursorLoopDescription.runConfig 1
              { state := rawBoundaryLengthCursorLoopReturnFalse
                tape := tapeAtCells left
                  (some bit ::
                    List.append (rest.map some) right) }) =
          { state := rawBoundaryLengthCursorLoopReturnFalse
            tape :=
              tapeAtCells
                (List.append ((bit :: rest).reverse.map some) left)
                right }
      rw [rawBoundaryLengthCursorLoopDescription_step_returnFalse_bit]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: left)

private theorem rawBoundaryLengthCursorLoopDescription_step_returnFalse_cursor
    (left right : List (Option Bool)) :
    rawBoundaryLengthCursorLoopDescription.runConfig 1
        { state := rawBoundaryLengthCursorLoopReturnFalse
          tape := tapeAtCells left (none :: right) } =
      { state := rawBoundaryLengthCursorLoopAdvance1
        tape := tapeAtCells (some false :: left) right } := by
  cases right <;>
    simp [runConfig, stepConfig, lookupTransition, Matches, transition,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]

private theorem rawBoundaryLengthCursorLoopDescription_run_advanceThree
    (b₁ b₂ b₃ : Bool) (left right : List (Option Bool)) :
    rawBoundaryLengthCursorLoopDescription.runConfig 3
        { state := rawBoundaryLengthCursorLoopAdvance1
          tape :=
            tapeAtCells left
              (some b₁ :: some b₂ :: some b₃ :: right) } =
      { state := rawBoundaryLengthCursorLoopCursorCheck
        tape :=
          tapeAtCells (some b₃ :: some b₂ :: some b₁ :: left)
            right } := by
  cases b₁ <;> cases b₂ <;> cases b₃ <;> cases right <;>
    simp [runConfig, stepConfig, lookupTransition, Matches, transition,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]

private theorem rawBoundaryLengthCursorLoopDescription_run_cursorCheck_halt
    (storedAnchor : Bool) (last : Bool) (rest : Word Bool)
    (right : List (Option Bool)) :
    rawBoundaryLengthCursorLoopDescription.runConfig 2
        { state := rawBoundaryLengthCursorLoopCursorCheck
          tape :=
            tapeAtCells
              (List.append ((last :: rest).map some)
                (if storedAnchor then [none] else []))
              (none :: right) } =
      { state := rawBoundaryLengthCursorLoopHalt
        tape :=
          tapeAtCells
            (List.append ((last :: rest).map some)
              (if storedAnchor then [none] else []))
            (none :: right) } := by
  cases storedAnchor <;> cases last <;> cases rest <;> cases right <;>
    simp [runConfig, stepConfig, lookupTransition, Matches, transition,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
      Tape.moveRight]

private theorem rawBoundaryLengthCursorLoopDescription_run_cursorCheck_cell_false
    (storedAnchor : Bool) (count : Nat) (processed remaining : Word Bool)
    (blankTail : Nat) (right : List (Option Bool)) :
    exists steps : Nat,
      rawBoundaryLengthCursorLoopDescription.runConfig steps
          { state := rawBoundaryLengthCursorLoopCursorCheck
            tape :=
              rawBoundaryLengthCursorCursorTape storedAnchor
                (List.append (rawBoundaryLengthCursorStageNatBits count)
                  processed)
                (List.append (rawBoundaryLengthCursorCellBits false)
                  (preservingCellPassCellBits remaining))
                blankTail right } =
        { state := rawBoundaryLengthCursorLoopCursorCheck
          tape :=
            rawBoundaryLengthCursorCursorTape false
              (List.append
                (rawBoundaryLengthCursorStageNatBits (count + 1))
                (List.append processed
                  (rawBoundaryLengthCursorCellBits false)))
              (preservingCellPassCellBits remaining) blankTail right } := by
  let emittedPrefix : Word Bool :=
    List.append (rawBoundaryLengthCursorStageNatBits count) processed
  have hprefix_ne : emittedPrefix ≠ [] := by
    intro hnil
    have hlen := congrArg List.length hnil
    simp [emittedPrefix] at hlen
    exact rawBoundaryLengthCursorStageNatBits_ne_nil count hlen.left
  cases hrev : emittedPrefix.reverse with
  | nil =>
      have hprefix_nil : emittedPrefix = [] := by
        have h := congrArg List.reverse hrev
        simpa using h
      exact False.elim (hprefix_ne hprefix_nil)
  | cons last rest =>
      refine ⟨2 * emittedPrefix.length + 12, ?_⟩
      rw [show 2 * emittedPrefix.length + 12 =
          1 + (emittedPrefix.length +
            (4 + ((3 + emittedPrefix.length) + (1 + 3)))) by
        lia]
      rw [MachineDescription.runConfig_add]
      simp only [rawBoundaryLengthCursorCursorTape,
        rawBoundaryLengthCursorCellBits_false, emittedPrefix, hrev,
        Bool.false_eq_true, ↓reduceIte]
      rw [show
          (List.map some
              (List.append [false, true, false, true]
                (preservingCellPassCellBits remaining))).append
              (none ::
                List.append
                  (List.replicate (blankTail + 1) (none : Option Bool))
                  right) =
            some false :: some true :: some false :: some true ::
              List.append
                ((preservingCellPassCellBits remaining).map some)
                (none ::
                  List.append
                    (List.replicate (blankTail + 1)
                      (none : Option Bool))
                    right) by
        simp]
      rw [rawBoundaryLengthCursorLoopDescription_step_cursorCheck_false]
      rw [MachineDescription.runConfig_add]
      rw [show emittedPrefix.length = (last :: rest).length by
        have hlen := congrArg List.length hrev
        simp [List.length_reverse] at hlen
        exact hlen]
      rw [rawBoundaryLengthCursorLoopDescription_run_carryFalse_to_anchor]
      rw [MachineDescription.runConfig_add]
      rw [rawBoundaryLengthCursorLoopDescription_run_tickWriteFalse]
      rw [MachineDescription.runConfig_add]
      rw [show 3 + (last :: rest).length =
          (List.append [false, true, false]
            (last :: rest).reverse).length by
        simp
        lia]
      change
        rawBoundaryLengthCursorLoopDescription.runConfig (1 + 3)
            (rawBoundaryLengthCursorLoopDescription.runConfig
              (List.append [false, true, false]
                (last :: rest).reverse).length
              { state := rawBoundaryLengthCursorLoopReturnFalse
                tape :=
                  tapeAtCells [some false]
                    (List.append
                      ((List.append [false, true, false]
                        (last :: rest).reverse).map some)
                      (none :: some true :: some false :: some true ::
                        List.append
                          ((preservingCellPassCellBits remaining).map some)
                          (none ::
                            List.append
                              (List.replicate (blankTail + 1)
                                (none : Option Bool))
                              right))) }) =
          { state := rawBoundaryLengthCursorLoopCursorCheck
            tape :=
              rawBoundaryLengthCursorCursorTape false
                (List.append
                  (rawBoundaryLengthCursorStageNatBits (count + 1))
                  (List.append processed
                    (rawBoundaryLengthCursorCellBits false)))
                (preservingCellPassCellBits remaining) blankTail right }
      rw [rawBoundaryLengthCursorLoopDescription_run_returnFalse_scanRight]
      rw [MachineDescription.runConfig_add]
      rw [rawBoundaryLengthCursorLoopDescription_step_returnFalse_cursor]
      rw [rawBoundaryLengthCursorLoopDescription_run_advanceThree]
      have hrev_rev : (last :: rest).reverse = emittedPrefix := by
        have h := congrArg List.reverse hrev
        simpa using h.symm
      rw [hrev_rev]
      simp [rawBoundaryLengthCursorCursorTape,
        rawBoundaryLengthCursorCellBits_false,
        emittedPrefix, List.map_append, List.reverse_append,
        List.append_assoc]

private theorem rawBoundaryLengthCursorLoopDescription_run_cursorCheck_cell_true
    (storedAnchor : Bool) (count : Nat) (processed remaining : Word Bool)
    (blankTail : Nat) (right : List (Option Bool)) :
    exists steps : Nat,
      rawBoundaryLengthCursorLoopDescription.runConfig steps
          { state := rawBoundaryLengthCursorLoopCursorCheck
            tape :=
              rawBoundaryLengthCursorCursorTape storedAnchor
                (List.append (rawBoundaryLengthCursorStageNatBits count)
                  processed)
                (List.append (rawBoundaryLengthCursorCellBits true)
                  (preservingCellPassCellBits remaining))
                blankTail right } =
        { state := rawBoundaryLengthCursorLoopCursorCheck
          tape :=
            rawBoundaryLengthCursorCursorTape false
              (List.append
                (rawBoundaryLengthCursorStageNatBits (count + 1))
                (List.append processed
                  (rawBoundaryLengthCursorCellBits true)))
              (preservingCellPassCellBits remaining) blankTail right } := by
  let emittedPrefix : Word Bool :=
    List.append (rawBoundaryLengthCursorStageNatBits count) processed
  have hprefix_ne : emittedPrefix ≠ [] := by
    intro hnil
    have hlen := congrArg List.length hnil
    simp [emittedPrefix] at hlen
    exact rawBoundaryLengthCursorStageNatBits_ne_nil count hlen.left
  cases hrev : emittedPrefix.reverse with
  | nil =>
      have hprefix_nil : emittedPrefix = [] := by
        have h := congrArg List.reverse hrev
        simpa using h
      exact False.elim (hprefix_ne hprefix_nil)
  | cons last rest =>
      refine ⟨2 * emittedPrefix.length + 12, ?_⟩
      rw [show 2 * emittedPrefix.length + 12 =
          1 + (emittedPrefix.length +
            (4 + ((3 + emittedPrefix.length) + (1 + 3)))) by
        lia]
      rw [MachineDescription.runConfig_add]
      simp only [rawBoundaryLengthCursorCursorTape,
        rawBoundaryLengthCursorCellBits_true, emittedPrefix, hrev,
        Bool.false_eq_true, ↓reduceIte]
      rw [show
          (List.map some
              (List.append [false, true, true, false]
                (preservingCellPassCellBits remaining))).append
              (none ::
                List.append
                  (List.replicate (blankTail + 1) (none : Option Bool))
                  right) =
            some false :: some true :: some true :: some false ::
              List.append
                ((preservingCellPassCellBits remaining).map some)
                (none ::
                  List.append
                    (List.replicate (blankTail + 1)
                      (none : Option Bool))
                    right) by
        simp]
      rw [rawBoundaryLengthCursorLoopDescription_step_cursorCheck_false]
      rw [MachineDescription.runConfig_add]
      rw [show emittedPrefix.length = (last :: rest).length by
        have hlen := congrArg List.length hrev
        simp [List.length_reverse] at hlen
        exact hlen]
      rw [rawBoundaryLengthCursorLoopDescription_run_carryFalse_to_anchor]
      rw [MachineDescription.runConfig_add]
      rw [rawBoundaryLengthCursorLoopDescription_run_tickWriteFalse]
      rw [MachineDescription.runConfig_add]
      rw [show 3 + (last :: rest).length =
          (List.append [false, true, false]
            (last :: rest).reverse).length by
        simp
        lia]
      change
        rawBoundaryLengthCursorLoopDescription.runConfig (1 + 3)
            (rawBoundaryLengthCursorLoopDescription.runConfig
              (List.append [false, true, false]
                (last :: rest).reverse).length
              { state := rawBoundaryLengthCursorLoopReturnFalse
                tape :=
                  tapeAtCells [some false]
                    (List.append
                      ((List.append [false, true, false]
                        (last :: rest).reverse).map some)
                      (none :: some true :: some true :: some false ::
                        List.append
                          ((preservingCellPassCellBits remaining).map some)
                          (none ::
                            List.append
                              (List.replicate (blankTail + 1)
                                (none : Option Bool))
                              right))) }) =
          { state := rawBoundaryLengthCursorLoopCursorCheck
            tape :=
              rawBoundaryLengthCursorCursorTape false
                (List.append
                  (rawBoundaryLengthCursorStageNatBits (count + 1))
                  (List.append processed
                    (rawBoundaryLengthCursorCellBits true)))
                (preservingCellPassCellBits remaining) blankTail right }
      rw [rawBoundaryLengthCursorLoopDescription_run_returnFalse_scanRight]
      rw [MachineDescription.runConfig_add]
      rw [rawBoundaryLengthCursorLoopDescription_step_returnFalse_cursor]
      rw [rawBoundaryLengthCursorLoopDescription_run_advanceThree]
      have hrev_rev : (last :: rest).reverse = emittedPrefix := by
        have h := congrArg List.reverse hrev
        simpa using h.symm
      rw [hrev_rev]
      simp [rawBoundaryLengthCursorCursorTape,
        rawBoundaryLengthCursorCellBits_true,
        emittedPrefix, List.map_append, List.reverse_append,
        List.append_assoc]

private theorem rawBoundaryLengthCursorLoopDescription_run_cursorCheck_noAnchor
    (layout : Word Bool) (count : Nat) (processed : Word Bool)
    (blankTail : Nat) (right : List (Option Bool)) :
    exists steps : Nat,
      rawBoundaryLengthCursorLoopDescription.runConfig steps
          { state := rawBoundaryLengthCursorLoopCursorCheck
            tape :=
              rawBoundaryLengthCursorCursorTape false
                (List.append (rawBoundaryLengthCursorStageNatBits count)
                  processed)
                (preservingCellPassCellBits layout) blankTail right } =
        { state := rawBoundaryLengthCursorLoopHalt
          tape :=
            rawBoundaryLengthCursorCursorTape false
              (List.append
                (rawBoundaryLengthCursorStageNatBits
                  (count + layout.length))
                (List.append processed
                  (preservingCellPassCellBits layout)))
              [] blankTail right } := by
  induction layout generalizing count processed with
  | nil =>
      let emittedPrefix : Word Bool :=
        List.append (rawBoundaryLengthCursorStageNatBits count) processed
      have hprefix_ne : emittedPrefix ≠ [] := by
        intro hnil
        have hlen := congrArg List.length hnil
        simp [emittedPrefix] at hlen
        exact rawBoundaryLengthCursorStageNatBits_ne_nil count hlen.left
      cases hrev : emittedPrefix.reverse with
      | nil =>
          have hprefix_nil : emittedPrefix = [] := by
            have h := congrArg List.reverse hrev
            simpa using h
          exact False.elim (hprefix_ne hprefix_nil)
      | cons last rest =>
          refine ⟨2, ?_⟩
          simp only [rawBoundaryLengthCursorCursorTape,
            preservingCellPassCellBits, emittedPrefix, hrev,
            Bool.false_eq_true, ↓reduceIte, List.map_nil]
          change
            rawBoundaryLengthCursorLoopDescription.runConfig 2
                { state := rawBoundaryLengthCursorLoopCursorCheck
                  tape :=
                    tapeAtCells
                      (List.append ((last :: rest).map some) [])
                      (none ::
                        List.append
                          (List.replicate (blankTail + 1)
                            (none : Option Bool))
                          right) } =
              { state := rawBoundaryLengthCursorLoopHalt
                tape :=
                  tapeAtCells
                    (List.append
                      ((List.append
                        (rawBoundaryLengthCursorStageNatBits
                          (count + [].length))
                        (List.append processed [])).reverse.map some)
                      [])
                    (none ::
                      List.append
                        (List.replicate (blankTail + 1)
                          (none : Option Bool))
                        right) }
          rw [show
              rawBoundaryLengthCursorLoopDescription.runConfig 2
                  { state := rawBoundaryLengthCursorLoopCursorCheck
                    tape :=
                      tapeAtCells
                        (List.append ((last :: rest).map some) [])
                        (none ::
                          List.append
                            (List.replicate (blankTail + 1)
                              (none : Option Bool))
                            right) } =
                { state := rawBoundaryLengthCursorLoopHalt
                  tape :=
                    tapeAtCells
                      (List.append ((last :: rest).map some) [])
                      (none ::
                        List.append
                          (List.replicate (blankTail + 1)
                            (none : Option Bool))
                          right) } by
            simpa using
              rawBoundaryLengthCursorLoopDescription_run_cursorCheck_halt
                false last rest
                (List.append
                  (List.replicate (blankTail + 1)
                    (none : Option Bool))
                  right)]
          rw [← hrev]
          simp [emittedPrefix, List.map_append, List.reverse_append]
  | cons bit rest ih =>
      cases bit
      · rcases
          rawBoundaryLengthCursorLoopDescription_run_cursorCheck_cell_false
            false count processed rest blankTail right with
        ⟨cellSteps, hcell⟩
        rcases
          ih (count + 1)
            (List.append processed
              (rawBoundaryLengthCursorCellBits false)) with
        ⟨recSteps, hrec⟩
        refine ⟨cellSteps + recSteps, ?_⟩
        rw [MachineDescription.runConfig_add]
        rw [show
            preservingCellPassCellBits (false :: rest) =
              List.append (rawBoundaryLengthCursorCellBits false)
                (preservingCellPassCellBits rest) by
          simp [preservingCellPassCellBits,
            rawBoundaryLengthCursorCellBits_false,
            preservingCellPassZeroBits]]
        rw [hcell]
        rw [hrec]
        simp [rawBoundaryLengthCursorCellBits_false,
          Nat.add_comm, Nat.add_left_comm, List.append_assoc]
      · rcases
          rawBoundaryLengthCursorLoopDescription_run_cursorCheck_cell_true
            false count processed rest blankTail right with
        ⟨cellSteps, hcell⟩
        rcases
          ih (count + 1)
            (List.append processed
              (rawBoundaryLengthCursorCellBits true)) with
        ⟨recSteps, hrec⟩
        refine ⟨cellSteps + recSteps, ?_⟩
        rw [MachineDescription.runConfig_add]
        rw [show
            preservingCellPassCellBits (true :: rest) =
              List.append (rawBoundaryLengthCursorCellBits true)
                (preservingCellPassCellBits rest) by
          simp [preservingCellPassCellBits,
            rawBoundaryLengthCursorCellBits_true,
            preservingCellPassOneBits]]
        rw [hcell]
        rw [hrec]
        simp [rawBoundaryLengthCursorCellBits_true,
          Nat.add_comm, Nat.add_left_comm, List.append_assoc]

theorem rawBoundaryLengthCursorOutputBits_eq_length_cells
    (layout : Word Bool) :
    rawBoundaryLengthCursorOutputBits layout =
      List.append
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          layout.length)
        (preservingCellPassCellBits layout) := by
  rfl

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC

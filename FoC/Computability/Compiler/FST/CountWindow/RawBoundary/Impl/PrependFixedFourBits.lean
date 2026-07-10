import FoC.Computability.Compiler.Core.TransitionTableChecks
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.TapeLemmas
import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Quoter.CellPass

set_option doc.verso true

/-!
# Raw-boundary right-edge fixed chunk prepender

This module contains the one-tape primitive used by the raw-boundary
right-edge emitter to prepend one fixed four-bit code chunk immediately to the
left of a live nonblank tail head, while restoring that live head exactly.
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

theorem preservingCellPassCellBits_reverse_cons_chunk
    (bit : Bool) (rest : Word Bool) :
    (preservingCellPassCellBits (bit :: rest)).reverse =
      List.append (preservingCellPassCellBits rest).reverse
        ((if bit then preservingCellPassOneBits
          else preservingCellPassZeroBits).reverse) := by
  cases bit <;>
    simp [preservingCellPassCellBits, preservingCellPassZeroBits,
      preservingCellPassOneBits]

theorem preservingCellPassCellBits_reverse_append
    (pref suffix : Word Bool) :
    (preservingCellPassCellBits (List.append pref suffix)).reverse =
      List.append (preservingCellPassCellBits suffix).reverse
        (preservingCellPassCellBits pref).reverse := by
  induction pref with
  | nil =>
      simp [preservingCellPassCellBits]
  | cons bit rest ih =>
      cases bit
      · simp [preservingCellPassCellBits, preservingCellPassZeroBits]
        simpa [List.append_assoc] using
          congrArg
            (fun xs => List.append xs [true, false, true, false])
            ih
      · simp [preservingCellPassCellBits, preservingCellPassOneBits]
        simpa [List.append_assoc] using
          congrArg
            (fun xs => List.append xs [false, true, true, false])
            ih

theorem stageNatBits_reverse_zero :
    (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
      0).reverse =
      (encodeCodeSymbolAsInput MachineCodeSymbol.done).reverse := by
  simp [
    DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_zero,
    encodeCodeSymbolAsInput]

theorem stageNatBits_reverse_succ_append_tick (n : Nat) :
    (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
      (n + 1)).reverse =
      List.append
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          n).reverse
        (encodeCodeSymbolAsInput MachineCodeSymbol.tick).reverse := by
  simp [
    DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_succ,
    encodeCodeSymbolAsInput]

def prependFixedFourBitsLeftOfHeadDescription
    (b0 b1 b2 b3 : Bool) : MachineDescription where
  stateCount := 30
  start := 0
  halt := 29
  transitions :=
    [ transition 0 (some false) none Direction.left 10
    , transition 0 (some true) none Direction.left 20
    , transition 10 (some false) (some false) Direction.left 10
    , transition 10 (some true) (some true) Direction.left 10
    , transition 10 none (some b3) Direction.left 11
    , transition 11 none (some b2) Direction.left 12
    , transition 12 none (some b1) Direction.left 13
    , transition 13 none (some b0) Direction.right 14
    , transition 14 (some false) (some false) Direction.right 14
    , transition 14 (some true) (some true) Direction.right 14
    , transition 14 none (some false) Direction.left 15
    , transition 15 (some false) (some false) Direction.right 29
    , transition 15 (some true) (some true) Direction.right 29
    , transition 20 (some false) (some false) Direction.left 20
    , transition 20 (some true) (some true) Direction.left 20
    , transition 20 none (some b3) Direction.left 21
    , transition 21 none (some b2) Direction.left 22
    , transition 22 none (some b1) Direction.left 23
    , transition 23 none (some b0) Direction.right 24
    , transition 24 (some false) (some false) Direction.right 24
    , transition 24 (some true) (some true) Direction.right 24
    , transition 24 none (some true) Direction.left 25
    , transition 25 (some false) (some false) Direction.right 29
    , transition 25 (some true) (some true) Direction.right 29 ]

theorem prependFixedFourBitsLeftOfHeadDescription_wellFormed
    (b0 b1 b2 b3 : Bool) :
    (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).WellFormed := by
  refine
    ⟨by simp [prependFixedFourBitsLeftOfHeadDescription],
      by simp [prependFixedFourBitsLeftOfHeadDescription],
      by simp [prependFixedFourBitsLeftOfHeadDescription], ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := (prependFixedFourBitsLeftOfHeadDescription
        b0 b1 b2 b3).transitions)
      (stateCount := (prependFixedFourBitsLeftOfHeadDescription
        b0 b1 b2 b3).stateCount)
      (by cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide)
  · exact transition_deterministic_of_all
      (l := (prependFixedFourBitsLeftOfHeadDescription
        b0 b1 b2 b3).transitions)
      (by cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide)

theorem prependFixedFourBitsLeftOfHeadDescription_haltTransitionFree
    (b0 b1 b2 b3 : Bool) :
    (prependFixedFourBitsLeftOfHeadDescription
      b0 b1 b2 b3).HaltTransitionFree := by
  exact transition_notFrom_of_all
    (l := (prependFixedFourBitsLeftOfHeadDescription
      b0 b1 b2 b3).transitions)
    (state := (prependFixedFourBitsLeftOfHeadDescription
      b0 b1 b2 b3).halt)
    (by cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide)

theorem prependFixedFourBitsLeftOfHeadDescription_subroutineReady
    (b0 b1 b2 b3 : Bool) :
    (prependFixedFourBitsLeftOfHeadDescription
      b0 b1 b2 b3).SubroutineReady :=
  ⟨prependFixedFourBitsLeftOfHeadDescription_wellFormed b0 b1 b2 b3,
    prependFixedFourBitsLeftOfHeadDescription_haltTransitionFree
      b0 b1 b2 b3⟩

def prependFixedFourBitsLeftScanTape
    (remainingRev : Word Bool) (right : List (Option Bool)) :
    Tape Bool :=
  match remainingRev with
  | [] => tapeAtCells [] (none :: right)
  | bit :: rest => tapeAtCells (rest.map some) (some bit :: right)

def prependFixedFourBitsLeftScanTapeWithScratch
    (remainingRev : Word Bool) (scratchBase right : List (Option Bool)) :
    Tape Bool :=
  match remainingRev with
  | [] => tapeAtCells scratchBase (none :: right)
  | bit :: rest =>
      tapeAtCells (List.append (rest.map some) (none :: scratchBase))
        (some bit :: right)

private theorem prependFixedFourBitsLeftOfHeadDescription_step_start_false
    (b0 b1 b2 b3 : Bool) (emitted : Word Bool)
    (tail : List (Option Bool)) :
    (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).runConfig 1
        { state := (prependFixedFourBitsLeftOfHeadDescription
            b0 b1 b2 b3).start
          tape := tapeAtCells (emitted.reverse.map some)
            (some false :: tail) } =
      { state := 10
        tape := prependFixedFourBitsLeftScanTape emitted.reverse
          (none :: tail) } := by
  cases hrev : emitted.reverse with
  | nil =>
      simp [prependFixedFourBitsLeftOfHeadDescription,
        prependFixedFourBitsLeftScanTape, runConfig, stepConfig,
        lookupTransition, Matches, transition, Tape.read, Tape.write,
        Tape.move, Tape.moveLeft, tapeAtCells]
  | cons bit rest =>
      cases bit <;>
        simp [prependFixedFourBitsLeftOfHeadDescription,
          prependFixedFourBitsLeftScanTape, runConfig, stepConfig,
          lookupTransition, Matches, transition, Tape.read, Tape.write,
          Tape.move, Tape.moveLeft, tapeAtCells]

private theorem prependFixedFourBitsLeftOfHeadDescription_step_start_true
    (b0 b1 b2 b3 : Bool) (emitted : Word Bool)
    (tail : List (Option Bool)) :
    (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).runConfig 1
        { state := (prependFixedFourBitsLeftOfHeadDescription
            b0 b1 b2 b3).start
          tape := tapeAtCells (emitted.reverse.map some)
            (some true :: tail) } =
      { state := 20
        tape := prependFixedFourBitsLeftScanTape emitted.reverse
          (none :: tail) } := by
  cases hrev : emitted.reverse with
  | nil =>
      simp [prependFixedFourBitsLeftOfHeadDescription,
        prependFixedFourBitsLeftScanTape, runConfig, stepConfig,
        lookupTransition, Matches, transition, Tape.read, Tape.write,
        Tape.move, Tape.moveLeft, tapeAtCells]
  | cons bit rest =>
      cases bit <;>
        simp [prependFixedFourBitsLeftOfHeadDescription,
          prependFixedFourBitsLeftScanTape, runConfig, stepConfig,
          lookupTransition, Matches, transition, Tape.read, Tape.write,
          Tape.move, Tape.moveLeft, tapeAtCells]

private theorem prependFixedFourBitsLeftOfHeadDescription_step_start_false_withScratch
    (b0 b1 b2 b3 : Bool) (emitted : Word Bool)
    (scratchBase tail : List (Option Bool)) :
    (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).runConfig 1
        { state := (prependFixedFourBitsLeftOfHeadDescription
            b0 b1 b2 b3).start
          tape :=
            tapeAtCells
              (List.append (emitted.reverse.map some)
                (none :: scratchBase))
              (some false :: tail) } =
      { state := 10
        tape :=
          prependFixedFourBitsLeftScanTapeWithScratch
            emitted.reverse scratchBase (none :: tail) } := by
  cases hrev : emitted.reverse with
  | nil =>
      simp [prependFixedFourBitsLeftOfHeadDescription,
        prependFixedFourBitsLeftScanTapeWithScratch, runConfig,
        stepConfig, lookupTransition, Matches, transition, Tape.read,
        Tape.write, Tape.move, Tape.moveLeft, tapeAtCells]
  | cons bit rest =>
      cases bit <;>
        simp [prependFixedFourBitsLeftOfHeadDescription,
          prependFixedFourBitsLeftScanTapeWithScratch, runConfig,
          stepConfig, lookupTransition, Matches, transition, Tape.read,
          Tape.write, Tape.move, Tape.moveLeft, tapeAtCells]

private theorem prependFixedFourBitsLeftOfHeadDescription_step_start_true_withScratch
    (b0 b1 b2 b3 : Bool) (emitted : Word Bool)
    (scratchBase tail : List (Option Bool)) :
    (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).runConfig 1
        { state := (prependFixedFourBitsLeftOfHeadDescription
            b0 b1 b2 b3).start
          tape :=
            tapeAtCells
              (List.append (emitted.reverse.map some)
                (none :: scratchBase))
              (some true :: tail) } =
      { state := 20
        tape :=
          prependFixedFourBitsLeftScanTapeWithScratch
            emitted.reverse scratchBase (none :: tail) } := by
  cases hrev : emitted.reverse with
  | nil =>
      simp [prependFixedFourBitsLeftOfHeadDescription,
        prependFixedFourBitsLeftScanTapeWithScratch, runConfig,
        stepConfig, lookupTransition, Matches, transition, Tape.read,
        Tape.write, Tape.move, Tape.moveLeft, tapeAtCells]
  | cons bit rest =>
      cases bit <;>
        simp [prependFixedFourBitsLeftOfHeadDescription,
          prependFixedFourBitsLeftScanTapeWithScratch, runConfig,
          stepConfig, lookupTransition, Matches, transition, Tape.read,
          Tape.write, Tape.move, Tape.moveLeft, tapeAtCells]

private theorem prependFixedFourBitsLeftOfHeadDescription_step_scanLeft_false
    (b0 b1 b2 b3 : Bool) (bit : Bool) (rest : Word Bool)
    (right : List (Option Bool)) :
    (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).runConfig 1
        { state := 10
          tape := prependFixedFourBitsLeftScanTape (bit :: rest) right } =
      { state := 10
        tape := prependFixedFourBitsLeftScanTape rest
          (some bit :: right) } := by
  cases bit <;> cases rest <;>
    simp [prependFixedFourBitsLeftOfHeadDescription,
      prependFixedFourBitsLeftScanTape, runConfig, stepConfig,
      lookupTransition, Matches, transition, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft, tapeAtCells]

private theorem prependFixedFourBitsLeftOfHeadDescription_step_scanLeft_true
    (b0 b1 b2 b3 : Bool) (bit : Bool) (rest : Word Bool)
    (right : List (Option Bool)) :
    (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).runConfig 1
        { state := 20
          tape := prependFixedFourBitsLeftScanTape (bit :: rest) right } =
      { state := 20
        tape := prependFixedFourBitsLeftScanTape rest
          (some bit :: right) } := by
  cases bit <;> cases rest <;>
    simp [prependFixedFourBitsLeftOfHeadDescription,
      prependFixedFourBitsLeftScanTape, runConfig, stepConfig,
      lookupTransition, Matches, transition, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft, tapeAtCells]

private theorem prependFixedFourBitsLeftOfHeadDescription_run_scanLeft_false
    (b0 b1 b2 b3 : Bool) (remainingRev : Word Bool)
    (right : List (Option Bool)) :
    (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).runConfig
        remainingRev.length
        { state := 10
          tape := prependFixedFourBitsLeftScanTape remainingRev right } =
      { state := 10
        tape := tapeAtCells []
          (none :: List.append (remainingRev.reverse.map some) right) } := by
  induction remainingRev generalizing right with
  | nil =>
      simp [prependFixedFourBitsLeftScanTape, runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        lia]
      rw [runConfig_add]
      rw [prependFixedFourBitsLeftOfHeadDescription_step_scanLeft_false]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: right)

private theorem prependFixedFourBitsLeftOfHeadDescription_run_scanLeft_true
    (b0 b1 b2 b3 : Bool) (remainingRev : Word Bool)
    (right : List (Option Bool)) :
    (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).runConfig
        remainingRev.length
        { state := 20
          tape := prependFixedFourBitsLeftScanTape remainingRev right } =
      { state := 20
        tape := tapeAtCells []
          (none :: List.append (remainingRev.reverse.map some) right) } := by
  induction remainingRev generalizing right with
  | nil =>
      simp [prependFixedFourBitsLeftScanTape, runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        lia]
      rw [runConfig_add]
      rw [prependFixedFourBitsLeftOfHeadDescription_step_scanLeft_true]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: right)

private theorem prependFixedFourBitsLeftOfHeadDescription_step_scanLeft_false_withScratch
    (b0 b1 b2 b3 : Bool) (bit : Bool) (rest : Word Bool)
    (scratchBase right : List (Option Bool)) :
    (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).runConfig 1
        { state := 10
          tape :=
            prependFixedFourBitsLeftScanTapeWithScratch
              (bit :: rest) scratchBase right } =
      { state := 10
        tape :=
          prependFixedFourBitsLeftScanTapeWithScratch
            rest scratchBase (some bit :: right) } := by
  cases bit <;> cases rest <;>
    simp [prependFixedFourBitsLeftOfHeadDescription,
      prependFixedFourBitsLeftScanTapeWithScratch, runConfig,
      stepConfig, lookupTransition, Matches, transition, Tape.read,
      Tape.write, Tape.move, Tape.moveLeft, tapeAtCells]

private theorem prependFixedFourBitsLeftOfHeadDescription_step_scanLeft_true_withScratch
    (b0 b1 b2 b3 : Bool) (bit : Bool) (rest : Word Bool)
    (scratchBase right : List (Option Bool)) :
    (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).runConfig 1
        { state := 20
          tape :=
            prependFixedFourBitsLeftScanTapeWithScratch
              (bit :: rest) scratchBase right } =
      { state := 20
        tape :=
          prependFixedFourBitsLeftScanTapeWithScratch
            rest scratchBase (some bit :: right) } := by
  cases bit <;> cases rest <;>
    simp [prependFixedFourBitsLeftOfHeadDescription,
      prependFixedFourBitsLeftScanTapeWithScratch, runConfig,
      stepConfig, lookupTransition, Matches, transition, Tape.read,
      Tape.write, Tape.move, Tape.moveLeft, tapeAtCells]

private theorem prependFixedFourBitsLeftOfHeadDescription_run_scanLeft_false_withScratch
    (b0 b1 b2 b3 : Bool) (remainingRev : Word Bool)
    (scratchBase right : List (Option Bool)) :
    (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).runConfig
        remainingRev.length
        { state := 10
          tape :=
            prependFixedFourBitsLeftScanTapeWithScratch
              remainingRev scratchBase right } =
      { state := 10
        tape :=
          tapeAtCells scratchBase
            (none :: List.append (remainingRev.reverse.map some)
              right) } := by
  induction remainingRev generalizing right with
  | nil =>
      simp [prependFixedFourBitsLeftScanTapeWithScratch, runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        lia]
      rw [runConfig_add]
      rw [prependFixedFourBitsLeftOfHeadDescription_step_scanLeft_false_withScratch]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: right)

private theorem prependFixedFourBitsLeftOfHeadDescription_run_scanLeft_true_withScratch
    (b0 b1 b2 b3 : Bool) (remainingRev : Word Bool)
    (scratchBase right : List (Option Bool)) :
    (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).runConfig
        remainingRev.length
        { state := 20
          tape :=
            prependFixedFourBitsLeftScanTapeWithScratch
              remainingRev scratchBase right } =
      { state := 20
        tape :=
          tapeAtCells scratchBase
            (none :: List.append (remainingRev.reverse.map some)
              right) } := by
  induction remainingRev generalizing right with
  | nil =>
      simp [prependFixedFourBitsLeftScanTapeWithScratch, runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        lia]
      rw [runConfig_add]
      rw [prependFixedFourBitsLeftOfHeadDescription_step_scanLeft_true_withScratch]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: right)

private theorem prependFixedFourBitsLeftOfHeadDescription_run_write_false
    (b0 b1 b2 b3 : Bool) (right : List (Option Bool)) :
    (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).runConfig 4
        { state := 10
          tape := tapeAtCells [] (none :: right) } =
      { state := 14
        tape := tapeAtCells [some b0]
          (some b1 :: some b2 :: some b3 :: right) } := by
  simp [prependFixedFourBitsLeftOfHeadDescription, runConfig,
    stepConfig, lookupTransition, Matches, transition, Tape.read,
    Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, tapeAtCells]

private theorem prependFixedFourBitsLeftOfHeadDescription_run_write_true
    (b0 b1 b2 b3 : Bool) (right : List (Option Bool)) :
    (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).runConfig 4
        { state := 20
          tape := tapeAtCells [] (none :: right) } =
      { state := 24
        tape := tapeAtCells [some b0]
          (some b1 :: some b2 :: some b3 :: right) } := by
  simp [prependFixedFourBitsLeftOfHeadDescription, runConfig,
    stepConfig, lookupTransition, Matches, transition, Tape.read,
    Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, tapeAtCells]

private theorem prependFixedFourBitsLeftOfHeadDescription_run_write_false_withScratch
    (b0 b1 b2 b3 : Bool) (baseLeft right : List (Option Bool)) :
    (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).runConfig 4
        { state := 10
          tape :=
            tapeAtCells
              (List.append
                (List.replicate 3 (none : Option Bool))
                baseLeft)
              (none :: right) } =
      { state := 14
        tape := tapeAtCells (some b0 :: baseLeft)
          (some b1 :: some b2 :: some b3 :: right) } := by
  cases baseLeft <;>
    simp [prependFixedFourBitsLeftOfHeadDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, Tape.read,
      Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, tapeAtCells]

private theorem prependFixedFourBitsLeftOfHeadDescription_run_write_true_withScratch
    (b0 b1 b2 b3 : Bool) (baseLeft right : List (Option Bool)) :
    (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).runConfig 4
        { state := 20
          tape :=
            tapeAtCells
              (List.append
                (List.replicate 3 (none : Option Bool))
                baseLeft)
              (none :: right) } =
      { state := 24
        tape := tapeAtCells (some b0 :: baseLeft)
          (some b1 :: some b2 :: some b3 :: right) } := by
  cases baseLeft <;>
    simp [prependFixedFourBitsLeftOfHeadDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, Tape.read,
      Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, tapeAtCells]

private theorem prependFixedFourBitsLeftOfHeadDescription_step_scanRight_false
    (b0 b1 b2 b3 : Bool) (bit : Bool)
    (left right : List (Option Bool)) :
    (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).runConfig 1
        { state := 14
          tape := tapeAtCells left (some bit :: right) } =
      { state := 14
        tape := tapeAtCells (some bit :: left) right } := by
  cases bit <;> cases right <;>
    simp [prependFixedFourBitsLeftOfHeadDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, Tape.read,
      Tape.write, Tape.move, Tape.moveRight, tapeAtCells]

private theorem prependFixedFourBitsLeftOfHeadDescription_step_scanRight_true
    (b0 b1 b2 b3 : Bool) (bit : Bool)
    (left right : List (Option Bool)) :
    (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).runConfig 1
        { state := 24
          tape := tapeAtCells left (some bit :: right) } =
      { state := 24
        tape := tapeAtCells (some bit :: left) right } := by
  cases bit <;> cases right <;>
    simp [prependFixedFourBitsLeftOfHeadDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, Tape.read,
      Tape.write, Tape.move, Tape.moveRight, tapeAtCells]

private theorem prependFixedFourBitsLeftOfHeadDescription_run_scanRight_false
    (b0 b1 b2 b3 : Bool) (bits : Word Bool)
    (left right : List (Option Bool)) :
    (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).runConfig
        bits.length
        { state := 14
          tape := tapeAtCells left
            (List.append (bits.map some) right) } =
      { state := 14
        tape := tapeAtCells
          (List.append (bits.reverse.map some) left) right } := by
  induction bits generalizing left with
  | nil =>
      simp [runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        lia]
      rw [runConfig_add]
      change
        (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).runConfig
            rest.length
            ((prependFixedFourBitsLeftOfHeadDescription
                b0 b1 b2 b3).runConfig 1
              { state := 14
                tape := tapeAtCells left
                  (some bit :: List.append (rest.map some) right) }) =
          { state := 14
            tape := tapeAtCells
              (List.append ((bit :: rest).reverse.map some) left) right }
      rw [prependFixedFourBitsLeftOfHeadDescription_step_scanRight_false]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: left)

private theorem prependFixedFourBitsLeftOfHeadDescription_run_scanRight_true
    (b0 b1 b2 b3 : Bool) (bits : Word Bool)
    (left right : List (Option Bool)) :
    (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).runConfig
        bits.length
        { state := 24
          tape := tapeAtCells left
            (List.append (bits.map some) right) } =
      { state := 24
        tape := tapeAtCells
          (List.append (bits.reverse.map some) left) right } := by
  induction bits generalizing left with
  | nil =>
      simp [runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        lia]
      rw [runConfig_add]
      change
        (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).runConfig
            rest.length
            ((prependFixedFourBitsLeftOfHeadDescription
                b0 b1 b2 b3).runConfig 1
              { state := 24
                tape := tapeAtCells left
                  (some bit :: List.append (rest.map some) right) }) =
          { state := 24
            tape := tapeAtCells
              (List.append ((bit :: rest).reverse.map some) left) right }
      rw [prependFixedFourBitsLeftOfHeadDescription_step_scanRight_true]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: left)

private theorem prependFixedFourBitsLeftOfHeadDescription_run_restore_false
    (b0 b1 b2 b3 : Bool) (leftRevTail tail : List (Option Bool))
    (cell : Bool) :
    (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).runConfig 2
        { state := 14
          tape := tapeAtCells (some cell :: leftRevTail) (none :: tail) } =
      { state := (prependFixedFourBitsLeftOfHeadDescription
          b0 b1 b2 b3).halt
        tape := tapeAtCells (some cell :: leftRevTail)
          (some false :: tail) } := by
  cases cell <;>
    simp [prependFixedFourBitsLeftOfHeadDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, Tape.read,
      Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, tapeAtCells]

private theorem prependFixedFourBitsLeftOfHeadDescription_run_restore_true
    (b0 b1 b2 b3 : Bool) (leftRevTail tail : List (Option Bool))
    (cell : Bool) :
    (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).runConfig 2
        { state := 24
          tape := tapeAtCells (some cell :: leftRevTail) (none :: tail) } =
      { state := (prependFixedFourBitsLeftOfHeadDescription
          b0 b1 b2 b3).halt
        tape := tapeAtCells (some cell :: leftRevTail)
          (some true :: tail) } := by
  cases cell <;>
    simp [prependFixedFourBitsLeftOfHeadDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, Tape.read,
      Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, tapeAtCells]

private theorem prependFixedFourBitsLeftOfHeadDescription_run_restore_false_bits
    (b0 b1 b2 b3 : Bool) (bits : Word Bool)
    (tail : List (Option Bool)) :
    (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).runConfig 2
        { state := 14
          tape := tapeAtCells
            (List.append (bits.map some)
              [some b3, some b2, some b1, some b0])
            (none :: tail) } =
      { state := (prependFixedFourBitsLeftOfHeadDescription
          b0 b1 b2 b3).halt
        tape := tapeAtCells
          (List.append (bits.map some)
            [some b3, some b2, some b1, some b0])
          (some false :: tail) } := by
  cases bits with
  | nil =>
      simpa [List.append_assoc] using
        prependFixedFourBitsLeftOfHeadDescription_run_restore_false
          b0 b1 b2 b3 [some b2, some b1, some b0] tail b3
  | cons bit rest =>
      simpa [List.append_assoc] using
        prependFixedFourBitsLeftOfHeadDescription_run_restore_false
          b0 b1 b2 b3
          (List.append (rest.map some)
            [some b3, some b2, some b1, some b0])
          tail bit

private theorem prependFixedFourBitsLeftOfHeadDescription_run_restore_true_bits
    (b0 b1 b2 b3 : Bool) (bits : Word Bool)
    (tail : List (Option Bool)) :
    (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).runConfig 2
        { state := 24
          tape := tapeAtCells
            (List.append (bits.map some)
              [some b3, some b2, some b1, some b0])
            (none :: tail) } =
      { state := (prependFixedFourBitsLeftOfHeadDescription
          b0 b1 b2 b3).halt
        tape := tapeAtCells
          (List.append (bits.map some)
            [some b3, some b2, some b1, some b0])
          (some true :: tail) } := by
  cases bits with
  | nil =>
      simpa [List.append_assoc] using
        prependFixedFourBitsLeftOfHeadDescription_run_restore_true
          b0 b1 b2 b3 [some b2, some b1, some b0] tail b3
  | cons bit rest =>
      simpa [List.append_assoc] using
        prependFixedFourBitsLeftOfHeadDescription_run_restore_true
          b0 b1 b2 b3
          (List.append (rest.map some)
            [some b3, some b2, some b1, some b0])
          tail bit

private theorem prependFixedFourBitsLeftOfHeadDescription_run_restore_false_bits_withBase
    (b0 b1 b2 b3 : Bool) (bits : Word Bool)
    (baseLeft tail : List (Option Bool)) :
    (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).runConfig 2
        { state := 14
          tape :=
            tapeAtCells
              (List.append
                (List.append (bits.map some)
                  [some b3, some b2, some b1, some b0])
                baseLeft)
              (none :: tail) } =
      { state := (prependFixedFourBitsLeftOfHeadDescription
          b0 b1 b2 b3).halt
        tape :=
          tapeAtCells
            (List.append
              (List.append (bits.map some)
                [some b3, some b2, some b1, some b0])
              baseLeft)
            (some false :: tail) } := by
  cases bits with
  | nil =>
      simpa [List.append_assoc] using
        prependFixedFourBitsLeftOfHeadDescription_run_restore_false
          b0 b1 b2 b3
          (List.append [some b2, some b1, some b0] baseLeft)
          tail b3
  | cons bit rest =>
      simpa [List.append_assoc] using
        prependFixedFourBitsLeftOfHeadDescription_run_restore_false
          b0 b1 b2 b3
          (List.append
            (List.append (rest.map some)
              [some b3, some b2, some b1, some b0])
            baseLeft)
          tail bit

private theorem prependFixedFourBitsLeftOfHeadDescription_run_restore_true_bits_withBase
    (b0 b1 b2 b3 : Bool) (bits : Word Bool)
    (baseLeft tail : List (Option Bool)) :
    (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).runConfig 2
        { state := 24
          tape :=
            tapeAtCells
              (List.append
                (List.append (bits.map some)
                  [some b3, some b2, some b1, some b0])
                baseLeft)
              (none :: tail) } =
      { state := (prependFixedFourBitsLeftOfHeadDescription
          b0 b1 b2 b3).halt
        tape :=
          tapeAtCells
            (List.append
              (List.append (bits.map some)
                [some b3, some b2, some b1, some b0])
              baseLeft)
            (some true :: tail) } := by
  cases bits with
  | nil =>
      simpa [List.append_assoc] using
        prependFixedFourBitsLeftOfHeadDescription_run_restore_true
          b0 b1 b2 b3
          (List.append [some b2, some b1, some b0] baseLeft)
          tail b3
  | cons bit rest =>
      simpa [List.append_assoc] using
        prependFixedFourBitsLeftOfHeadDescription_run_restore_true
          b0 b1 b2 b3
          (List.append
            (List.append (rest.map some)
              [some b3, some b2, some b1, some b0])
            baseLeft)
          tail bit

theorem prependFixedFourBitsLeftOfHeadDescription_run_false
    (b0 b1 b2 b3 : Bool) (emitted : Word Bool)
    (tail : List (Option Bool)) :
    (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).runConfig
        (2 * emitted.length + 10)
        { state := (prependFixedFourBitsLeftOfHeadDescription
            b0 b1 b2 b3).start
          tape := tapeAtCells (emitted.reverse.map some)
            (some false :: tail) } =
      { state := (prependFixedFourBitsLeftOfHeadDescription
          b0 b1 b2 b3).halt
        tape := tapeAtCells
          (List.append (emitted.reverse.map some)
            [some b3, some b2, some b1, some b0])
          (some false :: tail) } := by
  rw [show 2 * emitted.length + 10 =
      1 + (emitted.reverse.length + (4 +
        ((List.append [b1, b2, b3] emitted).length + 2))) by
    simp [List.length_reverse]
    lia]
  rw [runConfig_add]
  rw [prependFixedFourBitsLeftOfHeadDescription_step_start_false]
  rw [runConfig_add]
  rw [prependFixedFourBitsLeftOfHeadDescription_run_scanLeft_false]
  simp [List.reverse_reverse]
  rw [runConfig_add]
  rw [prependFixedFourBitsLeftOfHeadDescription_run_write_false]
  rw [runConfig_add]
  rw [show emitted.length + 1 + 1 + 1 =
      (List.append [b1, b2, b3] emitted).length by
    simp]
  rw [show some b1 :: some b2 :: some b3 ::
        (List.map some emitted ++ none :: tail) =
      List.append ((List.append [b1, b2, b3] emitted).map some)
        (none :: tail) by
    simp]
  rw [prependFixedFourBitsLeftOfHeadDescription_run_scanRight_false]
  rw [show
      List.append
          (List.map some (List.append [b1, b2, b3] emitted).reverse)
          [some b0] =
        List.append (emitted.reverse.map some)
          [some b3, some b2, some b1, some b0] by
    simp [List.map_reverse, List.append_assoc]]
  rw [prependFixedFourBitsLeftOfHeadDescription_run_restore_false_bits]
  simp [List.map_reverse]

theorem prependFixedFourBitsLeftOfHeadDescription_run_true
    (b0 b1 b2 b3 : Bool) (emitted : Word Bool)
    (tail : List (Option Bool)) :
    (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).runConfig
        (2 * emitted.length + 10)
        { state := (prependFixedFourBitsLeftOfHeadDescription
            b0 b1 b2 b3).start
          tape := tapeAtCells (emitted.reverse.map some)
            (some true :: tail) } =
      { state := (prependFixedFourBitsLeftOfHeadDescription
          b0 b1 b2 b3).halt
        tape := tapeAtCells
          (List.append (emitted.reverse.map some)
            [some b3, some b2, some b1, some b0])
          (some true :: tail) } := by
  rw [show 2 * emitted.length + 10 =
      1 + (emitted.reverse.length + (4 +
        ((List.append [b1, b2, b3] emitted).length + 2))) by
    simp [List.length_reverse]
    lia]
  rw [runConfig_add]
  rw [prependFixedFourBitsLeftOfHeadDescription_step_start_true]
  rw [runConfig_add]
  rw [prependFixedFourBitsLeftOfHeadDescription_run_scanLeft_true]
  simp [List.reverse_reverse]
  rw [runConfig_add]
  rw [prependFixedFourBitsLeftOfHeadDescription_run_write_true]
  rw [runConfig_add]
  rw [show emitted.length + 1 + 1 + 1 =
      (List.append [b1, b2, b3] emitted).length by
    simp]
  rw [show some b1 :: some b2 :: some b3 ::
        (List.map some emitted ++ none :: tail) =
      List.append ((List.append [b1, b2, b3] emitted).map some)
        (none :: tail) by
    simp]
  rw [prependFixedFourBitsLeftOfHeadDescription_run_scanRight_true]
  rw [show
      List.append
          (List.map some (List.append [b1, b2, b3] emitted).reverse)
          [some b0] =
        List.append (emitted.reverse.map some)
          [some b3, some b2, some b1, some b0] by
    simp [List.map_reverse, List.append_assoc]]
  rw [prependFixedFourBitsLeftOfHeadDescription_run_restore_true_bits]
  simp [List.map_reverse]

theorem prependFixedFourBitsLeftOfHeadDescription_run_false_withScratch
    (b0 b1 b2 b3 : Bool) (emitted : Word Bool)
    (baseLeft tail : List (Option Bool)) :
    (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).runConfig
        (2 * emitted.length + 10)
        { state := (prependFixedFourBitsLeftOfHeadDescription
            b0 b1 b2 b3).start
          tape :=
            tapeAtCells
              (List.append (emitted.reverse.map some)
                (List.append
                  (List.replicate 4 (none : Option Bool))
                  baseLeft))
              (some false :: tail) } =
      { state := (prependFixedFourBitsLeftOfHeadDescription
          b0 b1 b2 b3).halt
        tape :=
          tapeAtCells
            (List.append
              (List.append (emitted.reverse.map some)
                [some b3, some b2, some b1, some b0])
              baseLeft)
            (some false :: tail) } := by
  rw [show 2 * emitted.length + 10 =
      1 + (emitted.reverse.length + (4 +
        ((List.append [b1, b2, b3] emitted).length + 2))) by
    simp [List.length_reverse]
    lia]
  rw [show
      List.append (List.replicate 4 (none : Option Bool)) baseLeft =
        none ::
          List.append (List.replicate 3 (none : Option Bool)) baseLeft by
    rfl]
  rw [runConfig_add]
  rw [prependFixedFourBitsLeftOfHeadDescription_step_start_false_withScratch]
  rw [runConfig_add]
  rw [prependFixedFourBitsLeftOfHeadDescription_run_scanLeft_false_withScratch]
  simp [List.reverse_reverse]
  rw [runConfig_add]
  change
    (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).runConfig
        (List.length emitted + 1 + 1 + 1 + 2)
        ((prependFixedFourBitsLeftOfHeadDescription
            b0 b1 b2 b3).runConfig 4
          { state := 10
            tape :=
              tapeAtCells
                (List.append
                  (List.replicate 3 (none : Option Bool))
                  baseLeft)
                (none :: (List.map some emitted ++ none :: tail)) }) =
      { state := (prependFixedFourBitsLeftOfHeadDescription
          b0 b1 b2 b3).halt
        tape :=
          tapeAtCells
            (List.append (List.map some emitted).reverse
              (some b3 :: some b2 :: some b1 :: some b0 :: baseLeft))
            (some false :: tail) }
  rw [prependFixedFourBitsLeftOfHeadDescription_run_write_false_withScratch]
  rw [runConfig_add]
  rw [show emitted.length + 1 + 1 + 1 =
      (List.append [b1, b2, b3] emitted).length by
    simp]
  rw [show some b1 :: some b2 :: some b3 ::
        (List.map some emitted ++ none :: tail) =
      List.append ((List.append [b1, b2, b3] emitted).map some)
        (none :: tail) by
    simp]
  rw [prependFixedFourBitsLeftOfHeadDescription_run_scanRight_false]
  rw [show
      List.append
          (List.map some (List.append [b1, b2, b3] emitted).reverse)
          (some b0 :: baseLeft) =
        List.append
          (List.append (emitted.reverse.map some)
            [some b3, some b2, some b1, some b0])
          baseLeft by
    simp [List.map_reverse, List.append_assoc]]
  simpa using
    prependFixedFourBitsLeftOfHeadDescription_run_restore_false_bits_withBase
      b0 b1 b2 b3 emitted.reverse baseLeft tail

theorem prependFixedFourBitsLeftOfHeadDescription_run_true_withScratch
    (b0 b1 b2 b3 : Bool) (emitted : Word Bool)
    (baseLeft tail : List (Option Bool)) :
    (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).runConfig
        (2 * emitted.length + 10)
        { state := (prependFixedFourBitsLeftOfHeadDescription
            b0 b1 b2 b3).start
          tape :=
            tapeAtCells
              (List.append (emitted.reverse.map some)
                (List.append
                  (List.replicate 4 (none : Option Bool))
                  baseLeft))
              (some true :: tail) } =
      { state := (prependFixedFourBitsLeftOfHeadDescription
          b0 b1 b2 b3).halt
        tape :=
          tapeAtCells
            (List.append
              (List.append (emitted.reverse.map some)
                [some b3, some b2, some b1, some b0])
              baseLeft)
            (some true :: tail) } := by
  rw [show 2 * emitted.length + 10 =
      1 + (emitted.reverse.length + (4 +
        ((List.append [b1, b2, b3] emitted).length + 2))) by
    simp [List.length_reverse]
    lia]
  rw [show
      List.append (List.replicate 4 (none : Option Bool)) baseLeft =
        none ::
          List.append (List.replicate 3 (none : Option Bool)) baseLeft by
    rfl]
  rw [runConfig_add]
  rw [prependFixedFourBitsLeftOfHeadDescription_step_start_true_withScratch]
  rw [runConfig_add]
  rw [prependFixedFourBitsLeftOfHeadDescription_run_scanLeft_true_withScratch]
  simp [List.reverse_reverse]
  rw [runConfig_add]
  change
    (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).runConfig
        (List.length emitted + 1 + 1 + 1 + 2)
        ((prependFixedFourBitsLeftOfHeadDescription
            b0 b1 b2 b3).runConfig 4
          { state := 20
            tape :=
              tapeAtCells
                (List.append
                  (List.replicate 3 (none : Option Bool))
                  baseLeft)
                (none :: (List.map some emitted ++ none :: tail)) }) =
      { state := (prependFixedFourBitsLeftOfHeadDescription
          b0 b1 b2 b3).halt
        tape :=
          tapeAtCells
            (List.append (List.map some emitted).reverse
              (some b3 :: some b2 :: some b1 :: some b0 :: baseLeft))
            (some true :: tail) }
  rw [prependFixedFourBitsLeftOfHeadDescription_run_write_true_withScratch]
  rw [runConfig_add]
  rw [show emitted.length + 1 + 1 + 1 =
      (List.append [b1, b2, b3] emitted).length by
    simp]
  rw [show some b1 :: some b2 :: some b3 ::
        (List.map some emitted ++ none :: tail) =
      List.append ((List.append [b1, b2, b3] emitted).map some)
        (none :: tail) by
    simp]
  rw [prependFixedFourBitsLeftOfHeadDescription_run_scanRight_true]
  rw [show
      List.append
          (List.map some (List.append [b1, b2, b3] emitted).reverse)
          (some b0 :: baseLeft) =
        List.append
          (List.append (emitted.reverse.map some)
            [some b3, some b2, some b1, some b0])
          baseLeft by
    simp [List.map_reverse, List.append_assoc]]
  simpa using
    prependFixedFourBitsLeftOfHeadDescription_run_restore_true_bits_withBase
      b0 b1 b2 b3 emitted.reverse baseLeft tail

theorem prependFixedFourBitsLeftOfHeadDescription_haltsFrom_false
    (b0 b1 b2 b3 : Bool) (emitted : Word Bool)
    (tail : List (Option Bool)) :
    (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).HaltsFromTape
      (tapeAtCells (emitted.reverse.map some) (some false :: tail))
      (tapeAtCells
        (List.append (emitted.reverse.map some)
          [some b3, some b2, some b1, some b0])
        (some false :: tail)) := by
  refine ⟨2 * emitted.length + 10, ?_⟩
  constructor <;>
    rw [prependFixedFourBitsLeftOfHeadDescription_run_false]

theorem prependFixedFourBitsLeftOfHeadDescription_haltsFrom_true
    (b0 b1 b2 b3 : Bool) (emitted : Word Bool)
    (tail : List (Option Bool)) :
    (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).HaltsFromTape
      (tapeAtCells (emitted.reverse.map some) (some true :: tail))
      (tapeAtCells
        (List.append (emitted.reverse.map some)
          [some b3, some b2, some b1, some b0])
        (some true :: tail)) := by
  refine ⟨2 * emitted.length + 10, ?_⟩
  constructor <;>
    rw [prependFixedFourBitsLeftOfHeadDescription_run_true]

theorem prependFixedFourBitsLeftOfHeadDescription_haltsFrom_false_chunk
    (b0 b1 b2 b3 : Bool) (emitted : Word Bool)
    (tail : List (Option Bool)) :
    (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).HaltsFromTape
      (tapeAtCells (emitted.reverse.map some) (some false :: tail))
      (tapeAtCells
        (List.append (emitted.reverse.map some)
          (([b0, b1, b2, b3] : Word Bool).reverse.map some))
        (some false :: tail)) := by
  simpa using
    prependFixedFourBitsLeftOfHeadDescription_haltsFrom_false
      b0 b1 b2 b3 emitted tail

theorem prependFixedFourBitsLeftOfHeadDescription_haltsFrom_true_chunk
    (b0 b1 b2 b3 : Bool) (emitted : Word Bool)
    (tail : List (Option Bool)) :
    (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).HaltsFromTape
      (tapeAtCells (emitted.reverse.map some) (some true :: tail))
      (tapeAtCells
        (List.append (emitted.reverse.map some)
          (([b0, b1, b2, b3] : Word Bool).reverse.map some))
        (some true :: tail)) := by
  simpa using
    prependFixedFourBitsLeftOfHeadDescription_haltsFrom_true
      b0 b1 b2 b3 emitted tail

theorem prependFixedFourBitsLeftOfHeadDescription_haltsFrom_chunk
    (b0 b1 b2 b3 : Bool) (emitted : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) :
    (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).HaltsFromTape
      (tapeAtCells (emitted.reverse.map some)
        (some tailFirst :: tail))
      (tapeAtCells
        (List.append (emitted.reverse.map some)
          (([b0, b1, b2, b3] : Word Bool).reverse.map some))
        (some tailFirst :: tail)) := by
  cases tailFirst
  · simpa using
      prependFixedFourBitsLeftOfHeadDescription_haltsFrom_false_chunk
        b0 b1 b2 b3 emitted tail
  · simpa using
      prependFixedFourBitsLeftOfHeadDescription_haltsFrom_true_chunk
        b0 b1 b2 b3 emitted tail

theorem prependFixedFourBitsLeftOfHeadDescription_haltsFrom_prepend
    (b0 b1 b2 b3 : Bool) (emitted : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) :
    (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).HaltsFromTape
      (tapeAtCells (emitted.reverse.map some)
        (some tailFirst :: tail))
      (tapeAtCells
        ((List.append ([b0, b1, b2, b3] : Word Bool) emitted).reverse.map
          some)
        (some tailFirst :: tail)) := by
  simpa [List.reverse_append, List.map_append] using
    prependFixedFourBitsLeftOfHeadDescription_haltsFrom_chunk
      b0 b1 b2 b3 emitted tailFirst tail

theorem prependFixedFourBitsLeftOfHeadDescription_haltsFrom_prepend_withScratch
    (b0 b1 b2 b3 : Bool) (emitted : Word Bool)
    (baseLeft : List (Option Bool)) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (prependFixedFourBitsLeftOfHeadDescription b0 b1 b2 b3).HaltsFromTape
      (tapeAtCells
        (List.append (emitted.reverse.map some)
          (List.append
            (List.replicate 4 (none : Option Bool))
            baseLeft))
        (some tailFirst :: tail))
      (tapeAtCells
        (List.append
          ((List.append ([b0, b1, b2, b3] : Word Bool)
            emitted).reverse.map some)
          baseLeft)
        (some tailFirst :: tail)) := by
  cases tailFirst
  · refine ⟨2 * emitted.length + 10, ?_⟩
    constructor
    · rw [prependFixedFourBitsLeftOfHeadDescription_run_false_withScratch]
    · rw [prependFixedFourBitsLeftOfHeadDescription_run_false_withScratch]
      simp [List.map_append, List.append_assoc]
  · refine ⟨2 * emitted.length + 10, ?_⟩
    constructor
    · rw [prependFixedFourBitsLeftOfHeadDescription_run_true_withScratch]
    · rw [prependFixedFourBitsLeftOfHeadDescription_run_true_withScratch]
      simp [List.map_append, List.append_assoc]

theorem prependFixedFourBitsLeftOfHeadDescription_target_moveLeftRight
    (b0 b1 b2 b3 : Bool) (emitted : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (tapeAtCells
            ((List.append ([b0, b1, b2, b3] : Word Bool)
              emitted).reverse.map some)
            (some tailFirst :: tail))) =
      tapeAtCells
        ((List.append ([b0, b1, b2, b3] : Word Bool)
          emitted).reverse.map some)
        (some tailFirst :: tail) := by
  simpa [List.reverse_append, List.map_append, List.append_assoc] using
    tapeAtCells_move_right_move_left_append_cons
      (emitted.reverse.map some)
      [some b2, some b1, some b0]
      (some tailFirst :: tail)
      (some b3)

def prependHeaderChunkLeftOfHeadDescription : MachineDescription :=
  prependFixedFourBitsLeftOfHeadDescription false false false false

theorem prependHeaderChunkLeftOfHeadDescription_subroutineReady :
    prependHeaderChunkLeftOfHeadDescription.SubroutineReady :=
  prependFixedFourBitsLeftOfHeadDescription_subroutineReady
    false false false false

theorem prependHeaderChunkLeftOfHeadDescription_haltsFrom_false
    (emitted : Word Bool) (tail : List (Option Bool)) :
    prependHeaderChunkLeftOfHeadDescription.HaltsFromTape
      (tapeAtCells (emitted.reverse.map some) (some false :: tail))
      (tapeAtCells
        (List.append (emitted.reverse.map some)
          ((encodeCodeSymbolAsInput MachineCodeSymbol.header).reverse.map
            some))
        (some false :: tail)) := by
  simpa [prependHeaderChunkLeftOfHeadDescription,
    encodeCodeSymbolAsInput] using
    prependFixedFourBitsLeftOfHeadDescription_haltsFrom_false_chunk
      false false false false emitted tail

theorem prependHeaderChunkLeftOfHeadDescription_haltsFrom_true
    (emitted : Word Bool) (tail : List (Option Bool)) :
    prependHeaderChunkLeftOfHeadDescription.HaltsFromTape
      (tapeAtCells (emitted.reverse.map some) (some true :: tail))
      (tapeAtCells
        (List.append (emitted.reverse.map some)
          ((encodeCodeSymbolAsInput MachineCodeSymbol.header).reverse.map
            some))
        (some true :: tail)) := by
  simpa [prependHeaderChunkLeftOfHeadDescription,
    encodeCodeSymbolAsInput] using
    prependFixedFourBitsLeftOfHeadDescription_haltsFrom_true_chunk
      false false false false emitted tail

theorem prependHeaderChunkLeftOfHeadDescription_haltsFrom
    (emitted : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    prependHeaderChunkLeftOfHeadDescription.HaltsFromTape
      (tapeAtCells (emitted.reverse.map some)
        (some tailFirst :: tail))
      (tapeAtCells
        (List.append (emitted.reverse.map some)
          ((encodeCodeSymbolAsInput MachineCodeSymbol.header).reverse.map
            some))
        (some tailFirst :: tail)) := by
  cases tailFirst
  · simpa using
      prependHeaderChunkLeftOfHeadDescription_haltsFrom_false emitted tail
  · simpa using
      prependHeaderChunkLeftOfHeadDescription_haltsFrom_true emitted tail

theorem prependHeaderChunkLeftOfHeadDescription_haltsFrom_prepend
    (emitted : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    prependHeaderChunkLeftOfHeadDescription.HaltsFromTape
      (tapeAtCells (emitted.reverse.map some)
        (some tailFirst :: tail))
      (tapeAtCells
        ((List.append (encodeCodeSymbolAsInput MachineCodeSymbol.header)
          emitted).reverse.map some)
        (some tailFirst :: tail)) := by
  simpa [prependHeaderChunkLeftOfHeadDescription,
    encodeCodeSymbolAsInput] using
    prependFixedFourBitsLeftOfHeadDescription_haltsFrom_prepend
      false false false false emitted tailFirst tail

theorem prependHeaderChunkLeftOfHeadDescription_haltsFrom_prepend_withScratch
    (emitted : Word Bool) (baseLeft : List (Option Bool))
    (tailFirst : Bool) (tail : List (Option Bool)) :
    prependHeaderChunkLeftOfHeadDescription.HaltsFromTape
      (tapeAtCells
        (List.append (emitted.reverse.map some)
          (List.append
            (List.replicate 4 (none : Option Bool))
            baseLeft))
        (some tailFirst :: tail))
      (tapeAtCells
        (List.append
          ((List.append (encodeCodeSymbolAsInput MachineCodeSymbol.header)
            emitted).reverse.map some)
          baseLeft)
        (some tailFirst :: tail)) := by
  simpa [prependHeaderChunkLeftOfHeadDescription,
    encodeCodeSymbolAsInput] using
    prependFixedFourBitsLeftOfHeadDescription_haltsFrom_prepend_withScratch
      false false false false emitted baseLeft tailFirst tail

def prependLengthTickChunkLeftOfHeadDescription : MachineDescription :=
  prependFixedFourBitsLeftOfHeadDescription false false true false

theorem prependLengthTickChunkLeftOfHeadDescription_subroutineReady :
    prependLengthTickChunkLeftOfHeadDescription.SubroutineReady :=
  prependFixedFourBitsLeftOfHeadDescription_subroutineReady
    false false true false

theorem prependLengthTickChunkLeftOfHeadDescription_haltsFrom_false
    (emitted : Word Bool) (tail : List (Option Bool)) :
    prependLengthTickChunkLeftOfHeadDescription.HaltsFromTape
      (tapeAtCells (emitted.reverse.map some) (some false :: tail))
      (tapeAtCells
        (List.append (emitted.reverse.map some)
          ((encodeCodeSymbolAsInput MachineCodeSymbol.tick).reverse.map
            some))
        (some false :: tail)) := by
  simpa [prependLengthTickChunkLeftOfHeadDescription,
    encodeCodeSymbolAsInput] using
    prependFixedFourBitsLeftOfHeadDescription_haltsFrom_false_chunk
      false false true false emitted tail

theorem prependLengthTickChunkLeftOfHeadDescription_haltsFrom_true
    (emitted : Word Bool) (tail : List (Option Bool)) :
    prependLengthTickChunkLeftOfHeadDescription.HaltsFromTape
      (tapeAtCells (emitted.reverse.map some) (some true :: tail))
      (tapeAtCells
        (List.append (emitted.reverse.map some)
          ((encodeCodeSymbolAsInput MachineCodeSymbol.tick).reverse.map
            some))
        (some true :: tail)) := by
  simpa [prependLengthTickChunkLeftOfHeadDescription,
    encodeCodeSymbolAsInput] using
    prependFixedFourBitsLeftOfHeadDescription_haltsFrom_true_chunk
      false false true false emitted tail

theorem prependLengthTickChunkLeftOfHeadDescription_haltsFrom
    (emitted : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    prependLengthTickChunkLeftOfHeadDescription.HaltsFromTape
      (tapeAtCells (emitted.reverse.map some)
        (some tailFirst :: tail))
      (tapeAtCells
        (List.append (emitted.reverse.map some)
          ((encodeCodeSymbolAsInput MachineCodeSymbol.tick).reverse.map
            some))
        (some tailFirst :: tail)) := by
  cases tailFirst
  · simpa using
      prependLengthTickChunkLeftOfHeadDescription_haltsFrom_false
        emitted tail
  · simpa using
      prependLengthTickChunkLeftOfHeadDescription_haltsFrom_true
        emitted tail

theorem prependLengthTickChunkLeftOfHeadDescription_haltsFrom_prepend
    (emitted : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    prependLengthTickChunkLeftOfHeadDescription.HaltsFromTape
      (tapeAtCells (emitted.reverse.map some)
        (some tailFirst :: tail))
      (tapeAtCells
        ((List.append (encodeCodeSymbolAsInput MachineCodeSymbol.tick)
          emitted).reverse.map some)
        (some tailFirst :: tail)) := by
  simpa [prependLengthTickChunkLeftOfHeadDescription,
    encodeCodeSymbolAsInput] using
    prependFixedFourBitsLeftOfHeadDescription_haltsFrom_prepend
      false false true false emitted tailFirst tail

theorem prependLengthTickChunkLeftOfHeadDescription_haltsFrom_prepend_withScratch
    (emitted : Word Bool) (baseLeft : List (Option Bool))
    (tailFirst : Bool) (tail : List (Option Bool)) :
    prependLengthTickChunkLeftOfHeadDescription.HaltsFromTape
      (tapeAtCells
        (List.append (emitted.reverse.map some)
          (List.append
            (List.replicate 4 (none : Option Bool))
            baseLeft))
        (some tailFirst :: tail))
      (tapeAtCells
        (List.append
          ((List.append (encodeCodeSymbolAsInput MachineCodeSymbol.tick)
            emitted).reverse.map some)
          baseLeft)
        (some tailFirst :: tail)) := by
  simpa [prependLengthTickChunkLeftOfHeadDescription,
    encodeCodeSymbolAsInput] using
    prependFixedFourBitsLeftOfHeadDescription_haltsFrom_prepend_withScratch
      false false true false emitted baseLeft tailFirst tail

theorem prependLengthTickChunkLeftOfHeadDescription_target_moveLeftRight
    (emitted : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (tapeAtCells
            ((List.append (encodeCodeSymbolAsInput MachineCodeSymbol.tick)
              emitted).reverse.map some)
            (some tailFirst :: tail))) =
      tapeAtCells
        ((List.append (encodeCodeSymbolAsInput MachineCodeSymbol.tick)
          emitted).reverse.map some)
        (some tailFirst :: tail) := by
  simpa [encodeCodeSymbolAsInput] using
    prependFixedFourBitsLeftOfHeadDescription_target_moveLeftRight
      false false true false emitted tailFirst tail

theorem prependLengthTickChunkLeftOfHeadDescription_haltsFrom_stageNatBits
    (n : Nat) (tailFirst : Bool) (tail : List (Option Bool)) :
    prependLengthTickChunkLeftOfHeadDescription.HaltsFromTape
      (tapeAtCells
        ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          n).reverse.map some)
        (some tailFirst :: tail))
      (tapeAtCells
        ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          (n + 1)).reverse.map some)
        (some tailFirst :: tail)) := by
  simpa [stageNatBits_reverse_succ_append_tick, List.map_append] using!
    prependLengthTickChunkLeftOfHeadDescription_haltsFrom
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        n)
      tailFirst tail

theorem prependLengthTickChunkLeftOfHeadDescription_haltsFrom_stageNatBitsSuffix
    (n : Nat) (suffix : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    prependLengthTickChunkLeftOfHeadDescription.HaltsFromTape
      (tapeAtCells
        ((List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            n)
          suffix).reverse.map some)
        (some tailFirst :: tail))
      (tapeAtCells
        ((List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            (n + 1))
          suffix).reverse.map some)
        (some tailFirst :: tail)) := by
  simpa [
    DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_succ,
    encodeCodeSymbolAsInput, List.append_assoc] using
    prependLengthTickChunkLeftOfHeadDescription_haltsFrom_prepend
      (List.append
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          n)
        suffix)
      tailFirst tail

theorem prependLengthTickChunkLeftOfHeadDescription_haltsFrom_stageNatBitsCellSuffix
    (n : Nat) (layout : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    prependLengthTickChunkLeftOfHeadDescription.HaltsFromTape
      (tapeAtCells
        ((List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            n)
          (preservingCellPassCellBits layout)).reverse.map some)
        (some tailFirst :: tail))
      (tapeAtCells
        ((List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            (n + 1))
          (preservingCellPassCellBits layout)).reverse.map some)
        (some tailFirst :: tail)) :=
  prependLengthTickChunkLeftOfHeadDescription_haltsFrom_stageNatBitsSuffix
    n (preservingCellPassCellBits layout) tailFirst tail

def prependLengthDoneChunkLeftOfHeadDescription : MachineDescription :=
  prependFixedFourBitsLeftOfHeadDescription false false true true

theorem prependLengthDoneChunkLeftOfHeadDescription_subroutineReady :
    prependLengthDoneChunkLeftOfHeadDescription.SubroutineReady :=
  prependFixedFourBitsLeftOfHeadDescription_subroutineReady
    false false true true

theorem prependLengthDoneChunkLeftOfHeadDescription_haltsFrom_false
    (emitted : Word Bool) (tail : List (Option Bool)) :
    prependLengthDoneChunkLeftOfHeadDescription.HaltsFromTape
      (tapeAtCells (emitted.reverse.map some) (some false :: tail))
      (tapeAtCells
        (List.append (emitted.reverse.map some)
          ((encodeCodeSymbolAsInput MachineCodeSymbol.done).reverse.map
            some))
        (some false :: tail)) := by
  simpa [prependLengthDoneChunkLeftOfHeadDescription,
    encodeCodeSymbolAsInput] using
    prependFixedFourBitsLeftOfHeadDescription_haltsFrom_false_chunk
      false false true true emitted tail

theorem prependLengthDoneChunkLeftOfHeadDescription_haltsFrom_true
    (emitted : Word Bool) (tail : List (Option Bool)) :
    prependLengthDoneChunkLeftOfHeadDescription.HaltsFromTape
      (tapeAtCells (emitted.reverse.map some) (some true :: tail))
      (tapeAtCells
        (List.append (emitted.reverse.map some)
          ((encodeCodeSymbolAsInput MachineCodeSymbol.done).reverse.map
            some))
        (some true :: tail)) := by
  simpa [prependLengthDoneChunkLeftOfHeadDescription,
    encodeCodeSymbolAsInput] using
    prependFixedFourBitsLeftOfHeadDescription_haltsFrom_true_chunk
      false false true true emitted tail

theorem prependLengthDoneChunkLeftOfHeadDescription_haltsFrom
    (emitted : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    prependLengthDoneChunkLeftOfHeadDescription.HaltsFromTape
      (tapeAtCells (emitted.reverse.map some)
        (some tailFirst :: tail))
      (tapeAtCells
        (List.append (emitted.reverse.map some)
          ((encodeCodeSymbolAsInput MachineCodeSymbol.done).reverse.map
            some))
        (some tailFirst :: tail)) := by
  cases tailFirst
  · simpa using
      prependLengthDoneChunkLeftOfHeadDescription_haltsFrom_false
        emitted tail
  · simpa using
      prependLengthDoneChunkLeftOfHeadDescription_haltsFrom_true
        emitted tail

theorem prependLengthDoneChunkLeftOfHeadDescription_haltsFrom_prepend
    (emitted : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    prependLengthDoneChunkLeftOfHeadDescription.HaltsFromTape
      (tapeAtCells (emitted.reverse.map some)
        (some tailFirst :: tail))
      (tapeAtCells
        ((List.append (encodeCodeSymbolAsInput MachineCodeSymbol.done)
          emitted).reverse.map some)
        (some tailFirst :: tail)) := by
  simpa [prependLengthDoneChunkLeftOfHeadDescription,
    encodeCodeSymbolAsInput] using
    prependFixedFourBitsLeftOfHeadDescription_haltsFrom_prepend
      false false true true emitted tailFirst tail

theorem prependLengthDoneChunkLeftOfHeadDescription_haltsFrom_prepend_withScratch
    (emitted : Word Bool) (baseLeft : List (Option Bool))
    (tailFirst : Bool) (tail : List (Option Bool)) :
    prependLengthDoneChunkLeftOfHeadDescription.HaltsFromTape
      (tapeAtCells
        (List.append (emitted.reverse.map some)
          (List.append
            (List.replicate 4 (none : Option Bool))
            baseLeft))
        (some tailFirst :: tail))
      (tapeAtCells
        (List.append
          ((List.append (encodeCodeSymbolAsInput MachineCodeSymbol.done)
            emitted).reverse.map some)
          baseLeft)
        (some tailFirst :: tail)) := by
  simpa [prependLengthDoneChunkLeftOfHeadDescription,
    encodeCodeSymbolAsInput] using
    prependFixedFourBitsLeftOfHeadDescription_haltsFrom_prepend_withScratch
      false false true true emitted baseLeft tailFirst tail

theorem prependLengthDoneChunkLeftOfHeadDescription_target_moveLeftRight
    (emitted : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (tapeAtCells
            ((List.append (encodeCodeSymbolAsInput MachineCodeSymbol.done)
              emitted).reverse.map some)
            (some tailFirst :: tail))) =
      tapeAtCells
        ((List.append (encodeCodeSymbolAsInput MachineCodeSymbol.done)
          emitted).reverse.map some)
        (some tailFirst :: tail) := by
  simpa [encodeCodeSymbolAsInput] using
    prependFixedFourBitsLeftOfHeadDescription_target_moveLeftRight
      false false true true emitted tailFirst tail

theorem prependLengthDoneChunkLeftOfHeadDescription_haltsFrom_stageNatBitsZero
    (tailFirst : Bool) (tail : List (Option Bool)) :
    prependLengthDoneChunkLeftOfHeadDescription.HaltsFromTape
      (tapeAtCells [] (some tailFirst :: tail))
      (tapeAtCells
        ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          0).reverse.map some)
        (some tailFirst :: tail)) := by
  simpa [stageNatBits_reverse_zero] using!
    prependLengthDoneChunkLeftOfHeadDescription_haltsFrom
      ([] : Word Bool) tailFirst tail

theorem prependLengthDoneChunkLeftOfHeadDescription_haltsFrom_stageNatBitsZeroSuffix
    (suffix : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    prependLengthDoneChunkLeftOfHeadDescription.HaltsFromTape
      (tapeAtCells (suffix.reverse.map some)
        (some tailFirst :: tail))
      (tapeAtCells
        ((List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            0)
          suffix).reverse.map some)
        (some tailFirst :: tail)) := by
  simpa [
    DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_zero,
    encodeCodeSymbolAsInput] using
    prependLengthDoneChunkLeftOfHeadDescription_haltsFrom_prepend
      suffix tailFirst tail

theorem prependLengthDoneChunkLeftOfHeadDescription_haltsFrom_stageNatBitsZeroCellSuffix
    (layout : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    prependLengthDoneChunkLeftOfHeadDescription.HaltsFromTape
      (tapeAtCells ((preservingCellPassCellBits layout).reverse.map some)
        (some tailFirst :: tail))
      (tapeAtCells
        ((List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            0)
          (preservingCellPassCellBits layout)).reverse.map some)
        (some tailFirst :: tail)) :=
  prependLengthDoneChunkLeftOfHeadDescription_haltsFrom_stageNatBitsZeroSuffix
    (preservingCellPassCellBits layout) tailFirst tail

def prependCellZeroChunkLeftOfHeadDescription : MachineDescription :=
  prependFixedFourBitsLeftOfHeadDescription false true false true

theorem prependCellZeroChunkLeftOfHeadDescription_subroutineReady :
    prependCellZeroChunkLeftOfHeadDescription.SubroutineReady :=
  prependFixedFourBitsLeftOfHeadDescription_subroutineReady
    false true false true

theorem prependCellZeroChunkLeftOfHeadDescription_haltsFrom_false
    (emitted : Word Bool) (tail : List (Option Bool)) :
    prependCellZeroChunkLeftOfHeadDescription.HaltsFromTape
      (tapeAtCells (emitted.reverse.map some) (some false :: tail))
      (tapeAtCells
        (List.append (emitted.reverse.map some)
          (preservingCellPassZeroBits.reverse.map some))
        (some false :: tail)) := by
  simpa [prependCellZeroChunkLeftOfHeadDescription,
    preservingCellPassZeroBits] using
    prependFixedFourBitsLeftOfHeadDescription_haltsFrom_false_chunk
      false true false true emitted tail

theorem prependCellZeroChunkLeftOfHeadDescription_haltsFrom_true
    (emitted : Word Bool) (tail : List (Option Bool)) :
    prependCellZeroChunkLeftOfHeadDescription.HaltsFromTape
      (tapeAtCells (emitted.reverse.map some) (some true :: tail))
      (tapeAtCells
        (List.append (emitted.reverse.map some)
          (preservingCellPassZeroBits.reverse.map some))
        (some true :: tail)) := by
  simpa [prependCellZeroChunkLeftOfHeadDescription,
    preservingCellPassZeroBits] using
    prependFixedFourBitsLeftOfHeadDescription_haltsFrom_true_chunk
      false true false true emitted tail

theorem prependCellZeroChunkLeftOfHeadDescription_haltsFrom
    (emitted : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    prependCellZeroChunkLeftOfHeadDescription.HaltsFromTape
      (tapeAtCells (emitted.reverse.map some)
        (some tailFirst :: tail))
      (tapeAtCells
        (List.append (emitted.reverse.map some)
          (preservingCellPassZeroBits.reverse.map some))
        (some tailFirst :: tail)) := by
  cases tailFirst
  · simpa using
      prependCellZeroChunkLeftOfHeadDescription_haltsFrom_false
        emitted tail
  · simpa using
      prependCellZeroChunkLeftOfHeadDescription_haltsFrom_true
        emitted tail

theorem prependCellZeroChunkLeftOfHeadDescription_haltsFrom_prepend
    (emitted : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    prependCellZeroChunkLeftOfHeadDescription.HaltsFromTape
      (tapeAtCells (emitted.reverse.map some)
        (some tailFirst :: tail))
      (tapeAtCells
        ((List.append preservingCellPassZeroBits emitted).reverse.map some)
        (some tailFirst :: tail)) := by
  simpa [prependCellZeroChunkLeftOfHeadDescription,
    preservingCellPassZeroBits] using
    prependFixedFourBitsLeftOfHeadDescription_haltsFrom_prepend
      false true false true emitted tailFirst tail

theorem prependCellZeroChunkLeftOfHeadDescription_haltsFrom_prepend_withScratch
    (emitted : Word Bool) (baseLeft : List (Option Bool))
    (tailFirst : Bool) (tail : List (Option Bool)) :
    prependCellZeroChunkLeftOfHeadDescription.HaltsFromTape
      (tapeAtCells
        (List.append (emitted.reverse.map some)
          (List.append
            (List.replicate 4 (none : Option Bool))
            baseLeft))
        (some tailFirst :: tail))
      (tapeAtCells
        (List.append
          ((List.append preservingCellPassZeroBits emitted).reverse.map some)
          baseLeft)
        (some tailFirst :: tail)) := by
  simpa [prependCellZeroChunkLeftOfHeadDescription,
    preservingCellPassZeroBits] using
    prependFixedFourBitsLeftOfHeadDescription_haltsFrom_prepend_withScratch
      false true false true emitted baseLeft tailFirst tail

def prependCellOneChunkLeftOfHeadDescription : MachineDescription :=
  prependFixedFourBitsLeftOfHeadDescription false true true false

theorem prependCellOneChunkLeftOfHeadDescription_subroutineReady :
    prependCellOneChunkLeftOfHeadDescription.SubroutineReady :=
  prependFixedFourBitsLeftOfHeadDescription_subroutineReady
    false true true false

theorem prependCellOneChunkLeftOfHeadDescription_haltsFrom_false
    (emitted : Word Bool) (tail : List (Option Bool)) :
    prependCellOneChunkLeftOfHeadDescription.HaltsFromTape
      (tapeAtCells (emitted.reverse.map some) (some false :: tail))
      (tapeAtCells
        (List.append (emitted.reverse.map some)
          (preservingCellPassOneBits.reverse.map some))
        (some false :: tail)) := by
  simpa [prependCellOneChunkLeftOfHeadDescription,
    preservingCellPassOneBits] using
    prependFixedFourBitsLeftOfHeadDescription_haltsFrom_false_chunk
      false true true false emitted tail

theorem prependCellOneChunkLeftOfHeadDescription_haltsFrom_true
    (emitted : Word Bool) (tail : List (Option Bool)) :
    prependCellOneChunkLeftOfHeadDescription.HaltsFromTape
      (tapeAtCells (emitted.reverse.map some) (some true :: tail))
      (tapeAtCells
        (List.append (emitted.reverse.map some)
          (preservingCellPassOneBits.reverse.map some))
        (some true :: tail)) := by
  simpa [prependCellOneChunkLeftOfHeadDescription,
    preservingCellPassOneBits] using
    prependFixedFourBitsLeftOfHeadDescription_haltsFrom_true_chunk
      false true true false emitted tail

theorem prependCellOneChunkLeftOfHeadDescription_haltsFrom
    (emitted : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    prependCellOneChunkLeftOfHeadDescription.HaltsFromTape
      (tapeAtCells (emitted.reverse.map some)
        (some tailFirst :: tail))
      (tapeAtCells
        (List.append (emitted.reverse.map some)
          (preservingCellPassOneBits.reverse.map some))
        (some tailFirst :: tail)) := by
  cases tailFirst
  · simpa using
      prependCellOneChunkLeftOfHeadDescription_haltsFrom_false
        emitted tail
  · simpa using
      prependCellOneChunkLeftOfHeadDescription_haltsFrom_true
        emitted tail

theorem prependCellOneChunkLeftOfHeadDescription_haltsFrom_prepend
    (emitted : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    prependCellOneChunkLeftOfHeadDescription.HaltsFromTape
      (tapeAtCells (emitted.reverse.map some)
        (some tailFirst :: tail))
      (tapeAtCells
        ((List.append preservingCellPassOneBits emitted).reverse.map some)
        (some tailFirst :: tail)) := by
  simpa [prependCellOneChunkLeftOfHeadDescription,
    preservingCellPassOneBits] using
    prependFixedFourBitsLeftOfHeadDescription_haltsFrom_prepend
      false true true false emitted tailFirst tail

theorem prependCellOneChunkLeftOfHeadDescription_haltsFrom_prepend_withScratch
    (emitted : Word Bool) (baseLeft : List (Option Bool))
    (tailFirst : Bool) (tail : List (Option Bool)) :
    prependCellOneChunkLeftOfHeadDescription.HaltsFromTape
      (tapeAtCells
        (List.append (emitted.reverse.map some)
          (List.append
            (List.replicate 4 (none : Option Bool))
            baseLeft))
        (some tailFirst :: tail))
      (tapeAtCells
        (List.append
          ((List.append preservingCellPassOneBits emitted).reverse.map some)
          baseLeft)
        (some tailFirst :: tail)) := by
  simpa [prependCellOneChunkLeftOfHeadDescription,
    preservingCellPassOneBits] using
    prependFixedFourBitsLeftOfHeadDescription_haltsFrom_prepend_withScratch
      false true true false emitted baseLeft tailFirst tail

def prependCellChunkLeftOfHeadDescription (bit : Bool) :
    MachineDescription :=
  if bit then
    prependCellOneChunkLeftOfHeadDescription
  else
    prependCellZeroChunkLeftOfHeadDescription

theorem prependCellChunkLeftOfHeadDescription_subroutineReady
    (bit : Bool) :
    (prependCellChunkLeftOfHeadDescription bit).SubroutineReady := by
  cases bit <;>
    simp [prependCellChunkLeftOfHeadDescription,
      prependCellZeroChunkLeftOfHeadDescription_subroutineReady,
      prependCellOneChunkLeftOfHeadDescription_subroutineReady]

theorem prependCellChunkLeftOfHeadDescription_haltsFrom
    (bit : Bool) (emitted : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (prependCellChunkLeftOfHeadDescription bit).HaltsFromTape
      (tapeAtCells (emitted.reverse.map some)
        (some tailFirst :: tail))
      (tapeAtCells
        (List.append (emitted.reverse.map some)
          ((if bit then preservingCellPassOneBits
            else preservingCellPassZeroBits).reverse.map some))
        (some tailFirst :: tail)) := by
  cases bit
  · cases tailFirst
    · simpa [prependCellChunkLeftOfHeadDescription, List.map_reverse] using
        prependCellZeroChunkLeftOfHeadDescription_haltsFrom_false
          emitted tail
    · simpa [prependCellChunkLeftOfHeadDescription, List.map_reverse] using
        prependCellZeroChunkLeftOfHeadDescription_haltsFrom_true
          emitted tail
  · cases tailFirst
    · simpa [prependCellChunkLeftOfHeadDescription, List.map_reverse] using
        prependCellOneChunkLeftOfHeadDescription_haltsFrom_false
          emitted tail
    · simpa [prependCellChunkLeftOfHeadDescription, List.map_reverse] using
        prependCellOneChunkLeftOfHeadDescription_haltsFrom_true
          emitted tail

theorem prependCellChunkLeftOfHeadDescription_haltsFrom_prepend
    (bit : Bool) (emitted : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (prependCellChunkLeftOfHeadDescription bit).HaltsFromTape
      (tapeAtCells (emitted.reverse.map some)
        (some tailFirst :: tail))
      (tapeAtCells
        ((List.append
          (if bit then preservingCellPassOneBits
            else preservingCellPassZeroBits)
          emitted).reverse.map some)
        (some tailFirst :: tail)) := by
  cases bit
  · simpa [prependCellChunkLeftOfHeadDescription] using
      prependCellZeroChunkLeftOfHeadDescription_haltsFrom_prepend
        emitted tailFirst tail
  · simpa [prependCellChunkLeftOfHeadDescription] using
      prependCellOneChunkLeftOfHeadDescription_haltsFrom_prepend
        emitted tailFirst tail

theorem prependCellChunkLeftOfHeadDescription_haltsFrom_prepend_withScratch
    (bit : Bool) (emitted : Word Bool)
    (baseLeft : List (Option Bool)) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (prependCellChunkLeftOfHeadDescription bit).HaltsFromTape
      (tapeAtCells
        (List.append (emitted.reverse.map some)
          (List.append
            (List.replicate 4 (none : Option Bool))
            baseLeft))
        (some tailFirst :: tail))
      (tapeAtCells
        (List.append
          ((List.append
            (if bit then preservingCellPassOneBits
              else preservingCellPassZeroBits)
            emitted).reverse.map some)
          baseLeft)
        (some tailFirst :: tail)) := by
  cases bit
  · simpa [prependCellChunkLeftOfHeadDescription] using
      prependCellZeroChunkLeftOfHeadDescription_haltsFrom_prepend_withScratch
        emitted baseLeft tailFirst tail
  · simpa [prependCellChunkLeftOfHeadDescription] using
      prependCellOneChunkLeftOfHeadDescription_haltsFrom_prepend_withScratch
        emitted baseLeft tailFirst tail

theorem prependCellChunkLeftOfHeadDescription_target_moveLeftRight
    (bit : Bool) (emitted : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (tapeAtCells
            ((List.append
              (if bit then preservingCellPassOneBits
                else preservingCellPassZeroBits)
              emitted).reverse.map some)
            (some tailFirst :: tail))) =
      tapeAtCells
        ((List.append
          (if bit then preservingCellPassOneBits
            else preservingCellPassZeroBits)
          emitted).reverse.map some)
        (some tailFirst :: tail) := by
  cases bit
  · simpa [preservingCellPassZeroBits] using
      prependFixedFourBitsLeftOfHeadDescription_target_moveLeftRight
        false true false true emitted tailFirst tail
  · simpa [preservingCellPassOneBits] using
      prependFixedFourBitsLeftOfHeadDescription_target_moveLeftRight
        false true true false emitted tailFirst tail

theorem prependCellChunkLeftOfHeadDescription_haltsFrom_cellSuffix
    (bit : Bool) (suffix : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (prependCellChunkLeftOfHeadDescription bit).HaltsFromTape
      (tapeAtCells ((preservingCellPassCellBits suffix).reverse.map some)
        (some tailFirst :: tail))
      (tapeAtCells
        ((preservingCellPassCellBits (bit :: suffix)).reverse.map some)
        (some tailFirst :: tail)) := by
  simpa [preservingCellPassCellBits_reverse_cons_chunk,
    List.map_append] using
    prependCellChunkLeftOfHeadDescription_haltsFrom
      bit (preservingCellPassCellBits suffix) tailFirst tail

theorem prependCellChunkLeftOfHeadDescription_haltsFrom_cellAppendSuffix
    (bit : Bool) (cellSuffix remainingBits : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) :
    (prependCellChunkLeftOfHeadDescription bit).HaltsFromTape
      (tapeAtCells
        ((List.append (preservingCellPassCellBits cellSuffix)
          remainingBits).reverse.map some)
        (some tailFirst :: tail))
      (tapeAtCells
        ((List.append (preservingCellPassCellBits (bit :: cellSuffix))
          remainingBits).reverse.map some)
        (some tailFirst :: tail)) := by
  cases bit
  · simpa [preservingCellPassCellBits, preservingCellPassZeroBits,
      preservingCellPassOneBits, List.append_assoc] using
      prependCellChunkLeftOfHeadDescription_haltsFrom_prepend
        false
        (List.append (preservingCellPassCellBits cellSuffix)
          remainingBits)
        tailFirst tail
  · simpa [preservingCellPassCellBits, preservingCellPassZeroBits,
      preservingCellPassOneBits, List.append_assoc] using
      prependCellChunkLeftOfHeadDescription_haltsFrom_prepend
        true
        (List.append (preservingCellPassCellBits cellSuffix)
          remainingBits)
        tailFirst tail

theorem prependCellChunkLeftOfHeadDescription_haltsFrom_cellAppendSuffix_withScratch
    (bit : Bool) (cellSuffix remainingBits : Word Bool)
    (baseLeft : List (Option Bool)) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (prependCellChunkLeftOfHeadDescription bit).HaltsFromTape
      (tapeAtCells
        (List.append
          ((List.append (preservingCellPassCellBits cellSuffix)
            remainingBits).reverse.map some)
          (List.append
            (List.replicate 4 (none : Option Bool))
            baseLeft))
        (some tailFirst :: tail))
      (tapeAtCells
        (List.append
          ((List.append (preservingCellPassCellBits (bit :: cellSuffix))
            remainingBits).reverse.map some)
          baseLeft)
        (some tailFirst :: tail)) := by
  cases bit
  · simpa [preservingCellPassCellBits, preservingCellPassZeroBits,
      preservingCellPassOneBits, List.append_assoc] using
      prependCellChunkLeftOfHeadDescription_haltsFrom_prepend_withScratch
        false
        (List.append (preservingCellPassCellBits cellSuffix)
          remainingBits)
        baseLeft tailFirst tail
  · simpa [preservingCellPassCellBits, preservingCellPassZeroBits,
      preservingCellPassOneBits, List.append_assoc] using
      prependCellChunkLeftOfHeadDescription_haltsFrom_prepend_withScratch
        true
        (List.append (preservingCellPassCellBits cellSuffix)
          remainingBits)
        baseLeft tailFirst tail

theorem prependCellChunkLeftOfHeadDescription_cellAppendSuffix_target_moveLeftRight
    (bit : Bool) (cellSuffix remainingBits : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (tapeAtCells
            ((List.append (preservingCellPassCellBits (bit :: cellSuffix))
              remainingBits).reverse.map some)
            (some tailFirst :: tail))) =
      tapeAtCells
        ((List.append (preservingCellPassCellBits (bit :: cellSuffix))
          remainingBits).reverse.map some)
        (some tailFirst :: tail) := by
  cases bit
  · simpa [preservingCellPassCellBits, preservingCellPassZeroBits,
      preservingCellPassOneBits, List.append_assoc] using
      prependCellChunkLeftOfHeadDescription_target_moveLeftRight
        false
        (List.append (preservingCellPassCellBits cellSuffix)
          remainingBits)
        tailFirst tail
  · simpa [preservingCellPassCellBits, preservingCellPassZeroBits,
      preservingCellPassOneBits, List.append_assoc] using
      prependCellChunkLeftOfHeadDescription_target_moveLeftRight
        true
        (List.append (preservingCellPassCellBits cellSuffix)
          remainingBits)
        tailFirst tail

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC

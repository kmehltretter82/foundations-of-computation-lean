import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.CursorBoundaryGap

set_option doc.verso true

/-!
# Boundary suffix-gap creator core

This module starts the concrete machine side of the suffix-preserving singleton
head refresh path.  The first leaf is an online two-cell right-shift core.  It
scans from the opening separator to the separator after the first segment
payload, writes two blanks there, and carries overwritten cells two positions
to the right until it observes the trailing all-blank region.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

def headSuffixGapShiftPairState
    (first second : Option Bool) : Nat :=
  match first, second with
  | none, none => 3
  | none, some false => 4
  | none, some true => 5
  | some false, none => 6
  | some false, some false => 7
  | some false, some true => 8
  | some true, none => 9
  | some true, some false => 10
  | some true, some true => 11

def headSuffixGapShiftHalt : Nat :=
  12

def headSuffixGapShiftDescription : MachineDescription where
  stateCount := 13
  start := 0
  halt := headSuffixGapShiftHalt
  transitions :=
    [ transition 0 none none Direction.right 1
    , transition 1 (some false) (some false) Direction.right 1
    , transition 1 (some true) (some true) Direction.right 1
    , transition 1 none none Direction.right 2
    , transition 2 none none Direction.right
        (headSuffixGapShiftPairState none none)
    , transition 2 (some false) none Direction.right
        (headSuffixGapShiftPairState none (some false))
    , transition 2 (some true) none Direction.right
        (headSuffixGapShiftPairState none (some true))
    , transition (headSuffixGapShiftPairState none none)
        none none Direction.left headSuffixGapShiftHalt
    , transition (headSuffixGapShiftPairState none none)
        (some false) none Direction.right
        (headSuffixGapShiftPairState none (some false))
    , transition (headSuffixGapShiftPairState none none)
        (some true) none Direction.right
        (headSuffixGapShiftPairState none (some true))
    , transition (headSuffixGapShiftPairState none (some false))
        none none Direction.right
        (headSuffixGapShiftPairState (some false) none)
    , transition (headSuffixGapShiftPairState none (some false))
        (some false) none Direction.right
        (headSuffixGapShiftPairState (some false) (some false))
    , transition (headSuffixGapShiftPairState none (some false))
        (some true) none Direction.right
        (headSuffixGapShiftPairState (some false) (some true))
    , transition (headSuffixGapShiftPairState none (some true))
        none none Direction.right
        (headSuffixGapShiftPairState (some true) none)
    , transition (headSuffixGapShiftPairState none (some true))
        (some false) none Direction.right
        (headSuffixGapShiftPairState (some true) (some false))
    , transition (headSuffixGapShiftPairState none (some true))
        (some true) none Direction.right
        (headSuffixGapShiftPairState (some true) (some true))
    , transition (headSuffixGapShiftPairState (some false) none)
        none (some false) Direction.right
        (headSuffixGapShiftPairState none none)
    , transition (headSuffixGapShiftPairState (some false) none)
        (some false) (some false) Direction.right
        (headSuffixGapShiftPairState none (some false))
    , transition (headSuffixGapShiftPairState (some false) none)
        (some true) (some false) Direction.right
        (headSuffixGapShiftPairState none (some true))
    , transition (headSuffixGapShiftPairState (some false) (some false))
        none (some false) Direction.right
        (headSuffixGapShiftPairState (some false) none)
    , transition (headSuffixGapShiftPairState (some false) (some false))
        (some false) (some false) Direction.right
        (headSuffixGapShiftPairState (some false) (some false))
    , transition (headSuffixGapShiftPairState (some false) (some false))
        (some true) (some false) Direction.right
        (headSuffixGapShiftPairState (some false) (some true))
    , transition (headSuffixGapShiftPairState (some false) (some true))
        none (some false) Direction.right
        (headSuffixGapShiftPairState (some true) none)
    , transition (headSuffixGapShiftPairState (some false) (some true))
        (some false) (some false) Direction.right
        (headSuffixGapShiftPairState (some true) (some false))
    , transition (headSuffixGapShiftPairState (some false) (some true))
        (some true) (some false) Direction.right
        (headSuffixGapShiftPairState (some true) (some true))
    , transition (headSuffixGapShiftPairState (some true) none)
        none (some true) Direction.right
        (headSuffixGapShiftPairState none none)
    , transition (headSuffixGapShiftPairState (some true) none)
        (some false) (some true) Direction.right
        (headSuffixGapShiftPairState none (some false))
    , transition (headSuffixGapShiftPairState (some true) none)
        (some true) (some true) Direction.right
        (headSuffixGapShiftPairState none (some true))
    , transition (headSuffixGapShiftPairState (some true) (some false))
        none (some true) Direction.right
        (headSuffixGapShiftPairState (some false) none)
    , transition (headSuffixGapShiftPairState (some true) (some false))
        (some false) (some true) Direction.right
        (headSuffixGapShiftPairState (some false) (some false))
    , transition (headSuffixGapShiftPairState (some true) (some false))
        (some true) (some true) Direction.right
        (headSuffixGapShiftPairState (some false) (some true))
    , transition (headSuffixGapShiftPairState (some true) (some true))
        none (some true) Direction.right
        (headSuffixGapShiftPairState (some true) none)
    , transition (headSuffixGapShiftPairState (some true) (some true))
        (some false) (some true) Direction.right
        (headSuffixGapShiftPairState (some true) (some false))
    , transition (headSuffixGapShiftPairState (some true) (some true))
        (some true) (some true) Direction.right
        (headSuffixGapShiftPairState (some true) (some true)) ]

theorem headSuffixGapShiftDescription_wellFormed :
    headSuffixGapShiftDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := headSuffixGapShiftDescription.transitions)
      (stateCount := headSuffixGapShiftDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := headSuffixGapShiftDescription.transitions)
      (by decide)

theorem headSuffixGapShiftDescription_haltTransitionFree :
    headSuffixGapShiftDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := headSuffixGapShiftDescription.transitions)
    (state := headSuffixGapShiftDescription.halt)
    (by decide)

theorem headSuffixGapShiftDescription_subroutineReady :
    headSuffixGapShiftDescription.SubroutineReady :=
  ⟨headSuffixGapShiftDescription_wellFormed,
    headSuffixGapShiftDescription_haltTransitionFree⟩

theorem headSuffixGapShiftDescription_run_boundaryStep_none
    (left right : List (Option Bool)) :
    headSuffixGapShiftDescription.runConfig 1
        { state := 2
          tape := tapeAtCells left (none :: right) } =
      { state := headSuffixGapShiftPairState none none
        tape := tapeAtCells (none :: left) right } := by
  cases right <;>
    simp [headSuffixGapShiftDescription, MachineDescription.runConfig,
      MachineDescription.stepConfig, MachineDescription.lookupTransition,
      MachineDescription.Matches, transition, tapeAtCells, Tape.read,
      Tape.write, Tape.move, Tape.moveRight]

theorem headSuffixGapShiftDescription_run_boundaryStep_bit
    (bit : Bool) (left right : List (Option Bool)) :
    headSuffixGapShiftDescription.runConfig 1
        { state := 2
          tape := tapeAtCells left (some bit :: right) } =
      { state := headSuffixGapShiftPairState none (some bit)
        tape := tapeAtCells (none :: left) right } := by
  cases bit <;> cases right <;>
    simp [headSuffixGapShiftDescription, MachineDescription.runConfig,
      MachineDescription.stepConfig, MachineDescription.lookupTransition,
      MachineDescription.Matches, transition, tapeAtCells, Tape.read,
      Tape.write, Tape.move, Tape.moveRight]

theorem headSuffixGapShiftDescription_run_boundaryStep
    (current : Option Bool) (left right : List (Option Bool)) :
    headSuffixGapShiftDescription.runConfig 1
        { state := 2
          tape := tapeAtCells left (current :: right) } =
      { state := headSuffixGapShiftPairState none current
        tape := tapeAtCells (none :: left) right } := by
  cases current with
  | none =>
      exact headSuffixGapShiftDescription_run_boundaryStep_none left right
  | some bit =>
      exact headSuffixGapShiftDescription_run_boundaryStep_bit bit left right

theorem headSuffixGapShiftDescription_run_boundaryStep_nil
    (left : List (Option Bool)) :
    headSuffixGapShiftDescription.runConfig 1
        { state := 2
          tape := tapeAtCells left [] } =
      { state := headSuffixGapShiftPairState none none
        tape := tapeAtCells (none :: left) [] } := by
  simpa [tapeAtCells] using
    headSuffixGapShiftDescription_run_boundaryStep_none left []

theorem headSuffixGapShiftDescription_run_pairStep_none_none_bit
    (bit : Bool)
    (left right : List (Option Bool)) :
    headSuffixGapShiftDescription.runConfig 1
        { state := headSuffixGapShiftPairState none none
          tape := tapeAtCells left (some bit :: right) } =
      { state := headSuffixGapShiftPairState none (some bit)
        tape := tapeAtCells (none :: left) right } := by
  cases bit <;> cases right <;>
    simp [headSuffixGapShiftDescription, headSuffixGapShiftPairState,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      transition, tapeAtCells, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

theorem headSuffixGapShiftDescription_run_pairStep_none_some
    (second : Bool) (current : Option Bool)
    (left right : List (Option Bool)) :
    headSuffixGapShiftDescription.runConfig 1
        { state := headSuffixGapShiftPairState none (some second)
          tape := tapeAtCells left (current :: right) } =
      { state := headSuffixGapShiftPairState (some second) current
        tape := tapeAtCells (none :: left) right } := by
  cases second
  · cases current with
    | none =>
        cases right <;>
          simp [headSuffixGapShiftDescription, headSuffixGapShiftPairState,
            MachineDescription.runConfig, MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            transition, tapeAtCells, Tape.read, Tape.write, Tape.move,
            Tape.moveRight]
    | some currentBit =>
        cases currentBit <;> cases right <;>
          simp [headSuffixGapShiftDescription, headSuffixGapShiftPairState,
            MachineDescription.runConfig, MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            transition, tapeAtCells, Tape.read, Tape.write, Tape.move,
            Tape.moveRight]
  · cases current with
    | none =>
        cases right <;>
          simp [headSuffixGapShiftDescription, headSuffixGapShiftPairState,
            MachineDescription.runConfig, MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            transition, tapeAtCells, Tape.read, Tape.write, Tape.move,
            Tape.moveRight]
    | some currentBit =>
        cases currentBit <;> cases right <;>
          simp [headSuffixGapShiftDescription, headSuffixGapShiftPairState,
            MachineDescription.runConfig, MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            transition, tapeAtCells, Tape.read, Tape.write, Tape.move,
            Tape.moveRight]

theorem headSuffixGapShiftDescription_run_pairStep_some_false
    (second current : Option Bool)
    (left right : List (Option Bool)) :
    headSuffixGapShiftDescription.runConfig 1
        { state := headSuffixGapShiftPairState (some false) second
          tape := tapeAtCells left (current :: right) } =
      { state := headSuffixGapShiftPairState second current
        tape := tapeAtCells (some false :: left) right } := by
  cases second with
  | none =>
      cases current with
      | none =>
          cases right <;>
            simp [headSuffixGapShiftDescription, headSuffixGapShiftPairState,
              MachineDescription.runConfig, MachineDescription.stepConfig,
              MachineDescription.lookupTransition, MachineDescription.Matches,
              transition, tapeAtCells, Tape.read, Tape.write, Tape.move,
              Tape.moveRight]
      | some currentBit =>
          cases currentBit <;> cases right <;>
            simp [headSuffixGapShiftDescription, headSuffixGapShiftPairState,
              MachineDescription.runConfig, MachineDescription.stepConfig,
              MachineDescription.lookupTransition, MachineDescription.Matches,
              transition, tapeAtCells, Tape.read, Tape.write, Tape.move,
              Tape.moveRight]
  | some secondBit =>
      cases secondBit
      · cases current with
        | none =>
            cases right <;>
              simp [headSuffixGapShiftDescription, headSuffixGapShiftPairState,
                MachineDescription.runConfig, MachineDescription.stepConfig,
                MachineDescription.lookupTransition, MachineDescription.Matches,
                transition, tapeAtCells, Tape.read, Tape.write, Tape.move,
                Tape.moveRight]
        | some currentBit =>
            cases currentBit <;> cases right <;>
              simp [headSuffixGapShiftDescription, headSuffixGapShiftPairState,
                MachineDescription.runConfig, MachineDescription.stepConfig,
                MachineDescription.lookupTransition, MachineDescription.Matches,
                transition, tapeAtCells, Tape.read, Tape.write, Tape.move,
                Tape.moveRight]
      · cases current with
        | none =>
            cases right <;>
              simp [headSuffixGapShiftDescription, headSuffixGapShiftPairState,
                MachineDescription.runConfig, MachineDescription.stepConfig,
                MachineDescription.lookupTransition, MachineDescription.Matches,
                transition, tapeAtCells, Tape.read, Tape.write, Tape.move,
                Tape.moveRight]
        | some currentBit =>
            cases currentBit <;> cases right <;>
              simp [headSuffixGapShiftDescription, headSuffixGapShiftPairState,
                MachineDescription.runConfig, MachineDescription.stepConfig,
                MachineDescription.lookupTransition, MachineDescription.Matches,
                transition, tapeAtCells, Tape.read, Tape.write, Tape.move,
                Tape.moveRight]

theorem headSuffixGapShiftDescription_run_pairStep_some_true
    (second current : Option Bool)
    (left right : List (Option Bool)) :
    headSuffixGapShiftDescription.runConfig 1
        { state := headSuffixGapShiftPairState (some true) second
          tape := tapeAtCells left (current :: right) } =
      { state := headSuffixGapShiftPairState second current
        tape := tapeAtCells (some true :: left) right } := by
  cases second with
  | none =>
      cases current with
      | none =>
          cases right <;>
            simp [headSuffixGapShiftDescription, headSuffixGapShiftPairState,
              MachineDescription.runConfig, MachineDescription.stepConfig,
              MachineDescription.lookupTransition, MachineDescription.Matches,
              transition, tapeAtCells, Tape.read, Tape.write, Tape.move,
              Tape.moveRight]
      | some currentBit =>
          cases currentBit <;> cases right <;>
            simp [headSuffixGapShiftDescription, headSuffixGapShiftPairState,
              MachineDescription.runConfig, MachineDescription.stepConfig,
              MachineDescription.lookupTransition, MachineDescription.Matches,
              transition, tapeAtCells, Tape.read, Tape.write, Tape.move,
              Tape.moveRight]
  | some secondBit =>
      cases secondBit
      · cases current with
        | none =>
            cases right <;>
              simp [headSuffixGapShiftDescription, headSuffixGapShiftPairState,
                MachineDescription.runConfig, MachineDescription.stepConfig,
                MachineDescription.lookupTransition, MachineDescription.Matches,
                transition, tapeAtCells, Tape.read, Tape.write, Tape.move,
                Tape.moveRight]
        | some currentBit =>
            cases currentBit <;> cases right <;>
              simp [headSuffixGapShiftDescription, headSuffixGapShiftPairState,
                MachineDescription.runConfig, MachineDescription.stepConfig,
                MachineDescription.lookupTransition, MachineDescription.Matches,
                transition, tapeAtCells, Tape.read, Tape.write, Tape.move,
                Tape.moveRight]
      · cases current with
        | none =>
            cases right <;>
              simp [headSuffixGapShiftDescription, headSuffixGapShiftPairState,
                MachineDescription.runConfig, MachineDescription.stepConfig,
                MachineDescription.lookupTransition, MachineDescription.Matches,
                transition, tapeAtCells, Tape.read, Tape.write, Tape.move,
                Tape.moveRight]
        | some currentBit =>
            cases currentBit <;> cases right <;>
              simp [headSuffixGapShiftDescription, headSuffixGapShiftPairState,
                MachineDescription.runConfig, MachineDescription.stepConfig,
                MachineDescription.lookupTransition, MachineDescription.Matches,
                transition, tapeAtCells, Tape.read, Tape.write, Tape.move,
                Tape.moveRight]

theorem headSuffixGapShiftDescription_run_pairStep_some
    (first : Bool) (second current : Option Bool)
    (left right : List (Option Bool)) :
    headSuffixGapShiftDescription.runConfig 1
        { state := headSuffixGapShiftPairState (some first) second
          tape := tapeAtCells left (current :: right) } =
      { state := headSuffixGapShiftPairState second current
        tape := tapeAtCells (some first :: left) right } := by
  cases first
  · exact headSuffixGapShiftDescription_run_pairStep_some_false
      second current left right
  · exact headSuffixGapShiftDescription_run_pairStep_some_true
      second current left right

theorem headSuffixGapShiftDescription_run_pairStep
    (first second current : Option Bool)
    (hactive : first ≠ none ∨ second ≠ none ∨ current ≠ none)
    (left right : List (Option Bool)) :
    headSuffixGapShiftDescription.runConfig 1
        { state := headSuffixGapShiftPairState first second
          tape := tapeAtCells left (current :: right) } =
      { state := headSuffixGapShiftPairState second current
        tape := tapeAtCells (first :: left) right } := by
  cases first with
  | none =>
      cases second with
      | none =>
          cases current with
          | none =>
              simp at hactive
          | some currentBit =>
              exact headSuffixGapShiftDescription_run_pairStep_none_none_bit
                currentBit left right
      | some secondBit =>
          exact headSuffixGapShiftDescription_run_pairStep_none_some
            secondBit current left right
  | some firstBit =>
      exact headSuffixGapShiftDescription_run_pairStep_some
        firstBit second current left right

theorem headSuffixGapShiftDescription_run_pairStep_nil
    (first second : Option Bool)
    (hactive : first ≠ none ∨ second ≠ none)
    (left : List (Option Bool)) :
    headSuffixGapShiftDescription.runConfig 1
        { state := headSuffixGapShiftPairState first second
          tape := tapeAtCells left [] } =
      { state := headSuffixGapShiftPairState second none
        tape := tapeAtCells (first :: left) [] } := by
  have hactive' : first ≠ none ∨ second ≠ none ∨ (none : Option Bool) ≠ none := by
    cases hactive with
    | inl hfirst => exact Or.inl hfirst
    | inr hsecond => exact Or.inr (Or.inl hsecond)
  simpa [tapeAtCells] using
    headSuffixGapShiftDescription_run_pairStep first second none hactive'
      left []

def headSuffixGapShiftLoopPair
    (first second : Option Bool) :
    List (Option Bool) -> Option Bool × Option Bool
  | [] => (first, second)
  | current :: rest =>
      headSuffixGapShiftLoopPair second current rest

def headSuffixGapShiftLoopWrittenRev
    (first second : Option Bool) :
    List (Option Bool) -> List (Option Bool)
  | [] => []
  | current :: rest =>
      List.append
        (headSuffixGapShiftLoopWrittenRev second current rest)
        [first]

def headSuffixGapShiftLoopActive
    (first second : Option Bool) :
    List (Option Bool) -> Prop
  | [] => True
  | current :: rest =>
      (first ≠ none ∨ second ≠ none ∨ current ≠ none) ∧
        headSuffixGapShiftLoopActive second current rest

theorem headSuffixGapShiftLoopPair_append
    (first second : Option Bool)
    (left right : List (Option Bool)) :
    headSuffixGapShiftLoopPair first second (List.append left right) =
      headSuffixGapShiftLoopPair
        (headSuffixGapShiftLoopPair first second left).1
        (headSuffixGapShiftLoopPair first second left).2
        right := by
  induction left generalizing first second with
  | nil =>
      rfl
  | cons current rest ih =>
      exact ih second current

theorem headSuffixGapShiftLoopWrittenRev_append
    (first second : Option Bool)
    (left right : List (Option Bool)) :
    headSuffixGapShiftLoopWrittenRev first second (List.append left right) =
      List.append
        (headSuffixGapShiftLoopWrittenRev
          (headSuffixGapShiftLoopPair first second left).1
          (headSuffixGapShiftLoopPair first second left).2
          right)
        (headSuffixGapShiftLoopWrittenRev first second left) := by
  induction left generalizing first second with
  | nil =>
      simp [headSuffixGapShiftLoopPair, headSuffixGapShiftLoopWrittenRev]
  | cons current rest ih =>
      change
        List.append
            (headSuffixGapShiftLoopWrittenRev second current
              (List.append rest right))
            [first] =
          List.append
            (headSuffixGapShiftLoopWrittenRev
              (headSuffixGapShiftLoopPair second current rest).1
              (headSuffixGapShiftLoopPair second current rest).2
              right)
            (List.append
              (headSuffixGapShiftLoopWrittenRev second current rest)
              [first])
      rw [ih second current]
      simp [List.append_assoc]

theorem headSuffixGapShiftLoopActive_append
    (first second : Option Bool)
    (left right : List (Option Bool)) :
    headSuffixGapShiftLoopActive first second (List.append left right) ↔
      headSuffixGapShiftLoopActive first second left ∧
        headSuffixGapShiftLoopActive
          (headSuffixGapShiftLoopPair first second left).1
          (headSuffixGapShiftLoopPair first second left).2
          right := by
  induction left generalizing first second with
  | nil =>
      simp [headSuffixGapShiftLoopActive, headSuffixGapShiftLoopPair]
  | cons current rest ih =>
      change
        ((first ≠ none ∨ second ≠ none ∨ current ≠ none) ∧
            headSuffixGapShiftLoopActive second current
              (List.append rest right)) ↔
          ((first ≠ none ∨ second ≠ none ∨ current ≠ none) ∧
              headSuffixGapShiftLoopActive second current rest) ∧
            headSuffixGapShiftLoopActive
              (headSuffixGapShiftLoopPair second current rest).1
              (headSuffixGapShiftLoopPair second current rest).2
              right
      rw [ih second current]
      simp [and_assoc]

theorem headSuffixGapShiftLoopActive_second_some_mapSome_append_none
    (first : Option Bool) (second : Bool) (bits : Word Bool) :
    headSuffixGapShiftLoopActive first (some second)
      (List.append (bits.map some) [none]) := by
  induction bits generalizing first second with
  | nil =>
      simp [headSuffixGapShiftLoopActive]
  | cons bit rest ih =>
      simp [headSuffixGapShiftLoopActive]
      exact ih (some second) bit

theorem headSuffixGapShiftLoopPair_second_some_mapSome_append_none_second
    (first : Option Bool) (second : Bool) (bits : Word Bool) :
    (headSuffixGapShiftLoopPair first (some second)
      (List.append (bits.map some) [none])).2 = none := by
  induction bits generalizing first second with
  | nil =>
      simp [headSuffixGapShiftLoopPair]
  | cons bit rest ih =>
      simpa [headSuffixGapShiftLoopPair] using ih (some second) bit

theorem headSuffixGapShiftLoopPair_second_some_mapSome_append_none_first_ne
    (first : Option Bool) (second : Bool) (bits : Word Bool) :
    (headSuffixGapShiftLoopPair first (some second)
      (List.append (bits.map some) [none])).1 ≠ none := by
  induction bits generalizing first second with
  | nil =>
      simp [headSuffixGapShiftLoopPair]
  | cons bit rest ih =>
      simpa [headSuffixGapShiftLoopPair] using ih (some second) bit

theorem headSuffixGapShiftLoopActive_first_none_cons_mapSome_append_none
    (first : Option Bool) (bit : Bool) (bits : Word Bool) :
    headSuffixGapShiftLoopActive first none
      (some bit :: List.append (bits.map some) [none]) := by
  simp [headSuffixGapShiftLoopActive]
  exact
    headSuffixGapShiftLoopActive_second_some_mapSome_append_none
      none bit bits

theorem headSuffixGapShiftLoopPair_first_none_cons_mapSome_append_none_second
    (first : Option Bool) (bit : Bool) (bits : Word Bool) :
    (headSuffixGapShiftLoopPair first none
      (some bit :: List.append (bits.map some) [none])).2 = none := by
  simpa [headSuffixGapShiftLoopPair] using
    headSuffixGapShiftLoopPair_second_some_mapSome_append_none_second
      none bit bits

theorem headSuffixGapShiftLoopPair_first_none_cons_mapSome_append_none_first_ne
    (first : Option Bool) (bit : Bool) (bits : Word Bool) :
    (headSuffixGapShiftLoopPair first none
      (some bit :: List.append (bits.map some) [none])).1 ≠ none := by
  simpa [headSuffixGapShiftLoopPair] using
    headSuffixGapShiftLoopPair_second_some_mapSome_append_none_first_ne
      none bit bits

def encodedStructuredTapeCellsTail :
    List (Tape Bool) -> List (Option Bool)
  | [] => []
  | T :: rest =>
      List.append (logicalTapeCode T)
        (encodedStructuredTapeCells rest)

theorem encodedStructuredTapeCells_eq_cons_tail
    (logical : List (Tape Bool)) :
    encodedStructuredTapeCells logical =
      none :: encodedStructuredTapeCellsTail logical := by
  cases logical with
  | nil =>
      rfl
  | cons T rest =>
      rfl

theorem headSuffixGapShiftLoopReady_encodedStructuredTapeCellsTail
    (logical : List (Tape Bool)) (first : Option Bool)
    (hfirst : first ≠ none) :
    headSuffixGapShiftLoopActive first none
        (encodedStructuredTapeCellsTail logical) ∧
      (headSuffixGapShiftLoopPair first none
        (encodedStructuredTapeCellsTail logical)).1 ≠ none ∧
      (headSuffixGapShiftLoopPair first none
        (encodedStructuredTapeCellsTail logical)).2 = none := by
  induction logical generalizing first with
  | nil =>
      simp [encodedStructuredTapeCellsTail, headSuffixGapShiftLoopActive,
        headSuffixGapShiftLoopPair, hfirst]
  | cons T rest ih =>
      rcases logicalTapeBits_exists_cons T with ⟨bit, bits, hbits⟩
      let segment : List (Option Bool) :=
        some bit :: List.append (bits.map some) [none]
      have htail :
          encodedStructuredTapeCellsTail (T :: rest) =
            List.append segment (encodedStructuredTapeCellsTail rest) := by
        change
          List.append (logicalTapeCode T) (encodedStructuredTapeCells rest) =
            List.append segment (encodedStructuredTapeCellsTail rest)
        rw [logicalTapeCode_eq_map_some, hbits,
          encodedStructuredTapeCells_eq_cons_tail rest]
        simp [segment, List.append_assoc]
      have hsegActive :
          headSuffixGapShiftLoopActive first none segment := by
        simpa [segment] using
          headSuffixGapShiftLoopActive_first_none_cons_mapSome_append_none
            first bit bits
      have hsegFirst :
          (headSuffixGapShiftLoopPair first none segment).1 ≠ none := by
        simpa [segment] using
          headSuffixGapShiftLoopPair_first_none_cons_mapSome_append_none_first_ne
            first bit bits
      have hsegSecond :
          (headSuffixGapShiftLoopPair first none segment).2 = none := by
        simpa [segment] using
          headSuffixGapShiftLoopPair_first_none_cons_mapSome_append_none_second
            first bit bits
      have hrestReady :=
        ih (first := (headSuffixGapShiftLoopPair first none segment).1)
          hsegFirst
      constructor
      · rw [htail, headSuffixGapShiftLoopActive_append]
        refine ⟨hsegActive, ?_⟩
        simpa [hsegSecond] using hrestReady.1
      · constructor
        · rw [htail, headSuffixGapShiftLoopPair_append]
          simpa [hsegSecond] using hrestReady.2.1
        · rw [htail, headSuffixGapShiftLoopPair_append]
          simpa [hsegSecond] using hrestReady.2.2

theorem headSuffixGapShiftLoopReady_encodedStructuredTapeCellsTail_start
    (T : Tape Bool) (rest : List (Tape Bool)) :
    exists current : Option Bool, exists cells : List (Option Bool),
      encodedStructuredTapeCellsTail (T :: rest) = current :: cells ∧
        headSuffixGapShiftLoopActive none current cells ∧
          (headSuffixGapShiftLoopPair none current cells).1 ≠ none ∧
          (headSuffixGapShiftLoopPair none current cells).2 = none := by
  rcases logicalTapeBits_exists_cons T with ⟨bit, bits, hbits⟩
  let segmentTail : List (Option Bool) :=
    List.append (bits.map some) [none]
  let cells : List (Option Bool) :=
    List.append segmentTail (encodedStructuredTapeCellsTail rest)
  refine ⟨some bit, cells, ?_, ?_⟩
  · change
      List.append (logicalTapeCode T) (encodedStructuredTapeCells rest) =
        some bit :: cells
    rw [logicalTapeCode_eq_map_some, hbits,
      encodedStructuredTapeCells_eq_cons_tail rest]
    simp [cells, segmentTail, List.append_assoc]
  · have hsegActive :
        headSuffixGapShiftLoopActive none (some bit) segmentTail := by
      simpa [segmentTail] using
        headSuffixGapShiftLoopActive_second_some_mapSome_append_none
          none bit bits
    have hsegFirst :
        (headSuffixGapShiftLoopPair none (some bit) segmentTail).1 ≠
          none := by
      simpa [segmentTail] using
        headSuffixGapShiftLoopPair_second_some_mapSome_append_none_first_ne
          none bit bits
    have hsegSecond :
        (headSuffixGapShiftLoopPair none (some bit) segmentTail).2 =
          none := by
      simpa [segmentTail] using
        headSuffixGapShiftLoopPair_second_some_mapSome_append_none_second
          none bit bits
    have hrestReady :=
      headSuffixGapShiftLoopReady_encodedStructuredTapeCellsTail rest
        (headSuffixGapShiftLoopPair none (some bit) segmentTail).1
        hsegFirst
    constructor
    · rw [show cells =
          List.append segmentTail (encodedStructuredTapeCellsTail rest) by rfl]
      rw [headSuffixGapShiftLoopActive_append]
      refine ⟨hsegActive, ?_⟩
      simpa [hsegSecond] using hrestReady.1
    · constructor
      · rw [show cells =
            List.append segmentTail (encodedStructuredTapeCellsTail rest) by rfl]
        rw [headSuffixGapShiftLoopPair_append]
        simpa [hsegSecond] using hrestReady.2.1
      · rw [show cells =
            List.append segmentTail (encodedStructuredTapeCellsTail rest) by rfl]
        rw [headSuffixGapShiftLoopPair_append]
        simpa [hsegSecond] using hrestReady.2.2

theorem headSuffixGapShiftDescription_run_pairLoop
    (cells tail left : List (Option Bool))
    (first second : Option Bool)
    (hactive : headSuffixGapShiftLoopActive first second cells) :
    headSuffixGapShiftDescription.runConfig cells.length
        { state := headSuffixGapShiftPairState first second
          tape := tapeAtCells left (List.append cells tail) } =
      { state :=
          headSuffixGapShiftPairState
            (headSuffixGapShiftLoopPair first second cells).1
            (headSuffixGapShiftLoopPair first second cells).2
        tape :=
          tapeAtCells
            (List.append
              (headSuffixGapShiftLoopWrittenRev first second cells) left)
            tail } := by
  induction cells generalizing first second left with
  | nil =>
      simp [MachineDescription.runConfig, headSuffixGapShiftLoopPair,
        headSuffixGapShiftLoopWrittenRev]
  | cons current rest ih =>
      rcases hactive with ⟨hstepActive, hrestActive⟩
      rw [show (current :: rest).length = 1 + rest.length by
        simp [Nat.add_comm]]
      rw [MachineDescription.runConfig_add]
      change
        headSuffixGapShiftDescription.runConfig rest.length
            (headSuffixGapShiftDescription.runConfig 1
              { state := headSuffixGapShiftPairState first second
                tape := tapeAtCells left (current :: List.append rest tail) }) =
          { state :=
              headSuffixGapShiftPairState
                (headSuffixGapShiftLoopPair first second (current :: rest)).1
                (headSuffixGapShiftLoopPair first second (current :: rest)).2
            tape :=
              tapeAtCells
                (List.append
                  (headSuffixGapShiftLoopWrittenRev first second
                    (current :: rest)) left)
                tail }
      rw [headSuffixGapShiftDescription_run_pairStep first second current
        hstepActive left (List.append rest tail)]
      simpa [headSuffixGapShiftLoopPair, headSuffixGapShiftLoopWrittenRev,
        List.append_assoc] using
        ih (first := second) (second := current) (left := first :: left)
          hrestActive

theorem headSuffixGapShiftDescription_run_pairHalt
    (left right : List (Option Bool)) :
    headSuffixGapShiftDescription.runConfig 1
        { state := headSuffixGapShiftPairState none none
          tape := tapeAtCells left (none :: right) } =
      { state := headSuffixGapShiftHalt
        tape := Tape.move Direction.left (tapeAtCells left (none :: right)) } := by
  cases left <;> cases right <;>
    simp [headSuffixGapShiftDescription, headSuffixGapShiftPairState,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      transition, tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft]

theorem headSuffixGapShiftDescription_run_pairHalt_nil
    (left : List (Option Bool)) :
    headSuffixGapShiftDescription.runConfig 1
        { state := headSuffixGapShiftPairState none none
          tape := tapeAtCells left [] } =
      { state := headSuffixGapShiftHalt
        tape := Tape.move Direction.left (tapeAtCells left []) } := by
  cases left <;>
    simp [headSuffixGapShiftDescription, headSuffixGapShiftPairState,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      transition, tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft]

theorem headSuffixGapShiftDescription_run_pairHalt_cons
    (cell : Option Bool) (left right : List (Option Bool)) :
    headSuffixGapShiftDescription.runConfig 1
        { state := headSuffixGapShiftPairState none none
          tape := tapeAtCells (cell :: left) (none :: right) } =
      { state := headSuffixGapShiftHalt
        tape := tapeAtCells left (cell :: none :: right) } := by
  simpa [Tape.move, Tape.moveLeft, tapeAtCells] using
    headSuffixGapShiftDescription_run_pairHalt (cell :: left) right

theorem headSuffixGapShiftDescription_run_pairLoop_then_halt_nil
    (cells left : List (Option Bool))
    (first second : Option Bool)
    (hactive : headSuffixGapShiftLoopActive first second cells)
    (hfirst :
      (headSuffixGapShiftLoopPair first second cells).1 = none)
    (hsecond :
      (headSuffixGapShiftLoopPair first second cells).2 = none) :
    headSuffixGapShiftDescription.runConfig (cells.length + 1)
        { state := headSuffixGapShiftPairState first second
          tape := tapeAtCells left cells } =
      { state := headSuffixGapShiftHalt
        tape :=
          Tape.move Direction.left
            (tapeAtCells
              (List.append
                (headSuffixGapShiftLoopWrittenRev first second cells)
                left)
              []) } := by
  rw [MachineDescription.runConfig_add]
  rw [show tapeAtCells left cells =
      tapeAtCells left (List.append cells []) by simp]
  rw [headSuffixGapShiftDescription_run_pairLoop cells [] left first second
    hactive]
  rw [hfirst, hsecond]
  exact
    headSuffixGapShiftDescription_run_pairHalt_nil
      (List.append
        (headSuffixGapShiftLoopWrittenRev first second cells) left)

theorem headSuffixGapShiftDescription_run_pairLoop_then_implicitStep_halt_nil
    (cells left : List (Option Bool))
    (first second : Option Bool)
    (hactive : headSuffixGapShiftLoopActive first second cells)
    (hfirst :
      (headSuffixGapShiftLoopPair first second cells).1 ≠ none)
    (hsecond :
      (headSuffixGapShiftLoopPair first second cells).2 = none) :
    headSuffixGapShiftDescription.runConfig (cells.length + 2)
        { state := headSuffixGapShiftPairState first second
          tape := tapeAtCells left cells } =
      { state := headSuffixGapShiftHalt
        tape :=
          Tape.move Direction.left
            (tapeAtCells
              ((headSuffixGapShiftLoopPair first second cells).1 ::
                List.append
                  (headSuffixGapShiftLoopWrittenRev first second cells)
                  left)
              []) } := by
  rw [show cells.length + 2 = cells.length + (1 + 1) by lia]
  rw [MachineDescription.runConfig_add]
  rw [show tapeAtCells left cells =
      tapeAtCells left (List.append cells []) by simp]
  rw [headSuffixGapShiftDescription_run_pairLoop cells [] left first second
    hactive]
  rw [hsecond]
  rw [MachineDescription.runConfig_add]
  rw [headSuffixGapShiftDescription_run_pairStep_nil
    (headSuffixGapShiftLoopPair first second cells).1 none
    (Or.inl hfirst)
    (List.append
      (headSuffixGapShiftLoopWrittenRev first second cells) left)]
  exact
    headSuffixGapShiftDescription_run_pairHalt_nil
      ((headSuffixGapShiftLoopPair first second cells).1 ::
        List.append
          (headSuffixGapShiftLoopWrittenRev first second cells) left)

theorem headSuffixGapShiftDescription_run_boundaryLoop_then_halt_nil
    (current : Option Bool) (cells left : List (Option Bool))
    (hactive : headSuffixGapShiftLoopActive none current cells)
    (hfirst :
      (headSuffixGapShiftLoopPair none current cells).1 = none)
    (hsecond :
      (headSuffixGapShiftLoopPair none current cells).2 = none) :
    headSuffixGapShiftDescription.runConfig (cells.length + 2)
        { state := 2
          tape := tapeAtCells left (current :: cells) } =
      { state := headSuffixGapShiftHalt
        tape :=
          Tape.move Direction.left
            (tapeAtCells
              (List.append
                (headSuffixGapShiftLoopWrittenRev none current cells)
                (none :: left))
              []) } := by
  rw [show cells.length + 2 = 1 + (cells.length + 1) by lia]
  rw [MachineDescription.runConfig_add]
  rw [headSuffixGapShiftDescription_run_boundaryStep current left cells]
  exact
    headSuffixGapShiftDescription_run_pairLoop_then_halt_nil
      cells (none :: left) none current hactive hfirst hsecond

theorem headSuffixGapShiftDescription_run_boundaryLoop_then_implicitStep_halt_nil
    (current : Option Bool) (cells left : List (Option Bool))
    (hactive : headSuffixGapShiftLoopActive none current cells)
    (hfirst :
      (headSuffixGapShiftLoopPair none current cells).1 ≠ none)
    (hsecond :
      (headSuffixGapShiftLoopPair none current cells).2 = none) :
    headSuffixGapShiftDescription.runConfig (cells.length + 3)
        { state := 2
          tape := tapeAtCells left (current :: cells) } =
      { state := headSuffixGapShiftHalt
        tape :=
          Tape.move Direction.left
            (tapeAtCells
              ((headSuffixGapShiftLoopPair none current cells).1 ::
                List.append
                  (headSuffixGapShiftLoopWrittenRev none current cells)
                  (none :: left))
              []) } := by
  rw [show cells.length + 3 = 1 + (cells.length + 2) by lia]
  rw [MachineDescription.runConfig_add]
  rw [headSuffixGapShiftDescription_run_boundaryStep current left cells]
  exact
    headSuffixGapShiftDescription_run_pairLoop_then_implicitStep_halt_nil
      cells (none :: left) none current hactive hfirst hsecond

theorem headSuffixGapShiftDescription_run_boundary_encodedTail_nil
    (left : List (Option Bool)) :
    headSuffixGapShiftDescription.runConfig 2
        { state := 2
          tape := tapeAtCells left (encodedStructuredTapeCellsTail []) } =
      { state := headSuffixGapShiftHalt
        tape :=
          Tape.move Direction.left
            (tapeAtCells (none :: left) []) } := by
  rw [show 2 = 1 + 1 by rfl]
  rw [MachineDescription.runConfig_add]
  simp [encodedStructuredTapeCellsTail]
  rw [headSuffixGapShiftDescription_run_boundaryStep_nil]
  exact headSuffixGapShiftDescription_run_pairHalt_nil (none :: left)

theorem headSuffixGapShiftDescription_run_boundary_encodedTail_cons
    (T : Tape Bool) (rest : List (Tape Bool))
    (left : List (Option Bool)) :
    exists current : Option Bool, exists cells : List (Option Bool),
      encodedStructuredTapeCellsTail (T :: rest) = current :: cells ∧
        headSuffixGapShiftDescription.runConfig (cells.length + 3)
          { state := 2
            tape :=
              tapeAtCells left
                (encodedStructuredTapeCellsTail (T :: rest)) } =
          { state := headSuffixGapShiftHalt
            tape :=
              Tape.move Direction.left
                (tapeAtCells
                  ((headSuffixGapShiftLoopPair none current cells).1 ::
                    List.append
                      (headSuffixGapShiftLoopWrittenRev none current cells)
                      (none :: left))
                  []) } := by
  rcases headSuffixGapShiftLoopReady_encodedStructuredTapeCellsTail_start
      T rest with
    ⟨current, cells, htail, hactive, hfirst, hsecond⟩
  refine ⟨current, cells, htail, ?_⟩
  rw [htail]
  exact
    headSuffixGapShiftDescription_run_boundaryLoop_then_implicitStep_halt_nil
      current cells left hactive hfirst hsecond

theorem headSuffixGapShiftDescription_run_opening
    (bits : Word Bool) (suffixTail : List (Option Bool)) :
    headSuffixGapShiftDescription.runConfig 1
        { state := headSuffixGapShiftDescription.start
          tape :=
            tapeAtCells []
              (none :: List.append (bits.map some)
                (none :: suffixTail)) } =
      { state := 1
        tape :=
          tapeAtCells [none]
            (List.append (bits.map some) (none :: suffixTail)) } := by
  cases bits <;> cases suffixTail <;>
    simp [headSuffixGapShiftDescription, MachineDescription.runConfig,
      MachineDescription.stepConfig, MachineDescription.lookupTransition,
      MachineDescription.Matches, transition, tapeAtCells, Tape.read, Tape.write,
      Tape.move, Tape.moveRight]

theorem headSuffixGapShiftDescription_run_payloadScan
    (bits processed : Word Bool) (leftBase suffixTail : List (Option Bool)) :
    headSuffixGapShiftDescription.runConfig bits.length
        { state := 1
          tape :=
            tapeAtCells
              (List.append (processed.reverse.map some) leftBase)
              (List.append (bits.map some) (none :: suffixTail)) } =
      { state := 1
        tape :=
          tapeAtCells
            (List.append ((List.append processed bits).reverse.map some)
              leftBase)
            (none :: suffixTail) } := by
  induction bits generalizing processed with
  | nil =>
      simp [MachineDescription.runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp [Nat.add_comm]]
      rw [MachineDescription.runConfig_add]
      have hstep :
          headSuffixGapShiftDescription.runConfig 1
              { state := 1
                tape :=
                  tapeAtCells
                    (List.append (processed.reverse.map some) leftBase)
                    (List.append ((bit :: rest).map some)
                      (none :: suffixTail)) } =
            { state := 1
              tape :=
                tapeAtCells
                  (some bit ::
                    List.append (processed.reverse.map some) leftBase)
                  (List.append (rest.map some) (none :: suffixTail)) } := by
        cases bit <;> cases rest <;> cases suffixTail <;>
          simp [headSuffixGapShiftDescription,
            MachineDescription.runConfig, MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            transition, tapeAtCells, Tape.read, Tape.write, Tape.move,
            Tape.moveRight]
      rw [hstep]
      simpa [List.reverse_append, List.map_append, List.append_assoc]
        using ih (List.append processed [bit])

theorem headSuffixGapShiftDescription_run_to_boundary
    (bits : Word Bool) (suffixTail : List (Option Bool)) :
    headSuffixGapShiftDescription.runConfig (bits.length + 2)
        { state := headSuffixGapShiftDescription.start
          tape :=
            tapeAtCells []
              (none :: List.append (bits.map some)
                (none :: suffixTail)) } =
      { state := 2
        tape :=
          tapeAtCells
            (none :: List.append (bits.reverse.map some) [none])
            suffixTail } := by
  rw [show bits.length + 2 = 1 + (bits.length + 1) by lia]
  rw [MachineDescription.runConfig_add]
  rw [headSuffixGapShiftDescription_run_opening]
  rw [show bits.length + 1 = bits.length + 1 by rfl]
  rw [MachineDescription.runConfig_add]
  have hscan :
      headSuffixGapShiftDescription.runConfig bits.length
          { state := 1
            tape :=
              tapeAtCells [none]
                (List.append (bits.map some) (none :: suffixTail)) } =
        { state := 1
          tape :=
            tapeAtCells
              (List.append (bits.reverse.map some) [none])
              (none :: suffixTail) } := by
    simpa using
      headSuffixGapShiftDescription_run_payloadScan bits [] [none]
        suffixTail
  rw [hscan]
  cases suffixTail <;>
    simp [headSuffixGapShiftDescription, MachineDescription.runConfig,
      MachineDescription.stepConfig, MachineDescription.lookupTransition,
      MachineDescription.Matches, transition, tapeAtCells, Tape.read, Tape.write,
      Tape.move, Tape.moveRight]

theorem headSuffixGapShiftDescription_run_to_encodedTailBoundary
    (bits : Word Bool) (rest : List (Tape Bool)) :
    headSuffixGapShiftDescription.runConfig (bits.length + 2)
        { state := headSuffixGapShiftDescription.start
          tape := encodedStructuredHeadPayloadTapes bits rest } =
      { state := 2
        tape :=
          tapeAtCells
            (none :: List.append (bits.reverse.map some) [none])
            (encodedStructuredTapeCellsTail rest) } := by
  rw [encodedStructuredHeadPayloadTapes,
    encodedStructuredTapeCells_eq_cons_tail rest]
  simpa [tapeSeparatorCells, List.append_assoc] using
    headSuffixGapShiftDescription_run_to_boundary bits
      (encodedStructuredTapeCellsTail rest)

theorem headSuffixGapShiftDescription_run_payload_emptyRest
    (bits : Word Bool) :
    headSuffixGapShiftDescription.runConfig (bits.length + 4)
        { state := headSuffixGapShiftDescription.start
          tape := encodedStructuredHeadPayloadTapes bits [] } =
      { state := headSuffixGapShiftHalt
        tape :=
          Tape.move Direction.left
            (tapeAtCells
              (none :: none :: List.append (bits.reverse.map some) [none])
              []) } := by
  rw [show bits.length + 4 = (bits.length + 2) + 2 by lia]
  rw [MachineDescription.runConfig_add]
  rw [headSuffixGapShiftDescription_run_to_encodedTailBoundary]
  exact
    headSuffixGapShiftDescription_run_boundary_encodedTail_nil
      (none :: List.append (bits.reverse.map some) [none])

theorem headSuffixGapShiftDescription_run_payload_cons
    (bits : Word Bool) (T : Tape Bool) (rest : List (Tape Bool)) :
    exists current : Option Bool, exists cells : List (Option Bool),
      encodedStructuredTapeCellsTail (T :: rest) = current :: cells ∧
        headSuffixGapShiftDescription.runConfig
          ((bits.length + 2) + (cells.length + 3))
          { state := headSuffixGapShiftDescription.start
            tape := encodedStructuredHeadPayloadTapes bits (T :: rest) } =
          { state := headSuffixGapShiftHalt
            tape :=
              Tape.move Direction.left
                (tapeAtCells
                  ((headSuffixGapShiftLoopPair none current cells).1 ::
                    List.append
                      (headSuffixGapShiftLoopWrittenRev none current cells)
                      (none :: none ::
                        List.append (bits.reverse.map some) [none]))
                  []) } := by
  rcases headSuffixGapShiftDescription_run_boundary_encodedTail_cons
      T rest (none :: List.append (bits.reverse.map some) [none]) with
    ⟨current, cells, htail, hrunTail⟩
  refine ⟨current, cells, htail, ?_⟩
  rw [MachineDescription.runConfig_add]
  rw [headSuffixGapShiftDescription_run_to_encodedTailBoundary]
  exact hrunTail

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC

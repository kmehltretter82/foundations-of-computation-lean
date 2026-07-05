import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.CursorBoundaryGap
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.FiniteMachineTactics

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
    machine_step [headSuffixGapShiftDescription]

theorem headSuffixGapShiftDescription_run_boundaryStep_bit
    (bit : Bool) (left right : List (Option Bool)) :
    headSuffixGapShiftDescription.runConfig 1
        { state := 2
          tape := tapeAtCells left (some bit :: right) } =
      { state := headSuffixGapShiftPairState none (some bit)
        tape := tapeAtCells (none :: left) right } := by
  cases bit <;> cases right <;>
    machine_step [headSuffixGapShiftDescription]

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

def encodedStructuredTapeCellsScanRev :
    List (Tape Bool) -> List (Option Bool)
  | [] => []
  | T :: [] => (logicalTapeBits T).reverse.map some
  | T :: U :: rest =>
      List.append
        (List.append (encodedStructuredTapeCellsScanRev (U :: rest))
          [none])
        ((logicalTapeBits T).reverse.map some)

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

theorem headSuffixGapShiftLoopWrittenRev_reverse_pair
    (first second : Option Bool) (cells : List (Option Bool)) :
    List.append
        (headSuffixGapShiftLoopWrittenRev first second cells).reverse
        [ (headSuffixGapShiftLoopPair first second cells).1
        , (headSuffixGapShiftLoopPair first second cells).2 ] =
      first :: second :: cells := by
  induction cells generalizing first second with
  | nil =>
      simp [headSuffixGapShiftLoopWrittenRev, headSuffixGapShiftLoopPair]
  | cons current rest ih =>
      simpa [headSuffixGapShiftLoopWrittenRev, headSuffixGapShiftLoopPair,
        List.append_assoc] using ih second current

theorem headSuffixGapShiftLoopOutputSuffix_eq_cons
    (current : Option Bool) (cells : List (Option Bool))
    (hsecond :
      (headSuffixGapShiftLoopPair none current cells).2 = none) :
    List.append
        (headSuffixGapShiftLoopWrittenRev none current cells).reverse
        [ (headSuffixGapShiftLoopPair none current cells).1, none ] =
      none :: current :: cells := by
  have h :=
    headSuffixGapShiftLoopWrittenRev_reverse_pair none current cells
  simpa [hsecond] using h

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
      machine_run [headSuffixGapShiftLoopPair,
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
      machine_run []
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

theorem headSuffixGapShiftDescription_payload_emptyRest_cells
    (bits : Word Bool) :
    Tape.cells
        (Tape.move Direction.left
          (tapeAtCells
            (none :: none :: List.append (bits.reverse.map some) [none])
            [])) =
      Tape.cells (encodedStructuredHeadPayloadGapTapes bits []) := by
  simp [encodedStructuredHeadPayloadGapTapes, encodedStructuredTapeCells,
    tapeSeparatorCells, tapeAtCells, Tape.cells, Tape.move, Tape.moveLeft,
    List.reverse_append, List.map_reverse, List.append_assoc]

theorem headSuffixGapShiftDescription_run_payload_emptyRest_cells
    (bits : Word Bool) :
    Tape.cells
        ((headSuffixGapShiftDescription.runConfig (bits.length + 4)
          { state := headSuffixGapShiftDescription.start
            tape := encodedStructuredHeadPayloadTapes bits [] }).tape) =
      Tape.cells (encodedStructuredHeadPayloadGapTapes bits []) := by
  rw [headSuffixGapShiftDescription_run_payload_emptyRest]
  exact headSuffixGapShiftDescription_payload_emptyRest_cells bits

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

theorem headSuffixGapShiftDescription_payload_cons_cells
    (bits : Word Bool) (T : Tape Bool) (rest : List (Tape Bool))
    (current : Option Bool) (cells : List (Option Bool))
    (htail : encodedStructuredTapeCellsTail (T :: rest) = current :: cells)
    (hsecond :
      (headSuffixGapShiftLoopPair none current cells).2 = none) :
    Tape.cells
        (Tape.move Direction.left
          (tapeAtCells
            ((headSuffixGapShiftLoopPair none current cells).1 ::
              List.append
                (headSuffixGapShiftLoopWrittenRev none current cells)
                (none :: none ::
                  List.append (bits.reverse.map some) [none]))
            [])) =
      Tape.cells (encodedStructuredHeadPayloadGapTapes bits (T :: rest)) := by
  have hsuffix :
      List.append
          (headSuffixGapShiftLoopWrittenRev none current cells).reverse
          [ (headSuffixGapShiftLoopPair none current cells).1, none ] =
        none :: current :: cells :=
    headSuffixGapShiftLoopOutputSuffix_eq_cons current cells hsecond
  rw [← htail] at hsuffix
  simpa [encodedStructuredHeadPayloadGapTapes,
    encodedStructuredTapeCells_eq_cons_tail, tapeSeparatorCells, tapeAtCells,
    Tape.cells, Tape.move, Tape.moveLeft, List.reverse_append,
    List.map_reverse, List.append_assoc] using hsuffix

theorem headSuffixGapShiftDescription_run_payload_cons_cells
    (bits : Word Bool) (T : Tape Bool) (rest : List (Tape Bool)) :
    exists current : Option Bool, exists cells : List (Option Bool),
      encodedStructuredTapeCellsTail (T :: rest) = current :: cells ∧
        Tape.cells
          ((headSuffixGapShiftDescription.runConfig
            ((bits.length + 2) + (cells.length + 3))
            { state := headSuffixGapShiftDescription.start
              tape := encodedStructuredHeadPayloadTapes bits (T :: rest) }).tape) =
          Tape.cells (encodedStructuredHeadPayloadGapTapes bits (T :: rest)) := by
  rcases headSuffixGapShiftLoopReady_encodedStructuredTapeCellsTail_start
      T rest with
    ⟨current, cells, htail, hactive, hfirst, hsecond⟩
  refine ⟨current, cells, htail, ?_⟩
  have hrunBoundary :=
    headSuffixGapShiftDescription_run_boundaryLoop_then_implicitStep_halt_nil
      current cells (none :: List.append (bits.reverse.map some) [none])
      hactive hfirst hsecond
  have hrun :
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
    rw [MachineDescription.runConfig_add]
    rw [headSuffixGapShiftDescription_run_to_encodedTailBoundary]
    rw [htail]
    exact hrunBoundary
  rw [hrun]
  exact
    headSuffixGapShiftDescription_payload_cons_cells
      bits T rest current cells htail hsecond

theorem word_exists_reverse_append_singleton_of_cons
    (head : Bool) (tail : Word Bool) :
    exists scanRev : Word Bool, exists current : Bool,
      head :: tail = List.append scanRev.reverse [current] := by
  induction tail generalizing head with
  | nil =>
      exact ⟨[], head, by simp⟩
  | cons next rest ih =>
      rcases ih next with ⟨scanRev, current, htail⟩
      refine ⟨List.append scanRev [head], current, ?_⟩
      simp [List.reverse_append, htail]

theorem optionList_eq_append_none_of_reverse_append_none_eq
    {xs ys : List (Option Bool)}
    (h :
      List.append xs.reverse [none] =
        none :: List.append ys.reverse [none]) :
    xs = List.append ys [none] := by
  have hrev := congrArg List.reverse h
  simpa [List.reverse_append, List.append_assoc] using hrev

theorem optionList_cons_eq_append_none_split
    {first : Option Bool} {rest scan : List (Option Bool)}
    (h : first :: rest = List.append scan [none])
    (hfirst : first ≠ none) :
    exists scanRest : List (Option Bool),
      scan = first :: scanRest ∧
        rest = List.append scanRest [none] := by
  cases scan with
  | nil =>
      simp at h
      exact False.elim (hfirst h.1)
  | cons head tail =>
      simp at h
      rcases h with ⟨hhead, htail⟩
      subst hhead
      exact ⟨tail, rfl, htail⟩

def headSuffixGapOpeningRewindHalt : Nat :=
  6

/--
Return from the shifted block's right side to the global opening separator.

The scanner moves left while counting consecutive blank cells.  Internal
structured separators are single blanks, and the inserted suffix gap contributes
three blanks, so four consecutive blanks identify the implicit blank region to
the left of the whole encoded block.  After seeing the fourth blank it moves
right three cells and halts on the opening separator.
-/
def headSuffixGapOpeningRewindDescription : MachineDescription where
  stateCount := 7
  start := 0
  halt := headSuffixGapOpeningRewindHalt
  transitions :=
    [ transition 0 none none Direction.left 1
    , transition 0 (some false) (some false) Direction.left 0
    , transition 0 (some true) (some true) Direction.left 0
    , transition 1 none none Direction.left 2
    , transition 1 (some false) (some false) Direction.left 0
    , transition 1 (some true) (some true) Direction.left 0
    , transition 2 none none Direction.left 3
    , transition 2 (some false) (some false) Direction.left 0
    , transition 2 (some true) (some true) Direction.left 0
    , transition 3 none none Direction.right 4
    , transition 3 (some false) (some false) Direction.left 0
    , transition 3 (some true) (some true) Direction.left 0
    , transition 4 none none Direction.right 5
    , transition 5 none none Direction.right headSuffixGapOpeningRewindHalt ]

theorem headSuffixGapOpeningRewindDescription_wellFormed :
    headSuffixGapOpeningRewindDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := headSuffixGapOpeningRewindDescription.transitions)
      (stateCount := headSuffixGapOpeningRewindDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := headSuffixGapOpeningRewindDescription.transitions)
      (by decide)

theorem headSuffixGapOpeningRewindDescription_haltTransitionFree :
    headSuffixGapOpeningRewindDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := headSuffixGapOpeningRewindDescription.transitions)
    (state := headSuffixGapOpeningRewindDescription.halt)
    (by decide)

theorem headSuffixGapOpeningRewindDescription_subroutineReady :
    headSuffixGapOpeningRewindDescription.SubroutineReady :=
  ⟨headSuffixGapOpeningRewindDescription_wellFormed,
    headSuffixGapOpeningRewindDescription_haltTransitionFree⟩

def headSuffixGapOpeningRewindScanNext
    (state : Nat) : Option Bool -> Nat
  | some _ => headSuffixGapOpeningRewindDescription.start
  | none =>
      match state with
      | 0 => 1
      | 1 => 2
      | 2 => 3
      | _ => 4

def headSuffixGapOpeningRewindScanState
    (state : Nat) : List (Option Bool) -> Nat
  | [] => state
  | current :: rest =>
      headSuffixGapOpeningRewindScanState
        (headSuffixGapOpeningRewindScanNext state current) rest

def headSuffixGapOpeningRewindScanSafe
    (state : Nat) : List (Option Bool) -> Prop
  | [] => True
  | none :: rest =>
      state ≠ 3 ∧
        headSuffixGapOpeningRewindScanSafe
          (headSuffixGapOpeningRewindScanNext state none) rest
  | some bit :: rest =>
      headSuffixGapOpeningRewindScanSafe
        (headSuffixGapOpeningRewindScanNext state (some bit)) rest

def headSuffixGapOpeningRewindScanSource
    (scan left : List (Option Bool)) (stop : Option Bool)
    (right : List (Option Bool)) : Tape Bool :=
  match scan with
  | [] => tapeAtCells left (stop :: right)
  | current :: rest =>
      tapeAtCells (List.append rest (stop :: left)) (current :: right)

theorem headSuffixGapOpeningRewindScanState_append
    (state : Nat) (left right : List (Option Bool)) :
    headSuffixGapOpeningRewindScanState state
        (List.append left right) =
      headSuffixGapOpeningRewindScanState
        (headSuffixGapOpeningRewindScanState state left) right := by
  induction left generalizing state with
  | nil =>
      rfl
  | cons current rest ih =>
      exact ih (headSuffixGapOpeningRewindScanNext state current)

theorem headSuffixGapOpeningRewindScanSafe_append
    (state : Nat) (left right : List (Option Bool)) :
    headSuffixGapOpeningRewindScanSafe state
        (List.append left right) ↔
      headSuffixGapOpeningRewindScanSafe state left ∧
        headSuffixGapOpeningRewindScanSafe
          (headSuffixGapOpeningRewindScanState state left) right := by
  induction left generalizing state with
  | nil =>
      simp [headSuffixGapOpeningRewindScanSafe,
        headSuffixGapOpeningRewindScanState]
  | cons current rest ih =>
      cases current with
      | none =>
          simp [headSuffixGapOpeningRewindScanSafe,
            headSuffixGapOpeningRewindScanState]
          constructor
          · intro h
            rcases h with ⟨hstate, hrestRight⟩
            rcases
                (ih (headSuffixGapOpeningRewindScanNext state none)).mp
                  hrestRight with
              ⟨hrest, hright⟩
            exact ⟨⟨hstate, hrest⟩, hright⟩
          · intro h
            rcases h with ⟨⟨hstate, hrest⟩, hright⟩
            exact
              ⟨hstate,
                (ih (headSuffixGapOpeningRewindScanNext state none)).mpr
                  ⟨hrest, hright⟩⟩
      | some bit =>
          cases bit <;>
            simpa [headSuffixGapOpeningRewindScanSafe,
              headSuffixGapOpeningRewindScanState,
              headSuffixGapOpeningRewindScanNext] using
              ih headSuffixGapOpeningRewindDescription.start

theorem headSuffixGapOpeningRewindScanSafe_map_some
    (state : Nat) (bits : Word Bool) :
    headSuffixGapOpeningRewindScanSafe state (bits.map some) := by
  induction bits generalizing state with
  | nil =>
      trivial
  | cons bit rest ih =>
      cases bit <;>
        simpa [headSuffixGapOpeningRewindScanSafe,
          headSuffixGapOpeningRewindScanNext] using
          ih headSuffixGapOpeningRewindDescription.start

theorem headSuffixGapOpeningRewindScanState_zero_map_some
    (bits : Word Bool) :
    headSuffixGapOpeningRewindScanState
        headSuffixGapOpeningRewindDescription.start (bits.map some) =
      headSuffixGapOpeningRewindDescription.start := by
  induction bits with
  | nil =>
      rfl
  | cons bit rest ih =>
      cases bit <;>
        simpa [headSuffixGapOpeningRewindScanState,
          headSuffixGapOpeningRewindScanNext] using ih

theorem headSuffixGapOpeningRewindScanState_map_some_of_cons
    (state : Nat) (bit : Bool) (bits : Word Bool) :
    headSuffixGapOpeningRewindScanState state
        ((bit :: bits).map some) =
      headSuffixGapOpeningRewindDescription.start := by
  cases bit <;>
    simpa [headSuffixGapOpeningRewindScanState,
      headSuffixGapOpeningRewindScanNext] using
      headSuffixGapOpeningRewindScanState_zero_map_some bits

theorem headSuffixGapOpeningRewindScanState_reverse_map_some_of_cons
    (state : Nat) (bit : Bool) (bits : Word Bool) :
    headSuffixGapOpeningRewindScanState state
        ((bit :: bits).reverse.map some) =
      headSuffixGapOpeningRewindDescription.start := by
  rcases word_exists_reverse_append_singleton_of_cons bit bits with
    ⟨scanRev, current, hword⟩
  have hrev : (bit :: bits).reverse = current :: scanRev := by
    rw [hword]
    simp [List.reverse_append]
  rw [hrev]
  exact
    headSuffixGapOpeningRewindScanState_map_some_of_cons
      state current scanRev

theorem headSuffixGapOpeningRewindScanState_encodedScanRev_of_nonempty
    (logical : List (Tape Bool)) (hlogical : logical ≠ []) :
    headSuffixGapOpeningRewindScanState
        headSuffixGapOpeningRewindDescription.start
        (encodedStructuredTapeCellsScanRev logical) =
      headSuffixGapOpeningRewindDescription.start := by
  induction logical with
  | nil =>
      contradiction
  | cons T rest ih =>
      cases rest with
      | nil =>
          rcases logicalTapeBits_exists_cons T with ⟨bit, bits, hbits⟩
          rw [encodedStructuredTapeCellsScanRev, hbits]
          exact
            headSuffixGapOpeningRewindScanState_reverse_map_some_of_cons
              headSuffixGapOpeningRewindDescription.start bit bits
      | cons U rest =>
          rcases logicalTapeBits_exists_cons T with ⟨bit, bits, hbits⟩
          rw [encodedStructuredTapeCellsScanRev, hbits]
          rw [headSuffixGapOpeningRewindScanState_append]
          rw [headSuffixGapOpeningRewindScanState_append]
          rw [ih (by simp)]
          simp [headSuffixGapOpeningRewindScanState,
            headSuffixGapOpeningRewindScanNext,
            headSuffixGapOpeningRewindDescription]
          simpa [List.map_reverse,
            headSuffixGapOpeningRewindDescription] using
            headSuffixGapOpeningRewindScanState_reverse_map_some_of_cons
              1 bit bits

theorem headSuffixGapOpeningRewindScanState_encodedScanRev
    (T : Tape Bool) (rest : List (Tape Bool)) :
    headSuffixGapOpeningRewindScanState
        headSuffixGapOpeningRewindDescription.start
        (encodedStructuredTapeCellsScanRev (T :: rest)) =
      headSuffixGapOpeningRewindDescription.start :=
  headSuffixGapOpeningRewindScanState_encodedScanRev_of_nonempty
    (T :: rest) (by simp)

theorem headSuffixGapOpeningRewindScanSafe_encodedScanRev_of_nonempty
    (logical : List (Tape Bool)) (hlogical : logical ≠ []) :
    headSuffixGapOpeningRewindScanSafe
        headSuffixGapOpeningRewindDescription.start
        (encodedStructuredTapeCellsScanRev logical) := by
  induction logical with
  | nil =>
      contradiction
  | cons T rest ih =>
      cases rest with
      | nil =>
          exact
            headSuffixGapOpeningRewindScanSafe_map_some
              headSuffixGapOpeningRewindDescription.start
              (logicalTapeBits T).reverse
      | cons U rest =>
          rw [encodedStructuredTapeCellsScanRev]
          rw [headSuffixGapOpeningRewindScanSafe_append]
          constructor
          · rw [headSuffixGapOpeningRewindScanSafe_append]
            constructor
            · exact ih (by simp)
            · rw [headSuffixGapOpeningRewindScanState_encodedScanRev U rest]
              simp [headSuffixGapOpeningRewindScanSafe,
                headSuffixGapOpeningRewindDescription]
          · have hstateLeft :
                headSuffixGapOpeningRewindScanState
                    headSuffixGapOpeningRewindDescription.start
                    (List.append
                      (encodedStructuredTapeCellsScanRev (U :: rest))
                      [none]) = 1 := by
              rw [headSuffixGapOpeningRewindScanState_append]
              rw [headSuffixGapOpeningRewindScanState_encodedScanRev U rest]
              simp [headSuffixGapOpeningRewindScanState,
                headSuffixGapOpeningRewindScanNext,
                headSuffixGapOpeningRewindDescription]
            rw [hstateLeft]
            exact
              headSuffixGapOpeningRewindScanSafe_map_some 1
                (logicalTapeBits T).reverse

theorem headSuffixGapOpeningRewindScanSafe_encodedScanRev
    (T : Tape Bool) (rest : List (Tape Bool)) :
    headSuffixGapOpeningRewindScanSafe
        headSuffixGapOpeningRewindDescription.start
        (encodedStructuredTapeCellsScanRev (T :: rest)) :=
  headSuffixGapOpeningRewindScanSafe_encodedScanRev_of_nonempty
    (T :: rest) (by simp)

theorem encodedStructuredTapeCells_eq_scanRev_of_nonempty
    (logical : List (Tape Bool)) (hlogical : logical ≠ []) :
    encodedStructuredTapeCells logical =
      none ::
        List.append
          (encodedStructuredTapeCellsScanRev logical).reverse
          [none] := by
  induction logical with
  | nil =>
      contradiction
  | cons T rest ih =>
      cases rest with
      | nil =>
          simp [encodedStructuredTapeCells, encodedStructuredTapeCellsScanRev,
            logicalTapeCode_eq_map_some, tapeSeparatorCells,
            List.map_reverse]
      | cons U rest =>
          have ihRest := ih (by simp)
          have ihTail :
              List.append ((logicalTapeBits U).map some)
                  (encodedStructuredTapeCells rest) =
                List.append
                  (encodedStructuredTapeCellsScanRev (U :: rest)).reverse
                  [none] := by
            simpa [encodedStructuredTapeCells,
              logicalTapeCode_eq_map_some, tapeSeparatorCells,
              List.append_assoc] using ihRest
          simpa [encodedStructuredTapeCells, encodedStructuredTapeCellsScanRev,
            logicalTapeCode_eq_map_some, tapeSeparatorCells,
            List.reverse_append, List.map_reverse, List.append_assoc] using
            ihTail

theorem encodedStructuredTapeCells_eq_scanRev
    (T : Tape Bool) (rest : List (Tape Bool)) :
    encodedStructuredTapeCells (T :: rest) =
      none ::
        List.append
          (encodedStructuredTapeCellsScanRev (T :: rest)).reverse
          [none] :=
  encodedStructuredTapeCells_eq_scanRev_of_nonempty
    (T :: rest) (by simp)

theorem headSuffixGapOpeningRewindDescription_run_scanStep
    (state : Nat) (current stop : Option Bool)
    (rest left right : List (Option Bool))
    (hstate : state = 0 ∨ state = 1 ∨ state = 2 ∨ state = 3)
    (hsafe :
      headSuffixGapOpeningRewindScanSafe state (current :: rest)) :
    headSuffixGapOpeningRewindDescription.runConfig 1
        { state := state
          tape :=
            headSuffixGapOpeningRewindScanSource
              (current :: rest) left stop right } =
      { state := headSuffixGapOpeningRewindScanNext state current
        tape :=
          headSuffixGapOpeningRewindScanSource
            rest left stop (current :: right) } := by
  rcases hstate with rfl | rfl | rfl | rfl
  · cases current with
    | none =>
        cases rest <;>
          machine_step [headSuffixGapOpeningRewindDescription,
            headSuffixGapOpeningRewindScanSource,
            headSuffixGapOpeningRewindScanNext]
    | some bit =>
        cases bit <;> cases rest <;>
          machine_step [headSuffixGapOpeningRewindDescription,
            headSuffixGapOpeningRewindScanSource,
            headSuffixGapOpeningRewindScanNext]
  · cases current with
    | none =>
        cases rest <;>
          machine_step [headSuffixGapOpeningRewindDescription,
            headSuffixGapOpeningRewindScanSource,
            headSuffixGapOpeningRewindScanNext]
    | some bit =>
        cases bit <;> cases rest <;>
          machine_step [headSuffixGapOpeningRewindDescription,
            headSuffixGapOpeningRewindScanSource,
            headSuffixGapOpeningRewindScanNext]
  · cases current with
    | none =>
        cases rest <;>
          machine_step [headSuffixGapOpeningRewindDescription,
            headSuffixGapOpeningRewindScanSource,
            headSuffixGapOpeningRewindScanNext]
    | some bit =>
        cases bit <;> cases rest <;>
          machine_step [headSuffixGapOpeningRewindDescription,
            headSuffixGapOpeningRewindScanSource,
            headSuffixGapOpeningRewindScanNext]
  · cases current with
    | none =>
        simp [headSuffixGapOpeningRewindScanSafe] at hsafe
    | some bit =>
        cases bit <;> cases rest <;>
          machine_step [headSuffixGapOpeningRewindDescription,
            headSuffixGapOpeningRewindScanSource,
            headSuffixGapOpeningRewindScanNext]

theorem headSuffixGapOpeningRewindScanNext_state
    (state : Nat) (current : Option Bool)
    (hstate : state = 0 ∨ state = 1 ∨ state = 2 ∨ state = 3)
    (hsafe :
      headSuffixGapOpeningRewindScanSafe state [current]) :
    let next := headSuffixGapOpeningRewindScanNext state current
    next = 0 ∨ next = 1 ∨ next = 2 ∨ next = 3 := by
  rcases hstate with rfl | rfl | rfl | rfl <;>
    cases current with
    | none =>
        simp [headSuffixGapOpeningRewindScanSafe,
          headSuffixGapOpeningRewindScanNext] at hsafe ⊢
    | some bit =>
        cases bit <;>
          simp [headSuffixGapOpeningRewindScanNext,
            headSuffixGapOpeningRewindDescription]

theorem headSuffixGapOpeningRewindDescription_run_scanLeft
    (scan left right : List (Option Bool)) (stop : Option Bool)
    (state : Nat)
    (hstate : state = 0 ∨ state = 1 ∨ state = 2 ∨ state = 3)
    (hsafe : headSuffixGapOpeningRewindScanSafe state scan) :
    headSuffixGapOpeningRewindDescription.runConfig scan.length
        { state := state
          tape :=
            headSuffixGapOpeningRewindScanSource scan left stop right } =
      { state := headSuffixGapOpeningRewindScanState state scan
        tape :=
          tapeAtCells left
            (stop :: List.append scan.reverse right) } := by
  induction scan generalizing state right with
  | nil =>
      machine_run [headSuffixGapOpeningRewindScanSource,
        headSuffixGapOpeningRewindScanState]
  | cons current rest ih =>
      rw [show (current :: rest).length = 1 + rest.length by
        simp [Nat.add_comm]]
      rw [MachineDescription.runConfig_add]
      have hstep :=
        headSuffixGapOpeningRewindDescription_run_scanStep
          state current stop rest left right hstate hsafe
      rw [hstep]
      have hsafeRest :
          headSuffixGapOpeningRewindScanSafe
            (headSuffixGapOpeningRewindScanNext state current) rest := by
        cases current with
        | none =>
            simpa [headSuffixGapOpeningRewindScanSafe] using hsafe.2
        | some bit =>
            simpa [headSuffixGapOpeningRewindScanSafe,
              headSuffixGapOpeningRewindScanNext] using hsafe
      have hnextState :
          headSuffixGapOpeningRewindScanNext state current = 0 ∨
            headSuffixGapOpeningRewindScanNext state current = 1 ∨
            headSuffixGapOpeningRewindScanNext state current = 2 ∨
            headSuffixGapOpeningRewindScanNext state current = 3 := by
        have hsafeOne :
            headSuffixGapOpeningRewindScanSafe state [current] := by
          cases current with
          | none =>
              exact ⟨hsafe.1, trivial⟩
          | some bit =>
              trivial
        simpa using
          headSuffixGapOpeningRewindScanNext_state
            state current hstate hsafeOne
      simpa [headSuffixGapOpeningRewindScanState, List.reverse_cons,
        List.append_assoc] using
        ih (current :: right)
          (headSuffixGapOpeningRewindScanNext state current)
          hnextState hsafeRest

theorem headSuffixGapOpeningRewindDescription_run_shiftedSuffixScan
    (scanRest gap : List (Option Bool))
    (last current : Option Bool) (cells : List (Option Bool))
    (hsafe :
      headSuffixGapOpeningRewindScanSafe
        headSuffixGapOpeningRewindDescription.start
        (last :: scanRest))
    (hstate :
      headSuffixGapOpeningRewindScanState
        headSuffixGapOpeningRewindDescription.start
        (last :: scanRest) =
          headSuffixGapOpeningRewindDescription.start)
    (hcells :
      List.append scanRest.reverse [last, none] = current :: cells) :
    headSuffixGapOpeningRewindDescription.runConfig (scanRest.length + 1)
        { state := headSuffixGapOpeningRewindDescription.start
          tape :=
            Tape.move Direction.left
              (tapeAtCells
                (last :: List.append scanRest (none :: gap)) []) } =
      { state := headSuffixGapOpeningRewindDescription.start
        tape := tapeAtCells gap (none :: current :: cells) } := by
  rw [show scanRest.length + 1 = (last :: scanRest).length by
    simp]
  have hsource :
      Tape.move Direction.left
          (tapeAtCells
            (last :: List.append scanRest (none :: gap)) []) =
        headSuffixGapOpeningRewindScanSource
          (last :: scanRest) gap none [none] := by
    simp [headSuffixGapOpeningRewindScanSource, tapeAtCells,
      Tape.move, Tape.moveLeft]
  rw [hsource]
  have hrun :=
    headSuffixGapOpeningRewindDescription_run_scanLeft
      (last :: scanRest) gap [none] none
      headSuffixGapOpeningRewindDescription.start
      (Or.inl rfl) hsafe
  rw [hrun]
  simp [hstate, List.reverse_cons, List.append_assoc]
  exact congrArg (fun tail => tapeAtCells gap (none :: tail)) hcells

theorem headSuffixGapShiftLoop_scanRev_append_none
    (T : Tape Bool) (rest : List (Tape Bool))
    (current : Option Bool) (cells : List (Option Bool))
    (htail :
      encodedStructuredTapeCellsTail (T :: rest) = current :: cells)
    (hsecond :
      (headSuffixGapShiftLoopPair none current cells).2 = none) :
    (headSuffixGapShiftLoopPair none current cells).1 ::
        headSuffixGapShiftLoopWrittenRev none current cells =
      List.append (encodedStructuredTapeCellsScanRev (T :: rest)) [none] := by
  have hloop :
      List.append
          (headSuffixGapShiftLoopWrittenRev none current cells).reverse
          [ (headSuffixGapShiftLoopPair none current cells).1, none ] =
        none :: current :: cells :=
    headSuffixGapShiftLoopOutputSuffix_eq_cons current cells hsecond
  have hloop' :
      List.append
          ((headSuffixGapShiftLoopPair none current cells).1 ::
            headSuffixGapShiftLoopWrittenRev none current cells).reverse
          [none] =
        none :: current :: cells := by
    simpa [List.reverse_cons, List.append_assoc] using hloop
  have hencoded :
      none :: current :: cells =
        none ::
          List.append
            (encodedStructuredTapeCellsScanRev (T :: rest)).reverse
            [none] := by
    rw [← htail]
    rw [← encodedStructuredTapeCells_eq_cons_tail (T :: rest)]
    exact encodedStructuredTapeCells_eq_scanRev T rest
  exact
    optionList_eq_append_none_of_reverse_append_none_eq
      (by rw [hloop', hencoded])

theorem headSuffixGapOpeningRewindDescription_run_shiftedSuffixScan_encodedTail
    (gap : List (Option Bool)) (T : Tape Bool) (rest : List (Tape Bool))
    (current : Option Bool) (cells : List (Option Bool))
    (htail :
      encodedStructuredTapeCellsTail (T :: rest) = current :: cells)
    (hfirst :
      (headSuffixGapShiftLoopPair none current cells).1 ≠ none)
    (hsecond :
      (headSuffixGapShiftLoopPair none current cells).2 = none) :
    headSuffixGapOpeningRewindDescription.runConfig
        (encodedStructuredTapeCellsScanRev (T :: rest)).length
        { state := headSuffixGapOpeningRewindDescription.start
          tape :=
            Tape.move Direction.left
              (tapeAtCells
                ((headSuffixGapShiftLoopPair none current cells).1 ::
                  List.append
                    (headSuffixGapShiftLoopWrittenRev none current cells)
                    gap) []) } =
      { state := headSuffixGapOpeningRewindDescription.start
        tape := tapeAtCells gap (none :: current :: cells) } := by
  have hscanAppend :=
    headSuffixGapShiftLoop_scanRev_append_none
      T rest current cells htail hsecond
  rcases
      optionList_cons_eq_append_none_split
        hscanAppend hfirst with
    ⟨scanRest, hscan, hwritten⟩
  have hcells :
      List.append scanRest.reverse
          [ (headSuffixGapShiftLoopPair none current cells).1, none ] =
        current :: cells := by
    have hencoded :
        current :: cells =
          List.append
            (encodedStructuredTapeCellsScanRev (T :: rest)).reverse
            [none] := by
      have hencodedFull :
          none :: current :: cells =
            none ::
              List.append
                (encodedStructuredTapeCellsScanRev (T :: rest)).reverse
                [none] := by
        rw [← htail]
        rw [← encodedStructuredTapeCells_eq_cons_tail (T :: rest)]
        exact encodedStructuredTapeCells_eq_scanRev T rest
      simpa using congrArg List.tail hencodedFull
    rw [hscan] at hencoded
    simpa [List.reverse_cons, List.append_assoc] using hencoded.symm
  rw [show (encodedStructuredTapeCellsScanRev (T :: rest)).length =
      scanRest.length + 1 by
    rw [hscan]
    simp]
  rw [hwritten]
  simpa [List.append_assoc] using
    headSuffixGapOpeningRewindDescription_run_shiftedSuffixScan
      scanRest gap
      (headSuffixGapShiftLoopPair none current cells).1 current cells
      (by
        simpa [hscan] using
          headSuffixGapOpeningRewindScanSafe_encodedScanRev T rest)
      (by
        simpa [hscan] using
          headSuffixGapOpeningRewindScanState_encodedScanRev T rest)
      hcells

theorem headSuffixGapOpeningRewindDescription_run_openingFinish
    (rightTail : List (Option Bool)) :
    headSuffixGapOpeningRewindDescription.runConfig 6
        { state := headSuffixGapOpeningRewindDescription.start
          tape := tapeAtCells [] (none :: rightTail) } =
      { state := headSuffixGapOpeningRewindHalt
        tape := tapeAtCells [none, none, none] (none :: rightTail) } := by
  machine_step [headSuffixGapOpeningRewindDescription]

theorem headSuffixGapOpeningRewindDescription_run_payloadScan
    (leftStack : Word Bool) (current : Bool)
    (rightTail : List (Option Bool)) :
    headSuffixGapOpeningRewindDescription.runConfig (leftStack.length + 1)
        { state := headSuffixGapOpeningRewindDescription.start
          tape :=
            tapeAtCells
              (List.append (leftStack.map some) [none])
              (some current :: rightTail) } =
      { state := headSuffixGapOpeningRewindDescription.start
        tape :=
          tapeAtCells []
            (none ::
              List.append
                ((List.append leftStack.reverse [current]).map some)
                rightTail) } := by
  induction leftStack generalizing current rightTail with
  | nil =>
      cases current <;> cases rightTail <;>
        machine_step [headSuffixGapOpeningRewindDescription]
  | cons next rest ih =>
      rw [show (next :: rest).length + 1 =
        1 + (rest.length + 1) by
        simp
        lia]
      rw [MachineDescription.runConfig_add]
      have hstep :
          headSuffixGapOpeningRewindDescription.runConfig 1
              { state := headSuffixGapOpeningRewindDescription.start
                tape :=
                  tapeAtCells
                    (List.append ((next :: rest).map some) [none])
                    (some current :: rightTail) } =
            { state := headSuffixGapOpeningRewindDescription.start
              tape :=
                tapeAtCells
                  (List.append (rest.map some) [none])
                  (some next :: some current :: rightTail) } := by
        cases next <;> cases current <;> cases rightTail <;>
          machine_step [headSuffixGapOpeningRewindDescription]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc]
        using ih next (some current :: rightTail)

theorem headSuffixGapOpeningRewindDescription_run_payloadFinish
    (leftStack : Word Bool) (current : Bool)
    (rightTail : List (Option Bool)) :
    headSuffixGapOpeningRewindDescription.runConfig (leftStack.length + 7)
        { state := headSuffixGapOpeningRewindDescription.start
          tape :=
            tapeAtCells
              (List.append (leftStack.map some) [none])
              (some current :: rightTail) } =
      { state := headSuffixGapOpeningRewindHalt
        tape :=
          tapeAtCells [none, none, none]
            (none ::
              List.append
                ((List.append leftStack.reverse [current]).map some)
                rightTail) } := by
  rw [show leftStack.length + 7 = (leftStack.length + 1) + 6 by lia]
  rw [MachineDescription.runConfig_add]
  rw [headSuffixGapOpeningRewindDescription_run_payloadScan]
  exact headSuffixGapOpeningRewindDescription_run_openingFinish
    (List.append ((List.append leftStack.reverse [current]).map some)
      rightTail)

theorem headSuffixGapOpeningRewindDescription_haltsFrom_payload
    (leftStack : Word Bool) (current : Bool)
    (rightTail : List (Option Bool)) :
    headSuffixGapOpeningRewindDescription.HaltsFromTapeEquiv
      (tapeAtCells
        (List.append (leftStack.map some) [none])
        (some current :: rightTail))
      (tapeAtCells []
        (none ::
          List.append
            ((List.append leftStack.reverse [current]).map some)
            rightTail)) := by
  refine
    ⟨tapeAtCells [none, none, none]
        (none ::
          List.append
            ((List.append leftStack.reverse [current]).map some)
            rightTail),
      ?_, ?_⟩
  · refine ⟨leftStack.length + 7, ?_⟩
    constructor
    · rw [headSuffixGapOpeningRewindDescription_run_payloadFinish]
      rfl
    · rw [headSuffixGapOpeningRewindDescription_run_payloadFinish]
  · simp [Tape.Equiv, tapeAtCells, Tape.dropTrailingNone]

theorem headSuffixGapOpeningRewindDescription_run_gapPayloadFinish
    (leftStack : Word Bool) (current : Bool)
    (rightTail : List (Option Bool)) :
    headSuffixGapOpeningRewindDescription.runConfig (leftStack.length + 7)
        { state := 3
          tape :=
            tapeAtCells
              (List.append (leftStack.map some) [none])
              (some current :: rightTail) } =
      { state := headSuffixGapOpeningRewindHalt
        tape :=
          tapeAtCells [none, none, none]
            (none ::
              List.append
                ((List.append leftStack.reverse [current]).map some)
                rightTail) } := by
  induction leftStack generalizing current rightTail with
  | nil =>
      rw [show ([] : Word Bool).length + 7 = 1 + 6 by rfl]
      rw [MachineDescription.runConfig_add]
      have hstep :
          headSuffixGapOpeningRewindDescription.runConfig 1
              { state := 3
                tape :=
                  tapeAtCells
                    (List.append (([] : Word Bool).map some) [none])
                    (some current :: rightTail) } =
            { state := headSuffixGapOpeningRewindDescription.start
              tape := tapeAtCells [] (none :: some current :: rightTail) } := by
        cases current <;> cases rightTail <;>
          machine_step [headSuffixGapOpeningRewindDescription]
      rw [hstep]
      simpa using
        headSuffixGapOpeningRewindDescription_run_openingFinish
          (some current :: rightTail)
  | cons next rest ih =>
      rw [show (next :: rest).length + 7 =
        1 + (rest.length + 7) by
        simp
        lia]
      rw [MachineDescription.runConfig_add]
      have hstep :
          headSuffixGapOpeningRewindDescription.runConfig 1
              { state := 3
                tape :=
                  tapeAtCells
                    (List.append ((next :: rest).map some) [none])
                    (some current :: rightTail) } =
            { state := headSuffixGapOpeningRewindDescription.start
              tape :=
                tapeAtCells
                  (List.append (rest.map some) [none])
                  (some next :: some current :: rightTail) } := by
        cases next <;> cases current <;> cases rightTail <;>
          machine_step [headSuffixGapOpeningRewindDescription]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc]
        using
          headSuffixGapOpeningRewindDescription_run_payloadFinish
            rest next (some current :: rightTail)

theorem headSuffixGapOpeningRewindDescription_run_state2PayloadFinish
    (leftStack : Word Bool) (current : Bool)
    (rightTail : List (Option Bool)) :
    headSuffixGapOpeningRewindDescription.runConfig (leftStack.length + 7)
        { state := 2
          tape :=
            tapeAtCells
              (List.append (leftStack.map some) [none])
              (some current :: rightTail) } =
      { state := headSuffixGapOpeningRewindHalt
        tape :=
          tapeAtCells [none, none, none]
            (none ::
              List.append
                ((List.append leftStack.reverse [current]).map some)
                rightTail) } := by
  induction leftStack generalizing current rightTail with
  | nil =>
      rw [show ([] : Word Bool).length + 7 = 1 + 6 by rfl]
      rw [MachineDescription.runConfig_add]
      have hstep :
          headSuffixGapOpeningRewindDescription.runConfig 1
              { state := 2
                tape :=
                  tapeAtCells
                    (List.append (([] : Word Bool).map some) [none])
                    (some current :: rightTail) } =
            { state := headSuffixGapOpeningRewindDescription.start
              tape := tapeAtCells [] (none :: some current :: rightTail) } := by
        cases current <;> cases rightTail <;>
          machine_step [headSuffixGapOpeningRewindDescription]
      rw [hstep]
      simpa using
        headSuffixGapOpeningRewindDescription_run_openingFinish
          (some current :: rightTail)
  | cons next rest ih =>
      rw [show (next :: rest).length + 7 =
        1 + (rest.length + 7) by
        simp
        lia]
      rw [MachineDescription.runConfig_add]
      have hstep :
          headSuffixGapOpeningRewindDescription.runConfig 1
              { state := 2
                tape :=
                  tapeAtCells
                    (List.append ((next :: rest).map some) [none])
                    (some current :: rightTail) } =
            { state := headSuffixGapOpeningRewindDescription.start
              tape :=
                tapeAtCells
                  (List.append (rest.map some) [none])
                  (some next :: some current :: rightTail) } := by
        cases next <;> cases current <;> cases rightTail <;>
          machine_step [headSuffixGapOpeningRewindDescription]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc]
        using
          headSuffixGapOpeningRewindDescription_run_payloadFinish
            rest next (some current :: rightTail)

theorem headSuffixGapOpeningRewindDescription_run_twoBlankGapPayloadFinish
    (leftStack : Word Bool) (current : Bool)
    (rightTail : List (Option Bool)) :
    headSuffixGapOpeningRewindDescription.runConfig (leftStack.length + 9)
        { state := headSuffixGapOpeningRewindDescription.start
          tape :=
            tapeAtCells
              (none :: some current ::
                List.append (leftStack.map some) [none])
              (none :: rightTail) } =
      { state := headSuffixGapOpeningRewindHalt
        tape :=
          tapeAtCells [none, none, none]
            (none ::
              List.append
                ((List.append leftStack.reverse [current]).map some)
                (none :: none :: rightTail)) } := by
  rw [show leftStack.length + 9 = 2 + (leftStack.length + 7) by
    lia]
  rw [MachineDescription.runConfig_add]
  have hgap :
      headSuffixGapOpeningRewindDescription.runConfig 2
          { state := headSuffixGapOpeningRewindDescription.start
            tape :=
              tapeAtCells
                (none :: some current ::
                  List.append (leftStack.map some) [none])
                (none :: rightTail) } =
        { state := 2
          tape :=
            tapeAtCells
              (List.append (leftStack.map some) [none])
              (some current :: none :: none :: rightTail) } := by
    cases current <;> cases leftStack <;> cases rightTail <;>
      machine_step [headSuffixGapOpeningRewindDescription]
  rw [hgap]
  exact
    headSuffixGapOpeningRewindDescription_run_state2PayloadFinish
      leftStack current (none :: none :: rightTail)

theorem headSuffixGapOpeningRewindDescription_run_threeBlankGap
    (leftStack : Word Bool) (current : Bool)
    (rightTail : List (Option Bool)) :
    headSuffixGapOpeningRewindDescription.runConfig 3
        { state := headSuffixGapOpeningRewindDescription.start
          tape :=
            tapeAtCells
              (none :: none :: some current ::
                List.append (leftStack.map some) [none])
              (none :: rightTail) } =
      { state := 3
        tape :=
          tapeAtCells
            (List.append (leftStack.map some) [none])
            (some current :: none :: none :: none :: rightTail) } := by
  cases current <;> cases leftStack <;> cases rightTail <;>
    machine_step [headSuffixGapOpeningRewindDescription]

theorem headSuffixGapOpeningRewindDescription_run_threeBlankGapPayloadFinish
    (leftStack : Word Bool) (current : Bool)
    (rightTail : List (Option Bool)) :
    headSuffixGapOpeningRewindDescription.runConfig (leftStack.length + 10)
        { state := headSuffixGapOpeningRewindDescription.start
          tape :=
            tapeAtCells
              (none :: none :: some current ::
                List.append (leftStack.map some) [none])
              (none :: rightTail) } =
      { state := headSuffixGapOpeningRewindHalt
        tape :=
          tapeAtCells [none, none, none]
            (none ::
              List.append
                ((List.append leftStack.reverse [current]).map some)
                (none :: none :: none :: rightTail)) } := by
  rw [show leftStack.length + 10 = 3 + (leftStack.length + 7) by
    lia]
  rw [MachineDescription.runConfig_add]
  rw [headSuffixGapOpeningRewindDescription_run_threeBlankGap]
  exact
    headSuffixGapOpeningRewindDescription_run_gapPayloadFinish
      leftStack current (none :: none :: none :: rightTail)

theorem headSuffixGapOpeningRewindDescription_haltsFrom_threeBlankGapPayload
    (leftStack : Word Bool) (current : Bool)
    (rightTail : List (Option Bool)) :
    headSuffixGapOpeningRewindDescription.HaltsFromTapeEquiv
      (tapeAtCells
        (none :: none :: some current ::
          List.append (leftStack.map some) [none])
        (none :: rightTail))
      (tapeAtCells []
        (none ::
          List.append
            ((List.append leftStack.reverse [current]).map some)
            (none :: none :: none :: rightTail))) := by
  refine
    ⟨tapeAtCells [none, none, none]
        (none ::
          List.append
            ((List.append leftStack.reverse [current]).map some)
            (none :: none :: none :: rightTail)),
      ?_, ?_⟩
  · refine ⟨leftStack.length + 10, ?_⟩
    constructor
    · rw [headSuffixGapOpeningRewindDescription_run_threeBlankGapPayloadFinish]
      rfl
    · rw [headSuffixGapOpeningRewindDescription_run_threeBlankGapPayloadFinish]
  · simp [Tape.Equiv, tapeAtCells, Tape.dropTrailingNone]

theorem headSuffixGapOpeningRewindDescription_haltsFrom_shifted_cons
    (first : Bool) (bits : Word Bool)
    (T : Tape Bool) (rest : List (Tape Bool))
    (current : Option Bool) (cells : List (Option Bool))
    (htail :
      encodedStructuredTapeCellsTail (T :: rest) = current :: cells)
    (hfirst :
      (headSuffixGapShiftLoopPair none current cells).1 ≠ none)
    (hsecond :
      (headSuffixGapShiftLoopPair none current cells).2 = none) :
    headSuffixGapOpeningRewindDescription.HaltsFromTapeEquiv
      (Tape.move Direction.left
        (tapeAtCells
          ((headSuffixGapShiftLoopPair none current cells).1 ::
            List.append
              (headSuffixGapShiftLoopWrittenRev none current cells)
              (none :: none ::
                List.append ((first :: bits).reverse.map some) [none]))
          []))
      (encodedStructuredHeadPayloadGapTapes (first :: bits) (T :: rest)) := by
  rcases word_exists_reverse_append_singleton_of_cons first bits with
    ⟨leftStack, payloadCurrent, hpayload⟩
  let gap : List (Option Bool) :=
    none :: none ::
      List.append ((first :: bits).reverse.map some) [none]
  let actual :=
    tapeAtCells [none, none, none]
      (none ::
        List.append
          ((List.append leftStack.reverse [payloadCurrent]).map some)
          (none :: none :: none :: current :: cells))
  have hgap :
      gap =
        none :: none :: some payloadCurrent ::
          List.append (leftStack.map some) [none] := by
    simp [gap, hpayload, List.reverse_append]
  refine ⟨actual, ?_, ?_⟩
  · refine
      ⟨(encodedStructuredTapeCellsScanRev (T :: rest)).length +
          (leftStack.length + 10), ?_⟩
    constructor
    · rw [MachineDescription.runConfig_add]
      change
        (headSuffixGapOpeningRewindDescription.runConfig
          (leftStack.length + 10)
          (headSuffixGapOpeningRewindDescription.runConfig
            (encodedStructuredTapeCellsScanRev (T :: rest)).length
            { state := headSuffixGapOpeningRewindDescription.start
              tape :=
                Tape.move Direction.left
                  (tapeAtCells
                    ((headSuffixGapShiftLoopPair none current cells).1 ::
                      List.append
                        (headSuffixGapShiftLoopWrittenRev none current cells)
                        gap) []) })).state =
          headSuffixGapOpeningRewindDescription.halt
      rw [headSuffixGapOpeningRewindDescription_run_shiftedSuffixScan_encodedTail
        gap T rest current cells htail hfirst hsecond]
      rw [hgap]
      rw [headSuffixGapOpeningRewindDescription_run_threeBlankGapPayloadFinish]
      rfl
    · rw [MachineDescription.runConfig_add]
      change
        (headSuffixGapOpeningRewindDescription.runConfig
          (leftStack.length + 10)
          (headSuffixGapOpeningRewindDescription.runConfig
            (encodedStructuredTapeCellsScanRev (T :: rest)).length
            { state := headSuffixGapOpeningRewindDescription.start
              tape :=
                Tape.move Direction.left
                  (tapeAtCells
                    ((headSuffixGapShiftLoopPair none current cells).1 ::
                      List.append
                        (headSuffixGapShiftLoopWrittenRev none current cells)
                        gap) []) })).tape =
          actual
      rw [headSuffixGapOpeningRewindDescription_run_shiftedSuffixScan_encodedTail
        gap T rest current cells htail hfirst hsecond]
      rw [hgap]
      rw [headSuffixGapOpeningRewindDescription_run_threeBlankGapPayloadFinish]
  · simp [actual, encodedStructuredHeadPayloadGapTapes,
      encodedStructuredTapeCells_eq_cons_tail, htail, hpayload,
      tapeSeparatorCells,
      Tape.Equiv, tapeAtCells, Tape.dropTrailingNone,
      List.map_append, List.append_assoc]

theorem headSuffixGapOpeningRewindDescription_haltsFrom_shifted_emptyRest
    (first : Bool) (bits : Word Bool) :
    headSuffixGapOpeningRewindDescription.HaltsFromTapeEquiv
      (Tape.move Direction.left
        (tapeAtCells
          (none :: none ::
            List.append ((first :: bits).reverse.map some) [none])
          []))
      (encodedStructuredHeadPayloadGapTapes (first :: bits) []) := by
  rcases word_exists_reverse_append_singleton_of_cons first bits with
    ⟨leftStack, current, hbits⟩
  let actual :=
    tapeAtCells [none, none, none]
      (none ::
        List.append
          ((List.append leftStack.reverse [current]).map some)
          (none :: none :: [none]))
  have hsource :
      Tape.move Direction.left
          (tapeAtCells
            (none :: none ::
              List.append ((first :: bits).reverse.map some) [none])
            []) =
        tapeAtCells
          (none :: some current ::
            List.append (leftStack.map some) [none])
          (none :: [none]) := by
    rw [hbits]
    simp [tapeAtCells, Tape.move, Tape.moveLeft, List.reverse_append]
  refine ⟨actual, ?_, ?_⟩
  · refine ⟨leftStack.length + 9, ?_⟩
    have hrun :=
      headSuffixGapOpeningRewindDescription_run_twoBlankGapPayloadFinish
        leftStack current [none]
    constructor
    · rw [hsource]
      rw [hrun]
      rfl
    · rw [hsource]
      rw [hrun]
  · rw [hbits]
    simp [actual, encodedStructuredHeadPayloadGapTapes,
      encodedStructuredTapeCells, tapeSeparatorCells, Tape.Equiv,
      tapeAtCells, Tape.dropTrailingNone, List.map_append,
      List.append_assoc]

def headSuffixGapCreatorDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription
    headSuffixGapShiftDescription
    headSuffixGapOpeningRewindDescription

theorem headSuffixGapCreatorDescription_subroutineReady :
    headSuffixGapCreatorDescription.SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    headSuffixGapShiftDescription_subroutineReady
    headSuffixGapOpeningRewindDescription_subroutineReady

theorem headSuffixGapShiftDescription_haltsFrom_payload_emptyRest
    (bits : Word Bool) :
    headSuffixGapShiftDescription.HaltsFromTape
      (encodedStructuredHeadPayloadTapes bits [])
      (Tape.move Direction.left
        (tapeAtCells
          (none :: none :: List.append (bits.reverse.map some) [none])
          [])) := by
  refine ⟨bits.length + 4, ?_⟩
  constructor
  · rw [headSuffixGapShiftDescription_run_payload_emptyRest]
    rfl
  · rw [headSuffixGapShiftDescription_run_payload_emptyRest]

theorem headSuffixGapShiftDescription_haltsFrom_payload_cons
    (bits : Word Bool) (T : Tape Bool) (rest : List (Tape Bool)) :
    exists current : Option Bool, exists cells : List (Option Bool),
      encodedStructuredTapeCellsTail (T :: rest) = current :: cells ∧
        (headSuffixGapShiftLoopPair none current cells).1 ≠ none ∧
        (headSuffixGapShiftLoopPair none current cells).2 = none ∧
        headSuffixGapShiftDescription.HaltsFromTape
          (encodedStructuredHeadPayloadTapes bits (T :: rest))
          (Tape.move Direction.left
            (tapeAtCells
              ((headSuffixGapShiftLoopPair none current cells).1 ::
                List.append
                  (headSuffixGapShiftLoopWrittenRev none current cells)
                  (none :: none ::
                    List.append (bits.reverse.map some) [none]))
              [])) := by
  rcases headSuffixGapShiftLoopReady_encodedStructuredTapeCellsTail_start
      T rest with
    ⟨current, cells, htail, hactive, hfirst, hsecond⟩
  refine ⟨current, cells, htail, hfirst, hsecond, ?_⟩
  have hrunBoundary :=
    headSuffixGapShiftDescription_run_boundaryLoop_then_implicitStep_halt_nil
      current cells (none :: List.append (bits.reverse.map some) [none])
      hactive hfirst hsecond
  have hrun :
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
    rw [MachineDescription.runConfig_add]
    rw [headSuffixGapShiftDescription_run_to_encodedTailBoundary]
    rw [htail]
    exact hrunBoundary
  refine ⟨(bits.length + 2) + (cells.length + 3), ?_⟩
  constructor
  · rw [hrun]
    rfl
  · rw [hrun]

theorem headSuffixGapCreatorDescription_realizes_emptyRest
    (first : Bool) (bits : Word Bool) :
    headSuffixGapCreatorDescription.HaltsFromTapeEquiv
      (encodedStructuredHeadPayloadTapes (first :: bits) [])
      (encodedStructuredHeadPayloadGapTapes (first :: bits) []) := by
  exact
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      headSuffixGapShiftDescription_subroutineReady
      headSuffixGapOpeningRewindDescription_subroutineReady
      (MachineDescription.HaltsFromTape.toEquiv
        (headSuffixGapShiftDescription_haltsFrom_payload_emptyRest
          (first :: bits)))
      (headSuffixGapOpeningRewindDescription_haltsFrom_shifted_emptyRest
        first bits)

theorem headSuffixGapCreatorDescription_realizes_cons
    (first : Bool) (bits : Word Bool)
    (T : Tape Bool) (rest : List (Tape Bool)) :
    headSuffixGapCreatorDescription.HaltsFromTapeEquiv
      (encodedStructuredHeadPayloadTapes (first :: bits) (T :: rest))
      (encodedStructuredHeadPayloadGapTapes (first :: bits) (T :: rest)) := by
  rcases
      headSuffixGapShiftDescription_haltsFrom_payload_cons
        (first :: bits) T rest with
    ⟨current, cells, htail, hfirst, hsecond, hshift⟩
  exact
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      headSuffixGapShiftDescription_subroutineReady
      headSuffixGapOpeningRewindDescription_subroutineReady
      (MachineDescription.HaltsFromTape.toEquiv hshift)
      (headSuffixGapOpeningRewindDescription_haltsFrom_shifted_cons
        first bits T rest current cells htail hfirst hsecond)

/--
Nonempty raw payload contract for the suffix-gap creator.

The stronger {name}`HeadSuffixGapCreatorContract` in `CursorBoundaryGap.lean` is
still useful when available, but the singleton-boundary bridge only feeds
payloads of the form {name}`logicalTapeBits`, and those are always nonempty.
Keeping this narrower contract explicit avoids forcing the concrete
right-edge-to-opening return routine to solve the degenerate arbitrary-empty
payload case.
-/
structure HeadSuffixGapCreatorNonemptyContract
    (gapCreator : MachineDescription) : Prop where
  subroutineReady : gapCreator.SubroutineReady
  realizes :
    forall (first : Bool) (bits : Word Bool) (rest : List (Tape Bool)),
      gapCreator.HaltsFromTapeEquiv
        (encodedStructuredHeadPayloadTapes (first :: bits) rest)
        (encodedStructuredHeadPayloadGapTapes (first :: bits) rest)

theorem headSuffixGapCreatorDescription_nonemptyContract :
    HeadSuffixGapCreatorNonemptyContract headSuffixGapCreatorDescription where
  subroutineReady := headSuffixGapCreatorDescription_subroutineReady
  realizes := by
    intro first bits rest
    cases rest with
    | nil =>
        exact headSuffixGapCreatorDescription_realizes_emptyRest first bits
    | cons T rest =>
        exact headSuffixGapCreatorDescription_realizes_cons
          first bits T rest

namespace HeadSuffixGapCreatorContract

theorem toNonempty
    {gapCreator : MachineDescription}
    (hgap : HeadSuffixGapCreatorContract gapCreator) :
    HeadSuffixGapCreatorNonemptyContract gapCreator where
  subroutineReady := hgap.subroutineReady
  realizes := by
    intro first bits rest
    exact hgap.realizes (first :: bits) rest

end HeadSuffixGapCreatorContract

namespace HeadSuffixGapCreatorNonemptyContract

theorem toSingletonBoundary
    {gapCreator : MachineDescription}
    (hgap : HeadSuffixGapCreatorNonemptyContract gapCreator) :
    SingletonBoundaryGapCreatorContract gapCreator where
  subroutineReady := hgap.subroutineReady
  leftBoundary := by
    intro head right rest
    let T : Tape Bool :=
      { left := [], head := head, right := right ++ [none] }
    rcases logicalTapeBits_exists_cons T with ⟨first, bits, hbits⟩
    have hreal := hgap.realizes first bits rest
    rw [← hbits] at hreal
    simpa [T, encodedStructuredHeadPayloadTapes_eq_structuredTapes,
      encodedStructuredHeadPayloadGapTapes_eq_headGap] using hreal
  rightBoundary := by
    intro left head rest
    let T : Tape Bool :=
      { left := left ++ [none], head := head, right := [] }
    rcases logicalTapeBits_exists_cons T with ⟨first, bits, hbits⟩
    have hreal := hgap.realizes first bits rest
    rw [← hbits] at hreal
    simpa [T, encodedStructuredHeadPayloadTapes_eq_structuredTapes,
      encodedStructuredHeadPayloadGapTapes_eq_headGap] using hreal

theorem singletonHeadRefreshCaseContract
    {gapCreator : MachineDescription}
    (hgap : HeadSuffixGapCreatorNonemptyContract gapCreator) :
    SingletonHeadGuardSlackRefreshCaseContract
      (singletonHeadRefreshDescription gapCreator) :=
  singletonHeadRefreshDescription_caseContract
    (HeadSuffixGapCreatorNonemptyContract.toSingletonBoundary hgap)

end HeadSuffixGapCreatorNonemptyContract

theorem headSuffixGapCreatorDescription_singletonBoundaryContract :
    SingletonBoundaryGapCreatorContract headSuffixGapCreatorDescription :=
  HeadSuffixGapCreatorNonemptyContract.toSingletonBoundary
    headSuffixGapCreatorDescription_nonemptyContract

/-- Concrete singleton head refresh dispatcher backed by the suffix gap creator. -/
def concreteSingletonHeadRefreshDescription : MachineDescription :=
  singletonHeadRefreshDescription headSuffixGapCreatorDescription

theorem concreteSingletonHeadRefreshDescription_caseContract :
    SingletonHeadGuardSlackRefreshCaseContract
      concreteSingletonHeadRefreshDescription := by
  simpa [concreteSingletonHeadRefreshDescription] using
    HeadSuffixGapCreatorNonemptyContract.singletonHeadRefreshCaseContract
      headSuffixGapCreatorDescription_nonemptyContract

theorem concreteSingletonHeadRefreshDescription_subroutineReady :
    concreteSingletonHeadRefreshDescription.SubroutineReady :=
  concreteSingletonHeadRefreshDescription_caseContract.subroutineReady

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC

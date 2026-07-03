import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.OneGapCompactor

set_option doc.verso true

/-!
# Counted suffix-boundary locator

This module packages the reusable finite-machine obligation for locating the
boundary before a suffix when the right padding contains a blank count window
whose length is exactly the suffix length.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers

def countedSuffixBoundaryLocatorPadding
    (guard : Option Bool) (suffix : Word Bool)
    (tail : List (Option Bool)) : List (Option Bool) :=
  guard ::
    List.append
      (List.replicate suffix.length (none : Option Bool))
      tail

def countedSuffixBoundaryLocatorSourceTape
    (pref suffix : Word Bool) (guard : Option Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  rightEdgeScanTargetTapeFromLeft [none] (List.append pref suffix)
    (countedSuffixBoundaryLocatorPadding guard suffix tail)

def countedSuffixBoundaryLocatorTargetTape
    (pref suffix : Word Bool) (guard : Option Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  rightEdgeScanSourceTapeFromLeft
    (none :: pref.reverse.map some) suffix
    (countedSuffixBoundaryLocatorPadding guard suffix tail)

def CountedSuffixBoundaryLocatorSpec
    (locator : MachineDescription) : Prop :=
  locator.SubroutineReady ∧
    forall (pref suffixRest : Word Bool)
      (suffixFirst guardBit tailFirst : Bool)
      (tail : List (Option Bool)),
      locator.HaltsFromTape
        (countedSuffixBoundaryLocatorSourceTape
          pref (suffixFirst :: suffixRest) (some guardBit)
          (some tailFirst :: tail))
        (countedSuffixBoundaryLocatorTargetTape
          pref (suffixFirst :: suffixRest) (some guardBit)
          (some tailFirst :: tail))

def CountedSuffixBoundaryLocatorConstruction : Prop :=
  exists locator : MachineDescription,
    CountedSuffixBoundaryLocatorSpec locator

def countedSuffixBoundaryLeftAdvanceCurrentTape
    (pref leftStack : Word Bool) (current guardBit : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append (leftStack.map some)
      (List.append (pref.reverse.map some) [none]))
    (some current ::
      none ::
      some guardBit ::
      List.append
        (List.replicate (leftStack.length + 1) (none : Option Bool))
        tail)

def countedSuffixBoundaryLeftAdvanceTape
    (pref leftStack processed : Word Bool) (guardBit : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append (leftStack.map some)
      (List.append (pref.reverse.map some) [none]))
    (none ::
      List.append (processed.map some)
        (List.append
          (List.replicate processed.length (none : Option Bool))
          (some guardBit ::
            List.append
              (List.replicate leftStack.length (none : Option Bool))
              tail)))

def countedSuffixBoundaryLeftAdvancedTape
    (pref suffix : Word Bool) (guardBit : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append (pref.reverse.map some) [none])
    (none ::
      List.append (suffix.map some)
        (List.append
          (List.replicate suffix.length (none : Option Bool))
          (some guardBit :: tail)))

def countedSuffixBoundaryPrefixShiftedTape
    (pref suffix : Word Bool) (guardBit : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  tapeAtCells (none :: pref.reverse.map some)
    (none ::
      List.append (suffix.map some)
        (List.append
          (List.replicate suffix.length (none : Option Bool))
          (some guardBit :: tail)))

def countedSuffixBoundaryRestoreLoopTape
    (pref processed remaining : Word Bool) (guardBit : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append (processed.reverse.map some)
      (none :: pref.reverse.map some))
    (none ::
      List.append (remaining.map some)
        (List.append
          (List.replicate remaining.length (none : Option Bool))
          (some guardBit ::
            List.append
              (List.replicate processed.length (none : Option Bool))
              tail)))

def countedSuffixBoundaryLeftAdvanceDescription : MachineDescription where
  stateCount := 30
  start := 0
  halt := 29
  transitions :=
    [ transition 0 (some false) (some false) Direction.right 1
    , transition 0 (some true) (some true) Direction.right 1
    , transition 1 none none Direction.right 2
    , transition 2 (some false) none Direction.right 3
    , transition 2 (some true) none Direction.right 4
    , transition 3 none (some false) Direction.left 5
    , transition 4 none (some true) Direction.left 5
    , transition 5 none none Direction.left 5
    , transition 5 (some false) none Direction.right 6
    , transition 5 (some true) none Direction.right 7
    , transition 6 none (some false) Direction.left 20
    , transition 7 none (some true) Direction.left 20

    , transition 20 none none Direction.right 21
    , transition 21 (some false) (some false) Direction.right 21
    , transition 21 (some true) (some true) Direction.right 21
    , transition 21 none none Direction.right 22
    , transition 22 none none Direction.right 22
    , transition 22 (some false) (some false) Direction.right 23
    , transition 22 (some true) (some true) Direction.right 24
    , transition 23 none (some false) Direction.left 25
    , transition 24 none (some true) Direction.left 26
    , transition 23 (some false) (some false) Direction.left 27
    , transition 23 (some true) (some true) Direction.left 27
    , transition 24 (some false) (some false) Direction.left 27
    , transition 24 (some true) (some true) Direction.left 27
    , transition 25 (some false) none Direction.left 28
    , transition 26 (some true) none Direction.left 28
    , transition 27 (some false) (some false) Direction.left 15
    , transition 27 (some true) (some true) Direction.left 15
    , transition 28 none none Direction.left 28
    , transition 28 (some false) (some false) Direction.left 11
    , transition 28 (some true) (some true) Direction.left 11
    , transition 11 (some false) (some false) Direction.left 11
    , transition 11 (some true) (some true) Direction.left 11
    , transition 11 none none Direction.left 12
    , transition 12 (some false) none Direction.right 13
    , transition 12 (some true) none Direction.right 14
    , transition 13 none (some false) Direction.left 20
    , transition 14 none (some true) Direction.left 20

    , transition 27 none none Direction.left 15
    , transition 15 none none Direction.left 15
    , transition 15 (some false) (some false) Direction.left 16
    , transition 15 (some true) (some true) Direction.left 16
    , transition 16 (some false) (some false) Direction.left 16
    , transition 16 (some true) (some true) Direction.left 16
    , transition 16 none none Direction.right 17
    , transition 17 (some false) (some false) Direction.left 29
    , transition 17 (some true) (some true) Direction.left 29
    ]

def countedSuffixBoundaryPrefixShiftDescription : MachineDescription where
  stateCount := 14
  start := 0
  halt := 13
  transitions :=
    [ transition 0 none none Direction.left 1
    , transition 1 none none Direction.right 13
    , transition 1 (some false) none Direction.left 2
    , transition 1 (some true) none Direction.left 3
    , transition 2 none (some false) Direction.right 6
    , transition 2 (some false) (some false) Direction.left 2
    , transition 2 (some true) (some false) Direction.left 3
    , transition 3 none (some true) Direction.right 6
    , transition 3 (some false) (some true) Direction.left 2
    , transition 3 (some true) (some true) Direction.left 3
    , transition 6 (some false) (some false) Direction.right 6
    , transition 6 (some true) (some true) Direction.right 6
    , transition 6 none none Direction.right 13
    ]

def countedSuffixBoundaryRightRestoreDescription : MachineDescription where
  stateCount := 40
  start := 0
  halt := 39
  transitions :=
    [ transition 0 none none Direction.right 1
    , transition 1 (some false) none Direction.left 2
    , transition 1 (some true) none Direction.left 3
    , transition 2 none (some false) Direction.right 4
    , transition 3 none (some true) Direction.right 4
    , transition 4 none none Direction.right 30
    , transition 4 (some false) (some false) Direction.right 10
    , transition 4 (some true) (some true) Direction.right 10
    , transition 30 none none Direction.right 20
    , transition 30 (some false) (some false) Direction.right 10
    , transition 30 (some true) (some true) Direction.right 10

    , transition 10 (some false) (some false) Direction.right 10
    , transition 10 (some true) (some true) Direction.right 10
    , transition 10 none none Direction.right 11
    , transition 11 none none Direction.right 11
    , transition 11 (some false) none Direction.left 12
    , transition 11 (some true) none Direction.left 13
    , transition 12 none (some false) Direction.left 14
    , transition 13 none (some true) Direction.left 14
    , transition 14 none none Direction.left 14
    , transition 14 (some false) (some false) Direction.left 15
    , transition 14 (some true) (some true) Direction.left 15
    , transition 15 (some false) (some false) Direction.left 15
    , transition 15 (some true) (some true) Direction.left 15
    , transition 15 none none Direction.right 31
    , transition 31 (some false) (some false) Direction.left 0
    , transition 31 (some true) (some true) Direction.left 0

    , transition 20 none none Direction.right 20
    , transition 20 (some false) none Direction.left 21
    , transition 20 (some true) none Direction.left 22
    , transition 21 none (some false) Direction.left 39
    , transition 22 none (some true) Direction.left 39
    ]

def countedSuffixBoundaryLocatorDescription : MachineDescription :=
  canonicalSeqDescription
    countedSuffixBoundaryLeftAdvanceDescription
    (canonicalSeqDescription
      countedSuffixBoundaryPrefixShiftDescription
      (canonicalSeqDescription
        countedSuffixBoundaryRightRestoreDescription
        rightEdgeRewindDescription))

theorem countedSuffixBoundaryLeftAdvanceDescription_wellFormed :
    countedSuffixBoundaryLeftAdvanceDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := countedSuffixBoundaryLeftAdvanceDescription.transitions)
      (stateCount := countedSuffixBoundaryLeftAdvanceDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := countedSuffixBoundaryLeftAdvanceDescription.transitions)
      (by decide)

theorem countedSuffixBoundaryLeftAdvanceDescription_haltTransitionFree :
    countedSuffixBoundaryLeftAdvanceDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := countedSuffixBoundaryLeftAdvanceDescription.transitions)
    (state := countedSuffixBoundaryLeftAdvanceDescription.halt)
    (by decide)

theorem countedSuffixBoundaryLeftAdvanceDescription_subroutineReady :
    countedSuffixBoundaryLeftAdvanceDescription.SubroutineReady :=
  ⟨countedSuffixBoundaryLeftAdvanceDescription_wellFormed,
    countedSuffixBoundaryLeftAdvanceDescription_haltTransitionFree⟩

theorem countedSuffixBoundaryPrefixShiftDescription_wellFormed :
    countedSuffixBoundaryPrefixShiftDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := countedSuffixBoundaryPrefixShiftDescription.transitions)
      (stateCount := countedSuffixBoundaryPrefixShiftDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := countedSuffixBoundaryPrefixShiftDescription.transitions)
      (by decide)

theorem countedSuffixBoundaryPrefixShiftDescription_haltTransitionFree :
    countedSuffixBoundaryPrefixShiftDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := countedSuffixBoundaryPrefixShiftDescription.transitions)
    (state := countedSuffixBoundaryPrefixShiftDescription.halt)
    (by decide)

theorem countedSuffixBoundaryPrefixShiftDescription_subroutineReady :
    countedSuffixBoundaryPrefixShiftDescription.SubroutineReady :=
  ⟨countedSuffixBoundaryPrefixShiftDescription_wellFormed,
    countedSuffixBoundaryPrefixShiftDescription_haltTransitionFree⟩

theorem countedSuffixBoundaryRightRestoreDescription_wellFormed :
    countedSuffixBoundaryRightRestoreDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := countedSuffixBoundaryRightRestoreDescription.transitions)
      (stateCount := countedSuffixBoundaryRightRestoreDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := countedSuffixBoundaryRightRestoreDescription.transitions)
      (by decide)

theorem countedSuffixBoundaryRightRestoreDescription_haltTransitionFree :
    countedSuffixBoundaryRightRestoreDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := countedSuffixBoundaryRightRestoreDescription.transitions)
    (state := countedSuffixBoundaryRightRestoreDescription.halt)
    (by decide)

theorem countedSuffixBoundaryRightRestoreDescription_subroutineReady :
    countedSuffixBoundaryRightRestoreDescription.SubroutineReady :=
  ⟨countedSuffixBoundaryRightRestoreDescription_wellFormed,
    countedSuffixBoundaryRightRestoreDescription_haltTransitionFree⟩

theorem countedSuffixBoundaryLocatorDescription_subroutineReady :
    countedSuffixBoundaryLocatorDescription.SubroutineReady :=
  canonicalSeqDescription_subroutineReady
    countedSuffixBoundaryLeftAdvanceDescription_subroutineReady
    (canonicalSeqDescription_subroutineReady
      countedSuffixBoundaryPrefixShiftDescription_subroutineReady
      (canonicalSeqDescription_subroutineReady
        countedSuffixBoundaryRightRestoreDescription_subroutineReady
        rightEdgeRewindDescription_subroutineReady))

private abbrev LeftAdvance :=
  countedSuffixBoundaryLeftAdvanceDescription

private abbrev PrefixShift :=
  countedSuffixBoundaryPrefixShiftDescription

private abbrev RightRestore :=
  countedSuffixBoundaryRightRestoreDescription

theorem countedSuffixBoundaryLeftAdvanceDescription_run_initial
    (pref leftStack : Word Bool) (current guardBit : Bool)
    (tail : List (Option Bool)) :
    LeftAdvance.runConfig 8
        { state := LeftAdvance.start
          tape :=
            countedSuffixBoundaryLeftAdvanceCurrentTape
              pref leftStack current guardBit tail } =
      { state := 20
        tape :=
          countedSuffixBoundaryLeftAdvanceTape
            pref leftStack [current] guardBit tail } := by
  cases current <;> cases guardBit <;>
    simp [LeftAdvance, countedSuffixBoundaryLeftAdvanceDescription,
      countedSuffixBoundaryLeftAdvanceCurrentTape,
      countedSuffixBoundaryLeftAdvanceTape, runConfig, stepConfig,
      lookupTransition, Matches, transition, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft, Tape.moveRight, tapeAtCells,
      List.replicate_succ]

theorem countedSuffixBoundaryLeftAdvanceDescription_run_scan_processed
    (left : List (Option Bool)) (processed : Word Bool)
    (right : List (Option Bool)) :
    LeftAdvance.runConfig (processed.length + 1)
        { state := 21
          tape :=
            tapeAtCells left
              (List.append (processed.map some) (none :: right)) } =
      { state := 22
        tape :=
          tapeAtCells
            (none ::
              List.append (processed.reverse.map some) left)
            right } := by
  induction processed generalizing left with
  | nil =>
      cases right <;>
        simp [LeftAdvance, countedSuffixBoundaryLeftAdvanceDescription,
          runConfig, stepConfig, lookupTransition, Matches, transition,
          Tape.read, Tape.write, Tape.move, Tape.moveRight,
          tapeAtCells]
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 1 =
        1 + (rest.length + 1) by
        simp
        lia]
      rw [runConfig_add]
      change
        LeftAdvance.runConfig (rest.length + 1)
            (LeftAdvance.runConfig 1
              { state := 21
                tape :=
                  tapeAtCells left
                    (some bit ::
                      List.append (rest.map some) (none :: right)) }) =
          { state := 22
            tape :=
              tapeAtCells
                (none ::
                  List.append ((bit :: rest).reverse.map some) left)
                right }
      have hstep :
          LeftAdvance.runConfig 1
              { state := 21
                tape :=
                  tapeAtCells left
                    (some bit ::
                      List.append (rest.map some) (none :: right)) } =
            { state := 21
              tape :=
                tapeAtCells (some bit :: left)
                  (List.append (rest.map some) (none :: right)) } := by
        cases bit <;> cases hright :
            List.append (rest.map some) (none :: right) <;>
          simp [LeftAdvance,
            countedSuffixBoundaryLeftAdvanceDescription, runConfig,
            stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.write, Tape.move, Tape.moveRight,
            tapeAtCells]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: left)

theorem countedSuffixBoundaryLeftAdvanceDescription_run_scan_count_false
    (left : List (Option Bool)) (blanks : Nat)
    (right : List (Option Bool)) :
    LeftAdvance.runConfig (blanks + 1)
        { state := 22
          tape :=
            tapeAtCells left
              (List.append
                (List.replicate blanks (none : Option Bool))
                (some false :: right)) } =
      { state := 23
        tape :=
          tapeAtCells
            (some false ::
              List.append
                (List.replicate blanks (none : Option Bool))
                left)
            right } := by
  induction blanks generalizing left with
  | zero =>
      cases right <;>
        simp [LeftAdvance, countedSuffixBoundaryLeftAdvanceDescription,
          runConfig, stepConfig, lookupTransition, Matches, transition,
          Tape.read, Tape.write, Tape.move, Tape.moveRight,
          tapeAtCells]
  | succ blanks ih =>
      rw [show blanks + 1 + 1 = 1 + (blanks + 1) by lia]
      rw [runConfig_add]
      change
        LeftAdvance.runConfig (blanks + 1)
            (LeftAdvance.runConfig 1
              { state := 22
                tape :=
                  tapeAtCells left
                    (none ::
                      List.append
                        (List.replicate blanks (none : Option Bool))
                        (some false :: right)) }) =
          { state := 23
            tape :=
              tapeAtCells
                (some false ::
                  List.append
                    (List.replicate (blanks + 1) (none : Option Bool))
                    left)
                right }
      have hstep :
          LeftAdvance.runConfig 1
              { state := 22
                tape :=
                  tapeAtCells left
                    (none ::
                      List.append
                        (List.replicate blanks (none : Option Bool))
                        (some false :: right)) } =
            { state := 22
              tape :=
                tapeAtCells (none :: left)
                  (List.append
                    (List.replicate blanks (none : Option Bool))
                    (some false :: right)) } := by
        cases hright :
            List.append
              (List.replicate blanks (none : Option Bool))
              (some false :: right) <;>
          simp [LeftAdvance,
            countedSuffixBoundaryLeftAdvanceDescription, runConfig,
            stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.write, Tape.move, Tape.moveRight,
            tapeAtCells]
      rw [hstep]
      have htail :
          List.append
              (List.replicate blanks (none : Option Bool))
              (none :: left) =
            none ::
              List.append
                (List.replicate blanks (none : Option Bool))
                left :=
        replicate_none_append_none_cons blanks left
      have hih := ih (none :: left)
      rw [htail] at hih
      simpa [List.replicate_succ, List.append_assoc] using hih

theorem countedSuffixBoundaryLeftAdvanceDescription_run_scan_count_true
    (left : List (Option Bool)) (blanks : Nat)
    (right : List (Option Bool)) :
    LeftAdvance.runConfig (blanks + 1)
        { state := 22
          tape :=
            tapeAtCells left
              (List.append
                (List.replicate blanks (none : Option Bool))
                (some true :: right)) } =
      { state := 24
        tape :=
          tapeAtCells
            (some true ::
              List.append
                (List.replicate blanks (none : Option Bool))
                left)
            right } := by
  induction blanks generalizing left with
  | zero =>
      cases right <;>
        simp [LeftAdvance, countedSuffixBoundaryLeftAdvanceDescription,
          runConfig, stepConfig, lookupTransition, Matches, transition,
          Tape.read, Tape.write, Tape.move, Tape.moveRight,
          tapeAtCells]
  | succ blanks ih =>
      rw [show blanks + 1 + 1 = 1 + (blanks + 1) by lia]
      rw [runConfig_add]
      change
        LeftAdvance.runConfig (blanks + 1)
            (LeftAdvance.runConfig 1
              { state := 22
                tape :=
                  tapeAtCells left
                    (none ::
                      List.append
                        (List.replicate blanks (none : Option Bool))
                        (some true :: right)) }) =
          { state := 24
            tape :=
              tapeAtCells
                (some true ::
                  List.append
                    (List.replicate (blanks + 1) (none : Option Bool))
                    left)
                right }
      have hstep :
          LeftAdvance.runConfig 1
              { state := 22
                tape :=
                  tapeAtCells left
                    (none ::
                      List.append
                        (List.replicate blanks (none : Option Bool))
                        (some true :: right)) } =
            { state := 22
              tape :=
                tapeAtCells (none :: left)
                  (List.append
                    (List.replicate blanks (none : Option Bool))
                    (some true :: right)) } := by
        cases hright :
            List.append
              (List.replicate blanks (none : Option Bool))
              (some true :: right) <;>
          simp [LeftAdvance,
            countedSuffixBoundaryLeftAdvanceDescription, runConfig,
            stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.write, Tape.move, Tape.moveRight,
            tapeAtCells]
      rw [hstep]
      have htail :
          List.append
              (List.replicate blanks (none : Option Bool))
              (none :: left) =
            none ::
              List.append
                (List.replicate blanks (none : Option Bool))
                left :=
        replicate_none_append_none_cons blanks left
      have hih := ih (none :: left)
      rw [htail] at hih
      simpa [List.replicate_succ, List.append_assoc] using hih

def countedSuffixBoundaryLeftScanTape
    (baseLeft : List (Option Bool)) (processedLeft : Word Bool)
    (current : Bool) (right : List (Option Bool)) : Tape Bool :=
  match processedLeft with
  | [] => tapeAtCells (some current :: baseLeft) (none :: right)
  | bit :: rest =>
      tapeAtCells
        (List.append (rest.map some)
          (none :: some current :: baseLeft))
        (some bit :: right)

theorem countedSuffixBoundaryLeftAdvanceDescription_run_return_blanks
    (baseLeft : List (Option Bool)) (processedLeft : Word Bool)
    (blanks : Nat) (last current : Bool)
    (right : List (Option Bool)) :
    LeftAdvance.runConfig (blanks + 2)
        { state := 28
          tape :=
            tapeAtCells
              (List.append
                (List.replicate blanks (none : Option Bool))
                (some last ::
                  List.append (processedLeft.map some)
                    (none :: some current :: baseLeft)))
              (none :: right) } =
      { state := 11
        tape :=
          countedSuffixBoundaryLeftScanTape
            baseLeft processedLeft current
            (some last ::
              List.append
                (List.replicate (blanks + 1) (none : Option Bool))
                right) } := by
  induction blanks generalizing baseLeft processedLeft right with
  | zero =>
      cases last <;> cases current <;> cases processedLeft <;>
        simp [LeftAdvance, countedSuffixBoundaryLeftAdvanceDescription,
          countedSuffixBoundaryLeftScanTape, runConfig, stepConfig,
          lookupTransition, Matches, transition, Tape.read, Tape.write,
          Tape.move, Tape.moveLeft, tapeAtCells]
  | succ blanks ih =>
      rw [show blanks + 1 + 2 = 1 + (blanks + 2) by lia]
      rw [runConfig_add]
      change
        LeftAdvance.runConfig (blanks + 2)
            (LeftAdvance.runConfig 1
              { state := 28
                tape :=
                  tapeAtCells
                    (none ::
                      List.append
                        (List.replicate blanks (none : Option Bool))
                        (some last ::
                          List.append (processedLeft.map some)
                            (none :: some current :: baseLeft)))
                    (none :: right) }) =
          { state := 11
            tape :=
              countedSuffixBoundaryLeftScanTape
                baseLeft processedLeft current
                (some last ::
                  List.append
                    (List.replicate (blanks + 1 + 1)
                      (none : Option Bool))
                    right) }
      have hstep :
          LeftAdvance.runConfig 1
              { state := 28
                tape :=
                  tapeAtCells
                    (none ::
                      List.append
                        (List.replicate blanks (none : Option Bool))
                        (some last ::
                          List.append (processedLeft.map some)
                            (none :: some current :: baseLeft)))
                    (none :: right) } =
            { state := 28
              tape :=
                tapeAtCells
                  (List.append
                    (List.replicate blanks (none : Option Bool))
                    (some last ::
                      List.append (processedLeft.map some)
                        (none :: some current :: baseLeft)))
                  (none :: none :: right) } := by
        simp [LeftAdvance,
          countedSuffixBoundaryLeftAdvanceDescription, runConfig,
          stepConfig, lookupTransition, Matches, transition,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          tapeAtCells]
      rw [hstep]
      have hih :=
        ih baseLeft processedLeft (none :: right)
      have htail :
          List.append
              (List.replicate (blanks + 1) (none : Option Bool))
              (none :: right) =
            none ::
              List.append
                (List.replicate (blanks + 1) (none : Option Bool))
                right :=
        replicate_none_append_none_cons (blanks + 1) right
      rw [htail] at hih
      simpa [List.replicate_succ, List.append_assoc] using hih

theorem countedSuffixBoundaryLeftAdvanceDescription_run_scan_left_and_swap
    (baseLeft : List (Option Bool)) (processedLeft : Word Bool)
    (current : Bool) (right : List (Option Bool)) :
    LeftAdvance.runConfig (processedLeft.length + 3)
        { state := 11
          tape :=
            countedSuffixBoundaryLeftScanTape
              baseLeft processedLeft current right } =
      { state := 20
        tape :=
          tapeAtCells baseLeft
            (none ::
              some current ::
              List.append (processedLeft.reverse.map some) right) } := by
  induction processedLeft generalizing right with
  | nil =>
      cases current <;> cases right <;>
        simp [LeftAdvance, countedSuffixBoundaryLeftAdvanceDescription,
          countedSuffixBoundaryLeftScanTape, runConfig, stepConfig,
          lookupTransition, Matches, transition, Tape.read, Tape.write,
          Tape.move, Tape.moveLeft, Tape.moveRight, tapeAtCells]
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 3 =
        1 + (rest.length + 3) by
        simp
        lia]
      rw [runConfig_add]
      change
        LeftAdvance.runConfig (rest.length + 3)
            (LeftAdvance.runConfig 1
              { state := 11
                tape :=
                  countedSuffixBoundaryLeftScanTape
                    baseLeft (bit :: rest) current right }) =
          { state := 20
            tape :=
              tapeAtCells baseLeft
                (none ::
                  some current ::
                  List.append ((bit :: rest).reverse.map some)
                    right) }
      have hstep :
          LeftAdvance.runConfig 1
              { state := 11
                tape :=
                  countedSuffixBoundaryLeftScanTape
                    baseLeft (bit :: rest) current right } =
            { state := 11
              tape :=
                countedSuffixBoundaryLeftScanTape
                  baseLeft rest current (some bit :: right) } := by
        cases bit <;> cases rest <;> cases right <;>
          simp [LeftAdvance,
            countedSuffixBoundaryLeftAdvanceDescription,
            countedSuffixBoundaryLeftScanTape, runConfig, stepConfig,
            lookupTransition, Matches, transition, Tape.read,
            Tape.write, Tape.move, Tape.moveLeft, tapeAtCells]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: right)

theorem tapeAtCells_moveLeft_replicate_none_cons
    (n : Nat) (leftTail right : List (Option Bool)) :
    Tape.move Direction.left
        (tapeAtCells
          (List.append (List.replicate n (none : Option Bool))
            (none :: leftTail))
          (none :: right)) =
      tapeAtCells
        (List.append (List.replicate n (none : Option Bool))
          leftTail)
        (none :: none :: right) := by
  induction n generalizing leftTail with
  | zero =>
      cases leftTail <;> cases right <;>
        simp [tapeAtCells, Tape.move, Tape.moveLeft]
  | succ n ih =>
      simp [List.replicate_succ, tapeAtCells, Tape.move,
        Tape.moveLeft]
      exact replicate_none_append_none_cons n leftTail

theorem countedSuffixBoundaryLeftAdvanceDescription_run_shift_false
    (baseLeft : List (Option Bool)) (processedLeft : Word Bool)
    (last current : Bool) (rightTail : List (Option Bool)) :
    LeftAdvance.runConfig (2 * processedLeft.length + 7)
        { state := 23
          tape :=
            tapeAtCells
              (some false ::
                List.append
                  (List.replicate processedLeft.length
                    (none : Option Bool))
                  (none ::
                    some last ::
                    List.append (processedLeft.map some)
                      (none :: some current :: baseLeft)))
              (none :: rightTail) } =
      { state := 20
        tape :=
          tapeAtCells baseLeft
            (none ::
              some current ::
              List.append (processedLeft.reverse.map some)
                (some last ::
                  List.append
                    (List.replicate (processedLeft.length + 2)
                      (none : Option Bool))
                    (some false :: rightTail))) } := by
  rw [show 2 * processedLeft.length + 7 =
    2 + ((processedLeft.length + 2) +
      (processedLeft.length + 3)) by lia]
  rw [runConfig_add]
  have hshift :
      LeftAdvance.runConfig 2
          { state := 23
            tape :=
              tapeAtCells
                (some false ::
                  List.append
                    (List.replicate processedLeft.length
                      (none : Option Bool))
                    (none ::
                      some last ::
                      List.append (processedLeft.map some)
                        (none :: some current :: baseLeft)))
                (none :: rightTail) } =
        { state := 28
          tape :=
            tapeAtCells
              (List.append
                (List.replicate processedLeft.length
                  (none : Option Bool))
                (some last ::
                  List.append (processedLeft.map some)
                    (none :: some current :: baseLeft)))
              (none :: none :: some false :: rightTail) } := by
    have hmove :=
      tapeAtCells_moveLeft_replicate_none_cons
        processedLeft.length
        (some last ::
          List.append (processedLeft.map some)
            (none :: some current :: baseLeft))
        (some false :: rightTail)
    simpa [LeftAdvance, countedSuffixBoundaryLeftAdvanceDescription,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, tapeAtCells]
      using hmove
  rw [hshift]
  rw [runConfig_add]
  rw [
    countedSuffixBoundaryLeftAdvanceDescription_run_return_blanks
      baseLeft processedLeft processedLeft.length last current
      (none :: some false :: rightTail)]
  have htail :
      List.append
          (List.replicate (processedLeft.length + 1)
            (none : Option Bool))
          (none :: some false :: rightTail) =
        List.append
          (List.replicate (processedLeft.length + 2)
            (none : Option Bool))
          (some false :: rightTail) := by
    rw [replicate_none_append_none_cons]
    simp [List.replicate_succ]
  rw [htail]
  simpa [List.append_assoc] using
    countedSuffixBoundaryLeftAdvanceDescription_run_scan_left_and_swap
      baseLeft processedLeft current
      (some last ::
        List.append
          (List.replicate (processedLeft.length + 2)
            (none : Option Bool))
          (some false :: rightTail))

theorem countedSuffixBoundaryLeftAdvanceDescription_run_shift_true
    (baseLeft : List (Option Bool)) (processedLeft : Word Bool)
    (last current : Bool) (rightTail : List (Option Bool)) :
    LeftAdvance.runConfig (2 * processedLeft.length + 7)
        { state := 24
          tape :=
            tapeAtCells
              (some true ::
                List.append
                  (List.replicate processedLeft.length
                    (none : Option Bool))
                  (none ::
                    some last ::
                    List.append (processedLeft.map some)
                      (none :: some current :: baseLeft)))
              (none :: rightTail) } =
      { state := 20
        tape :=
          tapeAtCells baseLeft
            (none ::
              some current ::
              List.append (processedLeft.reverse.map some)
                (some last ::
                  List.append
                    (List.replicate (processedLeft.length + 2)
                      (none : Option Bool))
                    (some true :: rightTail))) } := by
  rw [show 2 * processedLeft.length + 7 =
    2 + ((processedLeft.length + 2) +
      (processedLeft.length + 3)) by lia]
  rw [runConfig_add]
  have hshift :
      LeftAdvance.runConfig 2
          { state := 24
            tape :=
              tapeAtCells
                (some true ::
                  List.append
                    (List.replicate processedLeft.length
                      (none : Option Bool))
                    (none ::
                      some last ::
                      List.append (processedLeft.map some)
                        (none :: some current :: baseLeft)))
                (none :: rightTail) } =
        { state := 28
          tape :=
            tapeAtCells
              (List.append
                (List.replicate processedLeft.length
                  (none : Option Bool))
                (some last ::
                  List.append (processedLeft.map some)
                    (none :: some current :: baseLeft)))
              (none :: none :: some true :: rightTail) } := by
    have hmove :=
      tapeAtCells_moveLeft_replicate_none_cons
        processedLeft.length
        (some last ::
          List.append (processedLeft.map some)
            (none :: some current :: baseLeft))
        (some true :: rightTail)
    simpa [LeftAdvance, countedSuffixBoundaryLeftAdvanceDescription,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, tapeAtCells]
      using hmove
  rw [hshift]
  rw [runConfig_add]
  rw [
    countedSuffixBoundaryLeftAdvanceDescription_run_return_blanks
      baseLeft processedLeft processedLeft.length last current
      (none :: some true :: rightTail)]
  have htail :
      List.append
          (List.replicate (processedLeft.length + 1)
            (none : Option Bool))
          (none :: some true :: rightTail) =
        List.append
          (List.replicate (processedLeft.length + 2)
            (none : Option Bool))
          (some true :: rightTail) := by
    rw [replicate_none_append_none_cons]
    simp [List.replicate_succ]
  rw [htail]
  simpa [List.append_assoc] using
    countedSuffixBoundaryLeftAdvanceDescription_run_scan_left_and_swap
      baseLeft processedLeft current
      (some last ::
        List.append
          (List.replicate (processedLeft.length + 2)
            (none : Option Bool))
          (some true :: rightTail))

def countedSuffixBoundaryLeftAdvanceLoopTape
    (pref remaining processedRev : Word Bool)
    (last guardBit : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  countedSuffixBoundaryLeftAdvanceTape pref remaining
    (List.append processedRev.reverse [last]) guardBit tail

theorem countedSuffixBoundaryLeftAdvanceDescription_run_loop_step
    (pref leftStack processedRev : Word Bool)
    (last current guardBit : Bool)
    (tail : List (Option Bool)) :
    exists steps : Nat,
      LeftAdvance.runConfig steps
          { state := 20
            tape :=
              countedSuffixBoundaryLeftAdvanceLoopTape
                pref (current :: leftStack) processedRev
                last guardBit tail } =
        { state := 20
          tape :=
            countedSuffixBoundaryLeftAdvanceLoopTape
              pref leftStack (List.append processedRev [current])
              last guardBit tail } := by
  refine ⟨4 * processedRev.length + 11, ?_⟩
  rw [show 4 * processedRev.length + 11 =
    1 + ((processedRev.length + 2) +
      ((processedRev.length + 1) +
        (2 * processedRev.length + 7))) by lia]
  rw [runConfig_add]
  let baseLeft : List (Option Bool) :=
    List.append (leftStack.map some)
      (List.append (pref.reverse.map some) [none])
  let processed : Word Bool :=
    List.append processedRev.reverse [last]
  have hstart :
      LeftAdvance.runConfig 1
          { state := 20
            tape :=
              countedSuffixBoundaryLeftAdvanceLoopTape
                pref (current :: leftStack) processedRev
                last guardBit tail } =
        { state := 21
          tape :=
            tapeAtCells
              (none :: some current :: baseLeft)
              (List.append (processed.map some)
                (none ::
                  List.append
                    (List.replicate processedRev.length
                      (none : Option Bool))
                    (some guardBit ::
                      List.append
                        (List.replicate (leftStack.length + 1)
                          (none : Option Bool))
                        tail))) } := by
    cases hrev : processedRev.reverse with
    | nil =>
        have hnil : processedRev = [] := by
          have h := congrArg List.reverse hrev
          simpa using h
        subst processedRev
        cases current <;> cases last <;> cases guardBit <;>
          simp [countedSuffixBoundaryLeftAdvanceLoopTape,
            countedSuffixBoundaryLeftAdvanceTape, baseLeft, processed,
            LeftAdvance, countedSuffixBoundaryLeftAdvanceDescription,
            runConfig, stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.write, Tape.move, Tape.moveRight,
            tapeAtCells, List.map_append, List.append_assoc]
    | cons head rest =>
        have hlen : rest.length + 1 = processedRev.length := by
          have h := congrArg List.length hrev
          simp at h
          omega
        cases current <;> cases last <;> cases guardBit <;>
          cases head <;>
          simp [countedSuffixBoundaryLeftAdvanceLoopTape,
            countedSuffixBoundaryLeftAdvanceTape, baseLeft, processed,
            LeftAdvance, countedSuffixBoundaryLeftAdvanceDescription,
            runConfig, stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.write, Tape.move, Tape.moveRight,
            tapeAtCells, List.map_append, List.append_assoc, hrev,
            hlen, List.replicate_succ]
  rw [hstart]
  rw [runConfig_add]
  rw [show processedRev.length + 2 = processed.length + 1 by
    simp [processed]]
  rw [
    countedSuffixBoundaryLeftAdvanceDescription_run_scan_processed
      (none :: some current :: baseLeft) processed
      (List.append
        (List.replicate processedRev.length (none : Option Bool))
        (some guardBit ::
          List.append
            (List.replicate (leftStack.length + 1)
              (none : Option Bool))
            tail))]
  rw [runConfig_add]
  have hprocessedLeft :
      List.append (processed.reverse.map some)
          (none :: some current :: baseLeft) =
        some last ::
          List.append (processedRev.map some)
            (none :: some current :: baseLeft) := by
    simp [processed, List.reverse_append, List.map_append,
      List.append_assoc]
  have hright :
      List.append
          (List.replicate (leftStack.length + 1)
            (none : Option Bool))
          tail =
        none ::
          List.append
            (List.replicate leftStack.length
              (none : Option Bool))
            tail := by
    simp [List.replicate_succ]
  cases guardBit
  · rw [
      countedSuffixBoundaryLeftAdvanceDescription_run_scan_count_false
        (none ::
          List.append (processed.reverse.map some)
            (none :: some current :: baseLeft))
        processedRev.length
        (List.append
          (List.replicate (leftStack.length + 1)
            (none : Option Bool))
          tail)]
    rw [hprocessedLeft, hright]
    rw [
      countedSuffixBoundaryLeftAdvanceDescription_run_shift_false
        baseLeft processedRev last current
        (List.append
          (List.replicate leftStack.length (none : Option Bool))
          tail)]
    simp [countedSuffixBoundaryLeftAdvanceLoopTape,
      countedSuffixBoundaryLeftAdvanceTape, baseLeft, processed,
      List.map_append, List.reverse_append, List.append_assoc,
      List.replicate_succ]
  · rw [
      countedSuffixBoundaryLeftAdvanceDescription_run_scan_count_true
        (none ::
          List.append (processed.reverse.map some)
            (none :: some current :: baseLeft))
        processedRev.length
        (List.append
          (List.replicate (leftStack.length + 1)
            (none : Option Bool))
          tail)]
    rw [hprocessedLeft, hright]
    rw [
      countedSuffixBoundaryLeftAdvanceDescription_run_shift_true
        baseLeft processedRev last current
        (List.append
          (List.replicate leftStack.length (none : Option Bool))
          tail)]
    simp [countedSuffixBoundaryLeftAdvanceLoopTape,
      countedSuffixBoundaryLeftAdvanceTape, baseLeft, processed,
      List.map_append, List.reverse_append, List.append_assoc,
      List.replicate_succ]

theorem countedSuffixBoundaryLeftAdvanceDescription_run_loop
    (pref remaining processedRev : Word Bool)
    (last guardBit : Bool)
    (tail : List (Option Bool)) :
    exists steps : Nat,
      LeftAdvance.runConfig steps
          { state := 20
            tape :=
              countedSuffixBoundaryLeftAdvanceLoopTape
                pref remaining processedRev last guardBit tail } =
        { state := 20
          tape :=
            countedSuffixBoundaryLeftAdvanceLoopTape
              pref [] (List.append processedRev remaining)
              last guardBit tail } := by
  induction remaining generalizing processedRev with
  | nil =>
      refine ⟨0, ?_⟩
      simp [runConfig]
  | cons current rest ih =>
      obtain ⟨stepCount, hstep⟩ :=
        countedSuffixBoundaryLeftAdvanceDescription_run_loop_step
          pref rest processedRev last current guardBit tail
      obtain ⟨restCount, hrest⟩ :=
        ih (List.append processedRev [current])
      refine ⟨stepCount + restCount, ?_⟩
      rw [runConfig_add]
      rw [hstep]
      simpa [List.append_assoc] using hrest

def countedSuffixBoundaryDoneScanTape
    (baseLeft : List (Option Bool)) (processedRev : Word Bool)
    (last : Bool) (right : List (Option Bool)) : Tape Bool :=
  match processedRev with
  | [] => tapeAtCells baseLeft (none :: some last :: right)
  | bit :: rest =>
      tapeAtCells
        (List.append (rest.map some) (none :: baseLeft))
        (some bit :: some last :: right)

theorem countedSuffixBoundaryLeftAdvanceDescription_run_done_scan_finish
    (baseLeft : List (Option Bool)) (processedRev : Word Bool)
    (last : Bool) (right : List (Option Bool)) :
    LeftAdvance.runConfig (processedRev.length + 2)
        { state := 16
          tape :=
            countedSuffixBoundaryDoneScanTape
              baseLeft processedRev last right } =
      { state := 29
        tape :=
          tapeAtCells baseLeft
            (none ::
              List.append (processedRev.reverse.map some)
                (some last :: right)) } := by
  induction processedRev generalizing last right with
  | nil =>
      cases last <;> cases right <;>
        simp [countedSuffixBoundaryDoneScanTape, LeftAdvance,
          countedSuffixBoundaryLeftAdvanceDescription, runConfig,
          stepConfig, lookupTransition, Matches, transition,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          Tape.moveRight, tapeAtCells]
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 2 =
        1 + (rest.length + 2) by
        simp
        lia]
      rw [runConfig_add]
      have hstep :
          LeftAdvance.runConfig 1
              { state := 16
                tape :=
                  countedSuffixBoundaryDoneScanTape
                    baseLeft (bit :: rest) last right } =
            { state := 16
              tape :=
                countedSuffixBoundaryDoneScanTape
                  baseLeft rest bit (some last :: right) } := by
        cases bit <;> cases last <;> cases rest <;> cases right <;>
          simp [countedSuffixBoundaryDoneScanTape, LeftAdvance,
            countedSuffixBoundaryLeftAdvanceDescription, runConfig,
            stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft,
            tapeAtCells]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih bit (some last :: right)

theorem countedSuffixBoundaryLeftAdvanceDescription_run_done_scan_bits
    (baseLeft : List (Option Bool)) (processedRev : Word Bool)
    (last : Bool) (right : List (Option Bool)) :
    LeftAdvance.runConfig (processedRev.length + 3)
        { state := 15
          tape :=
            tapeAtCells
              (List.append (processedRev.map some) (none :: baseLeft))
              (some last :: right) } =
      { state := 29
        tape :=
          tapeAtCells baseLeft
            (none ::
              List.append (processedRev.reverse.map some)
                (some last :: right)) } := by
  rw [show processedRev.length + 3 =
    1 + (processedRev.length + 2) by lia]
  rw [runConfig_add]
  have hstep :
      LeftAdvance.runConfig 1
          { state := 15
            tape :=
              tapeAtCells
                (List.append (processedRev.map some) (none :: baseLeft))
                (some last :: right) } =
        { state := 16
          tape :=
            countedSuffixBoundaryDoneScanTape
              baseLeft processedRev last right } := by
    cases processedRev <;> cases last <;>
      simp [countedSuffixBoundaryDoneScanTape, LeftAdvance,
        countedSuffixBoundaryLeftAdvanceDescription, runConfig,
        stepConfig, lookupTransition, Matches, transition,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft,
        tapeAtCells, List.replicate_succ]
  rw [hstep]
  exact
    countedSuffixBoundaryLeftAdvanceDescription_run_done_scan_finish
      baseLeft processedRev last right

theorem countedSuffixBoundaryLeftAdvanceDescription_run_done_return_blanks
    (baseLeft : List (Option Bool)) (processedRev : Word Bool)
    (blanks : Nat) (last : Bool) (right : List (Option Bool)) :
    LeftAdvance.runConfig (blanks + 1)
        { state := 15
          tape :=
            tapeAtCells
              (List.append
                (List.replicate blanks (none : Option Bool))
                (some last ::
                  List.append (processedRev.map some)
                    (none :: baseLeft)))
              (none :: right) } =
      { state := 15
        tape :=
          tapeAtCells
            (List.append (processedRev.map some) (none :: baseLeft))
            (some last ::
              List.append
                (List.replicate (blanks + 1)
                  (none : Option Bool))
                right) } := by
  induction blanks generalizing right with
  | zero =>
      cases last <;> cases processedRev <;> cases right <;>
        simp [LeftAdvance, countedSuffixBoundaryLeftAdvanceDescription,
          runConfig, stepConfig, lookupTransition, Matches, transition,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          tapeAtCells]
  | succ blanks ih =>
      rw [show blanks + 1 + 1 = 1 + (blanks + 1) by lia]
      rw [runConfig_add]
      rw [show
          List.append
              (List.replicate (blanks + 1) (none : Option Bool))
              (some last ::
                List.append (processedRev.map some)
                  (none :: baseLeft)) =
            none ::
              List.append
                (List.replicate blanks (none : Option Bool))
                (some last ::
                  List.append (processedRev.map some)
                    (none :: baseLeft)) by
        simp [List.replicate_succ]]
      have hstep :
          LeftAdvance.runConfig 1
              { state := 15
                tape :=
                  tapeAtCells
                    (none ::
                      List.append
                        (List.replicate blanks (none : Option Bool))
                        (some last ::
                          List.append (processedRev.map some)
                            (none :: baseLeft)))
                    (none :: right) } =
            { state := 15
              tape :=
                tapeAtCells
                  (List.append
                    (List.replicate blanks (none : Option Bool))
                    (some last ::
                      List.append (processedRev.map some)
                        (none :: baseLeft)))
                  (none :: none :: right) } := by
        simp [LeftAdvance, countedSuffixBoundaryLeftAdvanceDescription,
          runConfig, stepConfig, lookupTransition, Matches, transition,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          tapeAtCells]
      rw [hstep]
      have hih := ih (none :: right)
      have htail :
          List.append
              (List.replicate (blanks + 1) (none : Option Bool))
              (none :: right) =
            none ::
              List.append
                (List.replicate (blanks + 1)
                  (none : Option Bool))
                right :=
        replicate_none_append_none_cons (blanks + 1) right
      rw [htail] at hih
      have hrep :
          List.append
              (List.replicate (1 + (blanks + 1))
                (none : Option Bool))
              right =
            none ::
              none ::
                List.append
                  (List.replicate blanks (none : Option Bool))
                  right := by
        rw [show 1 + (blanks + 1) = (blanks + 1) + 1 by omega]
        simp [List.replicate_succ]
      rw [hrep]
      simpa [List.replicate_succ, List.append_assoc] using hih

theorem countedSuffixBoundaryLeftAdvanceDescription_run_done_false
    (baseLeft : List (Option Bool)) (processedRev : Word Bool)
    (last tailFirst : Bool) (tail : List (Option Bool)) :
    LeftAdvance.runConfig (2 * processedRev.length + 6)
        { state := 23
          tape :=
            tapeAtCells
              (some false ::
                List.append
                  (List.replicate processedRev.length
                    (none : Option Bool))
                  (none ::
                    some last ::
                    List.append (processedRev.map some)
                      (none :: baseLeft)))
              (some tailFirst :: tail) } =
      { state := 29
        tape :=
          tapeAtCells baseLeft
            (none ::
              List.append (processedRev.reverse.map some)
                (some last ::
                  List.append
                    (List.replicate (processedRev.length + 1)
                      (none : Option Bool))
                    (some false :: some tailFirst :: tail))) } := by
  rw [show 2 * processedRev.length + 6 =
    2 + ((processedRev.length + 1) +
      (processedRev.length + 3)) by lia]
  rw [runConfig_add]
  have hstart :
      LeftAdvance.runConfig 2
          { state := 23
            tape :=
              tapeAtCells
                (some false ::
                  List.append
                    (List.replicate processedRev.length
                      (none : Option Bool))
                    (none ::
                      some last ::
                      List.append (processedRev.map some)
                        (none :: baseLeft)))
                (some tailFirst :: tail) } =
        { state := 15
          tape :=
            tapeAtCells
              (List.append
                (List.replicate processedRev.length
                  (none : Option Bool))
                (some last ::
                  List.append (processedRev.map some)
                    (none :: baseLeft)))
              (none :: some false :: some tailFirst :: tail) } := by
    cases tailFirst <;> cases last <;> cases processedRev <;>
      simp [LeftAdvance, countedSuffixBoundaryLeftAdvanceDescription,
        runConfig, stepConfig, lookupTransition, Matches, transition,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft,
        tapeAtCells, List.replicate_succ] <;>
      try exact replicate_none_append_none_cons _ _
  rw [hstart]
  rw [runConfig_add]
  rw [
    countedSuffixBoundaryLeftAdvanceDescription_run_done_return_blanks
      baseLeft processedRev processedRev.length last
      (some false :: some tailFirst :: tail)]
  simpa [List.append_assoc] using
    countedSuffixBoundaryLeftAdvanceDescription_run_done_scan_bits
      baseLeft processedRev last
      (List.append
        (List.replicate (processedRev.length + 1)
          (none : Option Bool))
        (some false :: some tailFirst :: tail))

theorem countedSuffixBoundaryLeftAdvanceDescription_run_done_true
    (baseLeft : List (Option Bool)) (processedRev : Word Bool)
    (last tailFirst : Bool) (tail : List (Option Bool)) :
    LeftAdvance.runConfig (2 * processedRev.length + 6)
        { state := 24
          tape :=
            tapeAtCells
              (some true ::
                List.append
                  (List.replicate processedRev.length
                    (none : Option Bool))
                  (none ::
                    some last ::
                    List.append (processedRev.map some)
                      (none :: baseLeft)))
              (some tailFirst :: tail) } =
      { state := 29
        tape :=
          tapeAtCells baseLeft
            (none ::
              List.append (processedRev.reverse.map some)
                (some last ::
                  List.append
                    (List.replicate (processedRev.length + 1)
                      (none : Option Bool))
                    (some true :: some tailFirst :: tail))) } := by
  rw [show 2 * processedRev.length + 6 =
    2 + ((processedRev.length + 1) +
      (processedRev.length + 3)) by lia]
  rw [runConfig_add]
  have hstart :
      LeftAdvance.runConfig 2
          { state := 24
            tape :=
              tapeAtCells
                (some true ::
                  List.append
                    (List.replicate processedRev.length
                      (none : Option Bool))
                    (none ::
                      some last ::
                      List.append (processedRev.map some)
                        (none :: baseLeft)))
                (some tailFirst :: tail) } =
        { state := 15
          tape :=
            tapeAtCells
              (List.append
                (List.replicate processedRev.length
                  (none : Option Bool))
                (some last ::
                  List.append (processedRev.map some)
                    (none :: baseLeft)))
              (none :: some true :: some tailFirst :: tail) } := by
    cases tailFirst <;> cases last <;> cases processedRev <;>
      simp [LeftAdvance, countedSuffixBoundaryLeftAdvanceDescription,
        runConfig, stepConfig, lookupTransition, Matches, transition,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft,
        tapeAtCells, List.replicate_succ] <;>
      try exact replicate_none_append_none_cons _ _
  rw [hstart]
  rw [runConfig_add]
  rw [
    countedSuffixBoundaryLeftAdvanceDescription_run_done_return_blanks
      baseLeft processedRev processedRev.length last
      (some true :: some tailFirst :: tail)]
  simpa [List.append_assoc] using
    countedSuffixBoundaryLeftAdvanceDescription_run_done_scan_bits
      baseLeft processedRev last
      (List.append
        (List.replicate (processedRev.length + 1)
          (none : Option Bool))
        (some true :: some tailFirst :: tail))

theorem countedSuffixBoundaryLeftAdvanceDescription_run_done
    (pref processedRev : Word Bool)
    (last guardBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    exists steps : Nat,
      LeftAdvance.runConfig steps
          { state := 20
            tape :=
              countedSuffixBoundaryLeftAdvanceLoopTape
                pref [] processedRev last guardBit
                (some tailFirst :: tail) } =
        { state := 29
          tape :=
            countedSuffixBoundaryLeftAdvancedTape
              pref (List.append processedRev.reverse [last])
              guardBit (some tailFirst :: tail) } := by
  refine ⟨4 * processedRev.length + 10, ?_⟩
  rw [show 4 * processedRev.length + 10 =
    1 + ((processedRev.length + 2) +
      ((processedRev.length + 1) +
        (2 * processedRev.length + 6))) by lia]
  rw [runConfig_add]
  let baseLeft : List (Option Bool) :=
    List.append (pref.reverse.map some) [none]
  let processed : Word Bool :=
    List.append processedRev.reverse [last]
  have hstart :
      LeftAdvance.runConfig 1
          { state := 20
            tape :=
              countedSuffixBoundaryLeftAdvanceLoopTape
                pref [] processedRev last guardBit
                (some tailFirst :: tail) } =
        { state := 21
          tape :=
            tapeAtCells
              (none :: baseLeft)
              (List.append (processed.map some)
                (none ::
                  List.append
                    (List.replicate processedRev.length
                      (none : Option Bool))
                    (some guardBit :: some tailFirst :: tail))) } := by
    cases hrev : processedRev.reverse with
    | nil =>
        have hnil : processedRev = [] := by
          have h := congrArg List.reverse hrev
          simpa using h
        subst processedRev
        cases last <;> cases guardBit <;> cases tailFirst <;>
          simp [countedSuffixBoundaryLeftAdvanceLoopTape,
            countedSuffixBoundaryLeftAdvanceTape, baseLeft, processed,
            LeftAdvance, countedSuffixBoundaryLeftAdvanceDescription,
            runConfig, stepConfig, lookupTransition, Matches,
            transition, Tape.read, Tape.write, Tape.move,
            Tape.moveRight, tapeAtCells]
    | cons head rest =>
        have hlen : rest.length + 1 = processedRev.length := by
          have h := congrArg List.length hrev
          simp at h
          omega
        cases head <;> cases last <;> cases guardBit <;>
          cases tailFirst <;>
          simp [countedSuffixBoundaryLeftAdvanceLoopTape,
            countedSuffixBoundaryLeftAdvanceTape, baseLeft, processed,
            LeftAdvance, countedSuffixBoundaryLeftAdvanceDescription,
            runConfig, stepConfig, lookupTransition, Matches,
            transition, Tape.read, Tape.write, Tape.move,
            Tape.moveRight, tapeAtCells, hrev, hlen,
            List.replicate_succ]
  rw [hstart]
  rw [runConfig_add]
  rw [show processedRev.length + 2 = processed.length + 1 by
    simp [processed]]
  rw [
    countedSuffixBoundaryLeftAdvanceDescription_run_scan_processed
      (none :: baseLeft) processed
      (List.append
        (List.replicate processedRev.length (none : Option Bool))
        (some guardBit :: some tailFirst :: tail))]
  rw [runConfig_add]
  have hprocessedLeft :
      List.append (processed.reverse.map some)
          (none :: baseLeft) =
        some last ::
          List.append (processedRev.map some) (none :: baseLeft) := by
    simp [processed, List.reverse_append]
  cases guardBit
  · rw [
      countedSuffixBoundaryLeftAdvanceDescription_run_scan_count_false
        (none ::
          List.append (processed.reverse.map some)
            (none :: baseLeft))
        processedRev.length
        (some tailFirst :: tail)]
    rw [hprocessedLeft]
    rw [
      countedSuffixBoundaryLeftAdvanceDescription_run_done_false
        baseLeft processedRev last tailFirst tail]
    simp [countedSuffixBoundaryLeftAdvancedTape, baseLeft,
      processed, List.map_append, List.reverse_append,
      List.append_assoc]
  · rw [
      countedSuffixBoundaryLeftAdvanceDescription_run_scan_count_true
        (none ::
          List.append (processed.reverse.map some)
            (none :: baseLeft))
        processedRev.length
        (some tailFirst :: tail)]
    rw [hprocessedLeft]
    rw [
      countedSuffixBoundaryLeftAdvanceDescription_run_done_true
        baseLeft processedRev last tailFirst tail]
    simp [countedSuffixBoundaryLeftAdvancedTape, baseLeft,
      processed, List.map_append, List.reverse_append,
      List.append_assoc]

theorem countedSuffixBoundaryLeftAdvanceDescription_haltsFromTape
    (pref leftStack : Word Bool) (last guardBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    LeftAdvance.HaltsFromTape
      (countedSuffixBoundaryLeftAdvanceCurrentTape
        pref leftStack last guardBit (some tailFirst :: tail))
      (countedSuffixBoundaryLeftAdvancedTape
        pref (List.append leftStack.reverse [last]) guardBit
        (some tailFirst :: tail)) := by
  obtain ⟨loopSteps, hloop⟩ :=
    countedSuffixBoundaryLeftAdvanceDescription_run_loop
      pref leftStack [] last guardBit (some tailFirst :: tail)
  obtain ⟨doneSteps, hdone⟩ :=
    countedSuffixBoundaryLeftAdvanceDescription_run_done
      pref leftStack last guardBit tailFirst tail
  refine ⟨8 + loopSteps + doneSteps, ?_⟩
  have hrun :
      LeftAdvance.runConfig (8 + loopSteps + doneSteps)
          { state := LeftAdvance.start
            tape :=
              countedSuffixBoundaryLeftAdvanceCurrentTape
                pref leftStack last guardBit
                (some tailFirst :: tail) } =
        { state := 29
          tape :=
            countedSuffixBoundaryLeftAdvancedTape
              pref (List.append leftStack.reverse [last])
              guardBit (some tailFirst :: tail) } := by
    rw [runConfig_add]
    rw [runConfig_add]
    rw [
      countedSuffixBoundaryLeftAdvanceDescription_run_initial
        pref leftStack last guardBit (some tailFirst :: tail)]
    change
      LeftAdvance.runConfig doneSteps
          (LeftAdvance.runConfig loopSteps
            { state := 20
              tape :=
                countedSuffixBoundaryLeftAdvanceLoopTape
                  pref leftStack [] last guardBit
                  (some tailFirst :: tail) }) =
        { state := 29
          tape :=
            countedSuffixBoundaryLeftAdvancedTape
              pref (List.append leftStack.reverse [last])
              guardBit (some tailFirst :: tail) }
    rw [hloop]
    simpa using hdone
  constructor
  · rw [hrun]
    rfl
  · rw [hrun]

def countedSuffixBoundaryPrefixCarryState (carry : Bool) : Nat :=
  bif carry then 3 else 2

def countedSuffixBoundaryPrefixCarryTape
    (remaining : Word Bool) (right : List (Option Bool)) :
    Tape Bool :=
  match remaining with
  | [] => tapeAtCells [] (none :: right)
  | bit :: rest =>
      tapeAtCells (List.append (rest.map some) [none])
        (some bit :: right)

def countedSuffixBoundaryPrefixScanRightTape
    (shifted : Word Bool) (right : List (Option Bool)) :
    Tape Bool :=
  match shifted with
  | [] => tapeAtCells [] right
  | bit :: rest =>
      tapeAtCells [some bit]
        (List.append (rest.map some) right)

theorem countedSuffixBoundaryPrefixShiftDescription_run_carry_step
    (remaining : Word Bool) (current carry : Bool)
    (right : List (Option Bool)) :
    PrefixShift.runConfig 1
        { state := countedSuffixBoundaryPrefixCarryState carry
          tape :=
            countedSuffixBoundaryPrefixCarryTape
              (current :: remaining) right } =
      { state := countedSuffixBoundaryPrefixCarryState current
        tape :=
          countedSuffixBoundaryPrefixCarryTape
            remaining (some carry :: right) } := by
  cases current <;> cases carry <;> cases remaining <;> cases right <;>
    simp [PrefixShift, countedSuffixBoundaryPrefixShiftDescription,
      countedSuffixBoundaryPrefixCarryState,
      countedSuffixBoundaryPrefixCarryTape, runConfig, stepConfig,
      lookupTransition, Matches, transition, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft, tapeAtCells]

theorem countedSuffixBoundaryPrefixShiftDescription_run_carry_finish
    (carry : Bool) (right : List (Option Bool)) :
    PrefixShift.runConfig 1
        { state := countedSuffixBoundaryPrefixCarryState carry
          tape :=
            countedSuffixBoundaryPrefixCarryTape [] right } =
      { state := 6
        tape :=
          countedSuffixBoundaryPrefixScanRightTape [carry] right } := by
  cases carry <;> cases right <;>
    simp [PrefixShift, countedSuffixBoundaryPrefixShiftDescription,
      countedSuffixBoundaryPrefixCarryState,
      countedSuffixBoundaryPrefixCarryTape,
      countedSuffixBoundaryPrefixScanRightTape, runConfig,
      stepConfig, lookupTransition, Matches, transition, Tape.read,
      Tape.write, Tape.move, Tape.moveRight, tapeAtCells]

theorem countedSuffixBoundaryPrefixScanRightTape_append_last
    (first : Bool) (rest : Word Bool) (last : Bool)
    (right : List (Option Bool)) :
    countedSuffixBoundaryPrefixScanRightTape
        (List.append (first :: rest) [last]) right =
      countedSuffixBoundaryPrefixScanRightTape
        (first :: rest) (some last :: right) := by
  cases rest <;>
    simp [countedSuffixBoundaryPrefixScanRightTape,
      List.map_append, List.append_assoc]

theorem countedSuffixBoundaryPrefixShiftDescription_run_carry
    (remaining : Word Bool) (carry : Bool)
    (right : List (Option Bool)) :
    PrefixShift.runConfig (remaining.length + 1)
        { state := countedSuffixBoundaryPrefixCarryState carry
          tape :=
            countedSuffixBoundaryPrefixCarryTape remaining right } =
      { state := 6
        tape :=
          countedSuffixBoundaryPrefixScanRightTape
            ((carry :: remaining).reverse) right } := by
  induction remaining generalizing carry right with
  | nil =>
      simpa using
        countedSuffixBoundaryPrefixShiftDescription_run_carry_finish
          carry right
  | cons current rest ih =>
      rw [show (current :: rest).length + 1 =
        1 + (rest.length + 1) by
        simp
        lia]
      rw [runConfig_add]
      rw [
        countedSuffixBoundaryPrefixShiftDescription_run_carry_step
          rest current carry right]
      rw [ih current (some carry :: right)]
      cases hrev : (current :: rest).reverse with
      | nil =>
          simp at hrev
      | cons first scanRest =>
          rw [List.reverse_cons, hrev]
          exact
            congrArg
              (fun T => ({ state := 6, tape := T } : Configuration))
              (countedSuffixBoundaryPrefixScanRightTape_append_last
                first scanRest carry right).symm

theorem countedSuffixBoundaryPrefixShiftDescription_run_scan_right
    (left : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) :
    PrefixShift.runConfig (bits.length + 1)
        { state := 6
          tape :=
            tapeAtCells left
              (List.append (bits.map some) (none :: padding)) } =
      { state := 13
        tape :=
          tapeAtCells
            (none ::
              List.append (bits.reverse.map some) left)
            padding } := by
  induction bits generalizing left with
  | nil =>
      cases left <;> cases padding <;>
        simp [PrefixShift, countedSuffixBoundaryPrefixShiftDescription,
          runConfig, stepConfig, lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveRight, tapeAtCells]
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 1 =
        1 + (rest.length + 1) by
        simp
        lia]
      rw [runConfig_add]
      change
        PrefixShift.runConfig (rest.length + 1)
            (PrefixShift.runConfig 1
              { state := 6
                tape :=
                  tapeAtCells left
                    (some bit ::
                      List.append (rest.map some)
                        (none :: padding)) }) =
          { state := 13
            tape :=
              tapeAtCells
                (none ::
                  List.append ((bit :: rest).reverse.map some)
                    left)
                padding }
      have hstep :
          PrefixShift.runConfig 1
              { state := 6
                tape :=
                  tapeAtCells left
                    (some bit ::
                      List.append (rest.map some)
                        (none :: padding)) } =
            { state := 6
              tape :=
                tapeAtCells (some bit :: left)
                  (List.append (rest.map some)
                    (none :: padding)) } := by
        cases bit <;> cases rest <;> cases padding <;>
          simp [PrefixShift,
            countedSuffixBoundaryPrefixShiftDescription, runConfig,
            stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.write, Tape.move, Tape.moveRight,
            tapeAtCells]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append,
        List.append_assoc] using ih (some bit :: left)

theorem countedSuffixBoundaryPrefixShiftDescription_run_scan_right_source
    (first : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    PrefixShift.runConfig ((first :: rest).length)
        { state := 6
          tape :=
            countedSuffixBoundaryPrefixScanRightTape
              (first :: rest) (none :: padding) } =
      { state := 13
        tape :=
          tapeAtCells
            (none :: (first :: rest).reverse.map some)
            padding } := by
  simpa [countedSuffixBoundaryPrefixScanRightTape,
    List.append_assoc] using
    countedSuffixBoundaryPrefixShiftDescription_run_scan_right
      [some first] rest padding

theorem countedSuffixBoundaryPrefixShiftDescription_run_scan_right_reversed
    (first : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    PrefixShift.runConfig (first :: rest).length
        { state := 6
          tape :=
            countedSuffixBoundaryPrefixScanRightTape
              ((first :: rest).reverse) (none :: padding) } =
      { state := 13
        tape :=
          tapeAtCells
            (none :: (first :: rest).map some)
            padding } := by
  cases hrev : (first :: rest).reverse with
  | nil =>
      simp at hrev
  | cons scanFirst scanRest =>
      have hlen :
          (scanFirst :: scanRest).length =
            (first :: rest).length := by
        rw [← hrev]
        simp
      rw [← hlen]
      have hscan :=
        countedSuffixBoundaryPrefixShiftDescription_run_scan_right_source
          scanFirst scanRest padding
      have hmap :
          (List.map some scanRest).reverse ++ [some scanFirst] =
            some first :: List.map some rest := by
        have h :=
          congrArg (fun xs : Word Bool => xs.reverse.map some) hrev
        simpa [List.map_append] using h.symm
      simpa [hmap] using hscan

theorem countedSuffixBoundaryPrefixShiftDescription_run_to_target_rev
    (prefRev : Word Bool) (padding : List (Option Bool)) :
    PrefixShift.runConfig (2 * prefRev.length + 2)
        { state := PrefixShift.start
          tape :=
            tapeAtCells
              (List.append (prefRev.map some) [none])
              (none :: padding) } =
      { state := 13
        tape :=
          tapeAtCells (none :: prefRev.map some)
            (none :: padding) } := by
  cases prefRev with
  | nil =>
      cases padding <;>
        simp [PrefixShift, countedSuffixBoundaryPrefixShiftDescription,
          runConfig, stepConfig, lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, Tape.moveRight, tapeAtCells]
  | cons first rest =>
      rw [show 2 * (first :: rest).length + 2 =
        2 + ((rest.length + 1) + (first :: rest).length) by
        simp
        lia]
      rw [runConfig_add]
      have hstart :
          PrefixShift.runConfig 2
              { state := PrefixShift.start
                tape :=
                  tapeAtCells
                    (List.append ((first :: rest).map some) [none])
                    (none :: padding) } =
            { state := countedSuffixBoundaryPrefixCarryState first
              tape :=
                countedSuffixBoundaryPrefixCarryTape
                  rest (none :: none :: padding) } := by
        cases first <;> cases rest <;> cases padding <;>
          simp [PrefixShift,
            countedSuffixBoundaryPrefixShiftDescription,
            countedSuffixBoundaryPrefixCarryState,
            countedSuffixBoundaryPrefixCarryTape, runConfig,
            stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft,
            tapeAtCells]
      rw [hstart]
      rw [runConfig_add]
      rw [
        countedSuffixBoundaryPrefixShiftDescription_run_carry
          rest first (none :: none :: padding)]
      simpa [List.map_append, List.append_assoc] using
        countedSuffixBoundaryPrefixShiftDescription_run_scan_right_reversed
          first rest (none :: padding)

theorem countedSuffixBoundaryPrefixShiftDescription_haltsFromTape
    (pref suffix : Word Bool) (guardBit : Bool)
    (tail : List (Option Bool)) :
    PrefixShift.HaltsFromTape
      (countedSuffixBoundaryLeftAdvancedTape
        pref suffix guardBit tail)
      (countedSuffixBoundaryPrefixShiftedTape
        pref suffix guardBit tail) := by
  let padding : List (Option Bool) :=
    List.append (suffix.map some)
      (List.append
        (List.replicate suffix.length (none : Option Bool))
        (some guardBit :: tail))
  refine ⟨2 * pref.length + 2, ?_⟩
  have hrun :
      PrefixShift.runConfig (2 * pref.length + 2)
          { state := PrefixShift.start
            tape :=
              countedSuffixBoundaryLeftAdvancedTape
                pref suffix guardBit tail } =
        { state := 13
          tape :=
            countedSuffixBoundaryPrefixShiftedTape
              pref suffix guardBit tail } := by
    simpa [countedSuffixBoundaryLeftAdvancedTape,
      countedSuffixBoundaryPrefixShiftedTape, padding] using
      countedSuffixBoundaryPrefixShiftDescription_run_to_target_rev
        pref.reverse padding
  constructor
  · rw [hrun]
    rfl
  · rw [hrun]

theorem countedSuffixBoundaryRightRestoreDescription_run_final
    (pref processed : Word Bool) (last guardBit : Bool)
    (tail : List (Option Bool)) :
    RightRestore.runConfig 7
        { state := RightRestore.start
          tape :=
            countedSuffixBoundaryRestoreLoopTape
              pref processed [last] guardBit tail } =
      { state := 39
        tape :=
          countedSuffixBoundaryRestoreLoopTape
            pref (List.append processed [last]) [] guardBit tail } := by
  cases last <;> cases guardBit <;> cases processed <;> cases pref <;>
    cases tail <;>
    simp [RightRestore, countedSuffixBoundaryRightRestoreDescription,
      countedSuffixBoundaryRestoreLoopTape, runConfig, stepConfig,
      lookupTransition, Matches, transition, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft, Tape.moveRight, tapeAtCells,
      List.map_append, List.reverse_append, List.append_assoc,
      List.replicate_succ]

theorem countedSuffixBoundaryRightRestoreDescription_run_scan_suffix
    (left : List (Option Bool)) (bits : Word Bool)
    (right : List (Option Bool)) :
    RightRestore.runConfig (bits.length + 1)
        { state := 10
          tape :=
            tapeAtCells left
              (List.append (bits.map some) (none :: right)) } =
      { state := 11
        tape :=
          tapeAtCells
            (none ::
              List.append (bits.reverse.map some) left)
            right } := by
  induction bits generalizing left with
  | nil =>
      cases left <;> cases right <;>
        simp [RightRestore, countedSuffixBoundaryRightRestoreDescription,
          runConfig, stepConfig, lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveRight, tapeAtCells]
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 1 =
        1 + (rest.length + 1) by
        simp
        lia]
      rw [runConfig_add]
      change
        RightRestore.runConfig (rest.length + 1)
            (RightRestore.runConfig 1
              { state := 10
                tape :=
                  tapeAtCells left
                    (some bit ::
                      List.append (rest.map some)
                        (none :: right)) }) =
          { state := 11
            tape :=
              tapeAtCells
                (none ::
                  List.append ((bit :: rest).reverse.map some)
                    left)
                right }
      have hstep :
          RightRestore.runConfig 1
              { state := 10
                tape :=
                  tapeAtCells left
                    (some bit ::
                      List.append (rest.map some)
                        (none :: right)) } =
            { state := 10
              tape :=
                tapeAtCells (some bit :: left)
                  (List.append (rest.map some)
                    (none :: right)) } := by
        cases bit <;> cases rest <;> cases right <;>
          simp [RightRestore,
            countedSuffixBoundaryRightRestoreDescription, runConfig,
            stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.write, Tape.move, Tape.moveRight,
            tapeAtCells]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append,
        List.append_assoc] using ih (some bit :: left)

theorem countedSuffixBoundaryRightRestoreDescription_run_shift_guard
    (left : List (Option Bool)) (blanks : Nat)
    (guardBit : Bool) (right : List (Option Bool)) :
    RightRestore.runConfig (blanks + 3)
        { state := 11
          tape :=
            tapeAtCells (none :: left)
              (List.append
                (List.replicate (blanks + 1) (none : Option Bool))
                (some guardBit :: right)) } =
      { state := 14
        tape :=
          tapeAtCells
            (List.append
              (List.replicate blanks (none : Option Bool))
              left)
            (none :: some guardBit :: none :: right) } := by
  induction blanks generalizing left with
  | zero =>
      cases guardBit <;> cases left <;> cases right <;>
        simp [RightRestore, countedSuffixBoundaryRightRestoreDescription,
          runConfig, stepConfig, lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, Tape.moveRight, tapeAtCells]
  | succ blanks ih =>
      rw [show blanks + 1 + 3 = 1 + (blanks + 3) by lia]
      rw [runConfig_add]
      change
        RightRestore.runConfig (blanks + 3)
            (RightRestore.runConfig 1
              { state := 11
                tape :=
                  tapeAtCells (none :: left)
                    (none ::
                      List.append
                        (List.replicate (blanks + 1)
                          (none : Option Bool))
                        (some guardBit :: right)) }) =
          { state := 14
            tape :=
              tapeAtCells
                (List.append
                  (List.replicate (blanks + 1)
                    (none : Option Bool))
                  left)
                (none :: some guardBit :: none :: right) }
      have hstep :
          RightRestore.runConfig 1
              { state := 11
                tape :=
                  tapeAtCells (none :: left)
                    (none ::
                      List.append
                        (List.replicate (blanks + 1)
                          (none : Option Bool))
                        (some guardBit :: right)) } =
            { state := 11
              tape :=
                tapeAtCells (none :: none :: left)
                  (List.append
                    (List.replicate (blanks + 1)
                      (none : Option Bool))
                    (some guardBit :: right)) } := by
        simp [RightRestore,
          countedSuffixBoundaryRightRestoreDescription, runConfig,
          stepConfig, lookupTransition, Matches, transition,
          Tape.read, Tape.write, Tape.move, Tape.moveRight,
          tapeAtCells] <;> rfl
      rw [hstep]
      have hih := ih (none :: left)
      have hleft :
          List.append
              (List.replicate blanks (none : Option Bool))
              (none :: left) =
            none ::
              List.append
                (List.replicate blanks (none : Option Bool))
                left :=
        replicate_none_append_none_cons blanks left
      rw [hleft] at hih
      simpa [List.replicate_succ, List.append_assoc] using hih

def countedSuffixBoundaryRightReturnScanTape
    (baseLeft : List (Option Bool)) (processedRev : Word Bool)
    (last : Bool) (right : List (Option Bool)) : Tape Bool :=
  match processedRev with
  | [] => tapeAtCells baseLeft (none :: some last :: right)
  | bit :: rest =>
      tapeAtCells
        (List.append (rest.map some) (none :: baseLeft))
        (some bit :: some last :: right)

theorem countedSuffixBoundaryRightRestoreDescription_run_return_blanks
    (baseLeft : List (Option Bool)) (processedRev : Word Bool)
    (blanks : Nat) (last : Bool) (right : List (Option Bool)) :
    RightRestore.runConfig (blanks + 1)
        { state := 14
          tape :=
            tapeAtCells
              (List.append
                (List.replicate blanks (none : Option Bool))
                (some last ::
                  List.append (processedRev.map some)
                    (none :: baseLeft)))
              (none :: right) } =
      { state := 14
        tape :=
          tapeAtCells
            (List.append (processedRev.map some)
              (none :: baseLeft))
            (some last ::
              List.append
                (List.replicate (blanks + 1)
                  (none : Option Bool))
                right) } := by
  induction blanks generalizing right with
  | zero =>
      cases last <;> cases processedRev <;> cases right <;>
        simp [RightRestore, countedSuffixBoundaryRightRestoreDescription,
          runConfig, stepConfig, lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, tapeAtCells]
  | succ blanks ih =>
      rw [show blanks + 1 + 1 = 1 + (blanks + 1) by lia]
      rw [runConfig_add]
      rw [show
          List.append
              (List.replicate (blanks + 1) (none : Option Bool))
              (some last ::
                List.append (processedRev.map some)
                  (none :: baseLeft)) =
            none ::
              List.append
                (List.replicate blanks (none : Option Bool))
                (some last ::
                  List.append (processedRev.map some)
                    (none :: baseLeft)) by
        simp [List.replicate_succ]]
      have hstep :
          RightRestore.runConfig 1
              { state := 14
                tape :=
                  tapeAtCells
                    (none ::
                      List.append
                        (List.replicate blanks (none : Option Bool))
                        (some last ::
                          List.append (processedRev.map some)
                            (none :: baseLeft)))
                    (none :: right) } =
            { state := 14
              tape :=
                tapeAtCells
                  (List.append
                    (List.replicate blanks (none : Option Bool))
                    (some last ::
                      List.append (processedRev.map some)
                        (none :: baseLeft)))
                  (none :: none :: right) } := by
        simp [RightRestore,
          countedSuffixBoundaryRightRestoreDescription, runConfig,
          stepConfig, lookupTransition, Matches, transition,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          tapeAtCells]
      rw [hstep]
      have hih := ih (none :: right)
      have htail :
          List.append
              (List.replicate (blanks + 1) (none : Option Bool))
              (none :: right) =
            none ::
              List.append
                (List.replicate (blanks + 1)
                  (none : Option Bool))
                right :=
        replicate_none_append_none_cons (blanks + 1) right
      rw [htail] at hih
      have hrep :
          List.append
              (List.replicate (1 + (blanks + 1))
                (none : Option Bool))
              right =
            none ::
              none ::
                List.append
                  (List.replicate blanks (none : Option Bool))
                  right := by
        rw [show 1 + (blanks + 1) = (blanks + 1) + 1 by omega]
        simp [List.replicate_succ]
      rw [hrep]
      simpa [List.replicate_succ, List.append_assoc] using hih

theorem countedSuffixBoundaryRightRestoreDescription_run_return_scan_finish
    (baseLeft : List (Option Bool)) (processedRev : Word Bool)
    (last : Bool) (right : List (Option Bool)) :
    RightRestore.runConfig (processedRev.length + 2)
        { state := 15
          tape :=
            countedSuffixBoundaryRightReturnScanTape
              baseLeft processedRev last right } =
      { state := 0
        tape :=
          tapeAtCells baseLeft
            (none ::
              List.append (processedRev.reverse.map some)
                (some last :: right)) } := by
  induction processedRev generalizing last right with
  | nil =>
      cases last <;> cases right <;>
        simp [countedSuffixBoundaryRightReturnScanTape, RightRestore,
          countedSuffixBoundaryRightRestoreDescription, runConfig,
          stepConfig, lookupTransition, Matches, transition,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          Tape.moveRight, tapeAtCells]
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 2 =
        1 + (rest.length + 2) by
        simp
        lia]
      rw [runConfig_add]
      have hstep :
          RightRestore.runConfig 1
              { state := 15
                tape :=
                  countedSuffixBoundaryRightReturnScanTape
                    baseLeft (bit :: rest) last right } =
            { state := 15
              tape :=
                countedSuffixBoundaryRightReturnScanTape
                  baseLeft rest bit (some last :: right) } := by
        cases bit <;> cases last <;> cases rest <;> cases right <;>
          simp [countedSuffixBoundaryRightReturnScanTape, RightRestore,
            countedSuffixBoundaryRightRestoreDescription, runConfig,
            stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft,
            tapeAtCells]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih bit (some last :: right)

theorem countedSuffixBoundaryRightRestoreDescription_run_return_scan_bits
    (baseLeft : List (Option Bool)) (processedRev : Word Bool)
    (last : Bool) (right : List (Option Bool)) :
    RightRestore.runConfig (processedRev.length + 3)
        { state := 14
          tape :=
            tapeAtCells
              (List.append (processedRev.map some) (none :: baseLeft))
              (some last :: right) } =
      { state := 0
        tape :=
          tapeAtCells baseLeft
            (none ::
              List.append (processedRev.reverse.map some)
                (some last :: right)) } := by
  rw [show processedRev.length + 3 =
    1 + (processedRev.length + 2) by lia]
  rw [runConfig_add]
  have hstep :
      RightRestore.runConfig 1
          { state := 14
            tape :=
              tapeAtCells
                (List.append (processedRev.map some)
                  (none :: baseLeft))
                (some last :: right) } =
        { state := 15
          tape :=
            countedSuffixBoundaryRightReturnScanTape
              baseLeft processedRev last right } := by
    cases processedRev <;> cases last <;>
      simp [countedSuffixBoundaryRightReturnScanTape, RightRestore,
        countedSuffixBoundaryRightRestoreDescription, runConfig,
        stepConfig, lookupTransition, Matches, transition,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft,
        tapeAtCells]
  rw [hstep]
  exact
    countedSuffixBoundaryRightRestoreDescription_run_return_scan_finish
      baseLeft processedRev last right

theorem countedSuffixBoundaryRightRestoreDescription_run_return_to_separator_rev
    (baseLeft : List (Option Bool)) (processedRev : Word Bool)
    (last guardBit : Bool) (right : List (Option Bool)) :
    RightRestore.runConfig (2 * processedRev.length + 4)
        { state := 14
          tape :=
            tapeAtCells
              (List.append
                (List.replicate processedRev.length
                  (none : Option Bool))
                (some last ::
                  List.append (processedRev.map some)
                    (none :: baseLeft)))
              (none :: some guardBit :: right) } =
      { state := 0
        tape :=
          tapeAtCells baseLeft
            (none ::
              List.append ((last :: processedRev).reverse.map some)
                (List.append
                  (List.replicate (processedRev.length + 1)
                    (none : Option Bool))
                  (some guardBit :: right))) } := by
  rw [show 2 * processedRev.length + 4 =
    (processedRev.length + 1) + (processedRev.length + 3) by lia]
  rw [runConfig_add]
  rw [
    countedSuffixBoundaryRightRestoreDescription_run_return_blanks
      baseLeft processedRev processedRev.length last
      (some guardBit :: right)]
  simpa [List.reverse_cons, List.map_append, List.append_assoc] using
    countedSuffixBoundaryRightRestoreDescription_run_return_scan_bits
      baseLeft processedRev last
      (List.append
        (List.replicate (processedRev.length + 1)
          (none : Option Bool))
        (some guardBit :: right))

theorem countedSuffixBoundaryRightRestoreDescription_run_return_to_separator
    (baseLeft : List (Option Bool)) (rest : Word Bool)
    (next guardBit : Bool) (right : List (Option Bool)) :
    RightRestore.runConfig (2 * rest.length + 4)
        { state := 14
          tape :=
            tapeAtCells
              (List.append
                (List.replicate rest.length (none : Option Bool))
                (List.append ((next :: rest).reverse.map some)
                  (none :: baseLeft)))
              (none :: some guardBit :: right) } =
      { state := 0
        tape :=
          tapeAtCells baseLeft
            (none ::
              some next ::
                List.append (rest.map some)
                  (List.append
                    (List.replicate (rest.length + 1)
                      (none : Option Bool))
                    (some guardBit :: right))) } := by
  cases hrev : (next :: rest).reverse with
  | nil =>
      simp at hrev
  | cons last processedRev =>
      have hlen : processedRev.length = rest.length := by
        have h := congrArg List.length hrev
        simp at h
        omega
      have hmap :
          (last :: processedRev).reverse.map some =
            some next :: rest.map some := by
        rw [← hrev]
        simp
      have hmap' :
          (List.map some processedRev).reverse ++ [some last] =
            some next :: rest.map some := by
        simpa [List.reverse_cons, List.map_append] using hmap
      rw [← hlen]
      simpa [hrev, hmap', List.append_assoc] using
        countedSuffixBoundaryRightRestoreDescription_run_return_to_separator_rev
          baseLeft processedRev last guardBit right

theorem countedSuffixBoundaryRightRestoreDescription_run_continue
    (pref processed rest : Word Bool)
    (current next guardBit : Bool) (tail : List (Option Bool)) :
    RightRestore.runConfig (4 * rest.length + 13)
        { state := RightRestore.start
          tape :=
            countedSuffixBoundaryRestoreLoopTape
              pref processed (current :: next :: rest) guardBit
              tail } =
      { state := RightRestore.start
        tape :=
          countedSuffixBoundaryRestoreLoopTape
            pref (List.append processed [current]) (next :: rest)
            guardBit tail } := by
  rw [show 4 * rest.length + 13 =
    5 + ((rest.length + 1) +
      ((rest.length + 3) + (2 * rest.length + 4))) by lia]
  rw [runConfig_add]
  let baseLeft : List (Option Bool) :=
    List.append (processed.reverse.map some)
      (none :: pref.reverse.map some)
  let afterCurrentLeft : List (Option Bool) :=
    some current :: baseLeft
  let afterNextLeft : List (Option Bool) :=
    some next :: none :: afterCurrentLeft
  have hstart :
      RightRestore.runConfig 5
          { state := RightRestore.start
            tape :=
              countedSuffixBoundaryRestoreLoopTape
                pref processed (current :: next :: rest) guardBit
                tail } =
        { state := 10
          tape :=
            tapeAtCells afterNextLeft
              (List.append (rest.map some)
                (none ::
                  List.append
                    (List.replicate (rest.length + 1)
                      (none : Option Bool))
                    (some guardBit ::
                      List.append
                        (List.replicate processed.length
                          (none : Option Bool))
                        tail))) } := by
    cases current <;> cases next <;> cases guardBit <;>
      cases rest <;> cases processed <;> cases pref <;>
      cases tail <;>
      simp [RightRestore, countedSuffixBoundaryRightRestoreDescription,
        countedSuffixBoundaryRestoreLoopTape, baseLeft,
        afterCurrentLeft, afterNextLeft, runConfig, stepConfig,
        lookupTransition, Matches, transition, Tape.read, Tape.write,
        Tape.move, Tape.moveLeft, Tape.moveRight, tapeAtCells,
        List.replicate_succ, List.append_assoc]
  rw [hstart]
  rw [runConfig_add]
  rw [
    countedSuffixBoundaryRightRestoreDescription_run_scan_suffix
      afterNextLeft rest
      (List.append
        (List.replicate (rest.length + 1) (none : Option Bool))
        (some guardBit ::
          List.append
            (List.replicate processed.length (none : Option Bool))
            tail))]
  rw [runConfig_add]
  rw [
    countedSuffixBoundaryRightRestoreDescription_run_shift_guard
      (List.append (rest.reverse.map some) afterNextLeft)
      rest.length guardBit
      (List.append
        (List.replicate processed.length (none : Option Bool))
        tail)]
  simpa [countedSuffixBoundaryRestoreLoopTape, baseLeft,
    afterCurrentLeft, afterNextLeft, List.reverse_cons,
    List.map_append, List.reverse_append, List.append_assoc,
    List.replicate_succ] using
    countedSuffixBoundaryRightRestoreDescription_run_return_to_separator
      afterCurrentLeft rest next guardBit
      (none ::
        List.append
          (List.replicate processed.length (none : Option Bool))
          tail)

theorem countedSuffixBoundaryRightRestoreDescription_run_loop
    (pref processed : Word Bool)
    (suffixFirst : Bool) (suffixRest : Word Bool)
    (guardBit : Bool) (tail : List (Option Bool)) :
    exists steps : Nat,
      RightRestore.runConfig steps
          { state := RightRestore.start
            tape :=
              countedSuffixBoundaryRestoreLoopTape
                pref processed (suffixFirst :: suffixRest)
                guardBit tail } =
        { state := RightRestore.halt
          tape :=
            countedSuffixBoundaryRestoreLoopTape
              pref (List.append processed (suffixFirst :: suffixRest))
              [] guardBit tail } := by
  induction suffixRest generalizing processed suffixFirst with
  | nil =>
      refine ⟨7, ?_⟩
      simpa using
        countedSuffixBoundaryRightRestoreDescription_run_final
          pref processed suffixFirst guardBit tail
  | cons next rest ih =>
      obtain ⟨steps, hsteps⟩ :=
        ih (List.append processed [suffixFirst]) next
      refine ⟨4 * rest.length + 13 + steps, ?_⟩
      rw [runConfig_add]
      rw [
        countedSuffixBoundaryRightRestoreDescription_run_continue
          pref processed rest suffixFirst next guardBit tail]
      simpa [List.append_assoc] using hsteps

theorem countedSuffixBoundaryRightRestoreDescription_haltsFromTape
    (pref suffixRest : Word Bool)
    (suffixFirst guardBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    RightRestore.HaltsFromTape
      (countedSuffixBoundaryPrefixShiftedTape
        pref (suffixFirst :: suffixRest) guardBit
        (some tailFirst :: tail))
      (rightEdgeRewindSourceTapeWithBase
        (pref.reverse.map some) (suffixFirst :: suffixRest)
        (countedSuffixBoundaryLocatorPadding (some guardBit)
          (suffixFirst :: suffixRest) (some tailFirst :: tail))) := by
  obtain ⟨steps, hrun⟩ :=
    countedSuffixBoundaryRightRestoreDescription_run_loop
      pref [] suffixFirst suffixRest guardBit (some tailFirst :: tail)
  refine ⟨steps, ?_⟩
  have hrun' :
      RightRestore.runConfig steps
          { state := RightRestore.start
            tape :=
              countedSuffixBoundaryPrefixShiftedTape
                pref (suffixFirst :: suffixRest) guardBit
                (some tailFirst :: tail) } =
        { state := RightRestore.halt
          tape :=
            rightEdgeRewindSourceTapeWithBase
              (pref.reverse.map some) (suffixFirst :: suffixRest)
              (countedSuffixBoundaryLocatorPadding (some guardBit)
                (suffixFirst :: suffixRest)
                (some tailFirst :: tail)) } := by
    simpa [countedSuffixBoundaryPrefixShiftedTape,
      countedSuffixBoundaryRestoreLoopTape,
      rightEdgeRewindSourceTapeWithBase,
      countedSuffixBoundaryLocatorPadding, List.append_assoc] using hrun
  constructor
  · rw [hrun']
  · rw [hrun']

theorem countedSuffixBoundaryLocatorSourceTape_eq_leftAdvanceCurrentTape
    (pref suffix leftStack : Word Bool) (last guardBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hrev : suffix.reverse = last :: leftStack) :
    countedSuffixBoundaryLocatorSourceTape pref suffix (some guardBit)
        (some tailFirst :: tail) =
    countedSuffixBoundaryLeftAdvanceCurrentTape
        pref leftStack last guardBit (some tailFirst :: tail) := by
  have hlen : suffix.length = leftStack.length + 1 := by
    have h := congrArg List.length hrev
    simp at h
    omega
  simp [countedSuffixBoundaryLocatorSourceTape,
    countedSuffixBoundaryLeftAdvanceCurrentTape,
    countedSuffixBoundaryLocatorPadding,
    rightEdgeScanTargetTapeFromLeft, hrev, hlen, List.reverse_append,
    List.map_append, List.append_assoc, Tape.move, Tape.moveLeft,
    tapeAtCells]

theorem countedSuffixBoundaryLeftAdvancedTape_move_left_move_right
    (pref suffixRest : Word Bool)
    (suffixFirst guardBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (countedSuffixBoundaryLeftAdvancedTape
            pref (suffixFirst :: suffixRest) guardBit
            (some tailFirst :: tail))) =
      countedSuffixBoundaryLeftAdvancedTape
        pref (suffixFirst :: suffixRest) guardBit
        (some tailFirst :: tail) := by
  cases suffixFirst <;> cases guardBit <;> cases tailFirst <;>
    cases suffixRest <;> cases pref <;> cases tail <;>
    simp [countedSuffixBoundaryLeftAdvancedTape, Tape.move,
      Tape.moveLeft, Tape.moveRight, tapeAtCells,
      List.replicate_succ, List.append_assoc]

theorem countedSuffixBoundaryPrefixShiftedTape_move_left_move_right
    (pref suffixRest : Word Bool)
    (suffixFirst guardBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (countedSuffixBoundaryPrefixShiftedTape
            pref (suffixFirst :: suffixRest) guardBit
            (some tailFirst :: tail))) =
      countedSuffixBoundaryPrefixShiftedTape
        pref (suffixFirst :: suffixRest) guardBit
        (some tailFirst :: tail) := by
  cases suffixFirst <;> cases guardBit <;> cases tailFirst <;>
    cases suffixRest <;> cases pref <;> cases tail <;>
    simp [countedSuffixBoundaryPrefixShiftedTape, Tape.move,
      Tape.moveLeft, Tape.moveRight, tapeAtCells,
      List.replicate_succ]

theorem countedSuffixBoundaryLocatorConstruction_core :
    CountedSuffixBoundaryLocatorConstruction := by
  refine ⟨countedSuffixBoundaryLocatorDescription, ?_⟩
  constructor
  · exact countedSuffixBoundaryLocatorDescription_subroutineReady
  · intro pref suffixRest suffixFirst guardBit tailFirst tail
    cases hrev : (suffixFirst :: suffixRest).reverse with
    | nil =>
        simp at hrev
    | cons last leftStack =>
        have hsuffix :
            suffixFirst :: suffixRest =
              List.append leftStack.reverse [last] := by
          have h := congrArg List.reverse hrev
          simpa [List.reverse_append] using h
        have hLeft :
            LeftAdvance.HaltsFromTape
              (countedSuffixBoundaryLocatorSourceTape
                pref (suffixFirst :: suffixRest) (some guardBit)
                (some tailFirst :: tail))
              (countedSuffixBoundaryLeftAdvancedTape
                pref (suffixFirst :: suffixRest) guardBit
                (some tailFirst :: tail)) := by
          have hsource :=
            countedSuffixBoundaryLocatorSourceTape_eq_leftAdvanceCurrentTape
              pref (suffixFirst :: suffixRest) leftStack last guardBit
              tailFirst tail hrev
          rw [hsource]
          simpa [hsuffix] using
            countedSuffixBoundaryLeftAdvanceDescription_haltsFromTape
              pref leftStack last guardBit tailFirst tail
        have hPrefix :
            PrefixShift.HaltsFromTape
              (countedSuffixBoundaryLeftAdvancedTape
                pref (suffixFirst :: suffixRest) guardBit
                (some tailFirst :: tail))
              (countedSuffixBoundaryPrefixShiftedTape
                pref (suffixFirst :: suffixRest) guardBit
                (some tailFirst :: tail)) :=
          countedSuffixBoundaryPrefixShiftDescription_haltsFromTape
            pref (suffixFirst :: suffixRest) guardBit
            (some tailFirst :: tail)
        have hRight :
            RightRestore.HaltsFromTape
              (countedSuffixBoundaryPrefixShiftedTape
                pref (suffixFirst :: suffixRest) guardBit
                (some tailFirst :: tail))
              (rightEdgeRewindSourceTapeWithBase
                (pref.reverse.map some) (suffixFirst :: suffixRest)
                (countedSuffixBoundaryLocatorPadding (some guardBit)
                  (suffixFirst :: suffixRest)
                  (some tailFirst :: tail))) :=
          countedSuffixBoundaryRightRestoreDescription_haltsFromTape
            pref suffixRest suffixFirst guardBit tailFirst tail
        have hRewind :
            rightEdgeRewindDescription.HaltsFromTape
              (rightEdgeRewindSourceTapeWithBase
                (pref.reverse.map some) (suffixFirst :: suffixRest)
                (countedSuffixBoundaryLocatorPadding (some guardBit)
                  (suffixFirst :: suffixRest)
                  (some tailFirst :: tail)))
              (countedSuffixBoundaryLocatorTargetTape
                pref (suffixFirst :: suffixRest) (some guardBit)
                (some tailFirst :: tail)) := by
          simpa [countedSuffixBoundaryLocatorTargetTape,
            rightEdgeScanSourceTapeFromLeft,
            rightEdgeRewindTargetTapeWithBase] using
            rightEdgeRewindDescription_haltsFromTapeWithBase
              (pref.reverse.map some) (suffixFirst :: suffixRest)
              (countedSuffixBoundaryLocatorPadding (some guardBit)
                (suffixFirst :: suffixRest) (some tailFirst :: tail))
        have hRightBridge :
            Tape.move Direction.left
                (Tape.move Direction.right
                  (rightEdgeRewindSourceTapeWithBase
                    (pref.reverse.map some)
                    (suffixFirst :: suffixRest)
                    (countedSuffixBoundaryLocatorPadding
                      (some guardBit) (suffixFirst :: suffixRest)
                      (some tailFirst :: tail)))) =
              rightEdgeRewindSourceTapeWithBase
                (pref.reverse.map some) (suffixFirst :: suffixRest)
                (countedSuffixBoundaryLocatorPadding
                  (some guardBit) (suffixFirst :: suffixRest)
                  (some tailFirst :: tail)) := by
          simpa [countedSuffixBoundaryLocatorPadding,
            List.append_assoc] using
            rightEdgeRewindSourceTapeWithBase_move_left_move_right_padding_cons
              (pref.reverse.map some) (suffixFirst :: suffixRest)
              (some guardBit)
              (List.append
                (List.replicate (suffixFirst :: suffixRest).length
                  (none : Option Bool))
                (some tailFirst :: tail))
        have hRightRewind :
            (canonicalSeqDescription
              countedSuffixBoundaryRightRestoreDescription
              rightEdgeRewindDescription).HaltsFromTape
              (countedSuffixBoundaryPrefixShiftedTape
                pref (suffixFirst :: suffixRest) guardBit
                (some tailFirst :: tail))
              (countedSuffixBoundaryLocatorTargetTape
                pref (suffixFirst :: suffixRest) (some guardBit)
                (some tailFirst :: tail)) :=
          canonicalSeqDescription_haltsFromTape_of_haltsFromTape
            countedSuffixBoundaryRightRestoreDescription_subroutineReady
            rightEdgeRewindDescription_subroutineReady
            hRight hRightBridge hRewind
        have hPrefixRightRewind :
            (canonicalSeqDescription
              countedSuffixBoundaryPrefixShiftDescription
              (canonicalSeqDescription
                countedSuffixBoundaryRightRestoreDescription
                rightEdgeRewindDescription)).HaltsFromTape
              (countedSuffixBoundaryLeftAdvancedTape
                pref (suffixFirst :: suffixRest) guardBit
                (some tailFirst :: tail))
              (countedSuffixBoundaryLocatorTargetTape
                pref (suffixFirst :: suffixRest) (some guardBit)
                (some tailFirst :: tail)) :=
          canonicalSeqDescription_haltsFromTape_of_haltsFromTape
            countedSuffixBoundaryPrefixShiftDescription_subroutineReady
            (canonicalSeqDescription_subroutineReady
              countedSuffixBoundaryRightRestoreDescription_subroutineReady
              rightEdgeRewindDescription_subroutineReady)
            hPrefix
            (countedSuffixBoundaryPrefixShiftedTape_move_left_move_right
              pref suffixRest suffixFirst guardBit tailFirst tail)
            hRightRewind
        exact
          canonicalSeqDescription_haltsFromTape_of_haltsFromTape
            countedSuffixBoundaryLeftAdvanceDescription_subroutineReady
            (canonicalSeqDescription_subroutineReady
              countedSuffixBoundaryPrefixShiftDescription_subroutineReady
              (canonicalSeqDescription_subroutineReady
                countedSuffixBoundaryRightRestoreDescription_subroutineReady
                rightEdgeRewindDescription_subroutineReady))
            hLeft
            (countedSuffixBoundaryLeftAdvancedTape_move_left_move_right
              pref suffixRest suffixFirst guardBit tailFirst tail)
            hPrefixRightRewind

end FiniteTransducers
end CommonGround

end Computability
end FoC

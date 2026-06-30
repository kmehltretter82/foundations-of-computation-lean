import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.OneGapCompactor

set_option doc.verso true

/-!
# Sentinel-bounded gap compactor

This module starts the dynamic right-end compactor needed after optional-output
finite transducers have erased an interior field.  The machine repeatedly
closes the blank gap immediately to the left of the right payload.  It continues
while the cell to the left of that gap is blank, and performs a final closing
pass when that predecessor is a Boolean cell.

The stop condition is intentionally "nonblank predecessor", not "left tape
sentinel".  A blank-only left boundary is not locally distinguishable from a
larger blank gap.  Encoded-field consumers provide a nonempty kept prefix, so
the final gap is bounded on the left by an actual bit.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers

/--
Finite machine for repeatedly closing a right-side blank gap.

State layout:

* {lit}`0`: scan left over right scratch blanks until the right payload is found.
* {lit}`1`: scan left over the right payload until the current gap blank is found.
* {lit}`2`: inspect the cell immediately left of the gap.
* {lit}`3..7`: shift the payload one cell left and then loop.
* {lit}`8..12`: shift the payload one cell left and then halt.
* {lit}`13`: halt.
-/
def sentinelGapCompactorDescription : MachineDescription where
  stateCount := 14
  start := 0
  halt := 13
  transitions :=
    [ transition 0 none none Direction.left 0
    , transition 0 (some false) (some false) Direction.left 1
    , transition 0 (some true) (some true) Direction.left 1
    , transition 1 (some false) (some false) Direction.left 1
    , transition 1 (some true) (some true) Direction.left 1
    , transition 1 none none Direction.left 2
    , transition 2 none none Direction.right 3
    , transition 2 (some false) (some false) Direction.right 8
    , transition 2 (some true) (some true) Direction.right 8
    , transition 3 none none Direction.right 4
    , transition 4 none none Direction.right 0
    , transition 4 (some false) none Direction.left 5
    , transition 4 (some true) none Direction.left 6
    , transition 5 none (some false) Direction.right 7
    , transition 6 none (some true) Direction.right 7
    , transition 7 none none Direction.right 4
    , transition 8 none none Direction.right 9
    , transition 9 none none Direction.right 13
    , transition 9 (some false) none Direction.left 10
    , transition 9 (some true) none Direction.left 11
    , transition 10 none (some false) Direction.right 12
    , transition 11 none (some true) Direction.right 12
    , transition 12 none none Direction.right 9 ]

theorem sentinelGapCompactorDescription_wellFormed :
    sentinelGapCompactorDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := sentinelGapCompactorDescription.transitions)
      (stateCount := sentinelGapCompactorDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := sentinelGapCompactorDescription.transitions)
      (by decide)

theorem sentinelGapCompactorDescription_haltTransitionFree :
    sentinelGapCompactorDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := sentinelGapCompactorDescription.transitions)
    (state := sentinelGapCompactorDescription.halt)
    (by decide)

theorem sentinelGapCompactorDescription_subroutineReady :
    sentinelGapCompactorDescription.SubroutineReady :=
  ⟨sentinelGapCompactorDescription_wellFormed,
    sentinelGapCompactorDescription_haltTransitionFree⟩

def sentinelGapPayloadScanTape
    (baseLeft : List (Option Bool))
    (remaining processed : Word Bool)
    (padding : List (Option Bool)) : Tape Bool :=
  match remaining with
  | [] =>
      tapeAtCells baseLeft
        (none :: List.append (processed.map some) (none :: padding))
  | bit :: rest =>
      tapeAtCells
        (List.append (rest.map some) (none :: baseLeft))
        (some bit :: List.append (processed.map some) (none :: padding))

theorem sentinelGapCompactorDescription_run_scan_right_scratch
    (baseLeft : List (Option Bool)) (current : Bool)
    (leftRest : Word Bool) (paddingScratch : Nat)
    (rightPadding : List (Option Bool)) :
    sentinelGapCompactorDescription.runConfig (paddingScratch + 1)
        { state := 0
          tape :=
            rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
              baseLeft current leftRest paddingScratch rightPadding } =
      { state := 0
        tape :=
          tapeAtCells
            (List.append (leftRest.map some) (none :: baseLeft))
            (some current ::
              List.append
                (List.replicate paddingScratch (none : Option Bool))
                (none :: rightPadding)) } := by
  induction paddingScratch generalizing rightPadding with
  | zero =>
      cases current <;>
        simp [sentinelGapCompactorDescription,
          rightBlankLocalGapCompactorSourceTapeWithBaseAndRight,
          runConfig, stepConfig, lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, tapeAtCells]
  | succ paddingScratch ih =>
      rw [show paddingScratch + 1 + 1 =
          1 + (paddingScratch + 1) by omega]
      rw [runConfig_add]
      have hstep :
          sentinelGapCompactorDescription.runConfig 1
              { state := 0
                tape :=
                  rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
                    baseLeft current leftRest (paddingScratch + 1)
                    rightPadding } =
            { state := 0
              tape :=
                rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
                  baseLeft current leftRest paddingScratch
                  (none :: rightPadding) } := by
        cases rightPadding <;>
          simp [sentinelGapCompactorDescription,
            rightBlankLocalGapCompactorSourceTapeWithBaseAndRight,
            runConfig, stepConfig, lookupTransition, Matches,
            transition, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
            List.replicate_succ, tapeAtCells]
      rw [hstep]
      simpa [List.replicate_succ', List.append_assoc] using
        ih (none :: rightPadding)

theorem sentinelGapCompactorDescription_run_scan_payload
    (baseLeft : List (Option Bool))
    (remaining processed : Word Bool)
    (padding : List (Option Bool)) :
    sentinelGapCompactorDescription.runConfig (remaining.length + 1)
        { state := 1
          tape :=
            sentinelGapPayloadScanTape
              baseLeft remaining processed padding } =
      { state := 2
        tape :=
          Tape.move Direction.left
            (leadingBlankLeftShiftSourceTapeWithPadding
              baseLeft (List.append remaining.reverse processed)
              padding) } := by
  induction remaining generalizing processed with
  | nil =>
      cases baseLeft <;> cases padding <;> cases processed <;>
        simp [sentinelGapPayloadScanTape,
          sentinelGapCompactorDescription,
          leadingBlankLeftShiftSourceTapeWithPadding,
          runConfig, stepConfig, lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, tapeAtCells]
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 1 =
          1 + (rest.length + 1) by
        simp
        omega]
      rw [runConfig_add]
      have hstep :
          sentinelGapCompactorDescription.runConfig 1
              { state := 1
                tape :=
                  sentinelGapPayloadScanTape
                    baseLeft (bit :: rest) processed padding } =
            { state := 1
              tape :=
                sentinelGapPayloadScanTape
                  baseLeft rest (bit :: processed) padding } := by
        cases bit <;> cases rest <;> cases processed <;>
          cases padding <;>
          simp [sentinelGapPayloadScanTape,
            sentinelGapCompactorDescription, tapeAtCells, runConfig,
            stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (bit :: processed)

theorem sentinelGapCompactorDescription_run_enter_payload_scan
    (baseLeft : List (Option Bool)) (current : Bool)
    (leftRest : Word Bool) (padding : List (Option Bool)) :
    sentinelGapCompactorDescription.runConfig 1
        { state := 0
          tape :=
            tapeAtCells
              (List.append (leftRest.map some) (none :: baseLeft))
              (some current :: none :: padding) } =
      { state := 1
        tape :=
          sentinelGapPayloadScanTape
            baseLeft leftRest [current] padding } := by
  cases current <;> cases leftRest <;> cases padding <;>
    simp [sentinelGapPayloadScanTape,
      sentinelGapCompactorDescription, tapeAtCells, runConfig,
      stepConfig, lookupTransition, Matches, transition, Tape.read,
      Tape.write, Tape.move, Tape.moveLeft]

theorem sentinelGapCompactorDescription_run_scan_to_gap_predecessor
    (baseLeft : List (Option Bool)) (current : Bool)
    (leftRest : Word Bool) (paddingScratch : Nat)
    (rightPadding : List (Option Bool)) :
    sentinelGapCompactorDescription.runConfig
        (paddingScratch + leftRest.length + 3)
        { state := 0
          tape :=
            rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
              baseLeft current leftRest paddingScratch rightPadding } =
      { state := 2
        tape :=
          Tape.move Direction.left
            (leadingBlankLeftShiftSourceTapeWithPadding
              baseLeft (current :: leftRest).reverse
              (List.append
                (List.replicate paddingScratch (none : Option Bool))
                rightPadding)) } := by
  rw [show paddingScratch + leftRest.length + 3 =
      (paddingScratch + 1) + (1 + (leftRest.length + 1)) by
    omega]
  rw [runConfig_add]
  rw [sentinelGapCompactorDescription_run_scan_right_scratch]
  rw [replicate_none_append_none_cons]
  rw [runConfig_add]
  rw [sentinelGapCompactorDescription_run_enter_payload_scan]
  simpa [List.reverse_cons, List.append_assoc] using
    sentinelGapCompactorDescription_run_scan_payload
      baseLeft leftRest [current]
      (List.append
        (List.replicate paddingScratch (none : Option Bool))
        rightPadding)

theorem sentinelGapCompactorDescription_run_branch_continue
    (baseTail : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) :
    sentinelGapCompactorDescription.runConfig 1
        { state := 2
          tape :=
            Tape.move Direction.left
              (leadingBlankLeftShiftSourceTapeWithPadding
                (none :: baseTail) bits padding) } =
      { state := 3
        tape :=
          leadingBlankLeftShiftSourceTapeWithPadding
            (none :: baseTail) bits padding } := by
  cases baseTail <;> cases bits <;> cases padding <;>
    simp [sentinelGapCompactorDescription,
      leadingBlankLeftShiftSourceTapeWithPadding, tapeAtCells,
      runConfig, stepConfig, lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft, Tape.moveRight]

theorem sentinelGapCompactorDescription_run_branch_final
    (baseTail : List (Option Bool)) (leftBit : Bool)
    (bits : Word Bool) (padding : List (Option Bool)) :
    sentinelGapCompactorDescription.runConfig 1
        { state := 2
          tape :=
            Tape.move Direction.left
              (leadingBlankLeftShiftSourceTapeWithPadding
                (some leftBit :: baseTail) bits padding) } =
      { state := 8
        tape :=
          leadingBlankLeftShiftSourceTapeWithPadding
            (some leftBit :: baseTail) bits padding } := by
  cases leftBit <;> cases baseTail <;> cases bits <;> cases padding <;>
    simp [sentinelGapCompactorDescription,
      leadingBlankLeftShiftSourceTapeWithPadding, tapeAtCells,
      runConfig, stepConfig, lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft, Tape.moveRight]

theorem sentinelGapCompactorDescription_run_continue_shift_start
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) :
    sentinelGapCompactorDescription.runConfig 1
        { state := 3
          tape :=
            leadingBlankLeftShiftSourceTapeWithPadding
              baseLeft bits padding } =
      { state := 4
        tape :=
          leadingBlankLeftShiftLoopTapeWithPadding
            baseLeft [] bits padding } := by
  cases bits <;>
    simp [sentinelGapCompactorDescription,
      leadingBlankLeftShiftSourceTapeWithPadding,
      leadingBlankLeftShiftLoopTapeWithPadding, runConfig, stepConfig,
      lookupTransition, Matches, transition, Tape.read, Tape.write,
      Tape.move, Tape.moveRight, tapeAtCells]

theorem sentinelGapCompactorDescription_run_continue_shift_bit
    (baseLeft : List (Option Bool))
    (processed rest : Word Bool) (bit : Bool)
    (padding : List (Option Bool)) :
    sentinelGapCompactorDescription.runConfig 3
        { state := 4
          tape :=
            leadingBlankLeftShiftLoopTapeWithPadding
              baseLeft processed (bit :: rest) padding } =
      { state := 4
        tape :=
          leadingBlankLeftShiftLoopTapeWithPadding
            baseLeft (List.append processed [bit]) rest padding } := by
  cases bit <;> cases rest <;>
    simp [sentinelGapCompactorDescription,
      leadingBlankLeftShiftLoopTapeWithPadding, runConfig, stepConfig,
      lookupTransition, Matches, transition, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft, Tape.moveRight, tapeAtCells,
      List.reverse_append]

theorem sentinelGapCompactorDescription_run_continue_shift_finish
    (baseLeft : List (Option Bool)) (processed : Word Bool)
    (padding : List (Option Bool)) :
    sentinelGapCompactorDescription.runConfig 1
        { state := 4
          tape :=
            leadingBlankLeftShiftLoopTapeWithPadding
              baseLeft processed [] padding } =
      { state := 0
        tape :=
          leadingBlankLeftShiftTargetTapeWithPadding
            baseLeft processed padding } := by
  cases padding <;>
    simp [sentinelGapCompactorDescription,
      leadingBlankLeftShiftLoopTapeWithPadding,
      leadingBlankLeftShiftTargetTapeWithPadding,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveRight, tapeAtCells]

theorem sentinelGapCompactorDescription_run_continue_shift_loop
    (baseLeft : List (Option Bool))
    (processed remaining : Word Bool)
    (padding : List (Option Bool)) :
    sentinelGapCompactorDescription.runConfig
        (3 * remaining.length + 1)
        { state := 4
          tape :=
            leadingBlankLeftShiftLoopTapeWithPadding
              baseLeft processed remaining padding } =
      { state := 0
        tape :=
          leadingBlankLeftShiftTargetTapeWithPadding
            baseLeft (List.append processed remaining) padding } := by
  induction remaining generalizing processed with
  | nil =>
      simpa using
        sentinelGapCompactorDescription_run_continue_shift_finish
          baseLeft processed padding
  | cons bit rest ih =>
      rw [show 3 * (bit :: rest).length + 1 =
          3 + (3 * rest.length + 1) by
        simp
        omega]
      rw [runConfig_add]
      rw [sentinelGapCompactorDescription_run_continue_shift_bit]
      simpa [List.append_assoc] using
        ih (List.append processed [bit])

theorem sentinelGapCompactorDescription_run_continue_shift_to_target
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) :
    sentinelGapCompactorDescription.runConfig
        (3 * bits.length + 2)
        { state := 3
          tape :=
            leadingBlankLeftShiftSourceTapeWithPadding
              baseLeft bits padding } =
      { state := 0
        tape :=
          leadingBlankLeftShiftTargetTapeWithPadding
            baseLeft bits padding } := by
  rw [show 3 * bits.length + 2 =
      1 + (3 * bits.length + 1) by omega]
  rw [runConfig_add]
  rw [sentinelGapCompactorDescription_run_continue_shift_start]
  simpa using
    sentinelGapCompactorDescription_run_continue_shift_loop
      baseLeft [] bits padding

theorem sentinelGapCompactorDescription_run_final_shift_start
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) :
    sentinelGapCompactorDescription.runConfig 1
        { state := 8
          tape :=
            leadingBlankLeftShiftSourceTapeWithPadding
              baseLeft bits padding } =
      { state := 9
        tape :=
          leadingBlankLeftShiftLoopTapeWithPadding
            baseLeft [] bits padding } := by
  cases bits <;>
    simp [sentinelGapCompactorDescription,
      leadingBlankLeftShiftSourceTapeWithPadding,
      leadingBlankLeftShiftLoopTapeWithPadding, runConfig, stepConfig,
      lookupTransition, Matches, transition, Tape.read, Tape.write,
      Tape.move, Tape.moveRight, tapeAtCells]

theorem sentinelGapCompactorDescription_run_final_shift_bit
    (baseLeft : List (Option Bool))
    (processed rest : Word Bool) (bit : Bool)
    (padding : List (Option Bool)) :
    sentinelGapCompactorDescription.runConfig 3
        { state := 9
          tape :=
            leadingBlankLeftShiftLoopTapeWithPadding
              baseLeft processed (bit :: rest) padding } =
      { state := 9
        tape :=
          leadingBlankLeftShiftLoopTapeWithPadding
            baseLeft (List.append processed [bit]) rest padding } := by
  cases bit <;> cases rest <;>
    simp [sentinelGapCompactorDescription,
      leadingBlankLeftShiftLoopTapeWithPadding, runConfig, stepConfig,
      lookupTransition, Matches, transition, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft, Tape.moveRight, tapeAtCells,
      List.reverse_append]

theorem sentinelGapCompactorDescription_run_final_shift_finish
    (baseLeft : List (Option Bool)) (processed : Word Bool)
    (padding : List (Option Bool)) :
    sentinelGapCompactorDescription.runConfig 1
        { state := 9
          tape :=
            leadingBlankLeftShiftLoopTapeWithPadding
              baseLeft processed [] padding } =
      { state := sentinelGapCompactorDescription.halt
        tape :=
          leadingBlankLeftShiftTargetTapeWithPadding
            baseLeft processed padding } := by
  cases padding <;>
    simp [sentinelGapCompactorDescription,
      leadingBlankLeftShiftLoopTapeWithPadding,
      leadingBlankLeftShiftTargetTapeWithPadding,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveRight, tapeAtCells]

theorem sentinelGapCompactorDescription_run_final_shift_loop
    (baseLeft : List (Option Bool))
    (processed remaining : Word Bool)
    (padding : List (Option Bool)) :
    sentinelGapCompactorDescription.runConfig
        (3 * remaining.length + 1)
        { state := 9
          tape :=
            leadingBlankLeftShiftLoopTapeWithPadding
              baseLeft processed remaining padding } =
      { state := sentinelGapCompactorDescription.halt
        tape :=
          leadingBlankLeftShiftTargetTapeWithPadding
            baseLeft (List.append processed remaining) padding } := by
  induction remaining generalizing processed with
  | nil =>
      simpa using
        sentinelGapCompactorDescription_run_final_shift_finish
          baseLeft processed padding
  | cons bit rest ih =>
      rw [show 3 * (bit :: rest).length + 1 =
          3 + (3 * rest.length + 1) by
        simp
        omega]
      rw [runConfig_add]
      rw [sentinelGapCompactorDescription_run_final_shift_bit]
      simpa [List.append_assoc] using
        ih (List.append processed [bit])

theorem sentinelGapCompactorDescription_run_final_shift_to_target
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) :
    sentinelGapCompactorDescription.runConfig
        (3 * bits.length + 2)
        { state := 8
          tape :=
            leadingBlankLeftShiftSourceTapeWithPadding
              baseLeft bits padding } =
      { state := sentinelGapCompactorDescription.halt
        tape :=
          leadingBlankLeftShiftTargetTapeWithPadding
            baseLeft bits padding } := by
  rw [show 3 * bits.length + 2 =
      1 + (3 * bits.length + 1) by omega]
  rw [runConfig_add]
  rw [sentinelGapCompactorDescription_run_final_shift_start]
  simpa using
    sentinelGapCompactorDescription_run_final_shift_loop
      baseLeft [] bits padding

theorem sentinelGapCompactorDescription_run_continue_pass
    (baseTail : List (Option Bool)) (current : Bool)
    (leftRest : Word Bool) (paddingScratch : Nat)
    (rightPadding : List (Option Bool)) :
    sentinelGapCompactorDescription.runConfig
        ((paddingScratch + leftRest.length + 3) +
          (1 + (3 * (current :: leftRest).length + 2)))
        { state := 0
          tape :=
            rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
              (none :: baseTail) current leftRest paddingScratch
              rightPadding } =
      { state := 0
        tape :=
          leadingBlankLeftShiftTargetTapeWithPadding
            (none :: baseTail) (current :: leftRest).reverse
            (List.append
              (List.replicate paddingScratch (none : Option Bool))
              rightPadding) } := by
  rw [runConfig_add]
  rw [sentinelGapCompactorDescription_run_scan_to_gap_predecessor]
  rw [runConfig_add]
  rw [sentinelGapCompactorDescription_run_branch_continue]
  simpa using
    sentinelGapCompactorDescription_run_continue_shift_to_target
      (none :: baseTail) (current :: leftRest).reverse
      (List.append
        (List.replicate paddingScratch (none : Option Bool))
        rightPadding)

theorem sentinelGapCompactorDescription_run_final_pass
    (baseTail : List (Option Bool)) (leftBit current : Bool)
    (leftRest : Word Bool) (paddingScratch : Nat)
    (rightPadding : List (Option Bool)) :
    sentinelGapCompactorDescription.runConfig
        ((paddingScratch + leftRest.length + 3) +
          (1 + (3 * (current :: leftRest).length + 2)))
        { state := 0
          tape :=
            rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
              (some leftBit :: baseTail) current leftRest paddingScratch
              rightPadding } =
      { state := sentinelGapCompactorDescription.halt
        tape :=
          leadingBlankLeftShiftTargetTapeWithPadding
            (some leftBit :: baseTail) (current :: leftRest).reverse
            (List.append
              (List.replicate paddingScratch (none : Option Bool))
              rightPadding) } := by
  rw [runConfig_add]
  rw [sentinelGapCompactorDescription_run_scan_to_gap_predecessor]
  rw [runConfig_add]
  rw [sentinelGapCompactorDescription_run_branch_final]
  simpa using
    sentinelGapCompactorDescription_run_final_shift_to_target
      (some leftBit :: baseTail) (current :: leftRest).reverse
      (List.append
        (List.replicate paddingScratch (none : Option Bool))
        rightPadding)

theorem sentinelGapCompactorDescription_haltsFromTape_final_pass
    (baseTail : List (Option Bool)) (leftBit current : Bool)
    (leftRest : Word Bool) (paddingScratch : Nat)
    (rightPadding : List (Option Bool)) :
    sentinelGapCompactorDescription.HaltsFromTape
      (rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
        (some leftBit :: baseTail) current leftRest paddingScratch
        rightPadding)
      (leadingBlankLeftShiftTargetTapeWithPadding
        (some leftBit :: baseTail) (current :: leftRest).reverse
        (List.append
          (List.replicate paddingScratch (none : Option Bool))
          rightPadding)) := by
  refine ⟨(paddingScratch + leftRest.length + 3) +
    (1 + (3 * (current :: leftRest).length + 2)), ?_⟩
  constructor
  · simpa using
      congrArg
        (fun c : Configuration => c.state)
        (sentinelGapCompactorDescription_run_final_pass
          baseTail leftBit current leftRest paddingScratch rightPadding)
  · simpa using
      congrArg
        (fun c : Configuration => c.tape)
        (sentinelGapCompactorDescription_run_final_pass
          baseTail leftBit current leftRest paddingScratch rightPadding)

/--
Right padding accumulated by the sentinel gap compactor after closing a gap of
the given width.
-/
def sentinelGapCompactorFinalPadding :
    Nat -> Nat -> List (Option Bool) -> List (Option Bool)
  | 0, paddingScratch, rightPadding =>
      List.append
        (List.replicate paddingScratch (none : Option Bool))
        rightPadding
  | Nat.succ gap, 0, rightPadding =>
      sentinelGapCompactorFinalPadding gap 2 rightPadding
  | Nat.succ gap, Nat.succ paddingTail, rightPadding =>
      sentinelGapCompactorFinalPadding gap 2
        (List.append
          (List.replicate paddingTail (none : Option Bool))
          rightPadding)

theorem replicate_none_append_replicate_none
    (m n : Nat) :
    List.append (List.replicate m (none : Option Bool))
        (List.replicate n (none : Option Bool)) =
      List.replicate (m + n) (none : Option Bool) := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [List.replicate_succ]
      change none ::
          List.append (List.replicate m (none : Option Bool))
            (List.replicate n (none : Option Bool)) =
        List.replicate (Nat.succ m + n) (none : Option Bool)
      rw [ih]
      rw [show Nat.succ m + n = (m + n) + 1 by omega]
      rw [List.replicate_succ]

theorem sentinelGapCompactorFinalPadding_replicate
    (gap paddingTail extra : Nat) :
    sentinelGapCompactorFinalPadding gap (Nat.succ paddingTail)
        (List.replicate extra (none : Option Bool)) =
      List.replicate (Nat.succ paddingTail + gap + extra)
        (none : Option Bool) := by
  induction gap generalizing paddingTail extra with
  | zero =>
      rw [sentinelGapCompactorFinalPadding]
      exact replicate_none_append_replicate_none
        (Nat.succ paddingTail) extra
  | succ gap ih =>
      rw [sentinelGapCompactorFinalPadding]
      rw [replicate_none_append_replicate_none]
      rw [ih]
      congr 1
      omega

theorem replicate_add_two_none
    (n : Nat) :
    List.replicate (n + 2) (none : Option Bool) =
      none :: none :: List.replicate n (none : Option Bool) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [show Nat.succ n + 2 = (n + 2) + 1 by omega]
      rw [List.replicate_succ]
      rw [ih]
      rw [List.replicate_succ]

theorem sentinelGapCompactorFinalPadding_cons_cons
    (gap paddingTail : Nat) :
    sentinelGapCompactorFinalPadding gap
        (Nat.succ (Nat.succ paddingTail)) [] =
      none :: none ::
        List.replicate (paddingTail + gap) (none : Option Bool) := by
  have h := sentinelGapCompactorFinalPadding_replicate
    gap (Nat.succ paddingTail) 0
  simpa [replicate_add_two_none, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using h

theorem sentinelGapCompactorDescription_haltsFromTape_gapBase
    (gap : Nat) (baseTail : List (Option Bool))
    (leftBit current : Bool) (leftRest : Word Bool)
    (paddingTail : Nat) (rightPadding : List (Option Bool)) :
    sentinelGapCompactorDescription.HaltsFromTape
      (rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
        (rightBlankLocalGapBaseLeft gap (some leftBit :: baseTail))
        current leftRest (Nat.succ paddingTail) rightPadding)
      (leadingBlankLeftShiftTargetTapeWithPadding
        (some leftBit :: baseTail) (current :: leftRest).reverse
        (sentinelGapCompactorFinalPadding gap (Nat.succ paddingTail)
          rightPadding)) := by
  induction gap generalizing paddingTail rightPadding with
  | zero =>
      simpa [rightBlankLocalGapBaseLeft, sentinelGapCompactorFinalPadding] using
        sentinelGapCompactorDescription_haltsFromTape_final_pass
          baseTail leftBit current leftRest (Nat.succ paddingTail)
          rightPadding
  | succ gap ih =>
      let nextRightPadding : List (Option Bool) :=
        List.append
          (List.replicate paddingTail (none : Option Bool))
          rightPadding
      rcases ih 1 nextRightPadding with ⟨n, hn⟩
      let continueSteps : Nat :=
        ((Nat.succ paddingTail + leftRest.length + 3) +
          (1 + (3 * (current :: leftRest).length + 2)))
      refine ⟨continueSteps + n, ?_⟩
      constructor
      · rw [runConfig_add]
        change (sentinelGapCompactorDescription.runConfig n
          (sentinelGapCompactorDescription.runConfig continueSteps
            { state := 0
              tape :=
                rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
                  (rightBlankLocalGapBaseLeft (Nat.succ gap)
                    (some leftBit :: baseTail))
                  current leftRest (Nat.succ paddingTail)
                  rightPadding })).state = sentinelGapCompactorDescription.halt
        rw [show rightBlankLocalGapBaseLeft (Nat.succ gap)
              (some leftBit :: baseTail) =
            none :: rightBlankLocalGapBaseLeft gap
              (some leftBit :: baseTail) by
          exact rightBlankLocalGapBaseLeft_succ gap (some leftBit :: baseTail)]
        rw [show continueSteps =
            ((Nat.succ paddingTail + leftRest.length + 3) +
              (1 + (3 * (current :: leftRest).length + 2))) by rfl]
        rw [sentinelGapCompactorDescription_run_continue_pass]
        rw [show List.append
              (List.replicate (Nat.succ paddingTail) (none : Option Bool))
              rightPadding =
            List.append
              (List.replicate paddingTail (none : Option Bool))
              (none :: rightPadding) by
          simpa [List.replicate_succ] using
            (replicate_none_append_none_cons paddingTail rightPadding).symm]
        rw [
          leadingBlankLeftShiftTargetTapeWithPadding_eq_nextRightBlankLocalGapSource_append]
        exact hn.left
      · rw [runConfig_add]
        change (sentinelGapCompactorDescription.runConfig n
          (sentinelGapCompactorDescription.runConfig continueSteps
            { state := 0
              tape :=
                rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
                  (rightBlankLocalGapBaseLeft (Nat.succ gap)
                    (some leftBit :: baseTail))
                  current leftRest (Nat.succ paddingTail)
                  rightPadding })).tape =
            leadingBlankLeftShiftTargetTapeWithPadding
              (some leftBit :: baseTail) (current :: leftRest).reverse
              (sentinelGapCompactorFinalPadding (Nat.succ gap)
                (Nat.succ paddingTail) rightPadding)
        rw [show rightBlankLocalGapBaseLeft (Nat.succ gap)
              (some leftBit :: baseTail) =
            none :: rightBlankLocalGapBaseLeft gap
              (some leftBit :: baseTail) by
          exact rightBlankLocalGapBaseLeft_succ gap (some leftBit :: baseTail)]
        rw [show continueSteps =
            ((Nat.succ paddingTail + leftRest.length + 3) +
              (1 + (3 * (current :: leftRest).length + 2))) by rfl]
        rw [sentinelGapCompactorDescription_run_continue_pass]
        rw [show List.append
              (List.replicate (Nat.succ paddingTail) (none : Option Bool))
              rightPadding =
            List.append
              (List.replicate paddingTail (none : Option Bool))
              (none :: rightPadding) by
          simpa [List.replicate_succ] using
            (replicate_none_append_none_cons paddingTail rightPadding).symm]
        rw [
          leadingBlankLeftShiftTargetTapeWithPadding_eq_nextRightBlankLocalGapSource_append]
        simpa [sentinelGapCompactorFinalPadding, nextRightPadding] using hn.right

def rightEndSentinelGapCompactorSourceLeftCells
    (baseTail : List (Option Bool)) (leftBit current : Bool)
    (leftRest : Word Bool) (gap paddingScratch : Nat) :
    List (Option Bool) :=
  List.append baseTail.reverse
    (some leftBit ::
      List.append
        (List.replicate (Nat.succ gap) (none : Option Bool))
        (List.append (((current :: leftRest).reverse).map some)
          (List.replicate paddingScratch (none : Option Bool))))

theorem rightEndSentinelGapCompactorSourceLeftCells_eq_split
    (pref : Word Bool) (leftBit current : Bool)
    (leftRest : Word Bool) (gap paddingScratch : Nat) :
    rightEndSentinelGapCompactorSourceLeftCells
        (List.append (pref.reverse.map some) [none])
        leftBit current leftRest gap paddingScratch =
      List.append [none]
        (List.append ((List.append pref [leftBit]).map some)
          (List.append
            (List.replicate (Nat.succ gap) (none : Option Bool))
            (List.append (((current :: leftRest).reverse).map some)
              (List.replicate paddingScratch (none : Option Bool))))) := by
  simp [rightEndSentinelGapCompactorSourceLeftCells,
    List.reverse_append, List.map_reverse, List.map_append,
    List.append_assoc]

theorem rightBlankLocalGapCompactorSourceTapeWithBaseAndRight_eq_rightEndSentinelGapSource
    (baseTail : List (Option Bool)) (leftBit current : Bool)
    (leftRest : Word Bool) (gap paddingScratch : Nat) :
    rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
        (rightBlankLocalGapBaseLeft gap (some leftBit :: baseTail))
        current leftRest paddingScratch [] =
      rightEndCompactionSourceTape
        (rightEndSentinelGapCompactorSourceLeftCells
          baseTail leftBit current leftRest gap paddingScratch) := by
  simp [rightBlankLocalGapCompactorSourceTapeWithBaseAndRight,
    rightBlankLocalGapBaseLeft,
    rightEndCompactionSourceTape,
    rightEndSentinelGapCompactorSourceLeftCells,
    tapeAtCells, List.reverse_append, List.map_reverse,
    List.append_assoc, List.replicate_succ]
  exact (replicate_none_append_none_cons gap
    (some leftBit :: baseTail)).symm

theorem sentinelGapCompactorDescription_haltsFromTape_rightEndGapSource
    (gap : Nat) (baseTail : List (Option Bool))
    (leftBit current : Bool) (leftRest : Word Bool)
    (paddingTail : Nat) :
    sentinelGapCompactorDescription.HaltsFromTape
      (rightEndCompactionSourceTape
        (rightEndSentinelGapCompactorSourceLeftCells
          baseTail leftBit current leftRest gap (Nat.succ paddingTail)))
      (leadingBlankLeftShiftTargetTapeWithPadding
        (some leftBit :: baseTail) (current :: leftRest).reverse
        (sentinelGapCompactorFinalPadding gap (Nat.succ paddingTail) [])) := by
  rw [←
    rightBlankLocalGapCompactorSourceTapeWithBaseAndRight_eq_rightEndSentinelGapSource]
  exact
    sentinelGapCompactorDescription_haltsFromTape_gapBase
      gap baseTail leftBit current leftRest paddingTail []

theorem sentinelGapTarget_move_left_left_eq_rightEdgeRewindSourceWithBoundary
    (pref bits : Word Bool) (leftBit : Bool)
    (padding : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.left
          (leadingBlankLeftShiftTargetTapeWithPadding
            (some leftBit :: List.append (pref.reverse.map some) [none])
            bits padding)) =
      rightEdgeRewindSourceTapeWithBase []
        (List.append pref (leftBit :: bits))
        (none :: leadingBlankLeftShiftTargetVisiblePadding padding) := by
  cases bits <;> cases pref <;> cases padding <;>
    simp [leadingBlankLeftShiftTargetTapeWithPadding,
      rightEdgeRewindSourceTapeWithBase,
      leadingBlankLeftShiftTargetVisiblePadding, tapeAtCells,
      Tape.move, Tape.moveLeft, List.reverse_append,
      List.map_reverse, List.append_assoc]

theorem sentinelGapTarget_move_left_move_right_withBoundary_cons_cons
    (pref bits : Word Bool) (leftBit : Bool)
    (pad nextPad : Option Bool) (padding : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (leadingBlankLeftShiftTargetTapeWithPadding
            (some leftBit :: List.append (pref.reverse.map some) [none])
            bits (pad :: nextPad :: padding))) =
      leadingBlankLeftShiftTargetTapeWithPadding
        (some leftBit :: List.append (pref.reverse.map some) [none])
        bits (pad :: nextPad :: padding) := by
  cases bits <;> cases pref <;> cases pad <;> cases nextPad <;>
    cases padding <;>
      simp [leadingBlankLeftShiftTargetTapeWithPadding,
        tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight,
        List.map_reverse, List.append_assoc]

def leftMoveTwiceDescription : MachineDescription where
  stateCount := 3
  start := 0
  halt := 2
  transitions :=
    [ transition 0 none none Direction.left 1
    , transition 0 (some false) (some false) Direction.left 1
    , transition 0 (some true) (some true) Direction.left 1
    , transition 1 none none Direction.left 2
    , transition 1 (some false) (some false) Direction.left 2
    , transition 1 (some true) (some true) Direction.left 2 ]

theorem leftMoveTwiceDescription_wellFormed :
    leftMoveTwiceDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := leftMoveTwiceDescription.transitions)
      (stateCount := leftMoveTwiceDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := leftMoveTwiceDescription.transitions)
      (by decide)

theorem leftMoveTwiceDescription_haltTransitionFree :
    leftMoveTwiceDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := leftMoveTwiceDescription.transitions)
    (state := leftMoveTwiceDescription.halt)
    (by decide)

theorem leftMoveTwiceDescription_subroutineReady :
    leftMoveTwiceDescription.SubroutineReady :=
  ⟨leftMoveTwiceDescription_wellFormed,
    leftMoveTwiceDescription_haltTransitionFree⟩

theorem leftMoveTwiceDescription_run
    (T : Tape Bool) :
    leftMoveTwiceDescription.runConfig 2
        { state := leftMoveTwiceDescription.start
          tape := T } =
      { state := leftMoveTwiceDescription.halt
        tape := Tape.move Direction.left (Tape.move Direction.left T) } := by
  cases T with
  | mk left head right =>
      cases head with
      | none =>
          cases left with
          | nil =>
              simp [leftMoveTwiceDescription, runConfig, stepConfig,
                lookupTransition, Matches, transition, Tape.read,
                Tape.write, Tape.move, Tape.moveLeft]
          | cons lcell lrest =>
              cases lcell with
              | none =>
                  cases lrest <;>
                    simp [leftMoveTwiceDescription, runConfig,
                      stepConfig, lookupTransition, Matches,
                      transition, Tape.read, Tape.write, Tape.move,
                      Tape.moveLeft]
              | some b =>
                  cases b <;> cases lrest <;>
                    simp [leftMoveTwiceDescription, runConfig,
                      stepConfig, lookupTransition, Matches,
                      transition, Tape.read, Tape.write, Tape.move,
                      Tape.moveLeft]
      | some h =>
          cases h <;> cases left with
          | nil =>
              simp [leftMoveTwiceDescription, runConfig, stepConfig,
                lookupTransition, Matches, transition, Tape.read,
                Tape.write, Tape.move, Tape.moveLeft]
          | cons lcell lrest =>
              cases lcell with
              | none =>
                  cases lrest <;>
                    simp [leftMoveTwiceDescription, runConfig,
                      stepConfig, lookupTransition, Matches,
                      transition, Tape.read, Tape.write, Tape.move,
                      Tape.moveLeft]
              | some b =>
                  cases b <;> cases lrest <;>
                    simp [leftMoveTwiceDescription, runConfig,
                      stepConfig, lookupTransition, Matches,
                      transition, Tape.read, Tape.write, Tape.move,
                      Tape.moveLeft]

theorem leftMoveTwiceDescription_haltsFromTape
    (T : Tape Bool) :
    leftMoveTwiceDescription.HaltsFromTape T
      (Tape.move Direction.left (Tape.move Direction.left T)) := by
  refine ⟨2, ?_⟩
  constructor <;> rw [leftMoveTwiceDescription_run]

def sentinelBoundaryCleanupDescription : MachineDescription :=
  canonicalSeqDescription leftMoveTwiceDescription
    oneGapRightEndCompactorDescription

theorem sentinelBoundaryCleanupDescription_subroutineReady :
    sentinelBoundaryCleanupDescription.SubroutineReady :=
  canonicalSeqDescription_subroutineReady
    leftMoveTwiceDescription_subroutineReady
    oneGapRightEndCompactorDescription_subroutineReady

theorem sentinelBoundaryCleanupDescription_haltsFrom_sentinelTarget
    (pref bits : Word Bool) (leftBit : Bool)
    (padding : List (Option Bool)) :
    sentinelBoundaryCleanupDescription.HaltsFromTape
      (leadingBlankLeftShiftTargetTapeWithPadding
        (some leftBit :: List.append (pref.reverse.map some) [none])
        bits padding)
      (leadingBlankLeftShiftTargetTapeWithPadding []
        (List.append pref (leftBit :: bits))
        (none :: leadingBlankLeftShiftTargetVisiblePadding padding)) := by
  let fullBits : Word Bool := List.append pref (leftBit :: bits)
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      leftMoveTwiceDescription_subroutineReady
      oneGapRightEndCompactorDescription_subroutineReady
      (leftMoveTwiceDescription_haltsFromTape
        (leadingBlankLeftShiftTargetTapeWithPadding
          (some leftBit :: List.append (pref.reverse.map some) [none])
          bits padding))
      (by
        change Tape.move Direction.left
            (Tape.move Direction.right
              (Tape.move Direction.left
                (Tape.move Direction.left
                  (leadingBlankLeftShiftTargetTapeWithPadding
                    (some leftBit ::
                      List.append (pref.reverse.map some) [none])
                    bits padding)))) =
          rightEdgeRewindSourceTapeWithBase [] fullBits
            (none :: leadingBlankLeftShiftTargetVisiblePadding padding)
        rw [sentinelGapTarget_move_left_left_eq_rightEdgeRewindSourceWithBoundary]
        exact
          rightEdgeRewindSourceTapeWithBase_move_left_move_right_padding_cons
            [] fullBits none
            (leadingBlankLeftShiftTargetVisiblePadding padding))
      (by
        cases pref with
        | nil =>
            simpa [fullBits] using
              oneGapRightEndCompactorDescription_haltsFromTapeWithBase_cons
                [] leftBit bits
                (none :: leadingBlankLeftShiftTargetVisiblePadding padding)
        | cons first rest =>
            simpa [fullBits, List.append_assoc] using
              oneGapRightEndCompactorDescription_haltsFromTapeWithBase_cons
                [] first (List.append rest (leftBit :: bits))
                (none :: leadingBlankLeftShiftTargetVisiblePadding padding))

def sentinelRightEndGapCompactorDescription : MachineDescription :=
  canonicalSeqDescription sentinelGapCompactorDescription
    sentinelBoundaryCleanupDescription

theorem sentinelRightEndGapCompactorDescription_subroutineReady :
    sentinelRightEndGapCompactorDescription.SubroutineReady :=
  canonicalSeqDescription_subroutineReady
    sentinelGapCompactorDescription_subroutineReady
    sentinelBoundaryCleanupDescription_subroutineReady

theorem sentinelRightEndGapCompactorDescription_haltsFrom_rightEndGapSource
    (gap : Nat) (pref : Word Bool) (leftBit current : Bool)
    (leftRest : Word Bool) (paddingTail : Nat) :
    sentinelRightEndGapCompactorDescription.HaltsFromTape
      (rightEndCompactionSourceTape
        (rightEndSentinelGapCompactorSourceLeftCells
          (List.append (pref.reverse.map some) [none])
          leftBit current leftRest gap
          (Nat.succ (Nat.succ paddingTail))))
      (leadingBlankLeftShiftTargetTapeWithPadding []
        (List.append pref (leftBit :: (current :: leftRest).reverse))
        (none :: sentinelGapCompactorFinalPadding gap
          (Nat.succ (Nat.succ paddingTail)) [])) := by
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      sentinelGapCompactorDescription_subroutineReady
      sentinelBoundaryCleanupDescription_subroutineReady
      (sentinelGapCompactorDescription_haltsFromTape_rightEndGapSource
        gap (List.append (pref.reverse.map some) [none])
        leftBit current leftRest (Nat.succ paddingTail))
      (by
        rw [sentinelGapCompactorFinalPadding_cons_cons])
      (by
        simpa [sentinelGapCompactorFinalPadding_cons_cons,
          leadingBlankLeftShiftTargetVisiblePadding] using
          sentinelBoundaryCleanupDescription_haltsFrom_sentinelTarget
            pref (current :: leftRest).reverse leftBit
            (sentinelGapCompactorFinalPadding gap
              (Nat.succ (Nat.succ paddingTail)) []))

end FiniteTransducers
end CommonGround

end Computability
end FoC

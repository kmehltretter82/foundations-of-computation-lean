import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.CursorBasic
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.SingletonRefresh

set_option doc.verso true

/-!
# Boundary-gap refresh handoffs

This module isolates the gap-aware repair layer used by the singleton head
refresh path.  The machines in {module}`FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.CursorBasic` repair singleton boundary
slack once the two missing physical blank cells are available immediately
before the following structured suffix.  The remaining concrete machine
obligation is to create that two-cell gap.
-/

namespace FoC
namespace Computability

open Languages

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

private theorem rightBoundaryGuardSlackRefreshDescription_run_enter_withPadding
    (bits : Word Bool) (padding : List (Option Bool)) :
    rightBoundaryGuardSlackRefreshDescription.runConfig 1
        { state := rightBoundaryGuardSlackRefreshDescription.start
          tape :=
            tapeAtCells []
              (none ::
                List.append (bits.map some)
                  (none :: none :: none :: padding)) } =
      { state := 1
        tape :=
          tapeAtCells [none]
            (List.append (bits.map some)
              (none :: none :: none :: padding)) } := by
  cases bits with
  | nil =>
      cases padding <;>
        simp [rightBoundaryGuardSlackRefreshDescription,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]
  | cons bit rest =>
      cases bit <;> cases rest <;> cases padding <;>
        simp [rightBoundaryGuardSlackRefreshDescription,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]

private theorem rightBoundaryGuardSlackRefreshDescription_run_scan_right_withPadding
    (bits : Word Bool) (left padding : List (Option Bool)) :
    rightBoundaryGuardSlackRefreshDescription.runConfig bits.length
        { state := 1
          tape :=
            tapeAtCells left
              (List.append (bits.map some) (none :: padding)) } =
      { state := 1
        tape :=
          tapeAtCells
            (List.append (bits.reverse.map some) left)
            (none :: padding) } := by
  induction bits generalizing left with
  | nil =>
      simp [MachineDescription.runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp [Nat.add_comm]]
      rw [MachineDescription.runConfig_add]
      have hstep :
          rightBoundaryGuardSlackRefreshDescription.runConfig 1
              { state := 1
                tape :=
                  tapeAtCells left
                    (List.append (some bit :: rest.map some)
                      (none :: padding)) } =
            { state := 1
              tape :=
                tapeAtCells (some bit :: left)
                  (List.append (rest.map some) (none :: padding)) } := by
        cases bit <;> cases rest <;> cases padding <;>
          simp [rightBoundaryGuardSlackRefreshDescription,
            MachineDescription.runConfig, MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]
      simp only [List.map_cons] at hstep ⊢
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: left)

private theorem rightBoundaryGuardSlackRefreshDescription_run_append_blank_cell_withPadding
    (left padding : List (Option Bool)) :
    rightBoundaryGuardSlackRefreshDescription.runConfig 3
        { state := 1
          tape := tapeAtCells left (none :: none :: none :: padding) } =
      { state := 4
        tape :=
          tapeAtCells (some false :: left)
            (some false :: none :: padding) } := by
  cases left <;> cases padding <;>
    simp [rightBoundaryGuardSlackRefreshDescription,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
      Tape.moveRight]

private theorem rightBoundaryGuardSlackRefreshDescription_run_scan_left_forGap
    (leftStack : Word Bool) (current : Bool)
    (right : List (Option Bool)) :
    rightBoundaryGuardSlackRefreshDescription.runConfig
        (leftStack.length + 1)
        { state := 4
          tape :=
            tapeAtCells
              (List.append (leftStack.map some) [none])
              (some current :: right) } =
      { state := 4
        tape :=
          tapeAtCells []
            (none ::
              List.append
                ((List.append leftStack.reverse [current]).map some)
                right) } := by
  induction leftStack generalizing current right with
  | nil =>
      cases current <;> cases right <;>
        simp [rightBoundaryGuardSlackRefreshDescription,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft]
  | cons next rest ih =>
      rw [show (next :: rest).length + 1 =
          1 + (rest.length + 1) by
        simp
        lia]
      rw [MachineDescription.runConfig_add]
      have hstep :
          rightBoundaryGuardSlackRefreshDescription.runConfig 1
              { state := 4
                tape :=
                  tapeAtCells
                    (List.append ((next :: rest).map some) [none])
                    (some current :: right) } =
            { state := 4
              tape :=
                tapeAtCells
                  (List.append (rest.map some) [none])
                  (some next :: some current :: right) } := by
        cases current <;> cases next <;> cases right <;>
          simp [rightBoundaryGuardSlackRefreshDescription,
            MachineDescription.runConfig, MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih next (some current :: right)

private theorem rightBoundaryGuardSlackRefreshDescription_run_finish_withPadding
    (bits : Word Bool) (padding : List (Option Bool)) :
    rightBoundaryGuardSlackRefreshDescription.runConfig 2
        { state := 4
          tape :=
            tapeAtCells []
              (none ::
                List.append
                  ((List.append bits [false, false]).map some)
                  (none :: padding)) } =
      { state := rightBoundaryGuardSlackRefreshDescription.halt
        tape :=
          tapeAtCells []
            (none ::
              List.append
                ((List.append bits [false, false]).map some)
                (none :: padding)) } := by
  cases bits with
  | nil =>
      cases padding <;>
        simp [rightBoundaryGuardSlackRefreshDescription,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          Tape.moveRight]
  | cons bit rest =>
      cases bit <;> cases rest <;> cases padding <;>
        simp [rightBoundaryGuardSlackRefreshDescription,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          Tape.moveRight]

theorem rightBoundaryGuardSlackRefreshDescription_run_to_target_withGap
    (bits : Word Bool) (padding : List (Option Bool)) :
    rightBoundaryGuardSlackRefreshDescription.runConfig
        (1 + (bits.length +
          (3 + ((false :: bits.reverse).length + 1 + 2))))
        { state := rightBoundaryGuardSlackRefreshDescription.start
          tape :=
            tapeAtCells []
              (none ::
                List.append (bits.map some)
                  (none :: none :: none :: padding)) } =
      { state := rightBoundaryGuardSlackRefreshDescription.halt
        tape :=
          tapeAtCells []
            (none ::
              List.append
                ((List.append bits [false, false]).map some)
                (none :: padding)) } := by
  rw [MachineDescription.runConfig_add]
  rw [rightBoundaryGuardSlackRefreshDescription_run_enter_withPadding]
  rw [MachineDescription.runConfig_add]
  rw [rightBoundaryGuardSlackRefreshDescription_run_scan_right_withPadding]
  rw [MachineDescription.runConfig_add]
  rw [rightBoundaryGuardSlackRefreshDescription_run_append_blank_cell_withPadding]
  rw [MachineDescription.runConfig_add]
  change
    rightBoundaryGuardSlackRefreshDescription.runConfig 2
        (rightBoundaryGuardSlackRefreshDescription.runConfig
          ((false :: bits.reverse).length + 1)
          { state := 4
            tape :=
              tapeAtCells
                (List.append ((false :: bits.reverse).map some) [none])
                (some false :: none :: padding) }) =
      { state := rightBoundaryGuardSlackRefreshDescription.halt
        tape :=
          tapeAtCells []
            (none ::
              List.append
                ((List.append bits [false, false]).map some)
                (none :: padding)) }
  rw [rightBoundaryGuardSlackRefreshDescription_run_scan_left_forGap]
  simpa [List.reverse_cons, List.map_append, List.append_assoc] using
    rightBoundaryGuardSlackRefreshDescription_run_finish_withPadding
      bits padding

theorem rightBoundaryGuardSlackRefreshDescription_haltsFromPayloadWithGap
    (bits : Word Bool) (padding : List (Option Bool)) :
    rightBoundaryGuardSlackRefreshDescription.HaltsFromTape
      (tapeAtCells []
        (none ::
          List.append (bits.map some)
            (none :: none :: none :: padding)))
      (tapeAtCells []
        (none ::
          List.append ((List.append bits [false, false]).map some)
            (none :: padding))) := by
  refine
    ⟨1 + (bits.length +
      (3 + ((false :: bits.reverse).length + 1 + 2))), ?_⟩
  constructor <;>
    rw [rightBoundaryGuardSlackRefreshDescription_run_to_target_withGap]

theorem rightBoundaryGuardSlackRefreshDescription_haltsFrom_rightBoundarySlackWithGap
    (left : List (Option Bool)) (head : Option Bool)
    (padding : List (Option Bool)) :
    rightBoundaryGuardSlackRefreshDescription.HaltsFromTape
      (tapeAtCells []
        (none ::
          List.append
            ((logicalTapeBits
              ({ left := left, head := head, right := [] } :
                Tape Bool)).map some)
            (none :: none :: none :: padding)))
      (tapeAtCells []
        (none ::
          List.append
            ((logicalTapeBits
              ({ left := left, head := head, right := [none] } :
                Tape Bool)).map some)
            (none :: padding))) := by
  simpa [logicalTapeBits, logicalCellListBits,
    logicalCellListBits_append, logicalCellBits, List.map_append,
    List.append_assoc] using
    rightBoundaryGuardSlackRefreshDescription_haltsFromPayloadWithGap
      (logicalTapeBits
        ({ left := left, head := head, right := [] } : Tape Bool))
      padding

private def leftBoundaryGuardSlackShiftPairStateForGap
    (first second : Bool) : Nat :=
  match first, second with
  | false, false => 4
  | false, true => 5
  | true, false => 6
  | true, true => 7

private theorem leftBoundaryGuardSlackShiftDescription_run_initial_withGap
    (first second : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    leftBoundaryGuardSlackShiftDescription.runConfig 3
        { state := leftBoundaryGuardSlackShiftDescription.start
          tape :=
            tapeAtCells []
              (none ::
                List.append ((first :: second :: rest).map some)
                  (none :: none :: none :: padding)) } =
      { state := leftBoundaryGuardSlackShiftPairStateForGap first second
        tape :=
          tapeAtCells
            (List.append (([false, false] : Word Bool).reverse.map some)
              [none])
            (List.append (rest.map some)
              (none :: none :: none :: padding)) } := by
  cases first <;> cases second <;> cases rest <;> cases padding <;>
    simp [leftBoundaryGuardSlackShiftDescription,
      leftBoundaryGuardSlackShiftPairStateForGap, MachineDescription.runConfig,
      MachineDescription.stepConfig, MachineDescription.lookupTransition,
      MachineDescription.Matches, tapeAtCells, Tape.read, Tape.write,
      Tape.move, Tape.moveRight]

private theorem leftBoundaryGuardSlackShiftDescription_run_loop_bit_withGap
    (pref rest : Word Bool) (first second current : Bool)
    (padding : List (Option Bool)) :
    leftBoundaryGuardSlackShiftDescription.runConfig 1
        { state := leftBoundaryGuardSlackShiftPairStateForGap first second
          tape :=
            tapeAtCells
              (List.append (pref.reverse.map some) [none])
              (List.append ((current :: rest).map some)
                (none :: none :: none :: padding)) } =
      { state := leftBoundaryGuardSlackShiftPairStateForGap second current
        tape :=
          tapeAtCells
            (List.append ((List.append pref [first]).reverse.map some)
              [none])
            (List.append (rest.map some)
              (none :: none :: none :: padding)) } := by
  cases first <;> cases second <;> cases current <;>
    cases rest <;> cases padding <;>
    simp [leftBoundaryGuardSlackShiftDescription,
      leftBoundaryGuardSlackShiftPairStateForGap, MachineDescription.runConfig,
      MachineDescription.stepConfig, MachineDescription.lookupTransition,
      MachineDescription.Matches, tapeAtCells, Tape.read, Tape.write,
      Tape.move, Tape.moveRight, List.reverse_append]

private theorem leftBoundaryGuardSlackShiftDescription_run_loop_finish_withGap
    (pref : Word Bool) (first second : Bool)
    (padding : List (Option Bool)) :
    leftBoundaryGuardSlackShiftDescription.runConfig 2
        { state := leftBoundaryGuardSlackShiftPairStateForGap first second
          tape :=
            tapeAtCells
              (List.append (pref.reverse.map some) [none])
              (none :: none :: none :: padding) } =
      { state := leftBoundaryGuardSlackShiftDescription.halt
        tape :=
          tapeAtCells
            (List.append
              ((List.append pref [first, second]).reverse.map some)
              [none])
            (none :: padding) } := by
  cases first <;> cases second <;> cases padding <;>
    simp [leftBoundaryGuardSlackShiftDescription,
      leftBoundaryGuardSlackShiftPairStateForGap,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight,
      List.reverse_append]

private theorem leftBoundaryGuardSlackShiftDescription_run_loop_withGap
    (rest : Word Bool) (pref : Word Bool)
    (first second : Bool) (padding : List (Option Bool)) :
    leftBoundaryGuardSlackShiftDescription.runConfig (rest.length + 2)
        { state := leftBoundaryGuardSlackShiftPairStateForGap first second
          tape :=
            tapeAtCells
              (List.append (pref.reverse.map some) [none])
              (List.append (rest.map some)
                (none :: none :: none :: padding)) } =
      { state := leftBoundaryGuardSlackShiftDescription.halt
        tape :=
          tapeAtCells
            (List.append
              ((List.append pref (first :: second :: rest)).reverse.map some)
              [none])
            (none :: padding) } := by
  induction rest generalizing pref first second with
  | nil =>
      simpa [List.append_assoc] using
        leftBoundaryGuardSlackShiftDescription_run_loop_finish_withGap
          pref first second padding
  | cons current rest ih =>
      rw [show (current :: rest).length + 2 =
          1 + (rest.length + 2) by
        simp
        lia]
      rw [MachineDescription.runConfig_add]
      rw [leftBoundaryGuardSlackShiftDescription_run_loop_bit_withGap]
      simpa [List.append_assoc] using
        ih (List.append pref [first]) second current

theorem leftBoundaryGuardSlackShiftDescription_run_to_rightEdge_withGap
    (first second : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    leftBoundaryGuardSlackShiftDescription.runConfig
        (3 + (rest.length + 2))
        { state := leftBoundaryGuardSlackShiftDescription.start
          tape :=
            tapeAtCells []
              (none ::
                List.append ((first :: second :: rest).map some)
                  (none :: none :: none :: padding)) } =
      { state := leftBoundaryGuardSlackShiftDescription.halt
        tape :=
          tapeAtCells
            (List.append
              ((List.append ([false, false] : Word Bool)
                (first :: second :: rest)).reverse.map some)
              [none])
            (none :: padding) } := by
  rw [MachineDescription.runConfig_add]
  rw [leftBoundaryGuardSlackShiftDescription_run_initial_withGap]
  simpa [List.append_assoc] using
    leftBoundaryGuardSlackShiftDescription_run_loop_withGap
      rest ([false, false] : Word Bool) first second padding

theorem leftBoundaryGuardSlackShiftDescription_haltsFromPayloadWithGap
    (first second : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    leftBoundaryGuardSlackShiftDescription.HaltsFromTape
      (tapeAtCells []
        (none ::
          List.append ((first :: second :: rest).map some)
            (none :: none :: none :: padding)))
      (tapeAtCells
        (List.append
          ((List.append ([false, false] : Word Bool)
            (first :: second :: rest)).reverse.map some)
          [none])
        (none :: padding)) := by
  refine ⟨3 + (rest.length + 2), ?_⟩
  constructor <;>
    rw [leftBoundaryGuardSlackShiftDescription_run_to_rightEdge_withGap]

private theorem leftBoundaryGuardSlackShift_rightEdge_equiv_rewindSource_withPadding
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.Equiv
      (tapeAtCells (List.append (bits.reverse.map some) [none])
        (none :: padding))
      (rightEdgeRewindSourceTape bits padding) := by
  simp [rightEdgeRewindSourceTape, tapeAtCells, Tape.Equiv,
    dropTrailingNone_append_none]

theorem leftBoundaryGuardSlackRefreshDescription_haltsFromPayloadWithGap
    (first second : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    leftBoundaryGuardSlackRefreshDescription.HaltsFromTapeEquiv
      (tapeAtCells []
        (none ::
          List.append ((first :: second :: rest).map some)
            (none :: none :: none :: padding)))
      (tapeAtCells []
        (none ::
          List.append
            ((List.append ([false, false] : Word Bool)
              (first :: second :: rest)).map some)
            (none :: padding))) := by
  let shifted : Word Bool :=
    List.append ([false, false] : Word Bool) (first :: second :: rest)
  let Tmid : Tape Bool :=
    tapeAtCells (List.append (shifted.reverse.map some) [none])
      (none :: padding)
  let Trewound : Tape Bool :=
    rightEdgeRewindTargetTape shifted padding
  have hshift :
      leftBoundaryGuardSlackShiftDescription.HaltsFromTape
        (tapeAtCells []
          (none ::
            List.append ((first :: second :: rest).map some)
              (none :: none :: none :: padding)))
        Tmid := by
    simpa [Tmid, shifted] using
      leftBoundaryGuardSlackShiftDescription_haltsFromPayloadWithGap
        first second rest padding
  have hrewind :
      rightEdgeRewindDescription.HaltsFromTapeEquiv Tmid Trewound := by
    exact
      MachineDescription.HaltsFromTapeEquiv_of_input_equiv
        (D := rightEdgeRewindDescription)
        (Tin := rightEdgeRewindSourceTape shifted padding)
        (Tin' := Tmid)
        (Tout := Trewound)
        (Tape.Equiv.symm
          (leftBoundaryGuardSlackShift_rightEdge_equiv_rewindSource_withPadding
            shifted padding))
        (by
          simpa [Trewound] using
            rightEdgeRewindDescription_haltsFromTape shifted padding)
  have hshiftThenRewind :
      (canonicalPrimitiveSeqDescription
        leftBoundaryGuardSlackShiftDescription
        rightEdgeRewindDescription).HaltsFromTapeEquiv
          (tapeAtCells []
            (none ::
              List.append ((first :: second :: rest).map some)
                (none :: none :: none :: padding)))
          Trewound :=
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      leftBoundaryGuardSlackShiftDescription_subroutineReady
      rightEdgeRewindDescription_subroutineReady
      (MachineDescription.HaltsFromTape.toEquiv hshift)
      hrewind
  have hleft :
      leftMoveOnceDescription.HaltsFromTape Trewound
        (tapeAtCells []
          (none ::
            List.append (shifted.map some) (none :: padding))) := by
    simpa [Trewound, rightEdgeRewindTargetTape, tapeAtCells,
      Tape.move, Tape.moveLeft] using
      leftMoveOnceDescription_haltsFromTape Trewound
  simpa [leftBoundaryGuardSlackRefreshDescription, shifted] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      (canonicalPrimitiveSeqDescription_subroutineReady
        leftBoundaryGuardSlackShiftDescription_subroutineReady
        rightEdgeRewindDescription_subroutineReady)
      leftMoveOnceDescription_subroutineReady
      hshiftThenRewind
      (MachineDescription.HaltsFromTape.toEquiv hleft)

theorem leftBoundaryGuardSlackRefreshDescription_haltsFrom_leftBoundarySlackWithGap
    (head : Option Bool) (right : List (Option Bool))
    (padding : List (Option Bool)) :
    leftBoundaryGuardSlackRefreshDescription.HaltsFromTapeEquiv
      (tapeAtCells []
        (none ::
          List.append
            ((logicalTapeBits
              ({ left := [], head := head, right := right } :
                Tape Bool)).map some)
            (none :: none :: none :: padding)))
      (tapeAtCells []
        (none ::
          List.append
            ((logicalTapeBits
              ({ left := [none], head := head, right := right } :
                Tape Bool)).map some)
            (none :: padding))) := by
  simpa [logicalTapeBits, logicalCellListBits,
    logicalCellListBits_append, logicalCellBits, List.map_append,
    List.append_assoc] using
    leftBoundaryGuardSlackRefreshDescription_haltsFromPayloadWithGap true true
      (List.append (logicalCellBits head) (logicalCellListBits right))
      padding

/-- Encoding with a two-blank gap between the first segment and the suffix. -/
def encodedStructuredHeadGapTapes
    (head : Tape Bool) (rest : List (Tape Bool)) : Tape Bool :=
  tapeAtCells []
    (List.append tapeSeparatorCells
      (List.append (logicalTapeCode head)
        (none :: none :: encodedStructuredTapeCells rest)))

/--
Raw bit-level shape for a head-segment suffix gap creator.

The future concrete machine can be proved against this contract without
mentioning the left/right singleton boundary constructors.  The bridge below
specializes the raw payload bits to the two boundary shapes.
-/
def encodedStructuredHeadPayloadTapes
    (bits : Word Bool) (rest : List (Tape Bool)) : Tape Bool :=
  tapeAtCells []
    (List.append tapeSeparatorCells
      (List.append (bits.map some) (encodedStructuredTapeCells rest)))

/-- Target shape after inserting two physical blank cells before the suffix. -/
def encodedStructuredHeadPayloadGapTapes
    (bits : Word Bool) (rest : List (Tape Bool)) : Tape Bool :=
  tapeAtCells []
    (List.append tapeSeparatorCells
      (List.append (bits.map some)
        (none :: none :: encodedStructuredTapeCells rest)))

theorem encodedStructuredHeadPayloadTapes_eq_structuredTapes
    (head : Tape Bool) (rest : List (Tape Bool)) :
    encodedStructuredHeadPayloadTapes (logicalTapeBits head) rest =
      encodedStructuredTapes (head :: rest) := by
  simp [encodedStructuredHeadPayloadTapes, encodedStructuredTapes,
    encodedStructuredTapeCells, logicalTapeCode_eq_map_some]

theorem encodedStructuredHeadPayloadGapTapes_eq_headGap
    (head : Tape Bool) (rest : List (Tape Bool)) :
    encodedStructuredHeadPayloadGapTapes (logicalTapeBits head) rest =
      encodedStructuredHeadGapTapes head rest := by
  simp [encodedStructuredHeadPayloadGapTapes,
    encodedStructuredHeadGapTapes, logicalTapeCode_eq_map_some]

theorem rightBoundaryGuardSlackRefreshDescription_haltsFrom_rightBoundaryHeadGap
    (left : List (Option Bool)) (head : Option Bool)
    (rest : List (Tape Bool)) :
    rightBoundaryGuardSlackRefreshDescription.HaltsFromTapeEquiv
      (encodedStructuredHeadGapTapes
        ({ left := left, head := head, right := [] } : Tape Bool) rest)
      (encodedStructuredTapes
        (({ left := left, head := head, right := [none] } :
          Tape Bool) :: rest)) := by
  rcases encodedStructuredTapeCells_startsWith_separator rest with
    ⟨padding, hpadding⟩
  simpa [encodedStructuredHeadGapTapes, encodedStructuredTapes,
    encodedStructuredTapeCells, logicalTapeCode_eq_map_some,
    hpadding, tapeSeparatorCells, List.append_assoc] using
    MachineDescription.HaltsFromTape.toEquiv
      (rightBoundaryGuardSlackRefreshDescription_haltsFrom_rightBoundarySlackWithGap
        left head padding)

theorem leftBoundaryGuardSlackRefreshDescription_haltsFrom_leftBoundaryHeadGap
    (head : Option Bool) (right : List (Option Bool))
    (rest : List (Tape Bool)) :
    leftBoundaryGuardSlackRefreshDescription.HaltsFromTapeEquiv
      (encodedStructuredHeadGapTapes
        ({ left := [], head := head, right := right } : Tape Bool) rest)
      (encodedStructuredTapes
        (({ left := [none], head := head, right := right } :
          Tape Bool) :: rest)) := by
  rcases encodedStructuredTapeCells_startsWith_separator rest with
    ⟨padding, hpadding⟩
  simpa [encodedStructuredHeadGapTapes, encodedStructuredTapes,
    encodedStructuredTapeCells, logicalTapeCode_eq_map_some,
    hpadding, tapeSeparatorCells, List.append_assoc] using
    leftBoundaryGuardSlackRefreshDescription_haltsFrom_leftBoundarySlackWithGap
      head right padding

def singletonLeftBoundaryHeadRefreshDescription
    (gapCreator : MachineDescription) : MachineDescription :=
  canonicalPrimitiveSeqDescription gapCreator
    leftBoundaryGuardSlackRefreshDescription

def singletonRightBoundaryHeadRefreshDescription
    (gapCreator : MachineDescription) : MachineDescription :=
  canonicalPrimitiveSeqDescription gapCreator
    rightBoundaryGuardSlackRefreshDescription

theorem singletonLeftBoundaryHeadRefreshDescription_subroutineReady
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    (singletonLeftBoundaryHeadRefreshDescription gapCreator).SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady hgap
    leftBoundaryGuardSlackRefreshDescription_subroutineReady

theorem singletonRightBoundaryHeadRefreshDescription_subroutineReady
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    (singletonRightBoundaryHeadRefreshDescription gapCreator).SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady hgap
    rightBoundaryGuardSlackRefreshDescription_subroutineReady

structure SingletonBoundaryGapCreatorContract
    (gapCreator : MachineDescription) : Prop where
  subroutineReady : gapCreator.SubroutineReady
  leftBoundary :
    forall (head : Option Bool) (right : List (Option Bool))
      (rest : List (Tape Bool)),
      gapCreator.HaltsFromTapeEquiv
        (encodedStructuredTapes
          (({ left := [], head := head, right := right ++ [none] } :
            Tape Bool) :: rest))
        (encodedStructuredHeadGapTapes
          ({ left := [], head := head, right := right ++ [none] } :
            Tape Bool) rest)
  rightBoundary :
    forall (left : List (Option Bool)) (head : Option Bool)
      (rest : List (Tape Bool)),
      gapCreator.HaltsFromTapeEquiv
        (encodedStructuredTapes
          (({ left := left ++ [none], head := head, right := [] } :
            Tape Bool) :: rest))
        (encodedStructuredHeadGapTapes
          ({ left := left ++ [none], head := head, right := [] } :
            Tape Bool) rest)

/--
Raw payload contract for the remaining suffix-gap creator machine.

It is intentionally stated over arbitrary first-segment payload bits; this is
the direct tape-shape target for a machine that scans past the first structured
segment and shifts the encoded suffix two cells to the right.
-/
structure HeadSuffixGapCreatorContract
    (gapCreator : MachineDescription) : Prop where
  subroutineReady : gapCreator.SubroutineReady
  realizes :
    forall (bits : Word Bool) (rest : List (Tape Bool)),
      gapCreator.HaltsFromTapeEquiv
        (encodedStructuredHeadPayloadTapes bits rest)
        (encodedStructuredHeadPayloadGapTapes bits rest)

namespace HeadSuffixGapCreatorContract

theorem toSingletonBoundary
    {gapCreator : MachineDescription}
    (hgap : HeadSuffixGapCreatorContract gapCreator) :
    SingletonBoundaryGapCreatorContract gapCreator where
  subroutineReady := hgap.subroutineReady
  leftBoundary := by
    intro head right rest
    simpa [encodedStructuredHeadPayloadTapes_eq_structuredTapes,
      encodedStructuredHeadPayloadGapTapes_eq_headGap] using
      hgap.realizes
        (logicalTapeBits
          ({ left := [], head := head, right := right ++ [none] } :
            Tape Bool))
        rest
  rightBoundary := by
    intro left head rest
    simpa [encodedStructuredHeadPayloadTapes_eq_structuredTapes,
      encodedStructuredHeadPayloadGapTapes_eq_headGap] using
      hgap.realizes
        (logicalTapeBits
          ({ left := left ++ [none], head := head, right := [] } :
            Tape Bool))
        rest

end HeadSuffixGapCreatorContract

namespace SingletonBoundaryGapCreatorContract

theorem leftBoundaryRefresh
    {gapCreator : MachineDescription}
    (hgap : SingletonBoundaryGapCreatorContract gapCreator)
    (head : Option Bool) (right : List (Option Bool))
    (rest : List (Tape Bool)) :
    (singletonLeftBoundaryHeadRefreshDescription gapCreator).HaltsFromTapeEquiv
      (encodedStructuredTapes
        (({ left := [], head := head, right := right ++ [none] } :
          Tape Bool) :: rest))
      (encodedStructuredTapes
        (guardLogicalTape
          ({ left := [], head := head, right := right } : Tape Bool) ::
            rest)) := by
  simpa [singletonLeftBoundaryHeadRefreshDescription, guardLogicalTape,
    List.append_assoc] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      hgap.subroutineReady
      leftBoundaryGuardSlackRefreshDescription_subroutineReady
      (hgap.leftBoundary head right rest)
      (leftBoundaryGuardSlackRefreshDescription_haltsFrom_leftBoundaryHeadGap
        head (right ++ [none]) rest)

theorem rightBoundaryRefresh
    {gapCreator : MachineDescription}
    (hgap : SingletonBoundaryGapCreatorContract gapCreator)
    (left : List (Option Bool)) (head : Option Bool)
    (rest : List (Tape Bool)) :
    (singletonRightBoundaryHeadRefreshDescription gapCreator).HaltsFromTapeEquiv
      (encodedStructuredTapes
        (({ left := left ++ [none], head := head, right := [] } :
          Tape Bool) :: rest))
      (encodedStructuredTapes
        (guardLogicalTape
          ({ left := left, head := head, right := [] } : Tape Bool) ::
            rest)) := by
  simpa [singletonRightBoundaryHeadRefreshDescription, guardLogicalTape,
    List.append_assoc] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      hgap.subroutineReady
      rightBoundaryGuardSlackRefreshDescription_subroutineReady
      (hgap.rightBoundary left head rest)
      (rightBoundaryGuardSlackRefreshDescription_haltsFrom_rightBoundaryHeadGap
        (left ++ [none]) head rest)

end SingletonBoundaryGapCreatorContract

/-
Retargeted branch blocks for the future suffix-preserving singleton head
dispatcher.  They mirror the edge-only `singletonShape...RepairDescription`
blocks, but their local bodies first create the suffix gap and then run the
existing boundary repair leaf.
-/
def singletonHeadRefreshFinalHalt : Nat :=
  2

def singletonHeadLeftRepairOffset : Nat :=
  3

def singletonHeadLeftRepairDescription
    (gapCreator : MachineDescription) : MachineDescription :=
  MachineDescription.offsetRetargetDescription
    singletonHeadLeftRepairOffset
    singletonHeadRefreshFinalHalt
    (singletonLeftBoundaryHeadRefreshDescription gapCreator)

def singletonHeadLeftRepairStart
    (gapCreator : MachineDescription) : Nat :=
  (singletonHeadLeftRepairDescription gapCreator).start

def singletonHeadLeftRepairLimit
    (gapCreator : MachineDescription) : Nat :=
  (singletonHeadLeftRepairDescription gapCreator).stateCount

def singletonHeadRightRepairOffset
    (gapCreator : MachineDescription) : Nat :=
  singletonHeadLeftRepairLimit gapCreator

def singletonHeadRightRepairDescription
    (gapCreator : MachineDescription) : MachineDescription :=
  MachineDescription.offsetRetargetDescription
    (singletonHeadRightRepairOffset gapCreator)
    singletonHeadRefreshFinalHalt
    (singletonRightBoundaryHeadRefreshDescription gapCreator)

def singletonHeadRightRepairStart
    (gapCreator : MachineDescription) : Nat :=
  (singletonHeadRightRepairDescription gapCreator).start

def singletonHeadRightRepairLimit
    (gapCreator : MachineDescription) : Nat :=
  (singletonHeadRightRepairDescription gapCreator).stateCount

theorem singletonHeadRefreshFinalHalt_lt_leftRepairOffset :
    singletonHeadRefreshFinalHalt < singletonHeadLeftRepairOffset := by
  decide

theorem singletonHeadLeftRepairDescription_subroutineReady
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    (singletonHeadLeftRepairDescription gapCreator).SubroutineReady :=
  MachineDescription.offsetRetargetDescription_subroutineReady
    singletonHeadRefreshFinalHalt_lt_leftRepairOffset
    (singletonLeftBoundaryHeadRefreshDescription_subroutineReady hgap).left

theorem singletonHeadRefreshFinalHalt_lt_rightRepairOffset
    (gapCreator : MachineDescription) :
    singletonHeadRefreshFinalHalt <
      singletonHeadRightRepairOffset gapCreator := by
  simp [singletonHeadRightRepairOffset, singletonHeadLeftRepairLimit,
    singletonHeadLeftRepairDescription,
    MachineDescription.offsetRetargetDescription]
  exact
    Nat.lt_of_lt_of_le
      (Nat.lt_succ_self singletonHeadRefreshFinalHalt)
      (Nat.le_max_right
        (singletonHeadLeftRepairOffset +
          (singletonLeftBoundaryHeadRefreshDescription gapCreator).stateCount)
        (singletonHeadRefreshFinalHalt + 1))

theorem singletonHeadRightRepairDescription_subroutineReady
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    (singletonHeadRightRepairDescription gapCreator).SubroutineReady :=
  MachineDescription.offsetRetargetDescription_subroutineReady
    (singletonHeadRefreshFinalHalt_lt_rightRepairOffset gapCreator)
    (singletonRightBoundaryHeadRefreshDescription_subroutineReady hgap).left

theorem singletonHeadLeftRepairDescription_haltsFrom_leftBoundary
    {gapCreator : MachineDescription}
    (hgap : SingletonBoundaryGapCreatorContract gapCreator)
    (head : Option Bool) (right : List (Option Bool))
    (rest : List (Tape Bool)) :
    (singletonHeadLeftRepairDescription gapCreator).HaltsFromTapeEquiv
      (encodedStructuredTapes
        (({ left := [], head := head, right := right ++ [none] } :
          Tape Bool) :: rest))
      (encodedStructuredTapes
        (guardLogicalTape
          ({ left := [], head := head, right := right } : Tape Bool) ::
            rest)) := by
  rcases hgap.leftBoundaryRefresh head right rest with
    ⟨actual, hhalts, hequiv⟩
  refine ⟨actual, ?_, hequiv⟩
  simpa [singletonHeadLeftRepairDescription] using
    MachineDescription.offsetRetargetDescription_haltsFromTape
      singletonHeadRefreshFinalHalt_lt_leftRepairOffset
      (singletonLeftBoundaryHeadRefreshDescription_subroutineReady
        hgap.subroutineReady).right
      hhalts

theorem singletonHeadRightRepairDescription_haltsFrom_rightBoundary
    {gapCreator : MachineDescription}
    (hgap : SingletonBoundaryGapCreatorContract gapCreator)
    (left : List (Option Bool)) (head : Option Bool)
    (rest : List (Tape Bool)) :
    (singletonHeadRightRepairDescription gapCreator).HaltsFromTapeEquiv
      (encodedStructuredTapes
        (({ left := left ++ [none], head := head, right := [] } :
          Tape Bool) :: rest))
      (encodedStructuredTapes
        (guardLogicalTape
          ({ left := left, head := head, right := [] } : Tape Bool) ::
            rest)) := by
  rcases hgap.rightBoundaryRefresh left head rest with
    ⟨actual, hhalts, hequiv⟩
  refine ⟨actual, ?_, hequiv⟩
  simpa [singletonHeadRightRepairDescription] using
    MachineDescription.offsetRetargetDescription_haltsFromTape
      (singletonHeadRefreshFinalHalt_lt_rightRepairOffset
        gapCreator)
      (singletonRightBoundaryHeadRefreshDescription_subroutineReady
        hgap.subroutineReady).right
      hhalts

namespace HeadSuffixGapCreatorContract

theorem leftBoundaryRefresh
    {gapCreator : MachineDescription}
    (hgap : HeadSuffixGapCreatorContract gapCreator)
    (head : Option Bool) (right : List (Option Bool))
    (rest : List (Tape Bool)) :
    (singletonLeftBoundaryHeadRefreshDescription gapCreator).HaltsFromTapeEquiv
      (encodedStructuredTapes
        (({ left := [], head := head, right := right ++ [none] } :
          Tape Bool) :: rest))
      (encodedStructuredTapes
        (guardLogicalTape
          ({ left := [], head := head, right := right } : Tape Bool) ::
            rest)) :=
  (HeadSuffixGapCreatorContract.toSingletonBoundary hgap).leftBoundaryRefresh
    head right rest

theorem rightBoundaryRefresh
    {gapCreator : MachineDescription}
    (hgap : HeadSuffixGapCreatorContract gapCreator)
    (left : List (Option Bool)) (head : Option Bool)
    (rest : List (Tape Bool)) :
    (singletonRightBoundaryHeadRefreshDescription gapCreator).HaltsFromTapeEquiv
      (encodedStructuredTapes
        (({ left := left ++ [none], head := head, right := [] } :
          Tape Bool) :: rest))
      (encodedStructuredTapes
        (guardLogicalTape
          ({ left := left, head := head, right := [] } : Tape Bool) ::
            rest)) :=
  (HeadSuffixGapCreatorContract.toSingletonBoundary hgap).rightBoundaryRefresh
    left head rest

end HeadSuffixGapCreatorContract

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC

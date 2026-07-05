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

private def TransitionListDeterministic
    (transitions : List TransitionDescription) : Prop :=
  forall t u : TransitionDescription,
    t ∈ transitions -> u ∈ transitions ->
      TransitionDescription.SameKey t u ->
        TransitionDescription.SameAction t u

private def TransitionSourceDisjoint
    (left right : List TransitionDescription) : Prop :=
  forall t u : TransitionDescription,
    t ∈ left -> u ∈ right -> t.source ≠ u.source

private def TransitionSourcesBelow
    (bound : Nat) (transitions : List TransitionDescription) : Prop :=
  forall t : TransitionDescription, t ∈ transitions -> t.source < bound

private def TransitionSourcesAtLeast
    (bound : Nat) (transitions : List TransitionDescription) : Prop :=
  forall t : TransitionDescription, t ∈ transitions -> bound ≤ t.source

private theorem transitionListDeterministic_append_of_sourceDisjoint
    {left right : List TransitionDescription}
    (hleft : TransitionListDeterministic left)
    (hright : TransitionListDeterministic right)
    (hdisjoint : TransitionSourceDisjoint left right) :
    TransitionListDeterministic (left ++ right) := by
  intro t u ht hu hkey
  simp at ht hu
  rcases ht with ht | ht <;> rcases hu with hu | hu
  · exact hleft t u ht hu hkey
  · exact False.elim ((hdisjoint t u ht hu) hkey.left)
  · exact False.elim ((hdisjoint u t hu ht) hkey.left.symm)
  · exact hright t u ht hu hkey

private theorem transitionSourceDisjoint_of_below_atLeast
    {bound : Nat} {left right : List TransitionDescription}
    (hleft : TransitionSourcesBelow bound left)
    (hright : TransitionSourcesAtLeast bound right) :
    TransitionSourceDisjoint left right := by
  intro t u ht hu hsource
  have htBound := hleft t ht
  have huBound := hright u hu
  lia

private theorem transitionSourcesBelow_append
    {bound : Nat} {left right : List TransitionDescription}
    (hleft : TransitionSourcesBelow bound left)
    (hright : TransitionSourcesBelow bound right) :
    TransitionSourcesBelow bound (left ++ right) := by
  intro t ht
  simp at ht
  rcases ht with ht | ht
  · exact hleft t ht
  · exact hright t ht

private theorem transitionSourcesAtLeast_append
    {bound : Nat} {left right : List TransitionDescription}
    (hleft : TransitionSourcesAtLeast bound left)
    (hright : TransitionSourcesAtLeast bound right) :
    TransitionSourcesAtLeast bound (left ++ right) := by
  intro t ht
  simp at ht
  rcases ht with ht | ht
  · exact hleft t ht
  · exact hright t ht

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

def singletonHeadTerminalProbeOffset
    (gapCreator : MachineDescription) : Nat :=
  singletonHeadRightRepairLimit gapCreator

def singletonHeadTerminalLocalCanonicalExit : Nat :=
  11

def singletonHeadTerminalLocalRightBoundaryExit : Nat :=
  12

def singletonHeadTerminalLocalUnusedExit : Nat :=
  13

def singletonHeadTerminalLocalTarget
    (cell : Option Bool) : Nat :=
  match cell with
  | none => singletonHeadTerminalLocalCanonicalExit
  | some false => singletonHeadTerminalLocalRightBoundaryExit
  | some true => singletonHeadTerminalLocalUnusedExit

def singletonHeadTerminalTarget
    (gapCreator : MachineDescription) (cell : Option Bool) : Nat :=
  match cell with
  | none => singletonHeadRefreshFinalHalt
  | some false => singletonHeadRightRepairStart gapCreator
  | some true => singletonHeadRefreshFinalHalt

def singletonHeadTerminalLocalDescription : MachineDescription :=
  singletonTerminalPairProbeDescription
    singletonHeadTerminalLocalCanonicalExit
    singletonHeadTerminalLocalRightBoundaryExit

def singletonHeadTerminalProbeDescription
    (gapCreator : MachineDescription) : MachineDescription :=
  MachineDescription.offsetReadExitRetargetDescription
    (singletonHeadTerminalProbeOffset gapCreator)
    singletonHeadTerminalLocalTarget
    (singletonHeadTerminalTarget gapCreator)
    singletonHeadTerminalLocalDescription

def singletonHeadTerminalProbeStart
    (gapCreator : MachineDescription) : Nat :=
  (singletonHeadTerminalProbeDescription gapCreator).start

def singletonHeadRefreshOpeningDescription
    (gapCreator : MachineDescription) : MachineDescription :=
  singletonOpeningProbeDescription
    (singletonHeadTerminalProbeStart gapCreator)
    (singletonHeadLeftRepairStart gapCreator)

def singletonHeadRefreshDescription
    (gapCreator : MachineDescription) : MachineDescription where
  stateCount := (singletonHeadTerminalProbeDescription gapCreator).stateCount
  start := (singletonHeadRefreshOpeningDescription gapCreator).start
  halt := singletonHeadRefreshFinalHalt
  transitions :=
    (singletonHeadRefreshOpeningDescription gapCreator).transitions ++
      ((singletonHeadLeftRepairDescription gapCreator).transitions ++
        ((singletonHeadRightRepairDescription gapCreator).transitions ++
          (singletonHeadTerminalProbeDescription gapCreator).transitions))

theorem singletonHeadTerminalLocalDescription_subroutineReady :
    singletonHeadTerminalLocalDescription.SubroutineReady :=
  singletonTerminalPairProbeDescription_subroutineReady
    singletonHeadTerminalLocalCanonicalExit
    singletonHeadTerminalLocalRightBoundaryExit

theorem singletonHeadTerminalLocalDescription_transitionFreeAt
    (cell : Option Bool) :
    singletonHeadTerminalLocalDescription.TransitionFreeAt
      (singletonHeadTerminalLocalTarget cell) := by
  cases cell with
  | none =>
      exact
        transition_notFrom_of_all
          (l := singletonHeadTerminalLocalDescription.transitions)
          (state := singletonHeadTerminalLocalTarget none)
          (by decide)
  | some bit =>
      cases bit with
      | false =>
          exact
            transition_notFrom_of_all
              (l := singletonHeadTerminalLocalDescription.transitions)
              (state := singletonHeadTerminalLocalTarget (some false))
              (by decide)
      | true =>
          exact
            transition_notFrom_of_all
              (l := singletonHeadTerminalLocalDescription.transitions)
              (state := singletonHeadTerminalLocalTarget (some true))
              (by decide)

theorem singletonHeadTerminalTarget_lt_probeOffset
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    forall cell : Option Bool,
      singletonHeadTerminalTarget gapCreator cell <
        singletonHeadTerminalProbeOffset gapCreator := by
  intro cell
  cases cell with
  | none =>
      have hhalt :=
        (singletonHeadRightRepairDescription_subroutineReady
          hgap).left.right.right.left
      simpa [singletonHeadTerminalTarget,
        singletonHeadTerminalProbeOffset,
        singletonHeadRightRepairLimit,
        singletonHeadRightRepairDescription] using hhalt
  | some bit =>
      cases bit with
      | false =>
          have hstart :=
            (singletonHeadRightRepairDescription_subroutineReady
              hgap).left.right.left
          simpa [singletonHeadTerminalTarget,
            singletonHeadTerminalProbeOffset,
            singletonHeadRightRepairLimit,
            singletonHeadRightRepairStart] using hstart
      | true =>
          have hhalt :=
            (singletonHeadRightRepairDescription_subroutineReady
              hgap).left.right.right.left
          simpa [singletonHeadTerminalTarget,
            singletonHeadTerminalProbeOffset,
            singletonHeadRightRepairLimit,
            singletonHeadRightRepairDescription] using hhalt

theorem singletonHeadTerminalProbeDescription_subroutineReady
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    (singletonHeadTerminalProbeDescription gapCreator).SubroutineReady :=
  MachineDescription.offsetReadExitRetargetDescription_subroutineReady
    (singletonHeadTerminalTarget_lt_probeOffset hgap)
    singletonHeadTerminalLocalDescription_subroutineReady.left

theorem singletonHeadRefreshOpeningDescription_subroutineReady
    (gapCreator : MachineDescription) :
    (singletonHeadRefreshOpeningDescription gapCreator).SubroutineReady :=
  singletonOpeningProbeDescription_subroutineReady
    (singletonHeadTerminalProbeStart gapCreator)
    (singletonHeadLeftRepairStart gapCreator)

theorem singletonHeadRefreshOpeningDescription_sources_below_leftRepairOffset
    (gapCreator : MachineDescription) :
    TransitionSourcesBelow singletonHeadLeftRepairOffset
      (singletonHeadRefreshOpeningDescription gapCreator).transitions := by
  intro t ht
  simp [singletonHeadRefreshOpeningDescription,
    singletonOpeningProbeDescription] at ht
  rcases ht with rfl | rfl | rfl
  · simpa using (by decide : 0 < singletonHeadLeftRepairOffset)
  · simpa using (by decide : 1 < singletonHeadLeftRepairOffset)
  · simpa using (by decide : 1 < singletonHeadLeftRepairOffset)

theorem singletonHeadLeftRepairDescription_sources_in_block
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    forall t : TransitionDescription,
      t ∈ (singletonHeadLeftRepairDescription gapCreator).transitions ->
        singletonHeadLeftRepairOffset ≤ t.source ∧
          t.source < singletonHeadLeftRepairLimit gapCreator := by
  intro t ht
  rcases List.mem_map.mp (by
      simpa [singletonHeadLeftRepairDescription,
        MachineDescription.offsetRetargetDescription] using ht) with
    ⟨base, hbase, rfl⟩
  have hsource :=
    ((singletonLeftBoundaryHeadRefreshDescription_subroutineReady
      hgap).left.right.right.right.left base hbase).left
  constructor
  · simp [TransitionDescription.sharedExitRetargetStates]
  · simp [TransitionDescription.sharedExitRetargetStates,
      singletonHeadLeftRepairLimit, singletonHeadLeftRepairDescription,
      MachineDescription.offsetRetargetDescription]
    apply Nat.lt_of_lt_of_le
    · exact Nat.add_lt_add_left hsource singletonHeadLeftRepairOffset
    · exact Nat.le_max_left _ _

theorem singletonHeadRightRepairDescription_sources_in_block
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    forall t : TransitionDescription,
      t ∈ (singletonHeadRightRepairDescription gapCreator).transitions ->
        singletonHeadRightRepairOffset gapCreator ≤ t.source ∧
          t.source < singletonHeadRightRepairLimit gapCreator := by
  intro t ht
  rcases List.mem_map.mp (by
      simpa [singletonHeadRightRepairDescription,
        MachineDescription.offsetRetargetDescription] using ht) with
    ⟨base, hbase, rfl⟩
  have hsource :=
    ((singletonRightBoundaryHeadRefreshDescription_subroutineReady
      hgap).left.right.right.right.left base hbase).left
  constructor
  · simp [TransitionDescription.sharedExitRetargetStates]
  · simp [TransitionDescription.sharedExitRetargetStates,
      singletonHeadRightRepairLimit, singletonHeadRightRepairDescription,
      MachineDescription.offsetRetargetDescription]
    apply Nat.lt_of_lt_of_le
    · exact Nat.add_lt_add_left hsource
        (singletonHeadRightRepairOffset gapCreator)
    · exact Nat.le_max_left _ _

theorem singletonHeadTerminalProbeDescription_sources_in_block
    (gapCreator : MachineDescription) :
    forall t : TransitionDescription,
      t ∈ (singletonHeadTerminalProbeDescription gapCreator).transitions ->
        singletonHeadTerminalProbeOffset gapCreator ≤ t.source ∧
          t.source <
            (singletonHeadTerminalProbeDescription gapCreator).stateCount := by
  intro t ht
  rcases List.mem_map.mp (by
      simpa [singletonHeadTerminalProbeDescription,
        MachineDescription.offsetReadExitRetargetDescription] using ht) with
    ⟨base, hbase, rfl⟩
  have hsource :=
    (singletonHeadTerminalLocalDescription_subroutineReady.left.right.right.right.left
      base hbase).left
  constructor
  · simp [MachineDescription.readExitRetargetStates]
  · simp [MachineDescription.readExitRetargetStates,
      singletonHeadTerminalProbeDescription,
      MachineDescription.offsetReadExitRetargetDescription]
    simpa [singletonHeadTerminalLocalDescription] using
      Nat.add_lt_add_left hsource
        (singletonHeadTerminalProbeOffset gapCreator)

theorem singletonHeadLeftRepairOffset_lt_rightRepairOffset
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    singletonHeadLeftRepairOffset <
      singletonHeadRightRepairOffset gapCreator := by
  have hpos :=
    (singletonLeftBoundaryHeadRefreshDescription_subroutineReady
      hgap).left.left
  simp [singletonHeadRightRepairOffset, singletonHeadLeftRepairLimit,
    singletonHeadLeftRepairDescription,
    MachineDescription.offsetRetargetDescription]
  exact
    Nat.lt_of_lt_of_le
      (Nat.add_lt_add_left hpos singletonHeadLeftRepairOffset)
      (Nat.le_max_left _ _)

theorem singletonHeadLeftRepairOffset_le_rightRepairOffset
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    singletonHeadLeftRepairOffset ≤
      singletonHeadRightRepairOffset gapCreator :=
  Nat.le_of_lt (singletonHeadLeftRepairOffset_lt_rightRepairOffset hgap)

theorem singletonHeadRightRepairOffset_lt_terminalProbeOffset
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    singletonHeadRightRepairOffset gapCreator <
      singletonHeadTerminalProbeOffset gapCreator := by
  have hpos :=
    (singletonRightBoundaryHeadRefreshDescription_subroutineReady
      hgap).left.left
  simp [singletonHeadTerminalProbeOffset, singletonHeadRightRepairLimit,
    singletonHeadRightRepairDescription,
    MachineDescription.offsetRetargetDescription]
  exact
    Nat.lt_of_lt_of_le
      (Nat.add_lt_add_left hpos
        (singletonHeadRightRepairOffset gapCreator))
      (Nat.le_max_left _ _)

theorem singletonHeadRightRepairOffset_le_terminalProbeOffset
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    singletonHeadRightRepairOffset gapCreator ≤
      singletonHeadTerminalProbeOffset gapCreator :=
  Nat.le_of_lt
    (singletonHeadRightRepairOffset_lt_terminalProbeOffset hgap)

theorem singletonHeadLeftRepairLimit_le_terminalProbeOffset
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    singletonHeadLeftRepairLimit gapCreator ≤
      singletonHeadTerminalProbeOffset gapCreator := by
  simpa [singletonHeadTerminalProbeOffset,
    singletonHeadRightRepairOffset] using
    singletonHeadRightRepairOffset_le_terminalProbeOffset hgap

theorem singletonHeadLeftRepairOffset_le_terminalProbeOffset
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    singletonHeadLeftRepairOffset ≤
      singletonHeadTerminalProbeOffset gapCreator :=
  Nat.le_trans
    (singletonHeadLeftRepairOffset_le_rightRepairOffset hgap)
    (singletonHeadRightRepairOffset_le_terminalProbeOffset hgap)

theorem singletonHeadRefreshFinalHalt_lt_stateCount
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    singletonHeadRefreshFinalHalt <
      (singletonHeadRefreshDescription gapCreator).stateCount := by
  have hhalt :=
    (singletonHeadTerminalProbeDescription_subroutineReady
      hgap).left.right.right.left
  simpa [singletonHeadRefreshDescription,
    singletonHeadTerminalProbeDescription,
    singletonHeadTerminalTarget] using hhalt

theorem singletonHeadTerminalProbeOffset_lt_stateCount
    (gapCreator : MachineDescription) :
    singletonHeadTerminalProbeOffset gapCreator <
      (singletonHeadRefreshDescription gapCreator).stateCount := by
  have hpos := singletonHeadTerminalLocalDescription_subroutineReady.left.left
  simpa [singletonHeadRefreshDescription,
    singletonHeadTerminalProbeDescription,
    MachineDescription.offsetReadExitRetargetDescription] using
    Nat.lt_add_of_pos_right
      (n := singletonHeadTerminalProbeOffset gapCreator) hpos

theorem singletonHeadLeftRepairLimit_le_stateCount
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    singletonHeadLeftRepairLimit gapCreator ≤
      (singletonHeadRefreshDescription gapCreator).stateCount :=
  Nat.le_trans
    (singletonHeadLeftRepairLimit_le_terminalProbeOffset hgap)
    (Nat.le_of_lt
      (singletonHeadTerminalProbeOffset_lt_stateCount gapCreator))

theorem singletonHeadRightRepairLimit_le_stateCount
    (gapCreator : MachineDescription) :
    singletonHeadRightRepairLimit gapCreator ≤
      (singletonHeadRefreshDescription gapCreator).stateCount := by
  simpa [singletonHeadTerminalProbeOffset] using
    Nat.le_of_lt
      (singletonHeadTerminalProbeOffset_lt_stateCount gapCreator)

theorem singletonHeadLeftRepairDescription_sources_atLeast
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    TransitionSourcesAtLeast singletonHeadLeftRepairOffset
      (singletonHeadLeftRepairDescription gapCreator).transitions := by
  intro t ht
  exact
    (singletonHeadLeftRepairDescription_sources_in_block hgap t ht).left

theorem singletonHeadRightRepairDescription_sources_atLeast_leftOffset
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    TransitionSourcesAtLeast singletonHeadLeftRepairOffset
      (singletonHeadRightRepairDescription gapCreator).transitions := by
  intro t ht
  have hsource :=
    (singletonHeadRightRepairDescription_sources_in_block hgap t ht).left
  exact Nat.le_trans
    (singletonHeadLeftRepairOffset_le_rightRepairOffset hgap) hsource

theorem singletonHeadTerminalProbeDescription_sources_atLeast_leftOffset
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    TransitionSourcesAtLeast singletonHeadLeftRepairOffset
      (singletonHeadTerminalProbeDescription gapCreator).transitions := by
  intro t ht
  have hsource :=
    (singletonHeadTerminalProbeDescription_sources_in_block
      gapCreator t ht).left
  exact Nat.le_trans
    (singletonHeadLeftRepairOffset_le_terminalProbeOffset hgap) hsource

theorem singletonHeadRightRepairDescription_sources_atLeast_rightOffset
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    TransitionSourcesAtLeast (singletonHeadRightRepairOffset gapCreator)
      (singletonHeadRightRepairDescription gapCreator).transitions := by
  intro t ht
  exact
    (singletonHeadRightRepairDescription_sources_in_block hgap t ht).left

theorem singletonHeadTerminalProbeDescription_sources_atLeast_rightOffset
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    TransitionSourcesAtLeast (singletonHeadRightRepairOffset gapCreator)
      (singletonHeadTerminalProbeDescription gapCreator).transitions := by
  intro t ht
  have hsource :=
    (singletonHeadTerminalProbeDescription_sources_in_block
      gapCreator t ht).left
  exact Nat.le_trans
    (singletonHeadRightRepairOffset_le_terminalProbeOffset hgap) hsource

theorem singletonHeadTerminalProbeDescription_sources_atLeast_terminalOffset
    (gapCreator : MachineDescription) :
    TransitionSourcesAtLeast (singletonHeadTerminalProbeOffset gapCreator)
      (singletonHeadTerminalProbeDescription gapCreator).transitions := by
  intro t ht
  exact
    (singletonHeadTerminalProbeDescription_sources_in_block
      gapCreator t ht).left

theorem singletonHeadLeftRepairDescription_sources_below_rightOffset
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    TransitionSourcesBelow (singletonHeadRightRepairOffset gapCreator)
      (singletonHeadLeftRepairDescription gapCreator).transitions := by
  intro t ht
  simpa [singletonHeadRightRepairOffset] using
    (singletonHeadLeftRepairDescription_sources_in_block hgap t ht).right

theorem singletonHeadRightRepairDescription_sources_below_terminalOffset
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    TransitionSourcesBelow (singletonHeadTerminalProbeOffset gapCreator)
      (singletonHeadRightRepairDescription gapCreator).transitions := by
  intro t ht
  simpa [singletonHeadTerminalProbeOffset] using
    (singletonHeadRightRepairDescription_sources_in_block hgap t ht).right

theorem singletonHeadRefreshDescription_transitions_wellFormed
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    forall t : TransitionDescription,
      t ∈ (singletonHeadRefreshDescription gapCreator).transitions ->
        TransitionDescription.WellFormed
          (singletonHeadRefreshDescription gapCreator).stateCount t := by
  intro t ht
  simp [singletonHeadRefreshDescription] at ht
  rcases ht with hopen | hleft | hright | hterminal
  · simp [singletonHeadRefreshOpeningDescription,
      singletonOpeningProbeDescription] at hopen
    rcases hopen with rfl | rfl | rfl
    · constructor
      · exact Nat.lt_trans
          (by
            simpa using
              (by decide : 0 < singletonHeadRefreshFinalHalt))
          (singletonHeadRefreshFinalHalt_lt_stateCount hgap)
      · exact Nat.lt_trans
          (by
            simpa using
              (by decide : 1 < singletonHeadRefreshFinalHalt))
          (singletonHeadRefreshFinalHalt_lt_stateCount hgap)
    · constructor
      · exact Nat.lt_trans
          (by
            simpa using
              (by decide : 1 < singletonHeadRefreshFinalHalt))
          (singletonHeadRefreshFinalHalt_lt_stateCount hgap)
      · exact
          (singletonHeadTerminalProbeDescription_subroutineReady
            hgap).left.right.left
    · constructor
      · exact Nat.lt_trans
          (by
            simpa using
              (by decide : 1 < singletonHeadRefreshFinalHalt))
          (singletonHeadRefreshFinalHalt_lt_stateCount hgap)
      · exact
          Nat.lt_of_lt_of_le
            (singletonHeadLeftRepairDescription_subroutineReady
              hgap).left.right.left
            (singletonHeadLeftRepairLimit_le_stateCount hgap)
  · have hformed :=
      (singletonHeadLeftRepairDescription_subroutineReady
        hgap).left.right.right.right.left t hleft
    exact ⟨
      Nat.lt_of_lt_of_le hformed.left
        (singletonHeadLeftRepairLimit_le_stateCount hgap),
      Nat.lt_of_lt_of_le hformed.right
        (singletonHeadLeftRepairLimit_le_stateCount hgap)⟩
  · have hformed :=
      (singletonHeadRightRepairDescription_subroutineReady
        hgap).left.right.right.right.left t hright
    exact ⟨
      Nat.lt_of_lt_of_le hformed.left
        (singletonHeadRightRepairLimit_le_stateCount gapCreator),
      Nat.lt_of_lt_of_le hformed.right
        (singletonHeadRightRepairLimit_le_stateCount gapCreator)⟩
  · exact
      (singletonHeadTerminalProbeDescription_subroutineReady
        hgap).left.right.right.right.left t hterminal

theorem singletonHeadRefreshDescription_transitionListDeterministic
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    TransitionListDeterministic
      (singletonHeadRefreshDescription gapCreator).transitions := by
  unfold singletonHeadRefreshDescription
  apply transitionListDeterministic_append_of_sourceDisjoint
  · exact
      (singletonHeadRefreshOpeningDescription_subroutineReady
        gapCreator).left.right.right.right.right
  · apply transitionListDeterministic_append_of_sourceDisjoint
    · exact
        (singletonHeadLeftRepairDescription_subroutineReady
          hgap).left.right.right.right.right
    · apply transitionListDeterministic_append_of_sourceDisjoint
      · exact
          (singletonHeadRightRepairDescription_subroutineReady
            hgap).left.right.right.right.right
      · exact
          (singletonHeadTerminalProbeDescription_subroutineReady
            hgap).left.right.right.right.right
      · apply transitionSourceDisjoint_of_below_atLeast
        · exact
            singletonHeadRightRepairDescription_sources_below_terminalOffset
              hgap
        · exact
            singletonHeadTerminalProbeDescription_sources_atLeast_terminalOffset
              gapCreator
    · apply transitionSourceDisjoint_of_below_atLeast
      · exact
          singletonHeadLeftRepairDescription_sources_below_rightOffset
            hgap
      · apply transitionSourcesAtLeast_append
        · exact
            singletonHeadRightRepairDescription_sources_atLeast_rightOffset
              hgap
        · exact
            singletonHeadTerminalProbeDescription_sources_atLeast_rightOffset
              hgap
  · apply transitionSourceDisjoint_of_below_atLeast
    · exact
        singletonHeadRefreshOpeningDescription_sources_below_leftRepairOffset
          gapCreator
    · apply transitionSourcesAtLeast_append
      · exact singletonHeadLeftRepairDescription_sources_atLeast hgap
      · apply transitionSourcesAtLeast_append
        · exact
            singletonHeadRightRepairDescription_sources_atLeast_leftOffset
              hgap
        · exact
            singletonHeadTerminalProbeDescription_sources_atLeast_leftOffset
              hgap

theorem singletonHeadRefreshDescription_deterministic
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    (singletonHeadRefreshDescription gapCreator).Deterministic :=
  singletonHeadRefreshDescription_transitionListDeterministic hgap

theorem singletonHeadRefreshDescription_wellFormed
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    (singletonHeadRefreshDescription gapCreator).WellFormed := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact
      Nat.lt_of_lt_of_le
        (by decide : 0 < singletonHeadRefreshFinalHalt)
        (Nat.le_of_lt
          (singletonHeadRefreshFinalHalt_lt_stateCount hgap))
  · exact
      Nat.lt_of_lt_of_le
        (by decide : 0 < singletonHeadRefreshFinalHalt)
        (Nat.le_of_lt
          (singletonHeadRefreshFinalHalt_lt_stateCount hgap))
  · exact singletonHeadRefreshFinalHalt_lt_stateCount hgap
  · exact singletonHeadRefreshDescription_transitions_wellFormed hgap
  · exact singletonHeadRefreshDescription_deterministic hgap

theorem singletonHeadRefreshDescription_haltTransitionFree
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    (singletonHeadRefreshDescription gapCreator).HaltTransitionFree := by
  intro t ht
  simp [singletonHeadRefreshDescription] at ht
  rcases ht with hopening | hleft | hright | hterminal
  · simp [singletonHeadRefreshOpeningDescription,
      singletonOpeningProbeDescription] at hopening
    rcases hopening with rfl | rfl | rfl
    · simpa [singletonHeadRefreshDescription] using
        (by decide : 0 ≠ singletonHeadRefreshFinalHalt)
    · simpa [singletonHeadRefreshDescription] using
        (by decide : 1 ≠ singletonHeadRefreshFinalHalt)
    · simpa [singletonHeadRefreshDescription] using
        (by decide : 1 ≠ singletonHeadRefreshFinalHalt)
  · exact
      (singletonHeadLeftRepairDescription_subroutineReady
        hgap).right t hleft
  · exact
      (singletonHeadRightRepairDescription_subroutineReady
        hgap).right t hright
  · exact
      (singletonHeadTerminalProbeDescription_subroutineReady
        hgap).right t hterminal

theorem singletonHeadRefreshDescription_subroutineReady
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    (singletonHeadRefreshDescription gapCreator).SubroutineReady :=
  ⟨singletonHeadRefreshDescription_wellFormed hgap,
    singletonHeadRefreshDescription_haltTransitionFree hgap⟩

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

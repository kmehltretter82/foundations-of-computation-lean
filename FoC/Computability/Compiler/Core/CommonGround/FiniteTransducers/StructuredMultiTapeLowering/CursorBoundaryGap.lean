import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.CursorBasic

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

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC

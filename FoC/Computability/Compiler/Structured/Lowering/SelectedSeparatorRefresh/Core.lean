import FoC.Computability.Compiler.Structured.Lowering.StructuredRefresh
import FoC.Computability.Compiler.Structured.Lowering.FiniteMachineTactics
import FoC.Computability.Compiler.Structured.Lowering.SelectedSeparatorTerminalPairProbe
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.OneGapCompactor

set_option doc.verso true

/-!
# Selected-separator refresh support

This module starts the concrete local refresh layer for interior structured
segments.  The first reusable ingredient is a prefix-preserving version of the
gap-aware right-boundary repair: when the selected segment is not at the global
block start, the encoded prefix to the left of the selected separator must be
preserved literally.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

private theorem rightBoundaryGuardSlackRefreshDescription_run_enter_withPrefix
    (pref : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) :
    rightBoundaryGuardSlackRefreshDescription.runConfig 1
        { state := rightBoundaryGuardSlackRefreshDescription.start
          tape :=
            tapeAtCells pref
              (none ::
                List.append (bits.map some)
                  (none :: none :: none :: padding)) } =
      { state := 1
        tape :=
          tapeAtCells (none :: pref)
            (List.append (bits.map some)
              (none :: none :: none :: padding)) } := by
  cases bits with
  | nil =>
      cases padding <;>
        machine_step [rightBoundaryGuardSlackRefreshDescription]
  | cons bit rest =>
      cases bit <;> cases rest <;> cases padding <;>
        machine_step [rightBoundaryGuardSlackRefreshDescription]

private theorem rightBoundaryGuardSlackRefreshDescription_run_scan_right_withPrefix
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
          machine_step [rightBoundaryGuardSlackRefreshDescription]
      simp only [List.map_cons] at hstep ⊢
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: left)

private theorem rightBoundaryGuardSlackRefreshDescription_run_append_blank_cell_withPrefix
    (left padding : List (Option Bool)) :
    rightBoundaryGuardSlackRefreshDescription.runConfig 3
        { state := 1
          tape := tapeAtCells left (none :: none :: none :: padding) } =
      { state := 4
        tape :=
          tapeAtCells (some false :: left)
            (some false :: none :: padding) } := by
  cases left <;> cases padding <;>
    machine_step [rightBoundaryGuardSlackRefreshDescription]

private theorem rightBoundaryGuardSlackRefreshDescription_run_scan_left_forGap_withPrefix
    (pref : List (Option Bool)) (leftStack : Word Bool)
    (current : Bool) (right : List (Option Bool)) :
    rightBoundaryGuardSlackRefreshDescription.runConfig
        (leftStack.length + 1)
        { state := 4
          tape :=
            tapeAtCells
              (List.append (leftStack.map some) (none :: pref))
              (some current :: right) } =
      { state := 4
        tape :=
          tapeAtCells pref
            (none ::
              List.append
                ((List.append leftStack.reverse [current]).map some)
                right) } := by
  induction leftStack generalizing current right with
  | nil =>
      cases current <;> cases right <;>
        machine_step [rightBoundaryGuardSlackRefreshDescription]
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
                    (List.append ((next :: rest).map some)
                      (none :: pref))
                    (some current :: right) } =
            { state := 4
              tape :=
                tapeAtCells
                  (List.append (rest.map some) (none :: pref))
                  (some next :: some current :: right) } := by
        cases current <;> cases next <;> cases right <;>
          machine_step [rightBoundaryGuardSlackRefreshDescription]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih next (some current :: right)

private theorem rightBoundaryGuardSlackRefreshDescription_run_finish_withPrefix
    (pref : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) :
    rightBoundaryGuardSlackRefreshDescription.runConfig 2
        { state := 4
          tape :=
            tapeAtCells pref
              (none ::
                List.append
                  ((List.append bits [false, false]).map some)
                  (none :: padding)) } =
      { state := rightBoundaryGuardSlackRefreshDescription.halt
        tape :=
          tapeAtCells pref
            (none ::
              List.append
                ((List.append bits [false, false]).map some)
                (none :: padding)) } := by
  cases bits with
  | nil =>
      cases padding <;>
        machine_step [rightBoundaryGuardSlackRefreshDescription]
  | cons bit rest =>
      cases bit <;> cases rest <;> cases padding <;>
        machine_step [rightBoundaryGuardSlackRefreshDescription]

theorem rightBoundaryGuardSlackRefreshDescription_run_to_target_withGapPrefix
    (pref : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) :
    rightBoundaryGuardSlackRefreshDescription.runConfig
        (1 + (bits.length +
          (3 + ((false :: bits.reverse).length + 1 + 2))))
        { state := rightBoundaryGuardSlackRefreshDescription.start
          tape :=
            tapeAtCells pref
              (none ::
                List.append (bits.map some)
                  (none :: none :: none :: padding)) } =
      { state := rightBoundaryGuardSlackRefreshDescription.halt
        tape :=
          tapeAtCells pref
            (none ::
              List.append
                ((List.append bits [false, false]).map some)
                (none :: padding)) } := by
  rw [MachineDescription.runConfig_add]
  rw [rightBoundaryGuardSlackRefreshDescription_run_enter_withPrefix]
  rw [MachineDescription.runConfig_add]
  rw [rightBoundaryGuardSlackRefreshDescription_run_scan_right_withPrefix]
  rw [MachineDescription.runConfig_add]
  rw [rightBoundaryGuardSlackRefreshDescription_run_append_blank_cell_withPrefix]
  rw [MachineDescription.runConfig_add]
  change
    rightBoundaryGuardSlackRefreshDescription.runConfig 2
        (rightBoundaryGuardSlackRefreshDescription.runConfig
          ((false :: bits.reverse).length + 1)
          { state := 4
            tape :=
              tapeAtCells
                (List.append ((false :: bits.reverse).map some)
                  (none :: pref))
                (some false :: none :: padding) }) =
      { state := rightBoundaryGuardSlackRefreshDescription.halt
        tape :=
          tapeAtCells pref
            (none ::
              List.append
                ((List.append bits [false, false]).map some)
                (none :: padding)) }
  rw [rightBoundaryGuardSlackRefreshDescription_run_scan_left_forGap_withPrefix]
  simpa [List.reverse_cons, List.map_append, List.append_assoc] using
    rightBoundaryGuardSlackRefreshDescription_run_finish_withPrefix
      pref bits padding

theorem rightBoundaryGuardSlackRefreshDescription_haltsFromPayloadWithGapPrefix
    (pref : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) :
    rightBoundaryGuardSlackRefreshDescription.HaltsFromTape
      (tapeAtCells pref
        (none ::
          List.append (bits.map some)
            (none :: none :: none :: padding)))
      (tapeAtCells pref
        (none ::
          List.append ((List.append bits [false, false]).map some)
            (none :: padding))) := by
  refine
    ⟨1 + (bits.length +
      (3 + ((false :: bits.reverse).length + 1 + 2))), ?_⟩
  constructor <;>
    rw [rightBoundaryGuardSlackRefreshDescription_run_to_target_withGapPrefix]

theorem rightBoundaryGuardSlackRefreshDescription_haltsFrom_rightBoundarySlackWithGapPrefix
    (pref : List (Option Bool)) (left : List (Option Bool))
    (head : Option Bool) (padding : List (Option Bool)) :
    rightBoundaryGuardSlackRefreshDescription.HaltsFromTape
      (tapeAtCells pref
        (none ::
          List.append
            ((logicalTapeBits
              ({ left := left, head := head, right := [] } :
                Tape Bool)).map some)
            (none :: none :: none :: padding)))
      (tapeAtCells pref
        (none ::
          List.append
            ((logicalTapeBits
              ({ left := left, head := head, right := [none] } :
                Tape Bool)).map some)
            (none :: padding))) := by
  simpa [logicalTapeBits, logicalCellListBits,
    logicalCellListBits_append, logicalCellBits, List.map_append,
    List.append_assoc] using
    rightBoundaryGuardSlackRefreshDescription_haltsFromPayloadWithGapPrefix
      pref
      (logicalTapeBits
        ({ left := left, head := head, right := [] } : Tape Bool))
      padding

private def selectedLeftBoundaryShiftPairState
    (first second : Bool) : Nat :=
  match first, second with
  | false, false => 4
  | false, true => 5
  | true, false => 6
  | true, true => 7

private theorem leftBoundaryGuardSlackShiftDescription_run_initial_withGapPrefix
    (base : List (Option Bool)) (first second : Bool)
    (rest : Word Bool) (padding : List (Option Bool)) :
    leftBoundaryGuardSlackShiftDescription.runConfig 3
        { state := leftBoundaryGuardSlackShiftDescription.start
          tape :=
            tapeAtCells base
              (none ::
                List.append ((first :: second :: rest).map some)
                  (none :: none :: none :: padding)) } =
      { state := selectedLeftBoundaryShiftPairState first second
        tape :=
          tapeAtCells
            (List.append (([false, false] : Word Bool).reverse.map some)
              (none :: base))
            (List.append (rest.map some)
              (none :: none :: none :: padding)) } := by
  cases first <;> cases second <;> cases rest <;> cases padding <;>
    machine_step [leftBoundaryGuardSlackShiftDescription,
      selectedLeftBoundaryShiftPairState]

private theorem leftBoundaryGuardSlackShiftDescription_run_loop_bit_withGapPrefix
    (base : List (Option Bool)) (pref rest : Word Bool)
    (first second current : Bool) (padding : List (Option Bool)) :
    leftBoundaryGuardSlackShiftDescription.runConfig 1
        { state := selectedLeftBoundaryShiftPairState first second
          tape :=
            tapeAtCells
              (List.append (pref.reverse.map some) (none :: base))
              (List.append ((current :: rest).map some)
                (none :: none :: none :: padding)) } =
      { state := selectedLeftBoundaryShiftPairState second current
        tape :=
          tapeAtCells
            (List.append ((List.append pref [first]).reverse.map some)
              (none :: base))
            (List.append (rest.map some)
              (none :: none :: none :: padding)) } := by
  cases first <;> cases second <;> cases current <;>
    cases rest <;> cases padding <;>
    machine_step [leftBoundaryGuardSlackShiftDescription,
      selectedLeftBoundaryShiftPairState]

private theorem leftBoundaryGuardSlackShiftDescription_run_loop_finish_withGapPrefix
    (base : List (Option Bool)) (pref : Word Bool)
    (first second : Bool) (padding : List (Option Bool)) :
    leftBoundaryGuardSlackShiftDescription.runConfig 2
        { state := selectedLeftBoundaryShiftPairState first second
          tape :=
            tapeAtCells
              (List.append (pref.reverse.map some) (none :: base))
              (none :: none :: none :: padding) } =
      { state := leftBoundaryGuardSlackShiftDescription.halt
        tape :=
          tapeAtCells
            (List.append
              ((List.append pref [first, second]).reverse.map some)
              (none :: base))
            (none :: padding) } := by
  cases first <;> cases second <;> cases padding <;>
    machine_step [leftBoundaryGuardSlackShiftDescription,
      selectedLeftBoundaryShiftPairState]

private theorem leftBoundaryGuardSlackShiftDescription_run_loop_withGapPrefix
    (base : List (Option Bool)) (rest pref : Word Bool)
    (first second : Bool) (padding : List (Option Bool)) :
    leftBoundaryGuardSlackShiftDescription.runConfig (rest.length + 2)
        { state := selectedLeftBoundaryShiftPairState first second
          tape :=
            tapeAtCells
              (List.append (pref.reverse.map some) (none :: base))
              (List.append (rest.map some)
                (none :: none :: none :: padding)) } =
      { state := leftBoundaryGuardSlackShiftDescription.halt
        tape :=
          tapeAtCells
            (List.append
              ((List.append pref (first :: second :: rest)).reverse.map some)
              (none :: base))
            (none :: padding) } := by
  induction rest generalizing pref first second with
  | nil =>
      simpa [List.append_assoc] using
        leftBoundaryGuardSlackShiftDescription_run_loop_finish_withGapPrefix
          base pref first second padding
  | cons current rest ih =>
      rw [show (current :: rest).length + 2 =
          1 + (rest.length + 2) by
        simp
        lia]
      rw [MachineDescription.runConfig_add]
      rw [leftBoundaryGuardSlackShiftDescription_run_loop_bit_withGapPrefix]
      simpa [List.append_assoc] using
        ih (List.append pref [first]) second current

theorem leftBoundaryGuardSlackShiftDescription_run_to_rightEdge_withGapPrefix
    (base : List (Option Bool)) (first second : Bool)
    (rest : Word Bool) (padding : List (Option Bool)) :
    leftBoundaryGuardSlackShiftDescription.runConfig
        (3 + (rest.length + 2))
        { state := leftBoundaryGuardSlackShiftDescription.start
          tape :=
            tapeAtCells base
              (none ::
                List.append ((first :: second :: rest).map some)
                  (none :: none :: none :: padding)) } =
      { state := leftBoundaryGuardSlackShiftDescription.halt
        tape :=
          tapeAtCells
            (List.append
              ((List.append ([false, false] : Word Bool)
                (first :: second :: rest)).reverse.map some)
              (none :: base))
            (none :: padding) } := by
  rw [MachineDescription.runConfig_add]
  rw [leftBoundaryGuardSlackShiftDescription_run_initial_withGapPrefix]
  simpa [List.append_assoc] using
    leftBoundaryGuardSlackShiftDescription_run_loop_withGapPrefix
      base rest ([false, false] : Word Bool) first second padding

theorem leftBoundaryGuardSlackShiftDescription_haltsFromPayloadWithGapPrefix
    (base : List (Option Bool)) (first second : Bool)
    (rest : Word Bool) (padding : List (Option Bool)) :
    leftBoundaryGuardSlackShiftDescription.HaltsFromTape
      (tapeAtCells base
        (none ::
          List.append ((first :: second :: rest).map some)
            (none :: none :: none :: padding)))
      (tapeAtCells
        (List.append
          ((List.append ([false, false] : Word Bool)
            (first :: second :: rest)).reverse.map some)
          (none :: base))
        (none :: padding)) := by
  refine ⟨3 + (rest.length + 2), ?_⟩
  constructor <;>
    rw [leftBoundaryGuardSlackShiftDescription_run_to_rightEdge_withGapPrefix]

theorem leftBoundaryGuardSlackRefreshDescription_haltsFromPayloadWithGapPrefix
    (base : List (Option Bool)) (first second : Bool)
    (rest : Word Bool) (padding : List (Option Bool)) :
    leftBoundaryGuardSlackRefreshDescription.HaltsFromTapeEquiv
      (tapeAtCells base
        (none ::
          List.append ((first :: second :: rest).map some)
            (none :: none :: none :: padding)))
      (tapeAtCells base
        (none ::
          List.append
            ((List.append ([false, false] : Word Bool)
              (first :: second :: rest)).map some)
            (none :: padding))) := by
  let shifted : Word Bool :=
    List.append ([false, false] : Word Bool) (first :: second :: rest)
  let Tmid : Tape Bool :=
    tapeAtCells
      (List.append (shifted.reverse.map some) (none :: base))
      (none :: padding)
  let Trewound : Tape Bool :=
    rightEdgeRewindTargetTapeWithBase base shifted padding
  have hshift :
      leftBoundaryGuardSlackShiftDescription.HaltsFromTape
        (tapeAtCells base
          (none ::
            List.append ((first :: second :: rest).map some)
              (none :: none :: none :: padding)))
        Tmid := by
    simpa [Tmid, shifted] using
      leftBoundaryGuardSlackShiftDescription_haltsFromPayloadWithGapPrefix
        base first second rest padding
  have hrewind :
      rightEdgeRewindDescription.HaltsFromTapeEquiv Tmid Trewound := by
    simpa [Tmid, Trewound, rightEdgeRewindSourceTapeWithBase] using
      MachineDescription.HaltsFromTape.toEquiv
        (rightEdgeRewindDescription_haltsFromTapeWithBase
          base shifted padding)
  have hshiftThenRewind :
      (canonicalPrimitiveSeqDescription
        leftBoundaryGuardSlackShiftDescription
        rightEdgeRewindDescription).HaltsFromTapeEquiv
          (tapeAtCells base
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
        (tapeAtCells base
          (none ::
            List.append (shifted.map some) (none :: padding))) := by
    simpa [Trewound, rightEdgeRewindTargetTapeWithBase, tapeAtCells,
      Tape.move, Tape.moveLeft] using!
      leftMoveOnceDescription_haltsFromTape Trewound
  simpa [leftBoundaryGuardSlackRefreshDescription, shifted] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      (canonicalPrimitiveSeqDescription_subroutineReady
        leftBoundaryGuardSlackShiftDescription_subroutineReady
        rightEdgeRewindDescription_subroutineReady)
      leftMoveOnceDescription_subroutineReady
      hshiftThenRewind
      (MachineDescription.HaltsFromTape.toEquiv hleft)

theorem leftBoundaryGuardSlackRefreshDescription_haltsFrom_leftBoundarySlackWithGapPrefix
    (base : List (Option Bool)) (head : Option Bool)
    (right : List (Option Bool)) (padding : List (Option Bool)) :
    leftBoundaryGuardSlackRefreshDescription.HaltsFromTapeEquiv
      (tapeAtCells base
        (none ::
          List.append
            ((logicalTapeBits
              ({ left := [], head := head, right := right } :
                Tape Bool)).map some)
            (none :: none :: none :: padding)))
      (tapeAtCells base
        (none ::
          List.append
            ((logicalTapeBits
              ({ left := [none], head := head, right := right } :
                Tape Bool)).map some)
            (none :: padding))) := by
  simpa [logicalTapeBits, logicalCellListBits,
    logicalCellListBits_append, logicalCellBits, List.map_append,
    List.append_assoc] using
    leftBoundaryGuardSlackRefreshDescription_haltsFromPayloadWithGapPrefix
      base true true
      (List.append (logicalCellBits head) (logicalCellListBits right))
      padding

/--
Physical selected-separator shape after a local gap creator has inserted two
blank cells between the selected segment and the following structured suffix.
-/
def tapeAtSelectedHeadGap
    (encodedPrefix : List (Option Bool)) (head : Tape Bool)
    (rest : List (Tape Bool)) : Tape Bool :=
  tapeAtEncodedSplit encodedPrefix
    (List.append tapeSeparatorCells
      (List.append (logicalTapeCode head)
        (none :: none :: encodedStructuredTapeCells rest)))

theorem rightBoundaryGuardSlackRefreshDescription_haltsFrom_selectedHeadGap
    (encodedPrefix : List (Option Bool))
    (left : List (Option Bool)) (head : Option Bool)
    (rest : List (Tape Bool)) :
    rightBoundaryGuardSlackRefreshDescription.HaltsFromTapeEquiv
      (tapeAtSelectedHeadGap encodedPrefix
        ({ left := left, head := head, right := [] } : Tape Bool) rest)
      (tapeAtEncodedSplit encodedPrefix
        (encodedStructuredTapeCells
          (({ left := left, head := head, right := [none] } :
            Tape Bool) :: rest))) := by
  rcases encodedStructuredTapeCells_startsWith_separator rest with
    ⟨padding, hpadding⟩
  have hrun :
      rightBoundaryGuardSlackRefreshDescription.HaltsFromTape
        (tapeAtSelectedHeadGap encodedPrefix
          ({ left := left, head := head, right := [] } : Tape Bool) rest)
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells
            (({ left := left, head := head, right := [none] } :
              Tape Bool) :: rest))) := by
    simpa [tapeAtSelectedHeadGap, tapeAtEncodedSplit,
      encodedStructuredTapeCells, logicalTapeCode_eq_map_some,
      hpadding, tapeSeparatorCells, List.append_assoc] using
      rightBoundaryGuardSlackRefreshDescription_haltsFrom_rightBoundarySlackWithGapPrefix
        encodedPrefix.reverse left head padding
  exact MachineDescription.HaltsFromTape.toEquiv hrun

theorem leftBoundaryGuardSlackRefreshDescription_haltsFrom_selectedHeadGap
    (encodedPrefix : List (Option Bool)) (head : Option Bool)
    (right : List (Option Bool)) (rest : List (Tape Bool)) :
    leftBoundaryGuardSlackRefreshDescription.HaltsFromTapeEquiv
      (tapeAtSelectedHeadGap encodedPrefix
        ({ left := [], head := head, right := right } : Tape Bool) rest)
      (tapeAtEncodedSplit encodedPrefix
        (encodedStructuredTapeCells
          (({ left := [none], head := head, right := right } :
            Tape Bool) :: rest))) := by
  rcases encodedStructuredTapeCells_startsWith_separator rest with
    ⟨padding, hpadding⟩
  simpa [tapeAtSelectedHeadGap, tapeAtEncodedSplit,
    encodedStructuredTapeCells, logicalTapeCode_eq_map_some,
    hpadding, tapeSeparatorCells, List.append_assoc] using
    leftBoundaryGuardSlackRefreshDescription_haltsFrom_leftBoundarySlackWithGapPrefix
      encodedPrefix.reverse head right padding

def tapeAtSelectedHeadPayload
    (encodedPrefix : List (Option Bool)) (bits : Word Bool)
    (rest : List (Tape Bool)) : Tape Bool :=
  tapeAtEncodedSplit encodedPrefix
    (List.append tapeSeparatorCells
      (List.append (bits.map some) (encodedStructuredTapeCells rest)))

def tapeAtSelectedHeadPayloadGap
    (encodedPrefix : List (Option Bool)) (bits : Word Bool)
    (rest : List (Tape Bool)) : Tape Bool :=
  tapeAtEncodedSplit encodedPrefix
    (List.append tapeSeparatorCells
      (List.append (bits.map some)
        (none :: none :: encodedStructuredTapeCells rest)))

theorem tapeAtSelectedHeadPayload_logicalTapeBits
    (encodedPrefix : List (Option Bool)) (head : Tape Bool)
    (rest : List (Tape Bool)) :
    tapeAtSelectedHeadPayload encodedPrefix (logicalTapeBits head) rest =
      tapeAtEncodedSplit encodedPrefix
        (encodedStructuredTapeCells (head :: rest)) := by
  simp [tapeAtSelectedHeadPayload, tapeAtEncodedSplit,
    encodedStructuredTapeCells, logicalTapeCode_eq_map_some,
    tapeSeparatorCells]

theorem tapeAtSelectedHeadPayloadGap_logicalTapeBits
    (encodedPrefix : List (Option Bool)) (head : Tape Bool)
    (rest : List (Tape Bool)) :
    tapeAtSelectedHeadPayloadGap encodedPrefix (logicalTapeBits head) rest =
      tapeAtSelectedHeadGap encodedPrefix head rest := by
  simp [tapeAtSelectedHeadPayloadGap, tapeAtSelectedHeadGap,
    tapeAtEncodedSplit, logicalTapeCode_eq_map_some, tapeSeparatorCells]

theorem headSuffixGapShiftDescription_run_opening_withPrefix
    (base : List (Option Bool)) (bits : Word Bool)
    (suffixTail : List (Option Bool)) :
    headSuffixGapShiftDescription.runConfig 1
        { state := headSuffixGapShiftDescription.start
          tape :=
            tapeAtCells base
              (none :: List.append (bits.map some)
                (none :: suffixTail)) } =
      { state := 1
        tape :=
          tapeAtCells (none :: base)
            (List.append (bits.map some) (none :: suffixTail)) } := by
  cases bits <;> cases suffixTail <;>
    machine_step [headSuffixGapShiftDescription]

theorem headSuffixGapShiftDescription_run_to_boundary_withPrefix
    (base : List (Option Bool)) (bits : Word Bool)
    (suffixTail : List (Option Bool)) :
    headSuffixGapShiftDescription.runConfig (bits.length + 2)
        { state := headSuffixGapShiftDescription.start
          tape :=
            tapeAtCells base
              (none :: List.append (bits.map some)
                (none :: suffixTail)) } =
      { state := 2
        tape :=
          tapeAtCells
            (none ::
              List.append (bits.reverse.map some) (none :: base))
            suffixTail } := by
  rw [show bits.length + 2 = 1 + (bits.length + 1) by lia]
  rw [MachineDescription.runConfig_add]
  rw [headSuffixGapShiftDescription_run_opening_withPrefix]
  rw [show bits.length + 1 = bits.length + 1 by rfl]
  rw [MachineDescription.runConfig_add]
  have hscan :
      headSuffixGapShiftDescription.runConfig bits.length
          { state := 1
            tape :=
              tapeAtCells (none :: base)
                (List.append (bits.map some) (none :: suffixTail)) } =
        { state := 1
          tape :=
            tapeAtCells
              (List.append (bits.reverse.map some) (none :: base))
              (none :: suffixTail) } := by
    simpa using
      headSuffixGapShiftDescription_run_payloadScan bits [] (none :: base)
        suffixTail
  rw [hscan]
  cases suffixTail <;>
    machine_step [headSuffixGapShiftDescription]

theorem headSuffixGapShiftDescription_run_to_selectedTailBoundary
    (encodedPrefix : List (Option Bool)) (bits : Word Bool)
    (rest : List (Tape Bool)) :
    headSuffixGapShiftDescription.runConfig (bits.length + 2)
        { state := headSuffixGapShiftDescription.start
          tape := tapeAtSelectedHeadPayload encodedPrefix bits rest } =
      { state := 2
        tape :=
          tapeAtCells
            (none ::
              List.append (bits.reverse.map some)
                (none :: encodedPrefix.reverse))
            (encodedStructuredTapeCellsTail rest) } := by
  rw [tapeAtSelectedHeadPayload, tapeAtEncodedSplit,
    encodedStructuredTapeCells_eq_cons_tail rest]
  simpa [tapeSeparatorCells, List.append_assoc] using
    headSuffixGapShiftDescription_run_to_boundary_withPrefix
      encodedPrefix.reverse bits (encodedStructuredTapeCellsTail rest)

theorem headSuffixGapShiftDescription_haltsFrom_selectedPayload_emptyRest
    (encodedPrefix : List (Option Bool)) (bits : Word Bool) :
    headSuffixGapShiftDescription.HaltsFromTape
      (tapeAtSelectedHeadPayload encodedPrefix bits [])
      (Tape.move Direction.left
        (tapeAtCells
          (none :: none ::
            List.append (bits.reverse.map some)
              (none :: encodedPrefix.reverse))
          [])) := by
  refine ⟨bits.length + 4, ?_⟩
  constructor
  · rw [show bits.length + 4 = (bits.length + 2) + 2 by lia]
    rw [MachineDescription.runConfig_add]
    rw [headSuffixGapShiftDescription_run_to_selectedTailBoundary]
    exact
      congrArg (fun cfg => cfg.state)
        (headSuffixGapShiftDescription_run_boundary_encodedTail_nil
          (none ::
            List.append (bits.reverse.map some)
              (none :: encodedPrefix.reverse)))
  · rw [show bits.length + 4 = (bits.length + 2) + 2 by lia]
    rw [MachineDescription.runConfig_add]
    rw [headSuffixGapShiftDescription_run_to_selectedTailBoundary]
    exact
      congrArg (fun cfg => cfg.tape)
        (headSuffixGapShiftDescription_run_boundary_encodedTail_nil
          (none ::
            List.append (bits.reverse.map some)
              (none :: encodedPrefix.reverse)))

theorem headSuffixGapShiftDescription_haltsFrom_selectedPayload_cons
    (encodedPrefix : List (Option Bool)) (bits : Word Bool)
    (T : Tape Bool) (rest : List (Tape Bool)) :
    exists current : Option Bool, exists cells : List (Option Bool),
      encodedStructuredTapeCellsTail (T :: rest) = current :: cells ∧
        (headSuffixGapShiftLoopPair none current cells).1 ≠ none ∧
        (headSuffixGapShiftLoopPair none current cells).2 = none ∧
        headSuffixGapShiftDescription.HaltsFromTape
          (tapeAtSelectedHeadPayload encodedPrefix bits (T :: rest))
          (Tape.move Direction.left
            (tapeAtCells
              ((headSuffixGapShiftLoopPair none current cells).1 ::
                List.append
                  (headSuffixGapShiftLoopWrittenRev none current cells)
                  (none :: none ::
                    List.append (bits.reverse.map some)
                      (none :: encodedPrefix.reverse)))
              [])) := by
  rcases headSuffixGapShiftLoopReady_encodedStructuredTapeCellsTail_start
      T rest with
    ⟨current, cells, htail, hactive, hfirst, hsecond⟩
  refine ⟨current, cells, htail, hfirst, hsecond, ?_⟩
  have hrunBoundary :=
    headSuffixGapShiftDescription_run_boundaryLoop_then_implicitStep_halt_nil
      current cells
      (none ::
        List.append (bits.reverse.map some)
          (none :: encodedPrefix.reverse))
      hactive hfirst hsecond
  have hrun :
      headSuffixGapShiftDescription.runConfig
          ((bits.length + 2) + (cells.length + 3))
          { state := headSuffixGapShiftDescription.start
            tape := tapeAtSelectedHeadPayload encodedPrefix bits (T :: rest) } =
        { state := headSuffixGapShiftHalt
          tape :=
            Tape.move Direction.left
              (tapeAtCells
                ((headSuffixGapShiftLoopPair none current cells).1 ::
                  List.append
                    (headSuffixGapShiftLoopWrittenRev none current cells)
                    (none :: none ::
                      List.append (bits.reverse.map some)
                        (none :: encodedPrefix.reverse)))
                []) } := by
    rw [MachineDescription.runConfig_add]
    rw [headSuffixGapShiftDescription_run_to_selectedTailBoundary]
    rw [htail]
    exact hrunBoundary
  refine ⟨(bits.length + 2) + (cells.length + 3), ?_⟩
  constructor
  · rw [hrun]
    rfl
  · rw [hrun]

def selectedHeadGapOpeningRewindHalt : Nat :=
  5

/--
Return from the shifted selected segment's right side to that segment's opening
separator.

The scanner first looks for the inserted three-blank gap.  After the gap is
found, it switches to a payload-only scan and halts on the next separator to
the left, preserving the encoded prefix before that separator.
-/
def selectedHeadGapOpeningRewindDescription : MachineDescription where
  stateCount := 6
  start := 0
  halt := selectedHeadGapOpeningRewindHalt
  transitions :=
    [ transition 0 none none Direction.left 1
    , transition 0 (some false) (some false) Direction.left 0
    , transition 0 (some true) (some true) Direction.left 0
    , transition 1 none none Direction.left 2
    , transition 1 (some false) (some false) Direction.left 0
    , transition 1 (some true) (some true) Direction.left 0
    , transition 2 none none Direction.left 3
    , transition 2 (some false) (some false) Direction.left 3
    , transition 2 (some true) (some true) Direction.left 3
    , transition 3 none none Direction.right 4
    , transition 3 (some false) (some false) Direction.left 3
    , transition 3 (some true) (some true) Direction.left 3
    , transition 4 none none Direction.left selectedHeadGapOpeningRewindHalt
    , transition 4 (some false) (some false) Direction.left
        selectedHeadGapOpeningRewindHalt
    , transition 4 (some true) (some true) Direction.left
        selectedHeadGapOpeningRewindHalt ]

theorem selectedHeadGapOpeningRewindDescription_wellFormed :
    selectedHeadGapOpeningRewindDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := selectedHeadGapOpeningRewindDescription.transitions)
      (stateCount := selectedHeadGapOpeningRewindDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := selectedHeadGapOpeningRewindDescription.transitions)
      (by decide)

theorem selectedHeadGapOpeningRewindDescription_haltTransitionFree :
    selectedHeadGapOpeningRewindDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := selectedHeadGapOpeningRewindDescription.transitions)
    (state := selectedHeadGapOpeningRewindDescription.halt)
    (by decide)

theorem selectedHeadGapOpeningRewindDescription_subroutineReady :
    selectedHeadGapOpeningRewindDescription.SubroutineReady :=
  ⟨selectedHeadGapOpeningRewindDescription_wellFormed,
    selectedHeadGapOpeningRewindDescription_haltTransitionFree⟩

def selectedHeadGapOpeningRewindScanNext
    (state : Nat) : Option Bool -> Nat
  | some _ => selectedHeadGapOpeningRewindDescription.start
  | none =>
      match state with
      | 0 => 1
      | _ => 2

def selectedHeadGapOpeningRewindScanState
    (state : Nat) : List (Option Bool) -> Nat
  | [] => state
  | current :: rest =>
      selectedHeadGapOpeningRewindScanState
        (selectedHeadGapOpeningRewindScanNext state current) rest

def selectedHeadGapOpeningRewindScanSafe
    (state : Nat) : List (Option Bool) -> Prop
  | [] => True
  | none :: rest =>
      state = selectedHeadGapOpeningRewindDescription.start ∧
        selectedHeadGapOpeningRewindScanSafe 1 rest
  | some _bit :: rest =>
      selectedHeadGapOpeningRewindScanSafe
        selectedHeadGapOpeningRewindDescription.start rest

def selectedHeadGapOpeningRewindScanSource
    (scan left : List (Option Bool)) (stop : Option Bool)
    (right : List (Option Bool)) : Tape Bool :=
  match scan with
  | [] => tapeAtCells left (stop :: right)
  | current :: rest =>
      tapeAtCells (List.append rest (stop :: left)) (current :: right)

theorem selectedHeadGapOpeningRewindScanState_append
    (state : Nat) (left right : List (Option Bool)) :
    selectedHeadGapOpeningRewindScanState state
        (List.append left right) =
      selectedHeadGapOpeningRewindScanState
        (selectedHeadGapOpeningRewindScanState state left) right := by
  induction left generalizing state with
  | nil =>
      rfl
  | cons current rest ih =>
      exact ih (selectedHeadGapOpeningRewindScanNext state current)

theorem selectedHeadGapOpeningRewindScanSafe_append
    (state : Nat) (left right : List (Option Bool)) :
    selectedHeadGapOpeningRewindScanSafe state
        (List.append left right) ↔
      selectedHeadGapOpeningRewindScanSafe state left ∧
        selectedHeadGapOpeningRewindScanSafe
          (selectedHeadGapOpeningRewindScanState state left) right := by
  induction left generalizing state with
  | nil =>
      simp [selectedHeadGapOpeningRewindScanSafe,
        selectedHeadGapOpeningRewindScanState]
  | cons current rest ih =>
      cases current with
      | none =>
          simp [selectedHeadGapOpeningRewindScanSafe,
            selectedHeadGapOpeningRewindScanState]
          constructor
          · intro h
            rcases h with ⟨hstate, hrestRight⟩
            subst state
            rcases
                (ih 1).mp hrestRight with
              ⟨hrest, hright⟩
            exact ⟨⟨rfl, hrest⟩, hright⟩
          · intro h
            rcases h with ⟨⟨hstate, hrest⟩, hright⟩
            subst state
            exact ⟨rfl, (ih 1).mpr ⟨hrest, hright⟩⟩
      | some bit =>
          cases bit <;>
            simpa [selectedHeadGapOpeningRewindScanSafe,
              selectedHeadGapOpeningRewindScanState,
              selectedHeadGapOpeningRewindScanNext] using
              ih selectedHeadGapOpeningRewindDescription.start

theorem selectedHeadGapOpeningRewindScanSafe_map_some
    (state : Nat) (bits : Word Bool) :
    selectedHeadGapOpeningRewindScanSafe state (bits.map some) := by
  induction bits generalizing state with
  | nil =>
      trivial
  | cons bit rest ih =>
      cases bit <;>
        simpa [selectedHeadGapOpeningRewindScanSafe,
          selectedHeadGapOpeningRewindScanNext] using
          ih selectedHeadGapOpeningRewindDescription.start

theorem selectedHeadGapOpeningRewindScanState_zero_map_some
    (bits : Word Bool) :
    selectedHeadGapOpeningRewindScanState
        selectedHeadGapOpeningRewindDescription.start (bits.map some) =
      selectedHeadGapOpeningRewindDescription.start := by
  induction bits with
  | nil =>
      rfl
  | cons bit rest ih =>
      cases bit <;>
        simpa [selectedHeadGapOpeningRewindScanState,
          selectedHeadGapOpeningRewindScanNext] using ih

theorem selectedHeadGapOpeningRewindScanState_map_some_of_cons
    (state : Nat) (bit : Bool) (bits : Word Bool) :
    selectedHeadGapOpeningRewindScanState state
        ((bit :: bits).map some) =
      selectedHeadGapOpeningRewindDescription.start := by
  cases bit <;>
    simpa [selectedHeadGapOpeningRewindScanState,
      selectedHeadGapOpeningRewindScanNext] using
      selectedHeadGapOpeningRewindScanState_zero_map_some bits

theorem selectedHeadGapOpeningRewindScanState_reverse_map_some_of_cons
    (state : Nat) (bit : Bool) (bits : Word Bool) :
    selectedHeadGapOpeningRewindScanState state
        ((bit :: bits).reverse.map some) =
      selectedHeadGapOpeningRewindDescription.start := by
  rcases word_exists_reverse_append_singleton_of_cons bit bits with
    ⟨scanRev, current, hword⟩
  have hrev : (bit :: bits).reverse = current :: scanRev := by
    rw [hword]
    simp [List.reverse_append]
  rw [hrev]
  exact
    selectedHeadGapOpeningRewindScanState_map_some_of_cons
      state current scanRev

theorem selectedHeadGapOpeningRewindScanState_encodedScanRev_of_nonempty
    (logical : List (Tape Bool)) (hlogical : logical ≠ []) :
    selectedHeadGapOpeningRewindScanState
        selectedHeadGapOpeningRewindDescription.start
        (encodedStructuredTapeCellsScanRev logical) =
      selectedHeadGapOpeningRewindDescription.start := by
  induction logical with
  | nil =>
      contradiction
  | cons T rest ih =>
      cases rest with
      | nil =>
          rcases logicalTapeBits_exists_cons T with ⟨bit, bits, hbits⟩
          rw [encodedStructuredTapeCellsScanRev, hbits]
          exact
            selectedHeadGapOpeningRewindScanState_reverse_map_some_of_cons
              selectedHeadGapOpeningRewindDescription.start bit bits
      | cons U rest =>
          rcases logicalTapeBits_exists_cons T with ⟨bit, bits, hbits⟩
          rw [encodedStructuredTapeCellsScanRev, hbits]
          rw [selectedHeadGapOpeningRewindScanState_append]
          rw [selectedHeadGapOpeningRewindScanState_append]
          rw [ih (by simp)]
          simp [selectedHeadGapOpeningRewindScanState,
            selectedHeadGapOpeningRewindScanNext,
            selectedHeadGapOpeningRewindDescription]
          simpa [List.map_reverse,
            selectedHeadGapOpeningRewindDescription] using
            selectedHeadGapOpeningRewindScanState_reverse_map_some_of_cons
              1 bit bits

theorem selectedHeadGapOpeningRewindScanState_encodedScanRev
    (T : Tape Bool) (rest : List (Tape Bool)) :
    selectedHeadGapOpeningRewindScanState
        selectedHeadGapOpeningRewindDescription.start
        (encodedStructuredTapeCellsScanRev (T :: rest)) =
      selectedHeadGapOpeningRewindDescription.start :=
  selectedHeadGapOpeningRewindScanState_encodedScanRev_of_nonempty
    (T :: rest) (by simp)

theorem selectedHeadGapOpeningRewindScanSafe_encodedScanRev_of_nonempty
    (logical : List (Tape Bool)) (hlogical : logical ≠ []) :
    selectedHeadGapOpeningRewindScanSafe
        selectedHeadGapOpeningRewindDescription.start
        (encodedStructuredTapeCellsScanRev logical) := by
  induction logical with
  | nil =>
      contradiction
  | cons T rest ih =>
      cases rest with
      | nil =>
          exact
            selectedHeadGapOpeningRewindScanSafe_map_some
              selectedHeadGapOpeningRewindDescription.start
              (logicalTapeBits T).reverse
      | cons U rest =>
          rw [encodedStructuredTapeCellsScanRev]
          rw [selectedHeadGapOpeningRewindScanSafe_append]
          constructor
          · rw [selectedHeadGapOpeningRewindScanSafe_append]
            constructor
            · exact ih (by simp)
            · rw [selectedHeadGapOpeningRewindScanState_encodedScanRev U rest]
              simp [selectedHeadGapOpeningRewindScanSafe,
                selectedHeadGapOpeningRewindDescription]
          · have hstateLeft :
                selectedHeadGapOpeningRewindScanState
                    selectedHeadGapOpeningRewindDescription.start
                    (List.append
                      (encodedStructuredTapeCellsScanRev (U :: rest))
                      [none]) = 1 := by
              rw [selectedHeadGapOpeningRewindScanState_append]
              rw [selectedHeadGapOpeningRewindScanState_encodedScanRev U rest]
              simp [selectedHeadGapOpeningRewindScanState,
                selectedHeadGapOpeningRewindScanNext,
                selectedHeadGapOpeningRewindDescription]
            rw [hstateLeft]
            exact
              selectedHeadGapOpeningRewindScanSafe_map_some 1
                (logicalTapeBits T).reverse

theorem selectedHeadGapOpeningRewindScanSafe_encodedScanRev
    (T : Tape Bool) (rest : List (Tape Bool)) :
    selectedHeadGapOpeningRewindScanSafe
        selectedHeadGapOpeningRewindDescription.start
        (encodedStructuredTapeCellsScanRev (T :: rest)) :=
  selectedHeadGapOpeningRewindScanSafe_encodedScanRev_of_nonempty
    (T :: rest) (by simp)

theorem selectedHeadGapOpeningRewindDescription_run_scanStep
    (state : Nat) (current stop : Option Bool)
    (rest left right : List (Option Bool))
    (hstate : state = 0 ∨ state = 1)
    (hsafe :
      selectedHeadGapOpeningRewindScanSafe state (current :: rest)) :
    selectedHeadGapOpeningRewindDescription.runConfig 1
        { state := state
          tape :=
            selectedHeadGapOpeningRewindScanSource
              (current :: rest) left stop right } =
      { state := selectedHeadGapOpeningRewindScanNext state current
        tape :=
          selectedHeadGapOpeningRewindScanSource
            rest left stop (current :: right) } := by
  rcases hstate with rfl | rfl
  · cases current with
    | none =>
        cases rest <;>
          machine_step [selectedHeadGapOpeningRewindDescription,
            selectedHeadGapOpeningRewindScanSource,
            selectedHeadGapOpeningRewindScanNext]
    | some bit =>
        cases bit <;> cases rest <;>
          machine_step [selectedHeadGapOpeningRewindDescription,
            selectedHeadGapOpeningRewindScanSource,
            selectedHeadGapOpeningRewindScanNext]
  · cases current with
    | none =>
        simp [selectedHeadGapOpeningRewindScanSafe,
          selectedHeadGapOpeningRewindDescription] at hsafe
    | some bit =>
        cases bit <;> cases rest <;>
          machine_step [selectedHeadGapOpeningRewindDescription,
            selectedHeadGapOpeningRewindScanSource,
            selectedHeadGapOpeningRewindScanNext]

theorem selectedHeadGapOpeningRewindScanNext_state
    (state : Nat) (current : Option Bool)
    (hstate : state = 0 ∨ state = 1)
    (hsafe :
      selectedHeadGapOpeningRewindScanSafe state [current]) :
    let next := selectedHeadGapOpeningRewindScanNext state current
    next = 0 ∨ next = 1 := by
  rcases hstate with rfl | rfl <;>
    cases current with
    | none =>
        simp [selectedHeadGapOpeningRewindScanSafe,
          selectedHeadGapOpeningRewindScanNext,
          selectedHeadGapOpeningRewindDescription] at hsafe ⊢
    | some bit =>
        cases bit <;>
          simp [selectedHeadGapOpeningRewindScanNext,
            selectedHeadGapOpeningRewindDescription]

theorem selectedHeadGapOpeningRewindDescription_run_scanLeft
    (scan left right : List (Option Bool)) (stop : Option Bool)
    (state : Nat)
    (hstate : state = 0 ∨ state = 1)
    (hsafe : selectedHeadGapOpeningRewindScanSafe state scan) :
    selectedHeadGapOpeningRewindDescription.runConfig scan.length
        { state := state
          tape :=
            selectedHeadGapOpeningRewindScanSource scan left stop right } =
      { state := selectedHeadGapOpeningRewindScanState state scan
        tape :=
          tapeAtCells left
            (stop :: List.append scan.reverse right) } := by
  induction scan generalizing state right with
  | nil =>
      machine_run [selectedHeadGapOpeningRewindScanSource,
        selectedHeadGapOpeningRewindScanState]
  | cons current rest ih =>
      rw [show (current :: rest).length = 1 + rest.length by
        simp [Nat.add_comm]]
      rw [MachineDescription.runConfig_add]
      have hstep :=
        selectedHeadGapOpeningRewindDescription_run_scanStep
          state current stop rest left right hstate hsafe
      rw [hstep]
      have hsafeRest :
          selectedHeadGapOpeningRewindScanSafe
            (selectedHeadGapOpeningRewindScanNext state current) rest := by
        cases current with
        | none =>
            have hstate0 := hsafe.1
            subst state
            simpa [selectedHeadGapOpeningRewindScanNext,
              selectedHeadGapOpeningRewindDescription] using hsafe.2
        | some bit =>
            simpa [selectedHeadGapOpeningRewindScanSafe,
              selectedHeadGapOpeningRewindScanNext] using hsafe
      have hnextState :
          selectedHeadGapOpeningRewindScanNext state current = 0 ∨
            selectedHeadGapOpeningRewindScanNext state current = 1 := by
        have hsafeOne :
            selectedHeadGapOpeningRewindScanSafe state [current] := by
          cases current with
          | none =>
              exact ⟨hsafe.1, trivial⟩
          | some bit =>
              trivial
        simpa using
          selectedHeadGapOpeningRewindScanNext_state
            state current hstate hsafeOne
      simpa [selectedHeadGapOpeningRewindScanState, List.reverse_cons,
        List.append_assoc] using
        ih (current :: right)
          (selectedHeadGapOpeningRewindScanNext state current)
          hnextState hsafeRest

theorem selectedHeadGapOpeningRewindDescription_run_shiftedSuffixScan
    (scanRest gap : List (Option Bool))
    (last current : Option Bool) (cells : List (Option Bool))
    (hsafe :
      selectedHeadGapOpeningRewindScanSafe
        selectedHeadGapOpeningRewindDescription.start
        (last :: scanRest))
    (hstate :
      selectedHeadGapOpeningRewindScanState
        selectedHeadGapOpeningRewindDescription.start
        (last :: scanRest) =
          selectedHeadGapOpeningRewindDescription.start)
    (hcells :
      List.append scanRest.reverse [last, none] = current :: cells) :
    selectedHeadGapOpeningRewindDescription.runConfig (scanRest.length + 1)
        { state := selectedHeadGapOpeningRewindDescription.start
          tape :=
            Tape.move Direction.left
              (tapeAtCells
                (last :: List.append scanRest (none :: gap)) []) } =
      { state := selectedHeadGapOpeningRewindDescription.start
        tape := tapeAtCells gap (none :: current :: cells) } := by
  rw [show scanRest.length + 1 = (last :: scanRest).length by
    simp]
  have hsource :
      Tape.move Direction.left
          (tapeAtCells
            (last :: List.append scanRest (none :: gap)) []) =
        selectedHeadGapOpeningRewindScanSource
          (last :: scanRest) gap none [none] := by
    simp [selectedHeadGapOpeningRewindScanSource, tapeAtCells,
      Tape.move, Tape.moveLeft]
  rw [hsource]
  have hrun :=
    selectedHeadGapOpeningRewindDescription_run_scanLeft
      (last :: scanRest) gap [none] none
      selectedHeadGapOpeningRewindDescription.start
      (Or.inl rfl) hsafe
  rw [hrun]
  simp [hstate, List.reverse_cons, List.append_assoc]
  exact congrArg (fun tail => tapeAtCells gap (none :: tail)) hcells

theorem selectedHeadGapOpeningRewindDescription_run_shiftedSuffixScan_encodedTail
    (gap : List (Option Bool)) (T : Tape Bool) (rest : List (Tape Bool))
    (current : Option Bool) (cells : List (Option Bool))
    (htail :
      encodedStructuredTapeCellsTail (T :: rest) = current :: cells)
    (hfirst :
      (headSuffixGapShiftLoopPair none current cells).1 ≠ none)
    (hsecond :
      (headSuffixGapShiftLoopPair none current cells).2 = none) :
    selectedHeadGapOpeningRewindDescription.runConfig
        (encodedStructuredTapeCellsScanRev (T :: rest)).length
        { state := selectedHeadGapOpeningRewindDescription.start
          tape :=
            Tape.move Direction.left
              (tapeAtCells
                ((headSuffixGapShiftLoopPair none current cells).1 ::
                  List.append
                    (headSuffixGapShiftLoopWrittenRev none current cells)
                    gap) []) } =
      { state := selectedHeadGapOpeningRewindDescription.start
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
    selectedHeadGapOpeningRewindDescription_run_shiftedSuffixScan
      scanRest gap
      (headSuffixGapShiftLoopPair none current cells).1 current cells
      (by
        simpa [hscan] using
          selectedHeadGapOpeningRewindScanSafe_encodedScanRev T rest)
      (by
        simpa [hscan] using
          selectedHeadGapOpeningRewindScanState_encodedScanRev T rest)
      hcells

theorem selectedHeadGapOpeningRewindDescription_run_threeBlankGap
    (base : List (Option Bool)) (leftStack : Word Bool)
    (current : Bool) (rightTail : List (Option Bool)) :
    selectedHeadGapOpeningRewindDescription.runConfig 3
        { state := selectedHeadGapOpeningRewindDescription.start
          tape :=
            tapeAtCells
              (none :: none :: some current ::
                List.append (leftStack.map some) (none :: base))
              (none :: rightTail) } =
      { state := 3
        tape :=
          tapeAtCells
            (List.append (leftStack.map some) (none :: base))
            (some current :: none :: none :: none :: rightTail) } := by
  cases current <;> cases leftStack <;> cases rightTail <;>
    machine_step [selectedHeadGapOpeningRewindDescription]

theorem selectedHeadGapOpeningRewindDescription_run_payloadScan
    (base : List (Option Bool)) (leftStack : Word Bool)
    (current : Bool) (rightTail : List (Option Bool)) :
    selectedHeadGapOpeningRewindDescription.runConfig
        (leftStack.length + 1)
        { state := 3
          tape :=
            tapeAtCells
              (List.append (leftStack.map some) (none :: base))
              (some current :: rightTail) } =
      { state := 3
        tape :=
          tapeAtCells base
            (none ::
              List.append
                ((List.append leftStack.reverse [current]).map some)
                rightTail) } := by
  induction leftStack generalizing current rightTail with
  | nil =>
      cases current <;> cases rightTail <;>
        machine_step [selectedHeadGapOpeningRewindDescription]
  | cons next rest ih =>
      rw [show (next :: rest).length + 1 =
        1 + (rest.length + 1) by
        simp
        lia]
      rw [MachineDescription.runConfig_add]
      have hstep :
          selectedHeadGapOpeningRewindDescription.runConfig 1
              { state := 3
                tape :=
                  tapeAtCells
                    (List.append ((next :: rest).map some) (none :: base))
                    (some current :: rightTail) } =
            { state := 3
              tape :=
                tapeAtCells
                  (List.append (rest.map some) (none :: base))
                  (some next :: some current :: rightTail) } := by
        cases next <;> cases current <;> cases rightTail <;>
          machine_step [selectedHeadGapOpeningRewindDescription]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih next (some current :: rightTail)

private theorem selectedHeadGapOpeningRewindDescription_run_finishPayload
    (base : List (Option Bool)) (payload : Word Bool)
    (rightTail : List (Option Bool)) (hpayload : payload ≠ []) :
    selectedHeadGapOpeningRewindDescription.runConfig 2
        { state := 3
          tape :=
            tapeAtCells base
              (none :: List.append (payload.map some) rightTail) } =
      { state := selectedHeadGapOpeningRewindHalt
        tape :=
          tapeAtCells base
            (none :: List.append (payload.map some) rightTail) } := by
  cases payload with
  | nil =>
      contradiction
  | cons bit rest =>
      cases bit <;> cases rest <;> cases rightTail <;>
        machine_step [selectedHeadGapOpeningRewindDescription]

theorem selectedHeadGapOpeningRewindDescription_run_payloadFinish
    (base : List (Option Bool)) (leftStack : Word Bool)
    (current : Bool) (rightTail : List (Option Bool)) :
    selectedHeadGapOpeningRewindDescription.runConfig
        (leftStack.length + 3)
        { state := 3
          tape :=
            tapeAtCells
              (List.append (leftStack.map some) (none :: base))
              (some current :: rightTail) } =
      { state := selectedHeadGapOpeningRewindHalt
        tape :=
          tapeAtCells base
            (none ::
              List.append
                ((List.append leftStack.reverse [current]).map some)
                rightTail) } := by
  rw [show leftStack.length + 3 = (leftStack.length + 1) + 2 by lia]
  rw [MachineDescription.runConfig_add]
  rw [selectedHeadGapOpeningRewindDescription_run_payloadScan]
  have hpayload :
      List.append leftStack.reverse [current] ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    simp at hlen
  simpa using
    selectedHeadGapOpeningRewindDescription_run_finishPayload
      base (List.append leftStack.reverse [current]) rightTail
      hpayload

theorem selectedHeadGapOpeningRewindDescription_run_threeBlankGapPayloadFinish
    (base : List (Option Bool)) (leftStack : Word Bool)
    (current : Bool) (rightTail : List (Option Bool)) :
    selectedHeadGapOpeningRewindDescription.runConfig
        (leftStack.length + 6)
        { state := selectedHeadGapOpeningRewindDescription.start
          tape :=
            tapeAtCells
              (none :: none :: some current ::
                List.append (leftStack.map some) (none :: base))
              (none :: rightTail) } =
      { state := selectedHeadGapOpeningRewindHalt
        tape :=
          tapeAtCells base
            (none ::
              List.append
                ((List.append leftStack.reverse [current]).map some)
                (none :: none :: none :: rightTail)) } := by
  rw [show leftStack.length + 6 = 3 + (leftStack.length + 3) by lia]
  rw [MachineDescription.runConfig_add]
  rw [selectedHeadGapOpeningRewindDescription_run_threeBlankGap]
  exact
    selectedHeadGapOpeningRewindDescription_run_payloadFinish
      base leftStack current (none :: none :: none :: rightTail)

theorem selectedHeadGapOpeningRewindDescription_run_twoBlankGapPayloadFinish
    (base : List (Option Bool)) (leftStack : Word Bool)
    (current : Bool) (rightTail : List (Option Bool)) :
    selectedHeadGapOpeningRewindDescription.runConfig
        (leftStack.length + 5)
        { state := selectedHeadGapOpeningRewindDescription.start
          tape :=
            tapeAtCells
              (none :: some current ::
                List.append (leftStack.map some) (none :: base))
              (none :: rightTail) } =
      { state := selectedHeadGapOpeningRewindHalt
        tape :=
          tapeAtCells base
            (none ::
              List.append
                ((List.append leftStack.reverse [current]).map some)
                (none :: none :: rightTail)) } := by
  induction leftStack generalizing current rightTail with
  | nil =>
      cases current <;> cases rightTail <;> cases base <;>
        machine_step [selectedHeadGapOpeningRewindDescription]
  | cons next rest ih =>
      rw [show (next :: rest).length + 5 =
        3 + (rest.length + 3) by
        simp
        lia]
      rw [MachineDescription.runConfig_add]
      have hentry :
          selectedHeadGapOpeningRewindDescription.runConfig 3
              { state := selectedHeadGapOpeningRewindDescription.start
                tape :=
                  tapeAtCells
                    (none :: some current ::
                      List.append ((next :: rest).map some) (none :: base))
                    (none :: rightTail) } =
            { state := 3
              tape :=
                tapeAtCells
                  (List.append (rest.map some) (none :: base))
                  (some next :: some current :: none :: none :: rightTail) } := by
        cases next <;> cases current <;> cases rest <;>
          cases rightTail <;>
          machine_step [selectedHeadGapOpeningRewindDescription]
      rw [hentry]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        selectedHeadGapOpeningRewindDescription_run_payloadFinish
          base rest next (some current :: none :: none :: rightTail)

theorem selectedHeadGapOpeningRewindDescription_haltsFrom_threeBlankGapPayload
    (base : List (Option Bool)) (leftStack : Word Bool)
    (current : Bool) (rightTail : List (Option Bool)) :
    selectedHeadGapOpeningRewindDescription.HaltsFromTape
      (tapeAtCells
        (none :: none :: some current ::
          List.append (leftStack.map some) (none :: base))
        (none :: rightTail))
      (tapeAtCells base
        (none ::
          List.append
            ((List.append leftStack.reverse [current]).map some)
            (none :: none :: none :: rightTail))) := by
  refine ⟨leftStack.length + 6, ?_⟩
  constructor
  · rw [selectedHeadGapOpeningRewindDescription_run_threeBlankGapPayloadFinish]
    simp [selectedHeadGapOpeningRewindDescription]
  · rw [selectedHeadGapOpeningRewindDescription_run_threeBlankGapPayloadFinish]

theorem selectedHeadGapOpeningRewindDescription_haltsFrom_twoBlankGapPayload
    (base : List (Option Bool)) (leftStack : Word Bool)
    (current : Bool) (rightTail : List (Option Bool)) :
    selectedHeadGapOpeningRewindDescription.HaltsFromTape
      (tapeAtCells
        (none :: some current ::
          List.append (leftStack.map some) (none :: base))
        (none :: rightTail))
      (tapeAtCells base
        (none ::
          List.append
            ((List.append leftStack.reverse [current]).map some)
            (none :: none :: rightTail))) := by
  refine ⟨leftStack.length + 5, ?_⟩
  constructor
  · rw [selectedHeadGapOpeningRewindDescription_run_twoBlankGapPayloadFinish]
    simp [selectedHeadGapOpeningRewindDescription]
  · rw [selectedHeadGapOpeningRewindDescription_run_twoBlankGapPayloadFinish]

theorem selectedHeadGapOpeningRewindDescription_haltsFrom_shifted_emptyRest
    (encodedPrefix : List (Option Bool)) (first : Bool)
    (bits : Word Bool) :
    selectedHeadGapOpeningRewindDescription.HaltsFromTapeEquiv
      (Tape.move Direction.left
        (tapeAtCells
          (none :: none ::
            List.append ((first :: bits).reverse.map some)
              (none :: encodedPrefix.reverse))
          []))
      (tapeAtSelectedHeadPayloadGap encodedPrefix (first :: bits) []) := by
  rcases word_exists_reverse_append_singleton_of_cons first bits with
    ⟨leftStack, current, hpayload⟩
  let actual : Tape Bool :=
    tapeAtCells encodedPrefix.reverse
      (none ::
        List.append
          ((List.append leftStack.reverse [current]).map some)
          [none, none, none])
  have hsource :
      Tape.move Direction.left
          (tapeAtCells
            (none :: none ::
              List.append ((first :: bits).reverse.map some)
                (none :: encodedPrefix.reverse))
            []) =
        tapeAtCells
          (none :: some current ::
            List.append (leftStack.map some) (none :: encodedPrefix.reverse))
          (none :: [none]) := by
    rw [hpayload]
    simp [tapeAtCells, Tape.move, Tape.moveLeft, List.reverse_append]
  refine ⟨actual, ?_, ?_⟩
  · rw [hsource]
    simpa [actual] using
      selectedHeadGapOpeningRewindDescription_haltsFrom_twoBlankGapPayload
        encodedPrefix.reverse leftStack current [none]
  · rw [hpayload]
    simp [actual, tapeAtSelectedHeadPayloadGap, tapeAtEncodedSplit,
      encodedStructuredTapeCells, tapeSeparatorCells, Tape.Equiv,
      tapeAtCells, List.map_append, List.append_assoc]

theorem selectedHeadGapOpeningRewindDescription_haltsFrom_shifted_cons
    (encodedPrefix : List (Option Bool)) (first : Bool)
    (bits : Word Bool) (T : Tape Bool) (rest : List (Tape Bool))
    (current : Option Bool) (cells : List (Option Bool))
    (htail :
      encodedStructuredTapeCellsTail (T :: rest) = current :: cells)
    (hfirst :
      (headSuffixGapShiftLoopPair none current cells).1 ≠ none)
    (hsecond :
      (headSuffixGapShiftLoopPair none current cells).2 = none) :
    selectedHeadGapOpeningRewindDescription.HaltsFromTapeEquiv
      (Tape.move Direction.left
        (tapeAtCells
          ((headSuffixGapShiftLoopPair none current cells).1 ::
            List.append
              (headSuffixGapShiftLoopWrittenRev none current cells)
              (none :: none ::
                List.append ((first :: bits).reverse.map some)
                  (none :: encodedPrefix.reverse)))
          []))
      (tapeAtSelectedHeadPayloadGap encodedPrefix
        (first :: bits) (T :: rest)) := by
  rcases word_exists_reverse_append_singleton_of_cons first bits with
    ⟨leftStack, payloadCurrent, hpayload⟩
  let gap : List (Option Bool) :=
    none :: none ::
      List.append ((first :: bits).reverse.map some)
        (none :: encodedPrefix.reverse)
  let actual : Tape Bool :=
    tapeAtCells encodedPrefix.reverse
      (none ::
        List.append
          ((List.append leftStack.reverse [payloadCurrent]).map some)
          (none :: none :: none :: current :: cells))
  have hgap :
      gap =
        none :: none :: some payloadCurrent ::
          List.append (leftStack.map some)
            (none :: encodedPrefix.reverse) := by
    simp [gap, hpayload, List.reverse_append]
  refine ⟨actual, ?_, ?_⟩
  · refine
      ⟨(encodedStructuredTapeCellsScanRev (T :: rest)).length +
          (leftStack.length + 6), ?_⟩
    constructor
    · rw [MachineDescription.runConfig_add]
      change
        (selectedHeadGapOpeningRewindDescription.runConfig
          (leftStack.length + 6)
          (selectedHeadGapOpeningRewindDescription.runConfig
            (encodedStructuredTapeCellsScanRev (T :: rest)).length
            { state := selectedHeadGapOpeningRewindDescription.start
              tape :=
                Tape.move Direction.left
                  (tapeAtCells
                    ((headSuffixGapShiftLoopPair none current cells).1 ::
                      List.append
                        (headSuffixGapShiftLoopWrittenRev none current cells)
                        gap) []) })).state =
          selectedHeadGapOpeningRewindDescription.halt
      rw [selectedHeadGapOpeningRewindDescription_run_shiftedSuffixScan_encodedTail
        gap T rest current cells htail hfirst hsecond]
      rw [hgap]
      rw [selectedHeadGapOpeningRewindDescription_run_threeBlankGapPayloadFinish]
      rfl
    · rw [MachineDescription.runConfig_add]
      change
        (selectedHeadGapOpeningRewindDescription.runConfig
          (leftStack.length + 6)
          (selectedHeadGapOpeningRewindDescription.runConfig
            (encodedStructuredTapeCellsScanRev (T :: rest)).length
            { state := selectedHeadGapOpeningRewindDescription.start
              tape :=
                Tape.move Direction.left
                  (tapeAtCells
                    ((headSuffixGapShiftLoopPair none current cells).1 ::
                      List.append
                        (headSuffixGapShiftLoopWrittenRev none current cells)
                        gap) []) })).tape =
          actual
      rw [selectedHeadGapOpeningRewindDescription_run_shiftedSuffixScan_encodedTail
        gap T rest current cells htail hfirst hsecond]
      rw [hgap]
      rw [selectedHeadGapOpeningRewindDescription_run_threeBlankGapPayloadFinish]
  · simp [actual, tapeAtSelectedHeadPayloadGap, tapeAtEncodedSplit,
      encodedStructuredTapeCells_eq_cons_tail, htail, hpayload,
      tapeSeparatorCells, Tape.Equiv, tapeAtCells, List.map_append,
      List.append_assoc]

def selectedHeadGapCreatorDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription
    headSuffixGapShiftDescription
    selectedHeadGapOpeningRewindDescription

theorem selectedHeadGapCreatorDescription_subroutineReady :
    selectedHeadGapCreatorDescription.SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    headSuffixGapShiftDescription_subroutineReady
    selectedHeadGapOpeningRewindDescription_subroutineReady

theorem selectedHeadGapCreatorDescription_realizes_emptyRest
    (encodedPrefix : List (Option Bool)) (first : Bool)
    (bits : Word Bool) :
    selectedHeadGapCreatorDescription.HaltsFromTapeEquiv
      (tapeAtSelectedHeadPayload encodedPrefix (first :: bits) [])
      (tapeAtSelectedHeadPayloadGap encodedPrefix (first :: bits) []) :=
  canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    headSuffixGapShiftDescription_subroutineReady
    selectedHeadGapOpeningRewindDescription_subroutineReady
    (MachineDescription.HaltsFromTape.toEquiv
      (headSuffixGapShiftDescription_haltsFrom_selectedPayload_emptyRest
        encodedPrefix (first :: bits)))
    (selectedHeadGapOpeningRewindDescription_haltsFrom_shifted_emptyRest
      encodedPrefix first bits)

theorem selectedHeadGapCreatorDescription_realizes_cons
    (encodedPrefix : List (Option Bool)) (first : Bool)
    (bits : Word Bool) (T : Tape Bool) (rest : List (Tape Bool)) :
    selectedHeadGapCreatorDescription.HaltsFromTapeEquiv
      (tapeAtSelectedHeadPayload encodedPrefix (first :: bits) (T :: rest))
      (tapeAtSelectedHeadPayloadGap encodedPrefix
        (first :: bits) (T :: rest)) := by
  rcases
      headSuffixGapShiftDescription_haltsFrom_selectedPayload_cons
        encodedPrefix (first :: bits) T rest with
    ⟨current, cells, htail, hfirst, hsecond, hshift⟩
  exact
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      headSuffixGapShiftDescription_subroutineReady
      selectedHeadGapOpeningRewindDescription_subroutineReady
      (MachineDescription.HaltsFromTape.toEquiv hshift)
      (selectedHeadGapOpeningRewindDescription_haltsFrom_shifted_cons
        encodedPrefix first bits T rest current cells htail hfirst hsecond)

/--
Local gap-creator contract for a selected segment.

Unlike the head-segment gap creator used by
{name}`concreteSingletonHeadRefreshDescription`, this contract is explicitly
prefix-preserving: the machine starts and halts on the selected segment
separator inside a larger encoded block.
-/
structure SelectedHeadGapCreatorContract
    (gapCreator : MachineDescription) : Prop where
  subroutineReady : gapCreator.SubroutineReady
  realizes :
    forall (encodedPrefix : List (Option Bool)) (head : Tape Bool)
      (rest : List (Tape Bool)),
      gapCreator.HaltsFromTapeEquiv
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells (head :: rest)))
        (tapeAtSelectedHeadGap encodedPrefix head rest)

theorem selectedHeadGapCreatorDescription_contract :
    SelectedHeadGapCreatorContract selectedHeadGapCreatorDescription where
  subroutineReady := selectedHeadGapCreatorDescription_subroutineReady
  realizes := by
    intro encodedPrefix head rest
    rcases logicalTapeBits_exists_cons head with
      ⟨first, bits, hbits⟩
    cases rest with
    | nil =>
        have hrun :=
          selectedHeadGapCreatorDescription_realizes_emptyRest
            encodedPrefix first bits
        rw [← hbits] at hrun
        simpa [tapeAtSelectedHeadPayload_logicalTapeBits,
          tapeAtSelectedHeadPayloadGap_logicalTapeBits] using hrun
    | cons T rest =>
        have hrun :=
          selectedHeadGapCreatorDescription_realizes_cons
            encodedPrefix first bits T rest
        rw [← hbits] at hrun
        simpa [tapeAtSelectedHeadPayload_logicalTapeBits,
          tapeAtSelectedHeadPayloadGap_logicalTapeBits] using hrun

private theorem logicalTapeCode_eq_of_encodedStructuredTapes_singleton_eq
    {actual expected : Tape Bool}
    (h :
      encodedStructuredTapes [actual] =
        encodedStructuredTapes [expected]) :
    logicalTapeCode actual = logicalTapeCode expected := by
  unfold encodedStructuredTapes at h
  simp [encodedStructuredTapeCells] at h
  injection h with _ _ hcode
  simpa using hcode

private theorem encodedStructuredTapeCells_cons_eq_of_singleton_eq
    {actual expected : Tape Bool} {rest : List (Tape Bool)}
    (h :
      encodedStructuredTapes [actual] =
        encodedStructuredTapes [expected]) :
    encodedStructuredTapeCells (actual :: rest) =
      encodedStructuredTapeCells (expected :: rest) := by
  have hcode :=
    logicalTapeCode_eq_of_encodedStructuredTapes_singleton_eq h
  simp [encodedStructuredTapeCells, hcode]

/--
Case-split contract for a selected-separator local refresher.

This is the proof boundary for the eventual selected-separator classifier:
canonical selected segments may no-op, while the two boundary shapes use the
gap creator followed by the corresponding boundary repair.
-/
structure SelectedSeparatorGuardSlackRefreshCaseContract
    (refresh : MachineDescription) : Prop where
  subroutineReady : refresh.SubroutineReady
  canonical :
    forall (encodedPrefix : List (Option Bool))
      (target actual : Tape Bool) (rest : List (Tape Bool)),
      encodedStructuredTapes [actual] =
          encodedGuardedStructuredTapes [target] ->
        refresh.HaltsFromTapeEquiv
          (tapeAtEncodedSplit encodedPrefix
            (encodedStructuredTapeCells (actual :: rest)))
          (tapeAtEncodedSplit encodedPrefix
            (encodedStructuredTapeCells
              (guardLogicalTape target :: rest)))
  leftBoundary :
    forall (encodedPrefix : List (Option Bool))
      (head : Option Bool) (right : List (Option Bool))
      (rest : List (Tape Bool)),
      refresh.HaltsFromTapeEquiv
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells
            (({ left := [], head := head, right := right ++ [none] } :
              Tape Bool) :: rest)))
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells
            (guardLogicalTape
              ({ left := [], head := head, right := right } :
                Tape Bool) :: rest)))
  rightBoundary :
    forall (encodedPrefix : List (Option Bool))
      (left : List (Option Bool)) (head : Option Bool)
      (rest : List (Tape Bool)),
      refresh.HaltsFromTapeEquiv
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells
            (({ left := left ++ [none], head := head, right := [] } :
              Tape Bool) :: rest)))
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells
            (guardLogicalTape
              ({ left := left, head := head, right := [] } :
                Tape Bool) :: rest)))

namespace SelectedSeparatorGuardSlackRefreshCaseContract

theorem toSelectedSeparatorContract
    {refresh : MachineDescription}
    (hrefresh : SelectedSeparatorGuardSlackRefreshCaseContract refresh)
    (tapeIndex : Nat) :
    SelectedSeparatorGuardSlackRefreshContract refresh tapeIndex where
  subroutineReady := hrefresh.subroutineReady
  realizes := by
    intro target actual targetTape targetRest hlist hdrop
    rcases singletonGuardSlackEndpointShapeList_drop_eq_cons hlist hdrop with
      ⟨actualTape, actualRest, hactualDrop, hsegment, _hrest⟩
    have hsourceSuffix :
        encodedSuffixFromTape actual tapeIndex =
          encodedStructuredTapeCells (actualTape :: actualRest) := by
      simp [encodedSuffixFromTape, hactualDrop]
    have htargetPrefix :
        encodedPrefixBeforeTape
            (replaceTapeAt tapeIndex (guardLogicalTape targetTape) actual)
            tapeIndex =
          encodedPrefixBeforeTape actual tapeIndex :=
      encodedPrefixBeforeTape_replaceTapeAt_eq actual tapeIndex
        (guardLogicalTape targetTape)
    have htargetDrop :
        (replaceTapeAt tapeIndex (guardLogicalTape targetTape)
          actual).drop tapeIndex =
            guardLogicalTape targetTape :: actualRest :=
      replaceTapeAt_drop_eq_of_drop_eq_cons hactualDrop
    have htargetSuffix :
        encodedSuffixFromTape
            (replaceTapeAt tapeIndex (guardLogicalTape targetTape) actual)
            tapeIndex =
          encodedStructuredTapeCells
            (guardLogicalTape targetTape :: actualRest) := by
      simp [encodedSuffixFromTape, htargetDrop]
    generalize hphysicalEq :
      encodedStructuredTapes [actualTape] = physical at hsegment
    cases hsegment with
    | canonical hphysical =>
        have hcanonical :
            encodedStructuredTapes [actualTape] =
              encodedGuardedStructuredTapes [targetTape] := by
          rw [hphysicalEq, hphysical]
        simpa [hsourceSuffix, htargetPrefix, htargetSuffix] using
          hrefresh.canonical
            (encodedPrefixBeforeTape actual tapeIndex)
            targetTape actualTape actualRest hcanonical
    | leftBoundary head right =>
        let boundaryActual : Tape Bool :=
          { left := [], head := head, right := right ++ [none] }
        let boundaryTarget : Tape Bool :=
          { left := [], head := head, right := right }
        have hsourceCells :
            encodedStructuredTapeCells (actualTape :: actualRest) =
              encodedStructuredTapeCells
                (boundaryActual :: actualRest) := by
          exact
            encodedStructuredTapeCells_cons_eq_of_singleton_eq
              (by simpa [boundaryActual] using hphysicalEq)
        simpa [hsourceSuffix, htargetPrefix, htargetSuffix, hsourceCells,
          boundaryActual, boundaryTarget] using
          hrefresh.leftBoundary
            (encodedPrefixBeforeTape actual tapeIndex)
            head right actualRest
    | rightBoundary left head =>
        let boundaryActual : Tape Bool :=
          { left := left ++ [none], head := head, right := [] }
        let boundaryTarget : Tape Bool :=
          { left := left, head := head, right := [] }
        have hsourceCells :
            encodedStructuredTapeCells (actualTape :: actualRest) =
              encodedStructuredTapeCells
                (boundaryActual :: actualRest) := by
          exact
            encodedStructuredTapeCells_cons_eq_of_singleton_eq
              (by simpa [boundaryActual] using hphysicalEq)
        simpa [hsourceSuffix, htargetPrefix, htargetSuffix, hsourceCells,
          boundaryActual, boundaryTarget] using
          hrefresh.rightBoundary
            (encodedPrefixBeforeTape actual tapeIndex)
            left head actualRest

end SelectedSeparatorGuardSlackRefreshCaseContract

def selectedLeftBoundaryRefreshDescription
    (gapCreator : MachineDescription) : MachineDescription :=
  canonicalPrimitiveSeqDescription gapCreator
    leftBoundaryGuardSlackRefreshDescription

def selectedRightBoundaryRefreshDescription
    (gapCreator : MachineDescription) : MachineDescription :=
  canonicalPrimitiveSeqDescription gapCreator
    rightBoundaryGuardSlackRefreshDescription

theorem tapeAtEncodedSplit_selectedSeparator_read
    (encodedPrefix : List (Option Bool)) (head : Tape Bool)
    (rest : List (Tape Bool)) :
    Tape.read
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells (head :: rest))) = none := by
  simp [tapeAtEncodedSplit, encodedStructuredTapeCells, tapeSeparatorCells,
    tapeAtCells, Tape.read]

theorem tapeAtEncodedSplit_selectedCanonical_afterOpening_read
    (encodedPrefix : List (Option Bool))
    (target actual : Tape Bool) (rest : List (Tape Bool))
    (hcanonical :
      encodedStructuredTapes [actual] =
        encodedGuardedStructuredTapes [target]) :
    Tape.read
        (Tape.moveRight
          (tapeAtEncodedSplit encodedPrefix
            (encodedStructuredTapeCells (actual :: rest)))) =
      some false := by
  have hcode :
      logicalTapeCode actual =
        logicalTapeCode (guardLogicalTape target) := by
    have hsingleton :
        encodedStructuredTapes [actual] =
          encodedStructuredTapes [guardLogicalTape target] := by
      simpa [encodedGuardedStructuredTapes, guardLogicalTapes] using
        hcanonical
    exact logicalTapeCode_eq_of_encodedStructuredTapes_singleton_eq
      hsingleton
  simp [tapeAtEncodedSplit, encodedStructuredTapeCells, hcode,
    logicalTapeCode_eq_map_some, guardLogicalTape, logicalTapeBits,
    logicalCellListBits, logicalCellBits, tapeSeparatorCells, tapeAtCells,
    Tape.read, Tape.moveRight]

theorem tapeAtEncodedSplit_selectedLeftBoundary_afterOpening_read
    (encodedPrefix : List (Option Bool)) (head : Option Bool)
    (right : List (Option Bool)) (rest : List (Tape Bool)) :
    Tape.read
        (Tape.moveRight
          (tapeAtEncodedSplit encodedPrefix
            (encodedStructuredTapeCells
              (({ left := [], head := head, right := right ++ [none] } :
                Tape Bool) :: rest)))) =
      some true := by
  simp [tapeAtEncodedSplit, encodedStructuredTapeCells,
    logicalTapeCode_eq_map_some, logicalTapeBits, logicalCellListBits,
    logicalCellBits, tapeSeparatorCells, tapeAtCells,
    Tape.read, Tape.moveRight]

theorem tapeAtEncodedSplit_selectedRightBoundary_afterOpening_read
    (encodedPrefix : List (Option Bool))
    (left : List (Option Bool)) (head : Option Bool)
    (rest : List (Tape Bool)) :
    Tape.read
        (Tape.moveRight
          (tapeAtEncodedSplit encodedPrefix
            (encodedStructuredTapeCells
              (({ left := left ++ [none], head := head, right := [] } :
                Tape Bool) :: rest)))) =
      some false := by
  simp [tapeAtEncodedSplit, encodedStructuredTapeCells,
    logicalTapeCode_eq_map_some, logicalTapeBits, logicalCellListBits,
    logicalCellBits, tapeSeparatorCells, tapeAtCells,
    Tape.read, Tape.moveRight]

def concreteSelectedLeftBoundaryRefreshDescription : MachineDescription :=
  selectedLeftBoundaryRefreshDescription selectedHeadGapCreatorDescription

def concreteSelectedRightBoundaryRefreshDescription : MachineDescription :=
  selectedRightBoundaryRefreshDescription selectedHeadGapCreatorDescription

theorem concreteSelectedLeftBoundaryRefreshDescription_subroutineReady :
    concreteSelectedLeftBoundaryRefreshDescription.SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    selectedHeadGapCreatorDescription_contract.subroutineReady
    leftBoundaryGuardSlackRefreshDescription_subroutineReady

theorem concreteSelectedRightBoundaryRefreshDescription_subroutineReady :
    concreteSelectedRightBoundaryRefreshDescription.SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    selectedHeadGapCreatorDescription_contract.subroutineReady
    rightBoundaryGuardSlackRefreshDescription_subroutineReady


end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC

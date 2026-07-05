import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.StructuredRefresh
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.FiniteMachineTactics
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

def selectedLeftBoundaryRefreshDescription
    (gapCreator : MachineDescription) : MachineDescription :=
  canonicalPrimitiveSeqDescription gapCreator
    leftBoundaryGuardSlackRefreshDescription

def selectedRightBoundaryRefreshDescription
    (gapCreator : MachineDescription) : MachineDescription :=
  canonicalPrimitiveSeqDescription gapCreator
    rightBoundaryGuardSlackRefreshDescription

theorem selectedLeftBoundaryRefreshDescription_subroutineReady
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    (selectedLeftBoundaryRefreshDescription gapCreator).SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady hgap
    leftBoundaryGuardSlackRefreshDescription_subroutineReady

theorem selectedRightBoundaryRefreshDescription_subroutineReady
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    (selectedRightBoundaryRefreshDescription gapCreator).SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady hgap
    rightBoundaryGuardSlackRefreshDescription_subroutineReady

namespace SelectedHeadGapCreatorContract

theorem leftBoundaryRefresh
    {gapCreator : MachineDescription}
    (hgap : SelectedHeadGapCreatorContract gapCreator)
    (encodedPrefix : List (Option Bool))
    (head : Option Bool) (right : List (Option Bool))
    (rest : List (Tape Bool)) :
    (selectedLeftBoundaryRefreshDescription gapCreator).HaltsFromTapeEquiv
      (tapeAtEncodedSplit encodedPrefix
        (encodedStructuredTapeCells
          (({ left := [], head := head, right := right ++ [none] } :
            Tape Bool) :: rest)))
      (tapeAtEncodedSplit encodedPrefix
        (encodedStructuredTapeCells
          (guardLogicalTape
            ({ left := [], head := head, right := right } :
              Tape Bool) :: rest))) := by
  have hcreate :=
    hgap.realizes encodedPrefix
      ({ left := [], head := head, right := right ++ [none] } :
        Tape Bool)
      rest
  have hrepair :=
    leftBoundaryGuardSlackRefreshDescription_haltsFrom_selectedHeadGap
      encodedPrefix head (right ++ [none]) rest
  simpa [selectedLeftBoundaryRefreshDescription, guardLogicalTape,
    List.append_assoc] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      hgap.subroutineReady
      leftBoundaryGuardSlackRefreshDescription_subroutineReady
      hcreate hrepair

theorem rightBoundaryRefresh
    {gapCreator : MachineDescription}
    (hgap : SelectedHeadGapCreatorContract gapCreator)
    (encodedPrefix : List (Option Bool))
    (left : List (Option Bool)) (head : Option Bool)
    (rest : List (Tape Bool)) :
    (selectedRightBoundaryRefreshDescription gapCreator).HaltsFromTapeEquiv
      (tapeAtEncodedSplit encodedPrefix
        (encodedStructuredTapeCells
          (({ left := left ++ [none], head := head, right := [] } :
            Tape Bool) :: rest)))
      (tapeAtEncodedSplit encodedPrefix
        (encodedStructuredTapeCells
          (guardLogicalTape
            ({ left := left, head := head, right := [] } :
              Tape Bool) :: rest))) := by
  have hcreate :=
    hgap.realizes encodedPrefix
      ({ left := left ++ [none], head := head, right := [] } :
        Tape Bool)
      rest
  have hrepair :=
    rightBoundaryGuardSlackRefreshDescription_haltsFrom_selectedHeadGap
      encodedPrefix (left ++ [none]) head rest
  simpa [selectedRightBoundaryRefreshDescription, guardLogicalTape,
    List.append_assoc] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      hgap.subroutineReady
      rightBoundaryGuardSlackRefreshDescription_subroutineReady
      hcreate hrepair

end SelectedHeadGapCreatorContract

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC

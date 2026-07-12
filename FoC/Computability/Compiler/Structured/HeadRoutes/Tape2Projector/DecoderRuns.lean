import FoC.Computability.Compiler.Structured.HeadRoutes.Tape2Projector.Runs

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering
namespace Tape2Projector

def decoderSourceTape
    (outputPrefix : Word Bool) (gap : Nat)
    (cells : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append
      (List.replicate gap (none : Option Bool))
      (outputPrefix.reverse.map some))
    (List.append ((logicalCellListBits cells).map some) [some false])

def decoderHaltTape
    (outputPrefix : Word Bool) (gap : Nat) : Tape Bool :=
  tapeAtCells
    (none ::
      List.append
        (List.replicate gap (none : Option Bool))
        (outputPrefix.reverse.map some))
    []

def decoderFinalGap : Nat -> List (Option Bool) -> Nat
  | gap, [] => gap
  | gap, none :: rest => decoderFinalGap (gap + 2) rest
  | gap, some _ :: rest => decoderFinalGap (gap + 1) rest

private theorem decoderDescription_run_seek_blanks
    (padding : Nat) (left right : List (Option Bool)) :
    decoderDescription.runConfig padding
        { state := 0
          tape := tapeAtCells left
            (List.append
              (List.replicate padding (none : Option Bool)) right) } =
      { state := 0
        tape := tapeAtCells
          (List.append
            (List.replicate padding (none : Option Bool)) left) right } := by
  induction padding generalizing left with
  | zero =>
      rfl
  | succ padding ih =>
      rw [show padding + 1 = 1 + padding by lia]
      rw [runConfig_add]
      have hstep :
          decoderDescription.runConfig 1
              { state := 0
                tape := tapeAtCells left
                  (List.append
                    (List.replicate (1 + padding)
                      (none : Option Bool)) right) } =
            { state := 0
              tape := tapeAtCells (none :: left)
                (List.append
                  (List.replicate padding (none : Option Bool)) right) } := by
        rw [show 1 + padding = padding + 1 by lia]
        rw [List.replicate_succ]
        have hgeneric (rest : List (Option Bool)) :
            decoderDescription.runConfig 1
                { state := 0
                  tape := tapeAtCells left (none :: rest) } =
              { state := 0
                tape := tapeAtCells (none :: left) rest } := by
          cases rest <;>
            simp [decoderDescription, runConfig, stepConfig,
              lookupTransition, Matches, transition, tapeAtCells,
              Tape.read, Tape.write, Tape.move, Tape.moveRight]
        exact hgeneric _
      rw [hstep]
      rw [ih (none :: left)]
      rw [replicate_none_append_none_cons]
      rw [show 1 + padding = padding + 1 by lia]
      rw [List.replicate_succ]
      have hleft :
          none ::
              List.append
                (List.replicate padding (none : Option Bool)) left =
            List.append
              (none :: List.replicate padding (none : Option Bool)) left :=
        rfl
      rw [hleft]

private theorem decoderDescription_run_return_no_emit
    (gap : Nat) (anchor : Bool)
    (base right : List (Option Bool)) :
    decoderDescription.runConfig (gap + 1)
        { state := 7
          tape := Tape.move Direction.left
            (tapeAtCells
              (List.append
                (List.replicate gap (none : Option Bool))
                (some anchor :: base))
              (none :: none :: right)) } =
      { state := 0
        tape := tapeAtCells (some anchor :: base)
          (List.append
            (List.replicate (gap + 2) (none : Option Bool)) right) } := by
  induction gap generalizing right with
  | zero =>
      cases anchor <;> cases base <;> cases right <;>
        simp [decoderDescription, runConfig, stepConfig,
          lookupTransition, Matches, transition, tapeAtCells,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          Tape.moveRight, List.replicate_succ]
  | succ gap ih =>
      rw [show Nat.succ gap + 1 = 1 + (gap + 1) by lia]
      rw [runConfig_add]
      have hstep :
          decoderDescription.runConfig 1
              { state := 7
                tape := Tape.move Direction.left
                  (tapeAtCells
                    (List.append
                      (List.replicate (Nat.succ gap)
                        (none : Option Bool))
                      (some anchor :: base))
                    (none :: none :: right)) } =
            { state := 7
              tape := Tape.move Direction.left
                (tapeAtCells
                  (List.append
                    (List.replicate gap (none : Option Bool))
                    (some anchor :: base))
                  (none :: none :: none :: right)) } := by
        cases anchor <;> cases base <;> cases right <;>
          simp [decoderDescription, runConfig, stepConfig,
            lookupTransition, Matches, transition, tapeAtCells,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft,
            List.replicate_succ]
      rw [hstep]
      rw [ih (none :: right)]
      have hright :
          List.append
              (List.replicate (gap + 2) (none : Option Bool))
              (none :: right) =
            List.append
              (List.replicate (Nat.succ gap + 2) (none : Option Bool))
              right := by
        rw [replicate_none_append_none_cons]
        rw [show Nat.succ gap + 2 = (gap + 2) + 1 by lia]
        rw [List.replicate_succ]
        rfl
      rw [hright]

private theorem decoderDescription_run_return_emit_false
    (gap : Nat) (anchor : Bool)
    (base right : List (Option Bool)) :
    decoderDescription.runConfig (gap + 2)
        { state := 8
          tape := Tape.move Direction.left
            (tapeAtCells
              (List.append
                (List.replicate gap (none : Option Bool))
                (some anchor :: base))
              (none :: none :: right)) } =
      { state := 0
        tape := tapeAtCells (some false :: some anchor :: base)
          (List.append
            (List.replicate (gap + 1) (none : Option Bool)) right) } := by
  induction gap generalizing right with
  | zero =>
      cases anchor <;> cases base <;> cases right <;>
        simp [decoderDescription, runConfig, stepConfig,
          lookupTransition, Matches, transition, tapeAtCells,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          Tape.moveRight, List.replicate_succ]
  | succ gap ih =>
      rw [show Nat.succ gap + 2 = 1 + (gap + 2) by lia]
      rw [runConfig_add]
      have hstep :
          decoderDescription.runConfig 1
              { state := 8
                tape := Tape.move Direction.left
                  (tapeAtCells
                    (List.append
                      (List.replicate (Nat.succ gap)
                        (none : Option Bool))
                      (some anchor :: base))
                    (none :: none :: right)) } =
            { state := 8
              tape := Tape.move Direction.left
                (tapeAtCells
                  (List.append
                    (List.replicate gap (none : Option Bool))
                    (some anchor :: base))
                  (none :: none :: none :: right)) } := by
        cases anchor <;> cases base <;> cases right <;>
          simp [decoderDescription, runConfig, stepConfig,
            lookupTransition, Matches, transition, tapeAtCells,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft,
            List.replicate_succ]
      rw [hstep]
      rw [ih (none :: right)]
      have hright :
          List.append
              (List.replicate (gap + 1) (none : Option Bool))
              (none :: right) =
            List.append
              (List.replicate (Nat.succ gap + 1) (none : Option Bool))
              right := by
        rw [replicate_none_append_none_cons]
        rw [show Nat.succ gap + 1 = (gap + 1) + 1 by lia]
        rw [List.replicate_succ]
        rfl
      rw [hright]

private theorem decoderDescription_run_return_emit_true
    (gap : Nat) (anchor : Bool)
    (base right : List (Option Bool)) :
    decoderDescription.runConfig (gap + 2)
        { state := 9
          tape := Tape.move Direction.left
            (tapeAtCells
              (List.append
                (List.replicate gap (none : Option Bool))
                (some anchor :: base))
              (none :: none :: right)) } =
      { state := 0
        tape := tapeAtCells (some true :: some anchor :: base)
          (List.append
            (List.replicate (gap + 1) (none : Option Bool)) right) } := by
  induction gap generalizing right with
  | zero =>
      cases anchor <;> cases base <;> cases right <;>
        simp [decoderDescription, runConfig, stepConfig,
          lookupTransition, Matches, transition, tapeAtCells,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          Tape.moveRight, List.replicate_succ]
  | succ gap ih =>
      rw [show Nat.succ gap + 2 = 1 + (gap + 2) by lia]
      rw [runConfig_add]
      have hstep :
          decoderDescription.runConfig 1
              { state := 9
                tape := Tape.move Direction.left
                  (tapeAtCells
                    (List.append
                      (List.replicate (Nat.succ gap)
                        (none : Option Bool))
                      (some anchor :: base))
                    (none :: none :: right)) } =
            { state := 9
              tape := Tape.move Direction.left
                (tapeAtCells
                  (List.append
                    (List.replicate gap (none : Option Bool))
                    (some anchor :: base))
                  (none :: none :: none :: right)) } := by
        cases anchor <;> cases base <;> cases right <;>
          simp [decoderDescription, runConfig, stepConfig,
            lookupTransition, Matches, transition, tapeAtCells,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft,
            List.replicate_succ]
      rw [hstep]
      rw [ih (none :: right)]
      have hright :
          List.append
              (List.replicate (gap + 1) (none : Option Bool))
              (none :: right) =
            List.append
              (List.replicate (Nat.succ gap + 1) (none : Option Bool))
              right := by
        rw [replicate_none_append_none_cons]
        rw [show Nat.succ gap + 1 = (gap + 1) + 1 by lia]
        rw [List.replicate_succ]
        rfl
      rw [hright]

private theorem decoderDescription_run_pair_none
    (gap : Nat) (anchor : Bool)
    (base right : List (Option Bool)) :
    decoderDescription.runConfig (2 * gap + 6)
        { state := 0
          tape := tapeAtCells
            (List.append
              (List.replicate gap (none : Option Bool))
              (some anchor :: base))
            (some false :: some false :: right) } =
      { state := 0
        tape := tapeAtCells
          (List.append
            (List.replicate (gap + 2) (none : Option Bool))
            (some anchor :: base)) right } := by
  rw [show 2 * gap + 6 = 3 + ((gap + 1) + (gap + 2)) by lia]
  rw [runConfig_add]
  have hdecode :
      decoderDescription.runConfig 3
          { state := 0
            tape := tapeAtCells
              (List.append
                (List.replicate gap (none : Option Bool))
                (some anchor :: base))
              (some false :: some false :: right) } =
        { state := 7
          tape := Tape.move Direction.left
            (tapeAtCells
              (List.append
                (List.replicate gap (none : Option Bool))
                (some anchor :: base))
              (none :: none :: right)) } := by
    cases anchor <;> cases base <;> cases right <;>
      simp [decoderDescription, runConfig, stepConfig,
        lookupTransition, Matches, transition, tapeAtCells,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft,
        Tape.moveRight]
  rw [hdecode]
  rw [runConfig_add]
  rw [decoderDescription_run_return_no_emit]
  exact decoderDescription_run_seek_blanks (gap + 2)
    (some anchor :: base) right

private theorem decoderDescription_run_pair_false
    (gap : Nat) (anchor : Bool)
    (base right : List (Option Bool)) :
    decoderDescription.runConfig (2 * gap + 6)
        { state := 0
          tape := tapeAtCells
            (List.append
              (List.replicate gap (none : Option Bool))
              (some anchor :: base))
            (some false :: some true :: right) } =
      { state := 0
        tape := tapeAtCells
          (List.append
            (List.replicate (gap + 1) (none : Option Bool))
            (some false :: some anchor :: base)) right } := by
  rw [show 2 * gap + 6 = 3 + ((gap + 2) + (gap + 1)) by lia]
  rw [runConfig_add]
  have hdecode :
      decoderDescription.runConfig 3
          { state := 0
            tape := tapeAtCells
              (List.append
                (List.replicate gap (none : Option Bool))
                (some anchor :: base))
              (some false :: some true :: right) } =
        { state := 8
          tape := Tape.move Direction.left
            (tapeAtCells
              (List.append
                (List.replicate gap (none : Option Bool))
                (some anchor :: base))
              (none :: none :: right)) } := by
    cases anchor <;> cases base <;> cases right <;>
      simp [decoderDescription, runConfig, stepConfig,
        lookupTransition, Matches, transition, tapeAtCells,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft,
        Tape.moveRight]
  rw [hdecode]
  rw [runConfig_add]
  rw [decoderDescription_run_return_emit_false]
  exact decoderDescription_run_seek_blanks (gap + 1)
    (some false :: some anchor :: base) right

private theorem decoderDescription_run_pair_true
    (gap : Nat) (anchor : Bool)
    (base right : List (Option Bool)) :
    decoderDescription.runConfig (2 * gap + 6)
        { state := 0
          tape := tapeAtCells
            (List.append
              (List.replicate gap (none : Option Bool))
              (some anchor :: base))
            (some true :: some false :: right) } =
      { state := 0
        tape := tapeAtCells
          (List.append
            (List.replicate (gap + 1) (none : Option Bool))
            (some true :: some anchor :: base)) right } := by
  rw [show 2 * gap + 6 = 3 + ((gap + 2) + (gap + 1)) by lia]
  rw [runConfig_add]
  have hdecode :
      decoderDescription.runConfig 3
          { state := 0
            tape := tapeAtCells
              (List.append
                (List.replicate gap (none : Option Bool))
                (some anchor :: base))
              (some true :: some false :: right) } =
        { state := 9
          tape := Tape.move Direction.left
            (tapeAtCells
              (List.append
                (List.replicate gap (none : Option Bool))
                (some anchor :: base))
              (none :: none :: right)) } := by
    cases anchor <;> cases base <;> cases right <;>
      simp [decoderDescription, runConfig, stepConfig,
        lookupTransition, Matches, transition, tapeAtCells,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft,
        Tape.moveRight]
  rw [hdecode]
  rw [runConfig_add]
  rw [decoderDescription_run_return_emit_true]
  exact decoderDescription_run_seek_blanks (gap + 1)
    (some true :: some anchor :: base) right

private theorem decoderDescription_run_end_sentinel
    (left : List (Option Bool)) :
    decoderDescription.runConfig 3
        { state := 0
          tape := tapeAtCells left [some false] } =
      { state := decoderDescription.halt
        tape := tapeAtCells (none :: left) [] } := by
  cases left <;>
    simp [decoderDescription, runConfig, stepConfig,
      lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

def decodedLogicalCells (cells : List (Option Bool)) : Word Bool :=
  cells.filterMap (fun cell => cell)

def decoderSourceTapeRev
    (outputRev : Word Bool) (gap : Nat)
    (cells : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append
      (List.replicate gap (none : Option Bool))
      (outputRev.map some))
    (List.append ((logicalCellListBits cells).map some) [some false])

def decoderHaltTapeRev
    (outputRev : Word Bool) (gap : Nat) : Tape Bool :=
  tapeAtCells
    (none ::
      List.append
        (List.replicate gap (none : Option Bool))
        (outputRev.map some))
    []

def decoderRunSteps : Nat -> List (Option Bool) -> Nat
  | _, [] => 3
  | gap, none :: rest =>
      2 * gap + 6 + decoderRunSteps (gap + 2) rest
  | gap, some _ :: rest =>
      2 * gap + 6 + decoderRunSteps (gap + 1) rest

private theorem decoderDescription_run_rev
    (cells : List (Option Bool)) (gap : Nat)
    (anchor : Bool) (base : Word Bool) :
    decoderDescription.runConfig (decoderRunSteps gap cells)
        { state := 0
          tape := decoderSourceTapeRev (anchor :: base) gap cells } =
      { state := decoderDescription.halt
        tape := decoderHaltTapeRev
          (List.append (decodedLogicalCells cells).reverse (anchor :: base))
          (decoderFinalGap gap cells) } := by
  induction cells generalizing gap anchor base with
  | nil =>
      exact decoderDescription_run_end_sentinel
        (List.append
          (List.replicate gap (none : Option Bool))
          ((anchor :: base).map some))
  | cons cell rest ih =>
      cases cell with
      | none =>
          rw [decoderRunSteps]
          rw [runConfig_add]
          change
            decoderDescription.runConfig (decoderRunSteps (gap + 2) rest)
                (decoderDescription.runConfig (2 * gap + 6)
                  { state := 0
                    tape := tapeAtCells
                      (List.append
                        (List.replicate gap (none : Option Bool))
                        (some anchor :: base.map some))
                      (some false :: some false ::
                        List.append
                          ((logicalCellListBits rest).map some)
                          [some false]) }) =
              { state := decoderDescription.halt
                tape := decoderHaltTapeRev
                  (List.append
                    (decodedLogicalCells (none :: rest)).reverse
                    (anchor :: base))
                  (decoderFinalGap gap (none :: rest)) }
          rw [decoderDescription_run_pair_none]
          simpa [decoderSourceTapeRev, decoderHaltTapeRev,
            decodedLogicalCells, decoderFinalGap] using
            ih (gap + 2) anchor base
      | some bit =>
          cases bit with
          | false =>
              rw [decoderRunSteps]
              rw [runConfig_add]
              change
                decoderDescription.runConfig (decoderRunSteps (gap + 1) rest)
                    (decoderDescription.runConfig (2 * gap + 6)
                      { state := 0
                        tape := tapeAtCells
                          (List.append
                            (List.replicate gap (none : Option Bool))
                            (some anchor :: base.map some))
                          (some false :: some true ::
                            List.append
                              ((logicalCellListBits rest).map some)
                              [some false]) }) =
                  { state := decoderDescription.halt
                    tape := decoderHaltTapeRev
                      (List.append
                        (decodedLogicalCells (some false :: rest)).reverse
                        (anchor :: base))
                      (decoderFinalGap gap (some false :: rest)) }
              rw [decoderDescription_run_pair_false]
              simpa [decoderSourceTapeRev, decoderHaltTapeRev,
                decodedLogicalCells, decoderFinalGap,
                List.reverse_cons, List.append_assoc] using
                ih (gap + 1) false (anchor :: base)
          | true =>
              rw [decoderRunSteps]
              rw [runConfig_add]
              change
                decoderDescription.runConfig (decoderRunSteps (gap + 1) rest)
                    (decoderDescription.runConfig (2 * gap + 6)
                      { state := 0
                        tape := tapeAtCells
                          (List.append
                            (List.replicate gap (none : Option Bool))
                            (some anchor :: base.map some))
                          (some true :: some false ::
                            List.append
                              ((logicalCellListBits rest).map some)
                              [some false]) }) =
                  { state := decoderDescription.halt
                    tape := decoderHaltTapeRev
                      (List.append
                        (decodedLogicalCells (some true :: rest)).reverse
                        (anchor :: base))
                      (decoderFinalGap gap (some true :: rest)) }
              rw [decoderDescription_run_pair_true]
              simpa [decoderSourceTapeRev, decoderHaltTapeRev,
                decodedLogicalCells, decoderFinalGap,
                List.reverse_cons, List.append_assoc] using
                ih (gap + 1) true (anchor :: base)

theorem decoderDescription_run
    (outputFirst : Bool) (outputRest : Word Bool)
    (gap : Nat) (cells : List (Option Bool)) :
    decoderDescription.runConfig (decoderRunSteps gap cells)
        { state := decoderDescription.start
          tape := decoderSourceTape (outputFirst :: outputRest) gap cells } =
      { state := decoderDescription.halt
        tape := decoderHaltTape
          (List.append (outputFirst :: outputRest)
            (decodedLogicalCells cells))
          (decoderFinalGap gap cells) } := by
  cases hbackward : (outputFirst :: outputRest).reverse with
  | nil =>
      simp at hbackward
  | cons anchor base =>
      have hforward : (anchor :: base).reverse = outputFirst :: outputRest := by
        rw [← hbackward]
        simp
      have htail :
          some anchor :: base.map some =
            outputRest.reverse.map some ++ [some outputFirst] := by
        have hmapped := congrArg (List.map some) hbackward.symm
        simpa [List.reverse_cons, List.map_append] using hmapped
      have hrun := decoderDescription_run_rev cells gap anchor base
      simpa [decoderDescription, decoderSourceTape,
        decoderSourceTapeRev, decoderHaltTape, decoderHaltTapeRev,
        List.reverse_append, hbackward, hforward, htail] using hrun

theorem decoderDescription_haltsFromTape
    (outputFirst : Bool) (outputRest : Word Bool)
    (gap : Nat) (cells : List (Option Bool)) :
    decoderDescription.HaltsFromTape
      (decoderSourceTape (outputFirst :: outputRest) gap cells)
      (decoderHaltTape
        (List.append (outputFirst :: outputRest)
          (decodedLogicalCells cells))
        (decoderFinalGap gap cells)) := by
  refine ⟨decoderRunSteps gap cells, ?_⟩
  constructor <;>
    rw [decoderDescription_run]

/-!
# Blank-guarded right padding
The decoder never crosses the guard blank after its false end sentinel, so an unrelated
physical suffix may remain beyond it.
-/
def decoderPaddedSourceTapeRev (outputRev : Word Bool) (gap : Nat) (cells : List (Option Bool))
    (rightPadding : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append
      (List.replicate gap (none : Option Bool))
      (outputRev.map some))
    (List.append ((logicalCellListBits cells).map some)
      (some false :: none :: rightPadding))
def decoderPaddedHaltTapeRev (outputRev : Word Bool) (gap : Nat) (rightPadding : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (none ::
      List.append
        (List.replicate gap (none : Option Bool))
        (outputRev.map some))
    (none :: rightPadding)
private theorem decoderDescription_run_end_sentinel_withRight (left rightPadding : List (Option Bool)) :
    decoderDescription.runConfig 3
        { state := 0
          tape := tapeAtCells left
            (some false :: none :: rightPadding) } =
      { state := decoderDescription.halt
        tape := tapeAtCells (none :: left)
          (none :: rightPadding) } := by
  cases left <;> cases rightPadding <;>
    simp [decoderDescription, runConfig, stepConfig,
      lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
private theorem decoderDescription_run_rev_withRight (cells : List (Option Bool))
    (gap : Nat) (anchor : Bool) (base : Word Bool)
    (rightPadding : List (Option Bool)) :
    decoderDescription.runConfig (decoderRunSteps gap cells)
        { state := 0
          tape :=
            decoderPaddedSourceTapeRev
              (anchor :: base) gap cells rightPadding } =
      { state := decoderDescription.halt
        tape := decoderPaddedHaltTapeRev
          (List.append (decodedLogicalCells cells).reverse (anchor :: base))
          (decoderFinalGap gap cells) rightPadding } := by
  induction cells generalizing gap anchor base with
  | nil =>
      exact decoderDescription_run_end_sentinel_withRight
        (List.append
          (List.replicate gap (none : Option Bool))
          ((anchor :: base).map some))
        rightPadding
  | cons cell rest ih =>
      cases cell with
      | none =>
          rw [decoderRunSteps]
          rw [runConfig_add]
          change
            decoderDescription.runConfig (decoderRunSteps (gap + 2) rest)
                (decoderDescription.runConfig (2 * gap + 6)
                  { state := 0
                    tape := tapeAtCells
                      (List.append
                        (List.replicate gap (none : Option Bool))
                        (some anchor :: base.map some))
                      (some false :: some false ::
                        List.append
                          ((logicalCellListBits rest).map some)
                          (some false :: none :: rightPadding)) }) =
              { state := decoderDescription.halt
                tape := decoderPaddedHaltTapeRev
                  (List.append
                    (decodedLogicalCells (none :: rest)).reverse
                    (anchor :: base))
                  (decoderFinalGap gap (none :: rest)) rightPadding }
          rw [decoderDescription_run_pair_none]
          simpa [decoderPaddedSourceTapeRev,
            decoderPaddedHaltTapeRev, decodedLogicalCells,
            decoderFinalGap] using
            ih (gap + 2) anchor base
      | some bit =>
          cases bit with
          | false =>
              rw [decoderRunSteps]
              rw [runConfig_add]
              change
                decoderDescription.runConfig (decoderRunSteps (gap + 1) rest)
                    (decoderDescription.runConfig (2 * gap + 6)
                      { state := 0
                        tape := tapeAtCells
                          (List.append
                            (List.replicate gap (none : Option Bool))
                            (some anchor :: base.map some))
                          (some false :: some true ::
                            List.append
                              ((logicalCellListBits rest).map some)
                              (some false :: none :: rightPadding)) }) =
                  { state := decoderDescription.halt
                    tape := decoderPaddedHaltTapeRev
                      (List.append
                        (decodedLogicalCells (some false :: rest)).reverse
                        (anchor :: base))
                      (decoderFinalGap gap (some false :: rest))
                      rightPadding }
              rw [decoderDescription_run_pair_false]
              simpa [decoderPaddedSourceTapeRev,
                decoderPaddedHaltTapeRev, decodedLogicalCells,
                decoderFinalGap, List.reverse_cons,
                List.append_assoc] using
                ih (gap + 1) false (anchor :: base)
          | true =>
              rw [decoderRunSteps]
              rw [runConfig_add]
              change
                decoderDescription.runConfig (decoderRunSteps (gap + 1) rest)
                    (decoderDescription.runConfig (2 * gap + 6)
                      { state := 0
                        tape := tapeAtCells
                          (List.append
                            (List.replicate gap (none : Option Bool))
                            (some anchor :: base.map some))
                          (some true :: some false ::
                            List.append
                              ((logicalCellListBits rest).map some)
                              (some false :: none :: rightPadding)) }) =
                  { state := decoderDescription.halt
                    tape := decoderPaddedHaltTapeRev
                      (List.append
                        (decodedLogicalCells (some true :: rest)).reverse
                        (anchor :: base))
                      (decoderFinalGap gap (some true :: rest))
                      rightPadding }
              rw [decoderDescription_run_pair_true]
              simpa [decoderPaddedSourceTapeRev,
                decoderPaddedHaltTapeRev, decodedLogicalCells,
                decoderFinalGap, List.reverse_cons,
                List.append_assoc] using
                ih (gap + 1) true (anchor :: base)
def decoderPaddedSourceTape (outputPrefix : Word Bool) (gap : Nat) (cells : List (Option Bool))
    (rightPadding : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append
      (List.replicate gap (none : Option Bool))
      (outputPrefix.reverse.map some))
    (List.append ((logicalCellListBits cells).map some)
      (some false :: none :: rightPadding))
def decoderPaddedHaltTape (outputPrefix : Word Bool) (gap : Nat) (rightPadding : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (none ::
      List.append
        (List.replicate gap (none : Option Bool))
        (outputPrefix.reverse.map some))
    (none :: rightPadding)
theorem decoderDescription_haltsFromTape_withRight (outputFirst : Bool)
    (outputRest : Word Bool) (gap : Nat) (cells : List (Option Bool))
    (rightPadding : List (Option Bool)) :
    decoderDescription.HaltsFromTape
      (decoderPaddedSourceTape
        (outputFirst :: outputRest) gap cells rightPadding)
      (decoderPaddedHaltTape
        (List.append (outputFirst :: outputRest)
          (decodedLogicalCells cells))
        (decoderFinalGap gap cells) rightPadding) := by
  cases hbackward : (outputFirst :: outputRest).reverse with
  | nil =>
      simp at hbackward
  | cons anchor base =>
      have hforward :
          (anchor :: base).reverse = outputFirst :: outputRest := by
        rw [← hbackward]
        simp
      have htail :
          some anchor :: base.map some =
            outputRest.reverse.map some ++ [some outputFirst] := by
        have hmapped := congrArg (List.map some) hbackward.symm
        simpa [List.reverse_cons, List.map_append] using hmapped
      refine ⟨decoderRunSteps gap cells, ?_⟩
      have hrun := decoderDescription_run_rev_withRight
        cells gap anchor base rightPadding
      constructor
      · simpa [decoderDescription, decoderPaddedSourceTape,
          decoderPaddedSourceTapeRev, decoderPaddedHaltTape,
          decoderPaddedHaltTapeRev, List.reverse_append,
          hbackward, hforward, htail] using
          congrArg (fun c => c.state) hrun
      · simpa [decoderDescription, decoderPaddedSourceTape,
          decoderPaddedSourceTapeRev, decoderPaddedHaltTape,
          decoderPaddedHaltTapeRev, List.reverse_append,
          hbackward, hforward, htail] using
          congrArg (fun c => c.tape) hrun

theorem decoderDescription_haltsFrom_parserTargetTape
    (metadataFirst : Bool) (metadataRest bits : Word Bool)
    (gap : Nat) :
    decoderDescription.HaltsFromTape
      (parserTargetTape (metadataFirst :: metadataRest) gap
        (remainingEndpointBits bits))
      (decoderHaltTape
        (List.append (metadataFirst :: metadataRest) bits)
        (decoderFinalGap gap (remainingEndpointCells bits))) := by
  simpa [parserTargetTape, decoderSourceTape, remainingEndpointBits,
    decodedLogicalCells, remainingEndpointCells_filterMap] using
    decoderDescription_haltsFromTape metadataFirst metadataRest gap
      (remainingEndpointCells bits)

end Tape2Projector
end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC

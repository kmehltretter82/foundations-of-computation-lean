import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.GuardedEgress.RawPairMarker
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.SentinelGapCompactor
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.LengthCursorLoop

namespace FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
namespace GuardedEgress.RightLengthCopy

open Languages MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open GuardedEgress.RawPairQuoter
open GuardedEgress.RawPairDecoder
open DovetailInitialLayoutInitializer.StageInputMarkedScanner
open CommonGround.FiniteTransducers.CountWindowRawSourceEncoder.RawBoundaryRightEdgeEmitter
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.Tape2Projector

/-!
The preserved `0111` head-token sentinel is rewritten to the unary `done`
token.  On every cycle that `done` token moves right across one `01xy` cell:
its old position becomes `tick`, its new position becomes `done`, and the
crossed cell is appended after a blank separator.  The separator makes the
unprocessed and copied cell blocks locally distinguishable.  A subsequent
single-gap compaction removes it.
-/

def scanState : Bool -> Bool -> Nat
  | false, false => 18
  | false, true => 19
  | true, false => 20
  | true, true => 21

def scanCopiedState : Bool -> Bool -> Nat
  | false, false => 22
  | false, true => 23
  | true, false => 24
  | true, true => 21

def writeOneState : Bool -> Bool -> Nat
  | false, false => 25
  | false, true => 26
  | true, false => 27
  | true, true => 21

def writeXState : Bool -> Bool -> Nat
  | false, false => 28
  | false, true => 29
  | true, false => 30
  | true, true => 21

def writeYState : Bool -> Bool -> Nat
  | false, false => 31
  | false, true => 32
  | true, false => 33
  | true, true => 21

def description : MachineDescription where
  stateCount := 44
  start := 1
  halt := 0
  transitions :=
    [ transition 1 none none Direction.right 1
    , transition 1 (some false) (some false) Direction.right 2
    , transition 2 (some true) (some false) Direction.right 3
    , transition 3 (some true) (some true) Direction.right 4
    , transition 4 (some true) (some true) Direction.left 5
    , transition 5 (some true) (some true) Direction.left 6
    , transition 6 (some false) (some false) Direction.left 7

    , transition 7 (some false) (some false) Direction.right 8
    , transition 8 (some false) (some false) Direction.right 9
    , transition 9 (some true) (some true) Direction.right 10
    , transition 10 (some true) (some true) Direction.right 11
    , transition 11 none none Direction.right 0
    , transition 11 (some false) (some false) Direction.left 12
    , transition 12 (some true) (some false) Direction.right 13
    , transition 13 (some false) (some false) Direction.right 14
    , transition 14 (some true) (some false) Direction.right 15
    , transition 15 (some false) (some true) Direction.right 16
    , transition 15 (some true) (some true) Direction.right 17
    , transition 16 (some false) (some true) Direction.right 18
    , transition 16 (some true) (some true) Direction.right 19
    , transition 17 (some false) (some true) Direction.right 20

    , transition 18 (some false) (some false) Direction.right 18
    , transition 18 (some true) (some true) Direction.right 18
    , transition 19 (some false) (some false) Direction.right 19
    , transition 19 (some true) (some true) Direction.right 19
    , transition 20 (some false) (some false) Direction.right 20
    , transition 20 (some true) (some true) Direction.right 20
    , transition 18 none none Direction.right 22
    , transition 19 none none Direction.right 23
    , transition 20 none none Direction.right 24

    , transition 22 (some false) (some false) Direction.right 22
    , transition 22 (some true) (some true) Direction.right 22
    , transition 23 (some false) (some false) Direction.right 23
    , transition 23 (some true) (some true) Direction.right 23
    , transition 24 (some false) (some false) Direction.right 24
    , transition 24 (some true) (some true) Direction.right 24
    , transition 22 none (some false) Direction.right 25
    , transition 23 none (some false) Direction.right 26
    , transition 24 none (some false) Direction.right 27

    , transition 25 none (some true) Direction.right 28
    , transition 26 none (some true) Direction.right 29
    , transition 27 none (some true) Direction.right 30
    , transition 28 none (some false) Direction.right 31
    , transition 29 none (some false) Direction.right 32
    , transition 30 none (some true) Direction.right 33
    , transition 31 none (some false) Direction.left 34
    , transition 32 none (some true) Direction.left 34
    , transition 33 none (some false) Direction.left 34

    , transition 34 (some false) (some false) Direction.left 34
    , transition 34 (some true) (some true) Direction.left 34
    , transition 34 none none Direction.left 35
    , transition 35 (some false) (some false) Direction.left 36
    , transition 35 (some true) (some true) Direction.left 36
    , transition 36 (some false) (some false) Direction.left 37
    , transition 36 (some true) (some true) Direction.left 37
    , transition 37 (some false) (some false) Direction.left 38
    , transition 37 (some true) (some true) Direction.left 38
    , transition 38 (some false) (some false) Direction.right 39
    , transition 39 (some false) (some false) Direction.left 7
    , transition 39 (some true) (some true) Direction.left 40
    , transition 40 (some false) (some false) Direction.left 41
    , transition 41 (some false) (some false) Direction.left 42
    , transition 41 (some true) (some true) Direction.left 42
    , transition 42 (some false) (some false) Direction.left 43
    , transition 42 (some true) (some true) Direction.left 43
    , transition 43 (some false) (some false) Direction.left 38
    , transition 43 (some true) (some true) Direction.left 38 ]

theorem description_subroutineReady : description.SubroutineReady :=
  machineDescription_subroutineReady_of_transition_checks
    description (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

def markerBits : List Bool := [false, true, true, true]

def tickBits : List Bool :=
  encodeCodeSymbolAsInput MachineCodeSymbol.tick

def doneBits : List Bool :=
  encodeCodeSymbolAsInput MachineCodeSymbol.done

def ticksBits : Nat -> List Bool
  | 0 => []
  | n + 1 => List.append (ticksBits n) tickBits

def cellTokenBits : List (Bool × Bool) -> List Bool
  | [] => []
  | (x, y) :: rest =>
      List.append [false, true, x, y] (cellTokenBits rest)

def validCells (cells : List (Bool × Bool)) : Prop :=
  forall pair, pair ∈ cells -> pair ≠ (true, true)

def gapBaseLeft (base : Word Bool) (gap : Nat) : List (Option Bool) :=
  List.append (List.replicate (gap + 1) (none : Option Bool))
    (base.reverse.map some)

def cycleTape (base : Word Bool) (gap count : Nat)
    (remaining copied : List (Bool × Bool))
    (padding : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append ((ticksBits count).reverse.map some)
      (gapBaseLeft base gap))
    (List.append (doneBits.map some)
      (List.append ((cellTokenBits remaining).map some)
        (none ::
          List.append ((cellTokenBits copied).map some)
            (List.append
              (List.replicate (4 * remaining.length)
                (none : Option Bool))
              (none :: padding)))))

def sourceTape (base : Word Bool) (gap : Nat)
    (cells : List (Bool × Bool))
    (padding : List (Option Bool)) : Tape Bool :=
  tapeAtCells (base.reverse.map some)
    (none ::
      List.append (List.replicate gap (none : Option Bool))
        (List.append (markerBits.map some)
          (List.append ((cellTokenBits cells).map some)
            (none ::
              List.append
                (List.replicate (4 * cells.length)
                  (none : Option Bool))
                (none :: padding)))))

def copiedTargetTape (base : Word Bool) (gap : Nat)
    (cells : List (Bool × Bool))
    (padding : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (none ::
      List.append
        ((List.append (ticksBits cells.length) doneBits).reverse.map some)
        (gapBaseLeft base gap))
    (List.append ((cellTokenBits cells).map some)
      (none :: padding))

@[simp] theorem markerBits_eq : markerBits = [false, true, true, true] := rfl

@[simp] theorem tickBits_eq : tickBits = [false, false, true, false] := by
  simp [tickBits, encodeCodeSymbolAsInput]

@[simp] theorem doneBits_eq : doneBits = [false, false, true, true] := by
  simp [doneBits, encodeCodeSymbolAsInput]

private theorem run_scan_blanks (n : Nat)
    (left right : List (Option Bool)) :
    description.runConfig n
        { state := description.start
          tape := tapeAtCells left
            (List.append (List.replicate n (none : Option Bool)) right) } =
      { state := description.start
        tape := tapeAtCells
          (List.append (List.replicate n (none : Option Bool)) left)
          right } := by
  induction n generalizing left with
  | zero =>
      rfl
  | succ n ih =>
      rw [show n + 1 = 1 + n by lia]
      rw [runConfig_add]
      rw [show List.replicate (1 + n) (none : Option Bool) =
          none :: List.replicate n none by
        rw [show 1 + n = Nat.succ n by lia]
        rfl]
      have hstep :
          description.runConfig 1
              { state := description.start
                tape := tapeAtCells left
                  (none ::
                    List.append (List.replicate n none) right) } =
            { state := description.start
              tape := tapeAtCells (none :: left)
                (List.append (List.replicate n none) right) } := by
        cases hrest : List.append (List.replicate n
            (none : Option Bool)) right <;>
          simp [description, runConfig, stepConfig, lookupTransition,
            Matches, transition, tapeAtCells, Tape.read, Tape.write,
            Tape.move, Tape.moveRight]
      change description.runConfig n
          (description.runConfig 1
            { state := description.start
              tape := tapeAtCells left
                (none ::
                  List.append (List.replicate n none) right) }) =
        { state := description.start
          tape := tapeAtCells
            (none ::
              List.append (List.replicate n none) left) right }
      rw [hstep]
      rw [ih (none :: left)]
      rw [replicate_none_append_none_cons]

private theorem run_rewrite_marker
    (left right : List (Option Bool)) :
    description.runConfig 6
        { state := description.start
          tape := tapeAtCells left
            (List.append (markerBits.map some) right) } =
      { state := 7
        tape := tapeAtCells left
          (List.append (doneBits.map some) right) } := by
  change description.runConfig 6
      { state := description.start
        tape := tapeAtCells left
          (some false :: some true :: some true :: some true :: right) } =
    { state := 7
      tape := tapeAtCells left
        (some false :: some false :: some true :: some true :: right) }
  simp [description, runConfig, stepConfig,
    lookupTransition, Matches, transition, tapeAtCells, Tape.read,
    Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

private theorem source_run_to_cycle
    (base : Word Bool) (gap : Nat)
    (cells : List (Bool × Bool))
    (padding : List (Option Bool)) :
    description.runConfig (gap + 1 + 6)
        { state := description.start
          tape := sourceTape base gap cells padding } =
      { state := 7
        tape := cycleTape base gap 0 cells [] padding } := by
  rw [show gap + 1 + 6 = (gap + 1) + 6 by rfl]
  rw [runConfig_add]
  unfold sourceTape
  have hscan := run_scan_blanks (gap + 1)
      (base.reverse.map some)
      (List.append (markerBits.map some)
        (List.append ((cellTokenBits cells).map some)
          (none ::
            List.append
              (List.replicate (4 * cells.length) (none : Option Bool))
              (none :: padding))))
  rw [show none :: List.append (List.replicate gap
          (none : Option Bool))
        (List.append (markerBits.map some)
          (List.append ((cellTokenBits cells).map some)
            (none ::
              List.append
                (List.replicate (4 * cells.length) none)
                (none :: padding)))) =
      List.append (List.replicate (gap + 1) none)
        (List.append (markerBits.map some)
          (List.append ((cellTokenBits cells).map some)
            (none ::
              List.append
                (List.replicate (4 * cells.length) none)
                (none :: padding)))) by
    rw [show gap + 1 = Nat.succ gap by lia]
    rfl]
  rw [hscan]
  rw [run_rewrite_marker]
  simp [cycleTape, ticksBits, gapBaseLeft, cellTokenBits]

private theorem run_select_cell_raw
    (x y : Bool) (left right : List (Option Bool))
    (hvalid : (x, y) ≠ (true, true)) :
    description.runConfig 10
        { state := 7
          tape := tapeAtCells left
            (some false :: some false :: some true :: some true ::
              some false :: some true :: some x :: some y :: right) } =
      { state := scanState x y
        tape := tapeAtCells
          (some true :: some true :: some false :: some false ::
            some false :: some true :: some false :: some false :: left)
          right } := by
  cases x <;> cases y
  · cases right <;>
      simp [description, scanState, runConfig, stepConfig,
        lookupTransition, Matches, transition, tapeAtCells, Tape.read,
        Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
  · cases right <;>
      simp [description, scanState, runConfig, stepConfig,
        lookupTransition, Matches, transition, tapeAtCells, Tape.read,
        Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
  · cases right <;>
      simp [description, scanState, runConfig, stepConfig,
        lookupTransition, Matches, transition, tapeAtCells, Tape.read,
        Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
  · exact False.elim (hvalid rfl)

private theorem run_select_cell
    (base : Word Bool) (gap count : Nat)
    (x y : Bool) (remaining copied : List (Bool × Bool))
    (padding : List (Option Bool))
    (hvalid : (x, y) ≠ (true, true)) :
    description.runConfig 10
        { state := 7
          tape := cycleTape base gap count
            ((x, y) :: remaining) copied padding } =
      { state := scanState x y
        tape := tapeAtCells
          (List.append (doneBits.reverse.map some)
            (List.append ((ticksBits (count + 1)).reverse.map some)
              (gapBaseLeft base gap)))
          (List.append ((cellTokenBits remaining).map some)
            (none ::
              List.append ((cellTokenBits copied).map some)
                (List.append
                  (List.replicate (4 * (remaining.length + 1))
                    (none : Option Bool))
                  (none :: padding)))) } := by
  have hrun := run_select_cell_raw x y
      (List.append ((ticksBits count).reverse.map some)
        (gapBaseLeft base gap))
      (List.append ((cellTokenBits remaining).map some)
        (none ::
          List.append ((cellTokenBits copied).map some)
            (List.append
              (List.replicate (4 * (remaining.length + 1))
                (none : Option Bool))
              (none :: padding))))
      hvalid
  simpa [cycleTape, ticksBits, tickBits, doneBits,
    encodeCodeSymbolAsInput, cellTokenBits,
    List.reverse_append, List.map_append, List.append_assoc] using hrun

private theorem run_scan_right
    (x y : Bool) (bits : Word Bool)
    (left right : List (Option Bool))
    (hvalid : (x, y) ≠ (true, true)) :
    description.runConfig bits.length
        { state := scanState x y
          tape := tapeAtCells left
            (List.append (bits.map some) right) } =
      { state := scanState x y
        tape := tapeAtCells
          (List.append (bits.reverse.map some) left) right } := by
  induction bits generalizing left with
  | nil =>
      rfl
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp only [List.length_cons]
        lia]
      rw [runConfig_add]
      change description.runConfig rest.length
          (description.runConfig 1
            { state := scanState x y
              tape := tapeAtCells left
                (some bit :: List.append (rest.map some) right) }) = _
      have hstep :
          description.runConfig 1
              { state := scanState x y
                tape := tapeAtCells left
                  (some bit :: List.append (rest.map some) right) } =
            { state := scanState x y
              tape := tapeAtCells (some bit :: left)
                (List.append (rest.map some) right) } := by
        cases x <;> cases y
        · cases bit <;> cases htail :
              List.append (rest.map some) right <;>
            simp [description, scanState, runConfig, stepConfig,
              lookupTransition, Matches, transition, tapeAtCells,
              Tape.read, Tape.write, Tape.move, Tape.moveRight]
        · cases bit <;> cases htail :
              List.append (rest.map some) right <;>
            simp [description, scanState, runConfig, stepConfig,
              lookupTransition, Matches, transition, tapeAtCells,
              Tape.read, Tape.write, Tape.move, Tape.moveRight]
        · cases bit <;> cases htail :
              List.append (rest.map some) right <;>
            simp [description, scanState, runConfig, stepConfig,
              lookupTransition, Matches, transition, tapeAtCells,
              Tape.read, Tape.write, Tape.move, Tape.moveRight]
        · exact False.elim (hvalid rfl)
      rw [hstep]
      rw [ih (some bit :: left)]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

private theorem run_cross_separator
    (x y : Bool) (left right : List (Option Bool))
    (hvalid : (x, y) ≠ (true, true)) :
    description.runConfig 1
        { state := scanState x y
          tape := tapeAtCells left (none :: right) } =
      { state := scanCopiedState x y
        tape := tapeAtCells (none :: left) right } := by
  cases x <;> cases y
  · cases right <;>
      simp [description, scanState, scanCopiedState, runConfig,
        stepConfig, lookupTransition, Matches, transition, tapeAtCells,
        Tape.read, Tape.write, Tape.move, Tape.moveRight]
  · cases right <;>
      simp [description, scanState, scanCopiedState, runConfig,
        stepConfig, lookupTransition, Matches, transition, tapeAtCells,
        Tape.read, Tape.write, Tape.move, Tape.moveRight]
  · cases right <;>
      simp [description, scanState, scanCopiedState, runConfig,
        stepConfig, lookupTransition, Matches, transition, tapeAtCells,
        Tape.read, Tape.write, Tape.move, Tape.moveRight]
  · exact False.elim (hvalid rfl)

private theorem run_scan_copied
    (x y : Bool) (bits : Word Bool)
    (left right : List (Option Bool))
    (hvalid : (x, y) ≠ (true, true)) :
    description.runConfig bits.length
        { state := scanCopiedState x y
          tape := tapeAtCells left
            (List.append (bits.map some) right) } =
      { state := scanCopiedState x y
        tape := tapeAtCells
          (List.append (bits.reverse.map some) left) right } := by
  induction bits generalizing left with
  | nil =>
      rfl
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp only [List.length_cons]
        lia]
      rw [runConfig_add]
      change description.runConfig rest.length
          (description.runConfig 1
            { state := scanCopiedState x y
              tape := tapeAtCells left
                (some bit :: List.append (rest.map some) right) }) = _
      have hstep :
          description.runConfig 1
              { state := scanCopiedState x y
                tape := tapeAtCells left
                  (some bit :: List.append (rest.map some) right) } =
            { state := scanCopiedState x y
              tape := tapeAtCells (some bit :: left)
                (List.append (rest.map some) right) } := by
        cases x <;> cases y
        · cases bit <;> cases htail :
              List.append (rest.map some) right <;>
            simp [description, scanCopiedState, runConfig, stepConfig,
              lookupTransition, Matches, transition, tapeAtCells,
              Tape.read, Tape.write, Tape.move, Tape.moveRight]
        · cases bit <;> cases htail :
              List.append (rest.map some) right <;>
            simp [description, scanCopiedState, runConfig, stepConfig,
              lookupTransition, Matches, transition, tapeAtCells,
              Tape.read, Tape.write, Tape.move, Tape.moveRight]
        · cases bit <;> cases htail :
              List.append (rest.map some) right <;>
            simp [description, scanCopiedState, runConfig, stepConfig,
              lookupTransition, Matches, transition, tapeAtCells,
              Tape.read, Tape.write, Tape.move, Tape.moveRight]
        · exact False.elim (hvalid rfl)
      rw [hstep]
      rw [ih (some bit :: left)]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

private theorem run_write_copied_cell
    (x y : Bool) (left right : List (Option Bool))
    (hvalid : (x, y) ≠ (true, true)) :
    description.runConfig 4
        { state := scanCopiedState x y
          tape := tapeAtCells left
            (none :: none :: none :: none :: right) } =
      { state := 34
        tape := tapeAtCells
          (some true :: some false :: left)
          (some x :: some y :: right) } := by
  cases x <;> cases y
  · cases right <;>
      simp [description, scanCopiedState, runConfig, stepConfig,
        lookupTransition, Matches, transition, tapeAtCells, Tape.read,
        Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
  · cases right <;>
      simp [description, scanCopiedState, runConfig, stepConfig,
        lookupTransition, Matches, transition, tapeAtCells, Tape.read,
        Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
  · cases right <;>
      simp [description, scanCopiedState, runConfig, stepConfig,
        lookupTransition, Matches, transition, tapeAtCells, Tape.read,
        Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
  · exact False.elim (hvalid rfl)

private theorem run_return_left
    (leftRev : Word Bool) (current : Bool)
    (base right : List (Option Bool)) :
    description.runConfig (leftRev.length + 1)
        { state := 34
          tape := tapeAtCells
            (List.append (leftRev.map some) (none :: base))
            (some current :: right) } =
      { state := 34
        tape := tapeAtCells base
          (none ::
            List.append
              ((List.append leftRev.reverse [current]).map some) right) } := by
  induction leftRev generalizing current right with
  | nil =>
      cases current <;> cases right <;>
        simp [description, runConfig, stepConfig, lookupTransition,
          Matches, transition, tapeAtCells, Tape.read, Tape.write,
          Tape.move, Tape.moveLeft]
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 1 =
          1 + (rest.length + 1) by simp; lia]
      rw [runConfig_add]
      have hstep :
          description.runConfig 1
              { state := 34
                tape := tapeAtCells
                  (some bit ::
                    List.append (rest.map some) (none :: base))
                  (some current :: right) } =
            { state := 34
              tape := tapeAtCells
                (List.append (rest.map some) (none :: base))
                (some bit :: some current :: right) } := by
        cases bit <;> cases current <;>
          simp [description, runConfig, stepConfig, lookupTransition,
            Matches, transition, tapeAtCells, Tape.read, Tape.write,
            Tape.move, Tape.moveLeft]
      change description.runConfig (rest.length + 1)
          (description.runConfig 1
            { state := 34
              tape := tapeAtCells
                (some bit ::
                  List.append (rest.map some) (none :: base))
                (some current :: right) }) = _
      rw [hstep]
      rw [ih bit (some current :: right)]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

private theorem run_align_token
    (a b c d : Bool) (left right : List (Option Bool)) :
    description.runConfig 4
        { state := 34
          tape := tapeAtCells
            (some d :: some c :: some b :: some a :: left)
            (none :: right) } =
      { state := 38
        tape := tapeAtCells left
          (some a :: some b :: some c :: some d :: none :: right) } := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [description, runConfig, stepConfig, lookupTransition,
      Matches, transition, tapeAtCells, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft]

private theorem run_skip_cell_before_done
    (x y : Bool)
    (left right : List (Option Bool)) :
    description.runConfig 6
        { state := 38
          tape := tapeAtCells
            (some true :: some true :: some false :: some false :: left)
            (some false :: some true :: some x :: some y :: right) } =
      { state := 38
        tape := tapeAtCells left
          (some false :: some false :: some true :: some true ::
            some false :: some true :: some x :: some y :: right) } := by
  cases x <;> cases y <;>
    simp [description, runConfig, stepConfig, lookupTransition,
      Matches, transition, tapeAtCells, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft, Tape.moveRight]

set_option maxHeartbeats 800000 in
private theorem run_skip_cell_before_cell
    (a b x y : Bool)
    (left right : List (Option Bool)) :
    description.runConfig 6
        { state := 38
          tape := tapeAtCells
            (some b :: some a :: some true :: some false :: left)
            (some false :: some true :: some x :: some y :: right) } =
      { state := 38
        tape := tapeAtCells left
          (some false :: some true :: some a :: some b ::
            some false :: some true :: some x :: some y :: right) } := by
  cases a <;> cases b <;> cases x <;> cases y <;>
    simp [description, runConfig, stepConfig, lookupTransition,
      Matches, transition, tapeAtCells, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft, Tape.moveRight]

private theorem run_detect_done
    (left right : List (Option Bool)) :
    description.runConfig 2
        { state := 38
          tape := tapeAtCells left
            (some false :: some false :: some true :: some true :: right) } =
      { state := 7
        tape := tapeAtCells left
          (some false :: some false :: some true :: some true :: right) } := by
  simp [description, runConfig, stepConfig, lookupTransition,
    Matches, transition, tapeAtCells, Tape.read, Tape.write,
    Tape.move, Tape.moveLeft, Tape.moveRight]

def reverseTokenStack : List (Bool × Bool) -> List (Option Bool)
  | [] => []
  | (x, y) :: rest =>
      some y :: some x :: some true :: some false ::
        reverseTokenStack rest

private theorem reverseTokenStack_append
    (left right : List (Bool × Bool)) :
    reverseTokenStack (List.append left right) =
      List.append (reverseTokenStack left) (reverseTokenStack right) := by
  induction left with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨x, y⟩
      change
        some y :: some x :: some true :: some false ::
            reverseTokenStack (List.append rest right) =
          some y :: some x :: some true :: some false ::
            List.append (reverseTokenStack rest)
              (reverseTokenStack right)
      rw [ih]

private theorem reverseTokenStack_reverse
    (cells : List (Bool × Bool)) :
    reverseTokenStack cells.reverse =
      (cellTokenBits cells).reverse.map some := by
  induction cells with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨x, y⟩
      rw [List.reverse_cons]
      calc
        reverseTokenStack (List.append rest.reverse [(x, y)]) =
            List.append (reverseTokenStack rest.reverse)
              (reverseTokenStack [(x, y)]) :=
          reverseTokenStack_append rest.reverse [(x, y)]
        _ = (cellTokenBits ((x, y) :: rest)).reverse.map some := by
          simp [reverseTokenStack, cellTokenBits, ih,
            List.map_append, List.append_assoc]

private theorem cellTokenBits_append
    (left right : List (Bool × Bool)) :
    cellTokenBits (List.append left right) =
      List.append (cellTokenBits left) (cellTokenBits right) := by
  induction left with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨x, y⟩
      change
        false :: true :: x :: y ::
            cellTokenBits (List.append rest right) =
          false :: true :: x :: y ::
            List.append (cellTokenBits rest) (cellTokenBits right)
      rw [ih]

def backSourceTape (revCells : List (Bool × Bool))
    (baseLeft : List (Option Bool))
    (after : List (Option Bool)) : Tape Bool :=
  match revCells with
  | [] =>
      tapeAtCells baseLeft (List.append (doneBits.map some) after)
  | (x, y) :: rest =>
      tapeAtCells
        (List.append (reverseTokenStack rest)
          (List.append (doneBits.reverse.map some) baseLeft))
        (some false :: some true :: some x :: some y :: after)

private theorem run_skip_to_next
    (pair : Bool × Bool) (rest : List (Bool × Bool))
    (baseLeft after : List (Option Bool)) :
    description.runConfig 6
        { state := 38
          tape := backSourceTape (pair :: rest) baseLeft after } =
      { state := 38
        tape := backSourceTape rest baseLeft
          (List.append ([false, true, pair.1, pair.2].map some) after) } := by
  rcases pair with ⟨x, y⟩
  cases rest with
  | nil =>
      simpa [backSourceTape, reverseTokenStack, doneBits,
        encodeCodeSymbolAsInput, List.append_assoc] using
        run_skip_cell_before_done x y baseLeft after
  | cons next more =>
      rcases next with ⟨a, b⟩
      simpa [backSourceTape, reverseTokenStack, List.append_assoc] using
        run_skip_cell_before_cell a b x y
          (List.append (reverseTokenStack more)
            (List.append (doneBits.reverse.map some) baseLeft)) after

private theorem run_back_rev
    (revCells : List (Bool × Bool))
    (baseLeft after : List (Option Bool)) :
    description.runConfig (6 * revCells.length + 2)
        { state := 38
          tape := backSourceTape revCells baseLeft after } =
      { state := 7
        tape := tapeAtCells baseLeft
          (List.append (doneBits.map some)
            (List.append
              ((cellTokenBits revCells.reverse).map some) after)) } := by
  induction revCells generalizing after with
  | nil =>
      simpa [backSourceTape, cellTokenBits] using
        run_detect_done baseLeft after
  | cons pair rest ih =>
      rw [show 6 * (pair :: rest).length + 2 =
          6 + (6 * rest.length + 2) by simp; lia]
      rw [runConfig_add]
      rw [run_skip_to_next]
      rw [ih]
      rcases pair with ⟨x, y⟩
      simp only [List.reverse_cons]
      have hbits :
          cellTokenBits (List.append rest.reverse [(x, y)]) =
            List.append (cellTokenBits rest.reverse)
              [false, true, x, y] := by
        simpa [cellTokenBits] using
          cellTokenBits_append rest.reverse [(x, y)]
      let wrap : List Bool -> Configuration := fun bits =>
        { state := 7
          tape := tapeAtCells baseLeft
            (List.append (doneBits.map some)
              (List.append (bits.map some) after)) }
      simpa [wrap, List.map_append, List.append_assoc] using
        (congrArg wrap hbits).symm

private theorem run_align_to_backSource
    (revCells : List (Bool × Bool))
    (baseLeft after : List (Option Bool)) :
    description.runConfig 4
        { state := 34
          tape := tapeAtCells
            (List.append (reverseTokenStack revCells)
              (List.append (doneBits.reverse.map some) baseLeft))
            (none :: after) } =
      { state := 38
        tape := backSourceTape revCells baseLeft (none :: after) } := by
  cases revCells with
  | nil =>
      simpa [backSourceTape, reverseTokenStack, doneBits,
        encodeCodeSymbolAsInput, List.append_assoc] using
        run_align_token false false true true baseLeft after
  | cons pair rest =>
      rcases pair with ⟨x, y⟩
      simpa [backSourceTape, reverseTokenStack,
        List.append_assoc] using
        run_align_token false true x y
          (List.append (reverseTokenStack rest)
            (List.append (doneBits.reverse.map some) baseLeft)) after

private theorem run_back_to_done
    (cells : List (Bool × Bool))
    (baseLeft after : List (Option Bool)) :
    description.runConfig (6 * cells.length + 6)
        { state := 34
          tape := tapeAtCells
            (List.append ((cellTokenBits cells).reverse.map some)
              (List.append (doneBits.reverse.map some) baseLeft))
            (none :: after) } =
      { state := 7
        tape := tapeAtCells baseLeft
          (List.append (doneBits.map some)
            (List.append ((cellTokenBits cells).map some)
              (none :: after))) } := by
  rw [show 6 * cells.length + 6 = 4 + (6 * cells.reverse.length + 2) by
    simp
    lia]
  rw [runConfig_add]
  rw [← reverseTokenStack_reverse cells]
  rw [run_align_to_backSource]
  rw [run_back_rev]
  simp

@[simp] theorem cellTokenBits_length
    (cells : List (Bool × Bool)) :
    (cellTokenBits cells).length = 4 * cells.length := by
  induction cells with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨x, y⟩
      simp [cellTokenBits, ih]
      lia

private theorem run_cycle
    (base : Word Bool) (gap count : Nat)
    (x y : Bool) (remaining copied : List (Bool × Bool))
    (padding : List (Option Bool))
    (hvalid : (x, y) ≠ (true, true)) :
    exists steps : Nat,
      description.runConfig steps
          { state := 7
            tape := cycleTape base gap count
              ((x, y) :: remaining) copied padding } =
        { state := 7
          tape := cycleTape base gap (count + 1)
            remaining (List.append copied [(x, y)]) padding } := by
  let countLeft : List (Option Bool) :=
    List.append (doneBits.reverse.map some)
      (List.append ((ticksBits (count + 1)).reverse.map some)
        (gapBaseLeft base gap))
  let remainingBits : List Bool := cellTokenBits remaining
  let copiedBits : List Bool := cellTokenBits copied
  let copiedNextBits : List Bool :=
    List.append copiedBits [false, true, x, y]
  let scratchTail : List (Option Bool) :=
    List.append
      (List.replicate (4 * remaining.length) (none : Option Bool))
      (none :: padding)
  have hcopiedNext :
      cellTokenBits (List.append copied [(x, y)]) = copiedNextBits := by
    simpa [copiedNextBits, copiedBits, cellTokenBits] using
      cellTokenBits_append copied [(x, y)]
  have hselect :=
    run_select_cell base gap count x y remaining copied padding hvalid
  have hscanRemaining :=
    run_scan_right x y remainingBits countLeft
      (none ::
        List.append (copiedBits.map some)
          (List.append
            (List.replicate (4 * (remaining.length + 1))
              (none : Option Bool))
            (none :: padding))) hvalid
  have hcross :=
    run_cross_separator x y
      (List.append (remainingBits.reverse.map some) countLeft)
      (List.append (copiedBits.map some)
        (List.append
          (List.replicate (4 * (remaining.length + 1))
            (none : Option Bool))
          (none :: padding))) hvalid
  have hscanCopied :=
    run_scan_copied x y copiedBits
      (none ::
        List.append (remainingBits.reverse.map some) countLeft)
      (List.append
        (List.replicate (4 * (remaining.length + 1))
          (none : Option Bool))
        (none :: padding)) hvalid
  have hscratch :
      List.append
          (List.replicate (4 * (remaining.length + 1))
            (none : Option Bool))
          (none :: padding) =
        none :: none :: none :: none ::
          scratchTail := by
    rw [show 4 * (remaining.length + 1) =
        Nat.succ (Nat.succ (Nat.succ (Nat.succ
          (4 * remaining.length)))) by lia]
    simp only [List.replicate_succ, scratchTail]
    rfl
  have hwrite :=
    run_write_copied_cell x y
      (List.append (copiedBits.reverse.map some)
        (none ::
          List.append (remainingBits.reverse.map some) countLeft))
      scratchTail hvalid
  have hreturn :=
    run_return_left
      (List.append [true, false] copiedBits.reverse) x
      (List.append (remainingBits.reverse.map some)
        (List.append (doneBits.reverse.map some)
          (List.append ((ticksBits (count + 1)).reverse.map some)
            (gapBaseLeft base gap))))
      (some y :: scratchTail)
  have hreturnLeft :
      some true :: some false ::
          List.append (copiedBits.reverse.map some)
            (none ::
              List.append (remainingBits.reverse.map some) countLeft) =
        List.append
          ((List.append [true, false] copiedBits.reverse).map some)
          (none ::
            List.append (remainingBits.reverse.map some)
              (List.append (doneBits.reverse.map some)
                (List.append ((ticksBits (count + 1)).reverse.map some)
                  (gapBaseLeft base gap)))) := by
    simp [countLeft]
  have hback :=
    run_back_to_done remaining
      (List.append ((ticksBits (count + 1)).reverse.map some)
        (gapBaseLeft base gap))
      (List.append (copiedNextBits.map some) scratchTail)
  have hbackRight :
      List.append
          ((List.append
            (List.append [true, false] copiedBits.reverse).reverse
            [x]).map some)
          (some y :: scratchTail) =
        List.append (copiedNextBits.map some) scratchTail := by
    simp [copiedNextBits, List.map_append,
      List.append_assoc]
  let cycleSteps : Nat :=
    10 +
      (remainingBits.length +
        (1 +
          (copiedBits.length +
            (4 +
              ((List.append [true, false]
                copiedBits.reverse).length + 1 +
                (6 * remaining.length + 6))))))
  refine ⟨cycleSteps, ?_⟩
  unfold cycleSteps
  rw [runConfig_add]
  rw [hselect]
  change description.runConfig
      (remainingBits.length +
        (1 +
          (copiedBits.length +
            (4 +
              ((List.append [true, false]
                copiedBits.reverse).length + 1 +
                (6 * remaining.length + 6))))))
      { state := scanState x y
        tape := tapeAtCells countLeft
          (List.append (remainingBits.map some)
            (none ::
              List.append (copiedBits.map some)
                (List.append
                  (List.replicate (4 * (remaining.length + 1)) none)
                  (none :: padding)))) } = _
  rw [runConfig_add]
  rw [hscanRemaining]
  rw [runConfig_add]
  rw [hcross]
  rw [runConfig_add]
  rw [hscanCopied]
  rw [runConfig_add]
  rw [hscratch]
  rw [hwrite]
  rw [runConfig_add]
  rw [hreturnLeft]
  rw [hreturn]
  rw [hbackRight]
  simp only [remainingBits]
  rw [hback]
  unfold cycleTape
  rw [hcopiedNext]

private theorem run_finish
    (base : Word Bool) (gap : Nat)
    (cells : List (Bool × Bool))
    (padding : List (Option Bool)) :
    description.runConfig 5
        { state := 7
          tape := cycleTape base gap cells.length [] cells padding } =
      { state := description.halt
        tape := copiedTargetTape base gap cells padding } := by
  simp [description, cycleTape, copiedTargetTape, cellTokenBits,
    runConfig, stepConfig, lookupTransition, Matches, transition,
    tapeAtCells, Tape.read, Tape.write, Tape.move,
    Tape.moveRight, List.reverse_append]
  generalize htail :
      ((cellTokenBits cells).map some ++ (none :: padding)) = tail
  cases tail <;> rfl

private theorem run_cycles
    (base : Word Bool) (gap count : Nat)
    (remaining copied : List (Bool × Bool))
    (padding : List (Option Bool))
    (hvalid : validCells remaining) :
    exists steps : Nat,
      description.runConfig steps
          { state := 7
            tape := cycleTape base gap count remaining copied padding } =
        { state := 7
          tape := cycleTape base gap (count + remaining.length) []
            (List.append copied remaining) padding } := by
  induction remaining generalizing count copied with
  | nil =>
      refine ⟨0, ?_⟩
      change
        ({ state := 7
           tape := cycleTape base gap count [] copied padding } :
          Configuration) = _
      simp
  | cons pair rest ih =>
      rcases pair with ⟨x, y⟩
      have hxy : (x, y) ≠ (true, true) :=
        hvalid (x, y) (by simp)
      have hrest : validCells rest := by
        intro pair hmem
        exact hvalid pair (by simp [hmem])
      rcases run_cycle base gap count x y rest copied padding hxy with
        ⟨firstSteps, hfirst⟩
      rcases ih (count := count + 1)
          (copied := List.append copied [(x, y)]) hrest with
        ⟨restSteps, hrunRest⟩
      refine ⟨firstSteps + restSteps, ?_⟩
      rw [runConfig_add]
      rw [hfirst]
      rw [hrunRest]
      have hcount :
          count + 1 + rest.length =
            count + ((x, y) :: rest).length := by
        simp
        lia
      have hcopied :
          List.append (List.append copied [(x, y)]) rest =
            List.append copied ((x, y) :: rest) := by
        simp [List.append_assoc]
      rw [hcount, hcopied]

theorem description_haltsFromTape
    (base : Word Bool) (gap : Nat)
    (cells : List (Bool × Bool))
    (padding : List (Option Bool))
    (hvalid : validCells cells) :
    description.HaltsFromTape
      (sourceTape base gap cells padding)
      (copiedTargetTape base gap cells padding) := by
  rcases run_cycles base gap 0 cells [] padding hvalid with
    ⟨cycleSteps, hcycles⟩
  have hcycles' :
      description.runConfig cycleSteps
          { state := 7
            tape := cycleTape base gap 0 cells [] padding } =
        { state := 7
          tape := cycleTape base gap cells.length [] cells padding } := by
    simpa using hcycles
  let totalSteps : Nat :=
    (gap + 1 + 6) + (cycleSteps + 5)
  have hrun :
      description.runConfig totalSteps
          { state := description.start
            tape := sourceTape base gap cells padding } =
        { state := description.halt
          tape := copiedTargetTape base gap cells padding } := by
    unfold totalSteps
    rw [runConfig_add]
    rw [source_run_to_cycle]
    rw [runConfig_add]
    rw [hcycles']
    rw [run_finish]
  refine ⟨totalSteps, ?_, ?_⟩
  · exact congrArg Configuration.state hrun
  · exact congrArg Configuration.tape hrun

def shiftedBaseLeft (base : Word Bool) (gap : Nat)
    (cells : List (Bool × Bool)) : List (Option Bool) :=
  List.append
    ((List.append (ticksBits cells.length) doneBits).reverse.map some)
    (gapBaseLeft base gap)

theorem copiedTargetTape_move_left
    (base : Word Bool) (gap : Nat)
    (cells : List (Bool × Bool))
    (padding : List (Option Bool)) :
    Tape.move Direction.left
        (copiedTargetTape base gap cells padding) =
      leadingBlankLeftShiftSourceTapeWithPadding
        (shiftedBaseLeft base gap cells)
        (cellTokenBits cells) padding := by
  cases cells with
  | nil =>
      simp [copiedTargetTape, shiftedBaseLeft, cellTokenBits,
        leadingBlankLeftShiftSourceTapeWithPadding, tapeAtCells,
        Tape.move, Tape.moveLeft, List.reverse_append]
  | cons pair rest =>
      rcases pair with ⟨x, y⟩
      simp [copiedTargetTape, shiftedBaseLeft, cellTokenBits,
        leadingBlankLeftShiftSourceTapeWithPadding, tapeAtCells,
        Tape.move, Tape.moveLeft, List.reverse_append]

def copyThenLeftShiftDescription : MachineDescription :=
  seqSubroutine description leadingBlankLeftShiftDescription Direction.left

theorem copyThenLeftShiftDescription_subroutineReady :
    copyThenLeftShiftDescription.SubroutineReady :=
  seqSubroutine_subroutineReady
    description_subroutineReady
    leadingBlankLeftShiftDescription_subroutineReady

theorem copyThenLeftShiftDescription_haltsFromTape
    (base : Word Bool) (gap : Nat)
    (cells : List (Bool × Bool))
    (padding : List (Option Bool))
    (hvalid : validCells cells) :
    copyThenLeftShiftDescription.HaltsFromTape
      (sourceTape base gap cells padding)
      (leadingBlankLeftShiftTargetTapeWithPadding
        (shiftedBaseLeft base gap cells)
        (cellTokenBits cells) padding) := by
  exact
    CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      description_subroutineReady
      leadingBlankLeftShiftDescription_subroutineReady
      (description_haltsFromTape base gap cells padding hvalid)
      (copiedTargetTape_move_left base gap cells padding)
      (leadingBlankLeftShiftDescription_haltsFromTape_withPadding
        (shiftedBaseLeft base gap cells) (cellTokenBits cells) padding)

def compactedPayloadBits (cells : List (Bool × Bool)) : Word Bool :=
  List.append
    (List.append (ticksBits cells.length) doneBits)
    (cellTokenBits cells)

theorem compactedPayloadBits_ne_nil
    (cells : List (Bool × Bool)) :
    compactedPayloadBits cells ≠ [] := by
  intro hnil
  have hlength := congrArg List.length hnil
  simp [compactedPayloadBits, doneBits,
    encodeCodeSymbolAsInput] at hlength

theorem leftShiftTarget_eq_gapSource
    (base : Word Bool) (gap : Nat)
    (cells : List (Bool × Bool))
    (rightPadding : List (Option Bool))
    (leftBit current : Bool) (baseRest leftRest : Word Bool)
    (hbase : base.reverse = leftBit :: baseRest)
    (hpayload :
      (compactedPayloadBits cells).reverse = current :: leftRest) :
    leadingBlankLeftShiftTargetTapeWithPadding
        (shiftedBaseLeft base gap cells)
        (cellTokenBits cells) (none :: rightPadding) =
      rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
        (rightBlankLocalGapBaseLeft gap
          ((leftBit :: baseRest).map some))
        current leftRest 2 rightPadding := by
  have hbaseMap := congrArg (List.map some) hbase
  have hpayloadMap := congrArg (List.map some) hpayload
  simp [compactedPayloadBits, List.reverse_append,
    List.map_append, List.append_assoc] at hpayloadMap
  have hpayloadSuffix :=
    congrArg
      (fun bits : List (Option Bool) =>
        List.append bits
          (List.append
            (List.replicate (gap + 1) (none : Option Bool))
            (some leftBit :: baseRest.map some)))
      hpayloadMap
  simp [leadingBlankLeftShiftTargetTapeWithPadding,
    shiftedBaseLeft, gapBaseLeft,
    rightBlankLocalGapCompactorSourceTapeWithBaseAndRight,
    rightBlankLocalGapBaseLeft, tapeAtCells,
    hbaseMap, List.reverse_append]
  have hgap :
      List.replicate (gap + 1) (none : Option Bool) =
        none :: List.replicate gap none := by
    rw [show gap + 1 = Nat.succ gap by lia]
    rfl
  simpa [hgap, List.append_assoc] using hpayloadSuffix

def rightLengthAssemblyDescription : MachineDescription :=
  canonicalSeqDescription
    copyThenLeftShiftDescription sentinelGapCompactorDescription

theorem rightLengthAssemblyDescription_subroutineReady :
    rightLengthAssemblyDescription.SubroutineReady :=
  canonicalSeqDescription_subroutineReady
    copyThenLeftShiftDescription_subroutineReady
    sentinelGapCompactorDescription_subroutineReady

theorem rightLengthAssemblyDescription_haltsFromTape
    (base : Word Bool) (gap : Nat)
    (cells : List (Bool × Bool))
    (rightPaddingTail : List (Option Bool))
    (hbase : base ≠ [])
    (hvalid : validCells cells) :
    rightLengthAssemblyDescription.HaltsFromTape
      (sourceTape base gap cells
        (none :: none :: rightPaddingTail))
      (leadingBlankLeftShiftTargetTapeWithPadding
        (base.reverse.map some) (compactedPayloadBits cells)
        (sentinelGapCompactorFinalPadding gap 2
          (none :: rightPaddingTail))) := by
  cases hbaseRev : base.reverse with
  | nil =>
      exfalso
      have hbase' := hbase
      unfold Word at hbase'
      apply hbase'
      have h := congrArg List.reverse hbaseRev
      simpa using h
  | cons leftBit baseRest =>
      cases hpayloadRev : (compactedPayloadBits cells).reverse with
      | nil =>
          exfalso
          have hpayloadNonempty := compactedPayloadBits_ne_nil cells
          unfold Word at hpayloadNonempty
          apply hpayloadNonempty
          have h := congrArg List.reverse hpayloadRev
          simpa using h
      | cons current leftRest =>
          have hfirst :=
            copyThenLeftShiftDescription_haltsFromTape
              base gap cells (none :: none :: rightPaddingTail) hvalid
          have hsameHead :
              Tape.move Direction.left
                  (Tape.move Direction.right
                    (leadingBlankLeftShiftTargetTapeWithPadding
                      (shiftedBaseLeft base gap cells)
                      (cellTokenBits cells)
                      (none :: none :: rightPaddingTail))) =
                leadingBlankLeftShiftTargetTapeWithPadding
                  (shiftedBaseLeft base gap cells)
                  (cellTokenBits cells)
                  (none :: none :: rightPaddingTail) := by
            simp [leadingBlankLeftShiftTargetTapeWithPadding,
              tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]
          have hsource :=
            leftShiftTarget_eq_gapSource
              base gap cells (none :: rightPaddingTail)
              leftBit current baseRest leftRest hbaseRev hpayloadRev
          have hbridge :
              Tape.move Direction.left
                  (Tape.move Direction.right
                    (leadingBlankLeftShiftTargetTapeWithPadding
                      (shiftedBaseLeft base gap cells)
                      (cellTokenBits cells)
                      (none :: none :: rightPaddingTail))) =
                rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
                  (rightBlankLocalGapBaseLeft gap
                    ((leftBit :: baseRest).map some))
                  current leftRest 2 (none :: rightPaddingTail) := by
            rw [hsameHead]
            exact hsource
          have hpayloadBack :
              (current :: leftRest).reverse =
                compactedPayloadBits cells := by
            have h := congrArg List.reverse hpayloadRev
            simpa using h.symm
          have hlast :=
            sentinelGapCompactorDescription_haltsFromTape_gapBase
              gap (baseRest.map some) leftBit current leftRest 1
              (none :: rightPaddingTail)
          have hlast' :
              sentinelGapCompactorDescription.HaltsFromTape
                (rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
                  (rightBlankLocalGapBaseLeft gap
                    ((leftBit :: baseRest).map some))
                  current leftRest 2 (none :: rightPaddingTail))
                (leadingBlankLeftShiftTargetTapeWithPadding
                  ((leftBit :: baseRest).map some)
                  (compactedPayloadBits cells)
                  (sentinelGapCompactorFinalPadding gap 2
                    (none :: rightPaddingTail))) := by
            simpa [hpayloadBack] using hlast
          exact
            canonicalSeqDescription_haltsFromTape_of_haltsFromTape
              copyThenLeftShiftDescription_subroutineReady
              sentinelGapCompactorDescription_subroutineReady
              hfirst hbridge hlast'

/-!
## Real guarded-egress workspace

The raw-pair decoder leaves both its decoding gap and one blank for every raw
bit before the untouched later-tape suffix.  The right-length copier needs four
blank cells per right logical cell plus three handoff blanks.  The following
lemmas make that reservoir comparison exact and split the concrete rewind
padding into the prefix consumed by this phase and an untouched tail.
-/

theorem expandedCells_length (bits : Word Bool) :
    (expandedCells bits).length = 2 * bits.length := by
  induction bits with
  | nil =>
      rfl
  | cons bit rest ih =>
      simp [expandedCells, expandedCellsForBit, ih]
      lia

theorem decoderFinalGap_add_length_le
    (gap : Nat) (cells : List (Option Bool)) :
    gap + cells.length <= decoderFinalGap gap cells := by
  induction cells generalizing gap with
  | nil =>
      simp [decoderFinalGap]
  | cons cell rest ih =>
      cases cell with
      | none =>
          simp only [decoderFinalGap]
          simp only [List.length_cons]
          have h := ih (gap + 2)
          lia
      | some bit =>
          simp only [decoderFinalGap]
          simp only [List.length_cons]
          have h := ih (gap + 1)
          lia

theorem decoderGap_rawBits_lower_bound (i : Index) :
    2 * (rawBits i).length + 1 <= decoderGap i := by
  cases hraw : rawBits i with
  | nil =>
      exact False.elim (rawBits_ne_nil i hraw)
  | cons bit rest =>
      have hgap :=
        decoderFinalGap_add_length_le 2
          (remainingExpandedCells (rawBits i))
      rw [hraw] at hgap
      simp only [remainingExpandedCells, List.length_cons,
        expandedCells_length] at hgap
      simp only [decoderGap, hraw, List.length_cons,
        remainingExpandedCells]
      exact Nat.le_trans (by lia) hgap

theorem logicalCellBits_length_local (cell : Option Bool) :
    (logicalCellBits cell).length = 2 := by
  cases cell with
  | none =>
      rfl
  | some bit =>
      cases bit <;> rfl

theorem logicalCellListBits_length_local
    (cells : List (Option Bool)) :
    (logicalCellListBits cells).length = 2 * cells.length := by
  induction cells with
  | nil =>
      rfl
  | cons cell rest ih =>
      cases cell with
      | none =>
          simp [logicalCellListBits, logicalCellBits, ih]
          lia
      | some bit =>
          cases bit <;>
            simp [logicalCellListBits, logicalCellBits, ih] <;>
            lia

theorem rawBits_length (i : Index) :
    (rawBits i).length =
      2 * i.finalTape.left.length +
        2 * i.finalTape.right.length + 8 := by
  simp [rawBits, logicalTapeBits, guardLogicalTape,
    logicalCellListBits_length_local, logicalCellBits_length_local]
  lia

theorem rightAssemblyPaddingPrefix_le (i : Index) :
    4 * (guardLogicalTape i.finalTape).right.length + 3 <=
      decoderGap i + 1 + (rawBits i).length := by
  have hgap := decoderGap_rawBits_lower_bound i
  have hraw := rawBits_length i
  simp [guardLogicalTape] at *
  lia

def rightAssemblyPaddingTail (i : Index) : List (Option Bool) :=
  List.append
    (List.replicate
      ((decoderGap i + 1 + (rawBits i).length) -
        (4 * (guardLogicalTape i.finalTape).right.length + 3))
      (none : Option Bool))
    (suffixCells i)

theorem rewindPadding_eq_rightAssemblyPrefix (i : Index) :
    rewindPadding i =
      List.append
        (List.replicate
          (4 * (guardLogicalTape i.finalTape).right.length)
          (none : Option Bool))
        (none :: none :: none :: rightAssemblyPaddingTail i) := by
  let needed := 4 * (guardLogicalTape i.finalTape).right.length + 3
  let rawLength : Nat := (rawBits i).length
  let available := decoderGap i + 1 + rawLength
  have hle : needed <= available := by
    exact rightAssemblyPaddingPrefix_le i
  have havailable :
      available = needed + (available - needed) := by
    lia
  have hthree :
      List.replicate needed (none : Option Bool) =
        List.append
          (List.replicate
            (4 * (guardLogicalTape i.finalTape).right.length) none)
          [none, none, none] := by
    unfold needed
    rw [show 4 * (guardLogicalTape i.finalTape).right.length + 3 =
      4 * (guardLogicalTape i.finalTape).right.length + 3 by rfl]
    simpa [List.replicate_succ] using
      FoC.Computability.list_replicate_add_append
        (none : Option Bool)
        (4 * (guardLogicalTape i.finalTape).right.length) 3 []
  unfold rewindPadding decoderRightPadding rightAssemblyPaddingTail
  change
    List.append
        (List.replicate (decoderGap i + 1) (none : Option Bool))
        (List.append (List.replicate rawLength none) (suffixCells i)) =
      List.append
        (List.replicate
          (4 * (guardLogicalTape i.finalTape).right.length) none)
        (none :: none :: none ::
          List.append
            (List.replicate (available - needed) none)
            (suffixCells i))
  calc
    List.append
        (List.replicate (decoderGap i + 1) (none : Option Bool))
        (List.append (List.replicate rawLength none) (suffixCells i)) =
      List.append (List.replicate available none) (suffixCells i) := by
        unfold available
        exact
          (FoC.Computability.list_replicate_add_append
            (none : Option Bool) (decoderGap i + 1)
            rawLength (suffixCells i)).symm
    _ =
      List.append
        (List.replicate (needed + (available - needed)) none)
        (suffixCells i) := by
        rw [← havailable]
    _ =
      List.append (List.replicate needed none)
        (List.append (List.replicate (available - needed) none)
          (suffixCells i)) := by
        exact
          FoC.Computability.list_replicate_add_append
            (none : Option Bool) needed (available - needed)
            (suffixCells i)
    _ =
      List.append
        (List.replicate
          (4 * (guardLogicalTape i.finalTape).right.length) none)
        (none :: none :: none ::
          List.append
            (List.replicate (available - needed) none)
            (suffixCells i)) := by
        rw [hthree]
        simp [List.append_assoc]

end GuardedEgress.RightLengthCopy
end FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore

import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.GuardedEgress.RawPairMarker
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.LengthCursorLoop

namespace FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
namespace GuardedEgress.ChunkReverseScratch

open Languages MachineDescription
open CommonGround.FiniteTransducers
open RawPairQuoter
open CommonGround.FiniteTransducers.CountWindowRawSourceEncoder.RawBoundaryRightEdgeEmitter

def markerBits : Word Bool := [false, true, true, true]

def returnState : Bool → Bool → Nat
  | false, false => 10
  | false, true => 11
  | true, false => 12
  | true, true => 13

def guardSkipOneState : Bool → Bool → Nat
  | false, false => 14
  | false, true => 15
  | true, false => 16
  | true, true => 13

def guardSkipTwoState : Bool → Bool → Nat
  | false, false => 17
  | false, true => 18
  | true, false => 19
  | true, true => 13

def guardSkipThreeState : Bool → Bool → Nat
  | false, false => 20
  | false, true => 21
  | true, false => 22
  | true, true => 13

def outputScanState : Bool → Bool → Nat
  | false, false => 23
  | false, true => 24
  | true, false => 25
  | true, true => 13

def writeXState : Bool → Bool → Nat
  | false, false => 26
  | false, true => 27
  | true, false => 28
  | true, true => 13

def writeOneState : Bool → Bool → Nat
  | false, false => 29
  | false, true => 30
  | true, false => 31
  | true, true => 13

def writeZeroState : Bool → Bool → Nat
  | false, false => 32
  | false, true => 33
  | true, false => 34
  | true, true => 13

def description : MachineDescription where
  stateCount := 52
  start := 1
  halt := 0
  transitions :=
    [ transition 1 (some false) (some false) Direction.right 2
    , transition 2 (some true) (some true) Direction.right 3
    , transition 3 (some true) (some true) Direction.right 4
    , transition 4 (some true) (some true) Direction.right 5
    , transition 5 none none Direction.right 5
    , transition 5 (some false) none Direction.right 6
    , transition 6 (some true) none Direction.right 7
    , transition 7 (some false) none Direction.right 8
    , transition 7 (some true) none Direction.right 9
    , transition 8 (some false) none Direction.left 10
    , transition 8 (some true) none Direction.left 11
    , transition 9 (some false) none Direction.left 12
    , transition 9 (some true) none Direction.left 47

    , transition 10 none none Direction.left 10
    , transition 11 none none Direction.left 11
    , transition 12 none none Direction.left 12
    , transition 10 (some true) (some true) Direction.left 14
    , transition 11 (some true) (some true) Direction.left 15
    , transition 12 (some true) (some true) Direction.left 16
    , transition 14 (some true) (some true) Direction.left 17
    , transition 15 (some true) (some true) Direction.left 18
    , transition 16 (some true) (some true) Direction.left 19
    , transition 17 (some true) (some true) Direction.left 20
    , transition 18 (some true) (some true) Direction.left 21
    , transition 19 (some true) (some true) Direction.left 22
    , transition 20 (some false) (some false) Direction.left 23
    , transition 21 (some false) (some false) Direction.left 24
    , transition 22 (some false) (some false) Direction.left 25

    , transition 23 (some false) (some false) Direction.left 23
    , transition 23 (some true) (some true) Direction.left 23
    , transition 24 (some false) (some false) Direction.left 24
    , transition 24 (some true) (some true) Direction.left 24
    , transition 25 (some false) (some false) Direction.left 25
    , transition 25 (some true) (some true) Direction.left 25
    , transition 23 none (some false) Direction.left 26
    , transition 24 none (some true) Direction.left 27
    , transition 25 none (some false) Direction.left 28
    , transition 26 none (some false) Direction.left 29
    , transition 27 none (some false) Direction.left 30
    , transition 28 none (some true) Direction.left 31
    , transition 29 none (some true) Direction.left 32
    , transition 30 none (some true) Direction.left 33
    , transition 31 none (some true) Direction.left 34
    , transition 32 none (some false) Direction.right 35
    , transition 33 none (some false) Direction.right 35
    , transition 34 none (some false) Direction.right 35

    , transition 35 (some true) (some true) Direction.right 36
    , transition 36 (some false) (some false) Direction.right 37
    , transition 36 (some true) (some true) Direction.right 37
    , transition 37 (some false) (some false) Direction.right 38
    , transition 37 (some true) (some true) Direction.right 38
    , transition 38 (some false) (some false) Direction.right 39
    , transition 39 (some true) (some true) Direction.right 40
    , transition 40 (some false) (some false) Direction.right 41
    , transition 40 (some true) (some true) Direction.right 42
    , transition 41 (some false) (some false) Direction.right 38
    , transition 41 (some true) (some true) Direction.right 38
    , transition 42 (some false) (some false) Direction.right 38
    , transition 42 (some true) (some true) Direction.left 43
    , transition 43 (some true) (some true) Direction.left 44
    , transition 44 (some true) (some true) Direction.left 45
    , transition 45 (some false) (some false) Direction.left 46
    , transition 46 none none Direction.right 1
    , transition 46 (some false) (some false) Direction.right 1
    , transition 46 (some true) (some true) Direction.right 1

    , transition 47 none none Direction.left 47
    , transition 47 (some true) none Direction.left 48
    , transition 48 (some true) none Direction.left 49
    , transition 49 (some true) none Direction.left 50
    , transition 50 (some false) none Direction.left 51
    , transition 51 none none Direction.right 0
    , transition 51 (some false) (some false) Direction.right 0
    , transition 51 (some true) (some true) Direction.right 0 ]

theorem description_wellFormed : description.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := description.transitions)
      (stateCount := description.stateCount) (by decide)
  · exact transition_deterministic_of_all
      (l := description.transitions) (by decide)

theorem description_haltTransitionFree : description.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := description.transitions) (state := description.halt) (by decide)

theorem description_subroutineReady : description.SubroutineReady :=
  ⟨description_wellFormed, description_haltTransitionFree⟩

private theorem replicate_none_append_none_cons
    (n : Nat) (xs : List (Option Bool)) :
    List.append (List.replicate n (none : Option Bool)) (none :: xs) =
      none :: List.append (List.replicate n (none : Option Bool)) xs := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change
        none ::
            List.append (List.replicate n (none : Option Bool))
              (none :: xs) =
          none :: none ::
            List.append (List.replicate n (none : Option Bool)) xs
      rw [ih]

def loopTape (processed remaining : List (Bool × Bool))
    (right : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append
      ((quotedPairBits processed.reverse).reverse.map some) [none])
    (List.append (markerBits.map some)
      (List.append
        (List.replicate (4 * processed.length) (none : Option Bool))
        (List.append ((quotedPairBits remaining).map some)
          (List.append (markerBits.map some) right))))

def sourceTape (cells : List (Bool × Bool))
    (right : List (Option Bool)) : Tape Bool :=
  loopTape [] cells right

def targetTape (cells : List (Bool × Bool))
    (right : List (Option Bool)) : Tape Bool :=
  rawBoundaryLengthCursorSeparatorTape
    (quotedPairBits cells.reverse) (4 * cells.length + 6) right

def cycleActualTape (processed rest : List (Bool × Bool))
    (x y : Bool) (right : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append
      ((quotedPairBits processed.reverse).reverse.map some)
      [some y, some x, some true, some false])
    (List.append (markerBits.map some)
      (List.append
        (List.replicate (4 + 4 * processed.length) (none : Option Bool))
        (List.append ((quotedPairBits rest).map some)
          (List.append (markerBits.map some) right))))

theorem cycleActualTape_equiv_loopTape
    (processed rest : List (Bool × Bool))
    (x y : Bool) (right : List (Option Bool)) :
    Tape.Equiv (cycleActualTape processed rest x y right)
      (loopTape (List.append processed [(x, y)]) rest right) := by
  simp [cycleActualTape, loopTape, markerBits, quotedPairBits,
    Tape.Equiv, tapeAtCells, List.reverse_append, List.map_append,
    List.append_assoc]
  constructor
  · simpa [List.append_assoc] using
      (FoC.Computability.dropTrailingNone_append_none
        (((quotedPairBits processed.reverse).map some).reverse ++
          [some y, some x, some true, some false])).symm
  · have hgap : 4 + 4 * processed.length =
        4 * (processed.length + 1) := by lia
    rw [hgap]

def finishActualTape (cells : List (Bool × Bool))
    (right : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append ((quotedPairBits cells.reverse).reverse.map some) [none])
    (none ::
      List.append
        (List.replicate (4 * cells.length + 7) (none : Option Bool))
        right)

theorem finishActualTape_equiv_targetTape
    (cells : List (Bool × Bool)) (right : List (Option Bool)) :
    Tape.Equiv (finishActualTape cells right) (targetTape cells right) := by
  simp [finishActualTape, targetTape,
    rawBoundaryLengthCursorSeparatorTape, Tape.Equiv, tapeAtCells]
  exact
    FoC.Computability.dropTrailingNone_append_none
      ((quotedPairBits cells.reverse).map some |>.reverse)

private theorem run_start_marker
    (left right : List (Option Bool)) :
    description.runConfig 4
        { state := description.start
          tape := tapeAtCells left
            (List.append (markerBits.map some) right) } =
      { state := 5
        tape := tapeAtCells
          (List.append (markerBits.reverse.map some) left) right } := by
  cases right <;>
    simp [description, markerBits, runConfig, stepConfig,
      lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

private theorem run_scan_blanks (n : Nat)
    (left right : List (Option Bool)) :
    description.runConfig n
        { state := 5
          tape := tapeAtCells left
            (List.append (List.replicate n (none : Option Bool)) right) } =
      { state := 5
        tape := tapeAtCells
          (List.append (List.replicate n (none : Option Bool)) left)
          right } := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih =>
      simp only [List.replicate_succ]
      rw [show n + 1 = 1 + n by lia]
      rw [runConfig_add]
      change
        description.runConfig n
            (description.runConfig 1
              { state := 5
                tape := tapeAtCells left
                  (none ::
                    List.append (List.replicate n (none : Option Bool))
                      right) }) = _
      rw [show description.runConfig 1
          { state := 5
            tape := tapeAtCells left
              (none ::
                List.append (List.replicate n (none : Option Bool))
                  right) } =
          { state := 5
            tape := tapeAtCells (none :: left)
              (List.append (List.replicate n (none : Option Bool))
                right) } by
        cases htail :
            List.append (List.replicate n (none : Option Bool)) right <;>
          simp [description, runConfig, stepConfig, lookupTransition,
            Matches, transition, tapeAtCells, Tape.read, Tape.write,
            Tape.move, Tape.moveRight, htail]]
      rw [ih (none :: left)]
      change
        Configuration.mk 5
            (tapeAtCells
              (List.append (List.replicate n none) (none :: left)) right) =
          Configuration.mk 5
            (tapeAtCells
              (none :: List.append (List.replicate n none) left) right)
      rw [replicate_none_append_none_cons]

private theorem run_read_done_marker
    (left right : List (Option Bool)) :
    description.runConfig 4
        { state := 5
          tape := tapeAtCells left
            (List.append (markerBits.map some) right) } =
      { state := 47
        tape := tapeAtCells (none :: none :: left)
          (none :: none :: right) } := by
  cases right <;>
    simp [description, markerBits, runConfig, stepConfig,
      lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

private theorem run_done_scan_blanks (n : Nat)
    (base right : List (Option Bool)) :
    description.runConfig n
        { state := 47
          tape := tapeAtCells
            (List.append (List.replicate n (none : Option Bool)) base)
            (none :: right) } =
      { state := 47
        tape := tapeAtCells base
          (none ::
            List.append (List.replicate n (none : Option Bool)) right) } := by
  induction n generalizing right with
  | zero => rfl
  | succ n ih =>
      rw [show n + 1 = 1 + n by lia]
      rw [runConfig_add]
      rw [show List.replicate (1 + n) (none : Option Bool) =
          none :: List.replicate n none by
        rw [show 1 + n = n + 1 by lia]
        rfl]
      change description.runConfig n
        (description.runConfig 1
          { state := 47
            tape := tapeAtCells
              (none :: List.append (List.replicate n none) base)
              (none :: right) }) = _
      rw [show description.runConfig 1
          { state := 47
            tape := tapeAtCells
              (none :: List.append (List.replicate n none) base)
              (none :: right) } =
          { state := 47
            tape := tapeAtCells
              (List.append (List.replicate n none) base)
              (none :: none :: right) } by
        simp [description, runConfig, stepConfig, lookupTransition,
          Matches, transition, tapeAtCells, Tape.read, Tape.write,
          Tape.move, Tape.moveLeft]]
      rw [ih (none :: right)]
      simp only [replicate_none_append_none_cons]
      rfl

private theorem run_erase_done_guard
    (first : Option Bool) (left right : List (Option Bool)) :
    description.runConfig 6
        { state := 47
          tape := tapeAtCells
            (List.append (markerBits.reverse.map some) (first :: left))
            (none :: right) } =
      { state := description.halt
        tape := tapeAtCells (first :: left)
          (none :: none :: none :: none :: none :: right) } := by
  cases first with
  | none =>
      simp [description, markerBits, runConfig, stepConfig,
        lookupTransition, Matches, transition, tapeAtCells,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
  | some bit =>
      cases bit <;>
        simp [description, markerBits, runConfig, stepConfig,
          lookupTransition, Matches, transition, tapeAtCells,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

private theorem run_erase_done_guard_nonempty
    (base right : List (Option Bool)) (hbase : base ≠ []) :
    description.runConfig 6
        { state := 47
          tape := tapeAtCells
            (List.append (markerBits.reverse.map some) base)
            (none :: right) } =
      { state := description.halt
        tape := tapeAtCells base
          (none :: none :: none :: none :: none :: right) } := by
  cases base with
  | nil => exact False.elim (hbase rfl)
  | cons first rest => exact run_erase_done_guard first rest right

private theorem run_read_cell (x y : Bool)
    (hvalid : (x, y) ≠ (true, true))
    (left right : List (Option Bool)) :
    description.runConfig 4
        { state := 5
          tape := tapeAtCells left
            (some false :: some true :: some x :: some y :: right) } =
      { state := returnState x y
        tape := tapeAtCells (none :: none :: left)
          (none :: none :: right) } := by
  cases x <;> cases y
  · cases right <;> simp [description, returnState, runConfig, stepConfig,
      lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
  · cases right <;> simp [description, returnState, runConfig, stepConfig,
      lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
  · cases right <;> simp [description, returnState, runConfig, stepConfig,
      lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
  · exact False.elim (hvalid rfl)

private theorem run_return_blanks (x y : Bool) (n : Nat)
    (boundary : Bool) (base right : List (Option Bool)) :
    (x, y) ≠ (true, true) →
      description.runConfig (n + 1)
          { state := returnState x y
            tape := tapeAtCells
              (List.append (List.replicate n (none : Option Bool))
                (some boundary :: base))
              (none :: right) } =
        { state := returnState x y
          tape := tapeAtCells base
            (some boundary ::
              List.append
                (List.replicate (n + 1) (none : Option Bool)) right) } := by
  intro hvalid
  induction n generalizing right with
  | zero =>
      cases x <;> cases y
      · cases right <;> simp [description, returnState, runConfig,
          stepConfig, lookupTransition, Matches, transition, tapeAtCells,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      · cases right <;> simp [description, returnState, runConfig,
          stepConfig, lookupTransition, Matches, transition, tapeAtCells,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      · cases right <;> simp [description, returnState, runConfig,
          stepConfig, lookupTransition, Matches, transition, tapeAtCells,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      · exact False.elim (hvalid rfl)
  | succ n ih =>
      rw [show n + 1 + 1 = 1 + (n + 1) by lia]
      rw [runConfig_add]
      simp only [List.replicate_succ]
      change description.runConfig (n + 1)
        (description.runConfig 1
          { state := returnState x y
            tape := tapeAtCells
              (none :: List.append (List.replicate n none)
                (some boundary :: base))
              (none :: right) }) = _
      have hstep :
          description.runConfig 1
              { state := returnState x y
                tape := tapeAtCells
                  (none :: List.append (List.replicate n none)
                    (some boundary :: base))
                  (none :: right) } =
            { state := returnState x y
              tape := tapeAtCells
                (List.append (List.replicate n none)
                  (some boundary :: base))
                (none :: none :: right) } := by
        cases x <;> cases y
        · cases right <;> simp [description, returnState, runConfig,
            stepConfig, lookupTransition, Matches, transition, tapeAtCells,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft]
        · cases right <;> simp [description, returnState, runConfig,
            stepConfig, lookupTransition, Matches, transition, tapeAtCells,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft]
        · cases right <;> simp [description, returnState, runConfig,
            stepConfig, lookupTransition, Matches, transition, tapeAtCells,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft]
        · exact False.elim (hvalid rfl)
      rw [hstep]
      rw [ih (none :: right)]
      change
        Configuration.mk (returnState x y)
            (tapeAtCells base
              (some boundary ::
                List.append (List.replicate (n + 1) none)
                  (none :: right))) =
          Configuration.mk (returnState x y)
            (tapeAtCells base
              (some boundary ::
                List.append (List.replicate (1 + (n + 1)) none) right))
      rw [replicate_none_append_none_cons]
      rw [show 1 + (n + 1) = Nat.succ (n + 1) by lia]
      rfl

private def outputAnchorTape (bitsRev : Word Bool)
    (baseTail right : List (Option Bool)) : Tape Bool :=
  match bitsRev with
  | [] => tapeAtCells baseTail (none :: right)
  | bit :: rest =>
      tapeAtCells
        (List.append (rest.map some) (none :: baseTail))
        (some bit :: right)

private theorem run_skip_guard (x y : Bool)
    (hvalid : (x, y) ≠ (true, true))
    (bitsRev : Word Bool) (tail : List (Option Bool)) :
    description.runConfig 4
        { state := returnState x y
          tape := tapeAtCells
            (some true :: some true :: some false ::
              List.append (bitsRev.map some) [none])
            (some true :: tail) } =
      { state := outputScanState x y
        tape := outputAnchorTape bitsRev []
          (List.append (markerBits.map some) tail) } := by
  cases x <;> cases y <;> cases bitsRev <;> cases tail <;>
    simp_all [description, markerBits, returnState, guardSkipOneState,
      guardSkipTwoState, guardSkipThreeState, outputScanState,
      outputAnchorTape, runConfig, stepConfig, lookupTransition, Matches,
      transition, tapeAtCells, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft, List.append_assoc]

private theorem run_output_scan (x y : Bool)
    (hvalid : (x, y) ≠ (true, true))
    (bitsRev : Word Bool) (baseTail right : List (Option Bool)) :
    description.runConfig bitsRev.length
        { state := outputScanState x y
          tape := outputAnchorTape bitsRev baseTail right } =
      { state := outputScanState x y
        tape := tapeAtCells baseTail
          (none :: List.append (bitsRev.reverse.map some) right) } := by
  induction bitsRev generalizing right with
  | nil => rfl
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by simp; lia]
      rw [runConfig_add]
      change description.runConfig rest.length
        (description.runConfig 1
          { state := outputScanState x y
            tape := outputAnchorTape (bit :: rest) baseTail right }) = _
      have hstep :
          description.runConfig 1
              { state := outputScanState x y
                tape := outputAnchorTape (bit :: rest) baseTail right } =
            { state := outputScanState x y
              tape := outputAnchorTape rest baseTail (some bit :: right) } := by
        cases x <;> cases y <;> cases bit <;> cases rest <;>
          simp_all [description, outputScanState, outputAnchorTape,
            runConfig, stepConfig, lookupTransition, Matches, transition,
            tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
            List.append_assoc]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: right)

private theorem run_write_cell (x y : Bool)
    (hvalid : (x, y) ≠ (true, true))
    (right : List (Option Bool)) :
    description.runConfig 7
        { state := outputScanState x y
          tape := tapeAtCells [] (none :: right) } =
      { state := 38
        tape := tapeAtCells
          [some y, some x, some true, some false] right } := by
  cases x <;> cases y <;> cases right <;>
    simp_all [description, outputScanState, writeXState, writeOneState,
      writeZeroState, runConfig, stepConfig, lookupTransition, Matches,
      transition, tapeAtCells, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft, Tape.moveRight]

private theorem run_check_cell (x y : Bool)
    (hvalid : (x, y) ≠ (true, true))
    (left right : List (Option Bool)) :
    description.runConfig 4
        { state := 38
          tape := tapeAtCells left
            (some false :: some true :: some x :: some y :: right) } =
      { state := 38
        tape := tapeAtCells
          (some y :: some x :: some true :: some false :: left) right } := by
  cases x <;> cases y
  · cases right <;> simp [description, runConfig, stepConfig,
      lookupTransition, Matches, transition, tapeAtCells, Tape.read,
      Tape.write, Tape.move, Tape.moveRight]
  · cases right <;> simp [description, runConfig, stepConfig,
      lookupTransition, Matches, transition, tapeAtCells, Tape.read,
      Tape.write, Tape.move, Tape.moveRight]
  · cases right <;> simp [description, runConfig, stepConfig,
      lookupTransition, Matches, transition, tapeAtCells, Tape.read,
      Tape.write, Tape.move, Tape.moveRight]
  · exact False.elim (hvalid rfl)

private theorem run_check_marker
    (first : Option Bool) (left right : List (Option Bool)) :
    description.runConfig 8
        { state := 38
          tape := tapeAtCells (first :: left)
            (List.append (markerBits.map some) right) } =
      { state := description.start
        tape := tapeAtCells (first :: left)
          (List.append (markerBits.map some) right) } := by
  cases first with
  | none =>
      cases left <;> cases right <;>
        simp [description, markerBits, runConfig, stepConfig,
          lookupTransition, Matches, transition, tapeAtCells, Tape.read,
          Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
  | some bit =>
      cases bit <;> cases left <;> cases right <;>
        simp [description, markerBits, runConfig, stepConfig,
          lookupTransition, Matches, transition, tapeAtCells, Tape.read,
          Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

private theorem run_check_cells (cells : List (Bool × Bool))
    (left right : List (Option Bool)) :
    (forall pair, pair ∈ cells → pair ≠ (true, true)) →
      description.runConfig (4 * cells.length)
          { state := 38
            tape := tapeAtCells left
              (List.append ((quotedPairBits cells).map some) right) } =
        { state := 38
          tape := tapeAtCells
            (List.append ((quotedPairBits cells).reverse.map some) left)
            right } := by
  intro hvalid
  induction cells generalizing left with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨x, y⟩
      have hxy : (x, y) ≠ (true, true) := hvalid (x, y) (by simp)
      have hrest : forall pair, pair ∈ rest → pair ≠ (true, true) := by
        intro pair hpair
        exact hvalid pair (by simp [hpair])
      rw [show 4 * ((x, y) :: rest).length = 4 + 4 * rest.length by
        simp; lia]
      rw [runConfig_add]
      rw [show List.append ((quotedPairBits ((x, y) :: rest)).map some)
            right =
          some false :: some true :: some x :: some y ::
            List.append ((quotedPairBits rest).map some) right by rfl]
      rw [run_check_cell x y hxy]
      rw [ih (some y :: some x :: some true :: some false :: left) hrest]
      simp [quotedPairBits, List.reverse_append, List.map_append,
        List.append_assoc]

private theorem run_check_cells_marker (cells : List (Bool × Bool))
    (first : Option Bool) (left right : List (Option Bool))
    (hvalid : forall pair, pair ∈ cells → pair ≠ (true, true)) :
    description.runConfig (4 * cells.length + 8)
        { state := 38
          tape := tapeAtCells (first :: left)
            (List.append ((quotedPairBits cells).map some)
              (List.append (markerBits.map some) right)) } =
      { state := description.start
        tape := tapeAtCells
          (List.append ((quotedPairBits cells).reverse.map some)
            (first :: left))
          (List.append (markerBits.map some) right) } := by
  rw [runConfig_add]
  rw [run_check_cells cells (first :: left)
    (List.append (markerBits.map some) right) hvalid]
  cases hprefix : (quotedPairBits cells).reverse.map some with
  | nil =>
      simpa [hprefix] using run_check_marker first left right
  | cons cell rest =>
      simpa [hprefix, List.append_assoc] using
        run_check_marker cell (List.append rest (first :: left)) right

def ValidPairs (cells : List (Bool × Bool)) : Prop :=
  forall pair, pair ∈ cells → pair ≠ (true, true)

theorem validPairs_reverse {cells : List (Bool × Bool)}
    (h : ValidPairs cells) : ValidPairs cells.reverse := by
  intro pair hpair
  exact h pair (List.mem_reverse.mp hpair)

theorem validPairs_append {first second : List (Bool × Bool)}
    (hfirst : ValidPairs first) (hsecond : ValidPairs second) :
    ValidPairs (List.append first second) := by
  intro pair hpair
  rcases List.mem_append.mp hpair with hpair | hpair
  · exact hfirst pair hpair
  · exact hsecond pair hpair

private theorem run_cycle (processed rest : List (Bool × Bool))
    (x y : Bool) (right : List (Option Bool))
    (hprocessed : ValidPairs processed)
    (hxy : (x, y) ≠ (true, true)) :
    Structured.MultiTapeLowering.RunsFromStateTapeEquiv
      description description.start description.start
      (loopTape processed ((x, y) :: rest) right)
      (loopTape (List.append processed [(x, y)]) rest right) := by
  let gap := 4 * processed.length
  let outRev := (quotedPairBits processed.reverse).reverse
  let suffix : List (Option Bool) :=
    List.append ((quotedPairBits rest).map some)
      (List.append (markerBits.map some) right)
  let tail : List (Option Bool) :=
    List.append (List.replicate (gap + 4) (none : Option Bool))
      suffix
  refine
    ⟨4 + (gap + (4 + ((gap + 3) +
      (4 + (outRev.length +
        (7 + (4 * processed.reverse.length + 8))))))),
      cycleActualTape processed rest x y right, ?_,
      cycleActualTape_equiv_loopTape processed rest x y right⟩
  rw [runConfig_add]
  unfold loopTape
  rw [run_start_marker]
  rw [runConfig_add]
  rw [run_scan_blanks]
  rw [runConfig_add]
  change
    description.runConfig
        ((gap + 3) +
          (4 + (outRev.length +
            (7 + (4 * processed.reverse.length + 8)))))
      (description.runConfig 4
        { state := 5
          tape := tapeAtCells
            (List.append (List.replicate gap none)
              (List.append (markerBits.reverse.map some)
                (List.append (outRev.map some) [none])))
            (some false :: some true :: some x :: some y ::
              List.append ((quotedPairBits rest).map some)
                (List.append (markerBits.map some) right)) }) = _
  rw [run_read_cell x y hxy]
  rw [runConfig_add]
  have hreturn :=
    run_return_blanks x y (gap + 2) true
      (some true :: some true :: some false ::
        List.append (outRev.map some) [none])
      (none :: suffix) hxy
  have hreturn' :
      description.runConfig (gap + 3)
          { state := returnState x y
            tape := tapeAtCells
              (none :: none ::
                List.append (List.replicate gap none)
                  (some true :: some true :: some true :: some false ::
                    List.append (outRev.map some) [none]))
              (none :: none ::
                suffix) } =
        { state := returnState x y
          tape := tapeAtCells
            (some true :: some true :: some false ::
              List.append (outRev.map some) [none])
            (some true :: tail) } := by
    have hrep2 :
        List.replicate (gap + 2) (none : Option Bool) =
          none :: none :: List.replicate gap none := by
      rw [show gap + 2 = Nat.succ (Nat.succ gap) by lia]
      rfl
    have hrepTail :
        List.append (List.replicate (gap + 3) (none : Option Bool))
            (none :: suffix) =
          tail := by
      rw [replicate_none_append_none_cons]
      unfold tail
      rw [show gap + 4 = Nat.succ (gap + 3) by lia]
      rfl
    rw [hrep2] at hreturn
    rw [hrepTail] at hreturn
    simpa [markerBits, List.append_assoc] using hreturn
  have hreturn'' :
      description.runConfig (gap + 3)
          { state := returnState x y
            tape := tapeAtCells
              (none :: none ::
                List.append (List.replicate gap none)
                  (List.append (markerBits.reverse.map some)
                    (List.append (outRev.map some) [none])))
              (none :: none ::
                List.append ((quotedPairBits rest).map some)
                  (List.append (markerBits.map some) right)) } =
        { state := returnState x y
          tape := tapeAtCells
            (some true :: some true :: some false ::
              List.append (outRev.map some) [none])
            (some true :: tail) } := by
    simpa [markerBits, suffix] using hreturn'
  rw [hreturn'']
  rw [runConfig_add]
  rw [run_skip_guard x y hxy outRev tail]
  rw [runConfig_add]
  rw [run_output_scan x y hxy outRev []
    (List.append (markerBits.map some) tail)]
  rw [runConfig_add]
  rw [run_write_cell x y hxy]
  have hcheck := run_check_cells_marker processed.reverse
    (some y) [some x, some true, some false] tail
    (validPairs_reverse hprocessed)
  rw [show outRev.reverse = quotedPairBits processed.reverse by
    simp [outRev]]
  rw [hcheck]
  simp [gap, outRev, suffix, tail, cycleActualTape, markerBits,
    quotedPairBits, List.reverse_append, List.map_append,
    List.append_assoc, Nat.add_comm]

private theorem run_cycles (processed remaining : List (Bool × Bool))
    (right : List (Option Bool))
    (hprocessed : ValidPairs processed)
    (hremaining : ValidPairs remaining) :
    Structured.MultiTapeLowering.RunsFromStateTapeEquiv
      description description.start description.start
      (loopTape processed remaining right)
      (loopTape (List.append processed remaining) [] right) := by
  induction remaining generalizing processed with
  | nil =>
      simpa using
        Structured.MultiTapeLowering.runsFromStateTapeEquiv_refl
          description description.start (loopTape processed [] right)
  | cons pair rest ih =>
      rcases pair with ⟨x, y⟩
      have hxy : (x, y) ≠ (true, true) :=
        hremaining (x, y) (by simp)
      have hrest : ValidPairs rest := by
        intro candidate hcandidate
        exact hremaining candidate (by simp [hcandidate])
      have hsingleton : ValidPairs [(x, y)] := by
        intro candidate hcandidate
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hcandidate
        subst candidate
        exact hxy
      have hprocessed' :
          ValidPairs (List.append processed [(x, y)]) :=
        validPairs_append hprocessed hsingleton
      have hfirst :=
        run_cycle processed rest x y right hprocessed hxy
      have htail :=
        ih (List.append processed [(x, y)]) hprocessed' hrest
      simpa [List.append_assoc] using
        Structured.MultiTapeLowering.runsFromStateTapeEquiv_trans
          hfirst htail

private theorem run_finish (cells : List (Bool × Bool))
    (right : List (Option Bool)) :
    Structured.MultiTapeLowering.RunsFromStateTapeEquiv
      description description.start description.halt
      (loopTape cells [] right) (targetTape cells right) := by
  let gap := 4 * cells.length
  let outLeft : List (Option Bool) :=
    List.append ((quotedPairBits cells.reverse).reverse.map some) [none]
  have houtLeft : outLeft ≠ [] := by simp [outLeft]
  refine
    ⟨4 + (gap + (4 + ((gap + 2) + 6))),
      finishActualTape cells right, ?_,
      finishActualTape_equiv_targetTape cells right⟩
  rw [runConfig_add]
  unfold loopTape
  rw [run_start_marker]
  rw [runConfig_add]
  rw [run_scan_blanks]
  rw [runConfig_add]
  change
    description.runConfig ((gap + 2) + 6)
      (description.runConfig 4
        { state := 5
          tape := tapeAtCells
            (List.append (List.replicate gap none)
              (List.append (markerBits.reverse.map some) outLeft))
            (List.append (markerBits.map some) right) }) = _
  rw [run_read_done_marker]
  rw [runConfig_add]
  have hrep :
      List.replicate (gap + 2) (none : Option Bool) =
        none :: none :: List.replicate gap none := by
    rw [show gap + 2 = Nat.succ (Nat.succ gap) by lia]
    rfl
  have hscan :=
    run_done_scan_blanks (gap + 2)
      (List.append (markerBits.reverse.map some) outLeft)
      (none :: right)
  have hscan' :
      description.runConfig (gap + 2)
          { state := 47
            tape := tapeAtCells
              (none :: none ::
                List.append (List.replicate gap none)
                  (List.append (markerBits.reverse.map some) outLeft))
              (none :: none :: right) } =
        { state := 47
          tape := tapeAtCells
            (List.append (markerBits.reverse.map some) outLeft)
            (none ::
              List.append (List.replicate (gap + 2) none)
                (none :: right)) } := by
    simpa [hrep, List.append_assoc] using hscan
  rw [hscan']
  rw [run_erase_done_guard_nonempty outLeft
    (List.append (List.replicate (gap + 2) none) (none :: right))
    houtLeft]
  have hblankRest :
      none :: none :: none :: none ::
          List.append (List.replicate (gap + 2) none) (none :: right) =
        List.append (List.replicate (gap + 7) none) right := by
    change
      List.append (List.replicate 4 none)
          (List.append (List.replicate (gap + 2) none)
            (List.append (List.replicate 1 none) right)) =
        List.append (List.replicate (gap + 7) none) right
    calc
      _ = List.append
          (List.append (List.replicate 4 none)
            (List.replicate (gap + 2) none))
          (List.append (List.replicate 1 none) right) :=
        (List.append_assoc _ _ _).symm
      _ = List.append (List.replicate (4 + (gap + 2)) none)
          (List.append (List.replicate 1 none) right) := by
        exact congrArg
          (fun xs : List (Option Bool) =>
            List.append xs
              (List.append (List.replicate 1 none) right))
          (List.replicate_append_replicate
            (n := 4) (m := gap + 2) (a := (none : Option Bool)))
      _ = List.append
          (List.append (List.replicate (4 + (gap + 2)) none)
            (List.replicate 1 none)) right :=
        (List.append_assoc _ _ _).symm
      _ = List.append (List.replicate (4 + (gap + 2) + 1) none)
          right := by
        exact congrArg
          (fun xs : List (Option Bool) => List.append xs right)
          (List.replicate_append_replicate
            (n := 4 + (gap + 2)) (m := 1)
            (a := (none : Option Bool)))
      _ = List.append (List.replicate (gap + 7) none) right := by
        rw [show 4 + (gap + 2) + 1 = gap + 7 by lia]
  rw [hblankRest]
  simp [finishActualTape, outLeft, gap]

theorem description_haltsFromTapeEquiv
    (cells : List (Bool × Bool)) (right : List (Option Bool))
    (hvalid : ValidPairs cells) :
    description.HaltsFromTapeEquiv
      (sourceTape cells right) (targetTape cells right) := by
  have hempty : ValidPairs ([] : List (Bool × Bool)) := by
    intro pair hpair
    simp at hpair
  have hcycles :
      Structured.MultiTapeLowering.RunsFromStateTapeEquiv
        description description.start description.start
        (sourceTape cells right) (loopTape cells [] right) := by
    simpa [sourceTape] using run_cycles [] cells right hempty hvalid
  have hfinish := run_finish cells right
  have hall :=
    Structured.MultiTapeLowering.runsFromStateTapeEquiv_trans
      hcycles hfinish
  exact
    Structured.MultiTapeLowering.RunsFromStateTapeEquiv.toHaltsFromTapeEquiv
      hall rfl rfl

namespace InstallLeftGuard

def description : MachineDescription where
  stateCount := 6
  start := 0
  halt := 5
  transitions :=
    [ transition 0 (some false) (some false) Direction.left 0
    , transition 0 (some true) (some true) Direction.left 0
    , transition 0 none (some true) Direction.left 1
    , transition 1 none (some true) Direction.left 2
    , transition 2 none (some true) Direction.left 3
    , transition 3 none (some false) Direction.left 4
    , transition 4 none none Direction.right 5 ]

theorem description_subroutineReady : description.SubroutineReady :=
  machineDescription_subroutineReady_of_transition_checks
    description (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

private theorem run_scan_present_left
    (leftRev : Word Bool) (current : Bool)
    (right : List (Option Bool)) :
    description.runConfig (leftRev.length + 1)
        { state := description.start
          tape := tapeAtCells
            (List.append (leftRev.map some) [none])
            (some current :: right) } =
      { state := description.start
        tape := tapeAtCells []
          (none ::
            List.append (leftRev.reverse.map some)
              (some current :: right)) } := by
  induction leftRev generalizing current right with
  | nil =>
      cases current <;>
        simp [description, runConfig, stepConfig, lookupTransition,
          Matches, transition, tapeAtCells, Tape.read, Tape.write,
          Tape.move, Tape.moveLeft]
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 1 = 1 + (rest.length + 1) by
        simp
        lia]
      rw [runConfig_add]
      have hstep :
          description.runConfig 1
              { state := description.start
                tape := tapeAtCells
                  (List.append ((bit :: rest).map some) [none])
                  (some current :: right) } =
            { state := description.start
              tape := tapeAtCells
                (List.append (rest.map some) [none])
                (some bit :: some current :: right) } := by
        cases current <;>
          simp [description, runConfig, stepConfig, lookupTransition,
            Matches, transition, tapeAtCells, Tape.read, Tape.write,
            Tape.move, Tape.moveLeft]
      rw [hstep]
      rw [ih bit (some current :: right)]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

private theorem run_write_guard
    (bits : Word Bool) (current : Bool)
    (right : List (Option Bool)) :
    description.runConfig 5
        { state := description.start
          tape := tapeAtCells []
            (none ::
              List.append (bits.map some) (some current :: right)) } =
      { state := description.halt
        tape := tapeAtCells [none]
          (List.append (markerBits.map some)
            (List.append (bits.map some) (some current :: right))) } := by
  cases current <;>
    simp [description, markerBits, runConfig, stepConfig,
      lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem description_haltsFromTape
    (bits : Word Bool) (current : Bool)
    (right : List (Option Bool)) :
    description.HaltsFromTape
      (tapeAtCells
        (List.append (bits.reverse.map some) [none])
        (some current :: right))
      (tapeAtCells [none]
        (List.append (markerBits.map some)
          (List.append (bits.map some) (some current :: right)))) := by
  have hscan :
      description.runConfig (bits.length + 1)
          { state := description.start
            tape := tapeAtCells
              (List.append (bits.reverse.map some) [none])
              (some current :: right) } =
        { state := description.start
          tape := tapeAtCells []
            (none ::
              List.append (bits.map some) (some current :: right)) } := by
    simpa using run_scan_present_left bits.reverse current right
  have hfull :
      description.runConfig ((bits.length + 1) + 5)
          { state := description.start
            tape := tapeAtCells
              (List.append (bits.reverse.map some) [none])
              (some current :: right) } =
        { state := description.halt
          tape := tapeAtCells [none]
            (List.append (markerBits.map some)
              (List.append (bits.map some) (some current :: right))) } := by
    rw [runConfig_add]
    rw [hscan]
    rw [run_write_guard]
  refine ⟨(bits.length + 1) + 5, ?_⟩
  constructor
  · simpa using congrArg Configuration.state hfull
  · simpa using congrArg Configuration.tape hfull

def markerRightPayload (T : Tape Bool)
    (padding : List (Option Bool)) : List (Option Bool) :=
  List.append
    ((quotedPairBits
      (logicalCellPair T.head :: T.right.map logicalCellPair)).map some)
    (none :: padding)

theorem description_haltsFrom_markerTarget
    (T : Tape Bool) (padding : List (Option Bool)) :
    description.HaltsFromTape
      (RawPairMarker.targetTape T padding)
      (sourceTape (T.left.reverse.map logicalCellPair)
        (markerRightPayload T padding)) := by
  let headPair := logicalCellPair T.head
  let rightPairs := T.right.map logicalCellPair
  let rightRest : List (Option Bool) :=
    some true :: some headPair.1 :: some headPair.2 ::
      List.append ((quotedPairBits rightPairs).map some) (none :: padding)
  have hrun :=
    description_haltsFromTape
      (List.append
        (quotedPairBits (T.left.reverse.map logicalCellPair)) markerBits)
      false rightRest
  simpa [RawPairMarker.targetTape, sourceTape, loopTape,
    markerRightPayload, headPair, rightPairs, rightRest,
    markerBits, quotedPairBits, List.reverse_append,
    List.map_append, List.append_assoc] using hrun

end InstallLeftGuard

theorem validPairs_map_logicalCellPair
    (cells : List (Option Bool)) :
    ValidPairs (cells.map logicalCellPair) := by
  intro pair hpair
  rw [List.mem_map] at hpair
  rcases hpair with ⟨cell, _hcell, rfl⟩
  cases cell with
  | none => decide
  | some bit => cases bit <;> decide

def setupAndReverseDescription : MachineDescription :=
  SeqViaCanonical InstallLeftGuard.description description

theorem setupAndReverseDescription_subroutineReady :
    setupAndReverseDescription.SubroutineReady :=
  SeqViaCanonical_subroutineReady
    InstallLeftGuard.description_subroutineReady description_subroutineReady

theorem setupAndReverseDescription_haltsFrom_markerTarget
    (T : Tape Bool) (padding : List (Option Bool)) :
    setupAndReverseDescription.HaltsFromTapeEquiv
      (RawPairMarker.targetTape T padding)
      (targetTape (T.left.reverse.map logicalCellPair)
        (InstallLeftGuard.markerRightPayload T padding)) := by
  have hsetup :=
    InstallLeftGuard.description_haltsFrom_markerTarget T padding
  have hreverse :=
    description_haltsFromTapeEquiv
      (T.left.reverse.map logicalCellPair)
      (InstallLeftGuard.markerRightPayload T padding)
      (validPairs_map_logicalCellPair T.left.reverse)
  have hbridgeEq :
      Tape.move Direction.left
          (Tape.move Direction.right
            (sourceTape (T.left.reverse.map logicalCellPair)
              (InstallLeftGuard.markerRightPayload T padding))) =
        sourceTape (T.left.reverse.map logicalCellPair)
          (InstallLeftGuard.markerRightPayload T padding) := by
    apply Tape.move_left_move_right_eq_self_of_right_cons
      (cell := some true)
      (right :=
        some true :: some true ::
          List.append
            ((quotedPairBits
              (T.left.reverse.map logicalCellPair)).map some)
            (List.append (markerBits.map some)
              (InstallLeftGuard.markerRightPayload T padding)))
    simp [sourceTape, loopTape, markerBits, tapeAtCells]
  apply SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
    InstallLeftGuard.description_subroutineReady description_subroutineReady
    hsetup.toEquiv
  · rw [hbridgeEq]
    exact Tape.Equiv.refl _
  · exact hreverse

def leftLengthTargetTape (T : Tape Bool)
    (padding : List (Option Bool)) : Tape Bool :=
  rawBoundaryLengthCursorSeparatorTape
    (List.append
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        T.left.length)
      (EncRewriters.CanonicalLayouts.DovetailLayoutScanner.cellsCodeBits
        T.left))
    (4 * T.left.length + 6)
    (InstallLeftGuard.markerRightPayload T padding)

theorem reverseTarget_eq_leftLengthSource
    (T : Tape Bool) (padding : List (Option Bool)) :
    targetTape (T.left.reverse.map logicalCellPair)
        (InstallLeftGuard.markerRightPayload T padding) =
      rawBoundaryLengthCursorSeparatorTape
        (EncRewriters.CanonicalLayouts.DovetailLayoutScanner.cellsCodeBits
          T.left)
        (4 * T.left.length + 6)
        (InstallLeftGuard.markerRightPayload T padding) := by
  simp [targetTape, RawPairQuoter.quotedPairBits_map_logicalCellPair]

theorem cellTokenBits_eq_quotedPairBits
    (cells : List (Bool × Bool)) :
    rawBoundaryLengthCursorCellTokenBits cells = quotedPairBits cells := by
  induction cells with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨first, second⟩
      simp [rawBoundaryLengthCursorCellTokenBits, quotedPairBits, ih]

theorem lengthCursor_haltsFrom_reverseTarget
    (T : Tape Bool) (padding : List (Option Bool)) :
    rawBoundaryLengthCursorLoopDescription.HaltsFromTapeEquiv
      (targetTape (T.left.reverse.map logicalCellPair)
        (InstallLeftGuard.markerRightPayload T padding))
      (leftLengthTargetTape T padding) := by
  rw [reverseTarget_eq_leftLengthSource]
  simpa [leftLengthTargetTape,
    rawBoundaryLengthCursorCellTokenTargetTape,
    rawBoundaryLengthCursorCellTokenOutputBits,
    cellTokenBits_eq_quotedPairBits,
    RawPairQuoter.quotedPairBits_map_logicalCellPair] using
    rawBoundaryLengthCursorLoopDescription_haltsFrom_cellTokens
      (T.left.map logicalCellPair) (4 * T.left.length + 6)
      (InstallLeftGuard.markerRightPayload T padding)

theorem separator_move_left_move_right
    (emitted : Word Bool) (blankTail : Nat)
    (right : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (rawBoundaryLengthCursorSeparatorTape emitted blankTail right)) =
      rawBoundaryLengthCursorSeparatorTape emitted blankTail right := by
  apply Tape.move_left_move_right_eq_self_of_right_cons
    (cell := none)
    (right :=
      List.append
        (List.replicate blankTail (none : Option Bool)) right)
  simp [rawBoundaryLengthCursorSeparatorTape, tapeAtCells,
    List.replicate_succ]

def leftPreparedDescription : MachineDescription :=
  SeqViaCanonical setupAndReverseDescription
    rawBoundaryLengthCursorLoopDescription

theorem leftPreparedDescription_subroutineReady :
    leftPreparedDescription.SubroutineReady :=
  SeqViaCanonical_subroutineReady
    setupAndReverseDescription_subroutineReady
    rawBoundaryLengthCursorLoopDescription_subroutineReady

theorem leftPreparedDescription_haltsFrom_markerTarget
    (T : Tape Bool) (padding : List (Option Bool)) :
    leftPreparedDescription.HaltsFromTapeEquiv
      (RawPairMarker.targetTape T padding)
      (leftLengthTargetTape T padding) := by
  have hreverse :=
    setupAndReverseDescription_haltsFrom_markerTarget T padding
  have hlength := lengthCursor_haltsFrom_reverseTarget T padding
  rw [reverseTarget_eq_leftLengthSource] at hlength
  apply SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
    setupAndReverseDescription_subroutineReady
    rawBoundaryLengthCursorLoopDescription_subroutineReady
    hreverse
  · rw [reverseTarget_eq_leftLengthSource]
    rw [separator_move_left_move_right]
    exact Tape.Equiv.refl _
  · exact hlength

end GuardedEgress.ChunkReverseScratch
end FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore

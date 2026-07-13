import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.GuardedEgress.RawPairMarker
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.LengthCursorLoop

namespace FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
namespace GuardedEgress.HeadCellExtractorScratch

open Languages MachineDescription
open CommonGround.FiniteTransducers
open GuardedEgress.RawPairQuoter
open CommonGround.FiniteTransducers.CountWindowRawSourceEncoder.RawBoundaryRightEdgeEmitter

def returnState : Bool → Bool → Nat
  | false, false => 6
  | false, true => 7
  | true, false => 8
  | true, true => 9

def writeZeroState : Bool → Bool → Nat
  | false, false => 10
  | false, true => 11
  | true, false => 12
  | true, true => 9

def writeOneState : Bool → Bool → Nat
  | false, false => 13
  | false, true => 14
  | true, false => 15
  | true, true => 9

def writeXState : Bool → Bool → Nat
  | false, false => 16
  | false, true => 17
  | true, false => 18
  | true, true => 9

def writeYState : Bool → Bool → Nat
  | false, false => 19
  | false, true => 20
  | true, false => 21
  | true, true => 9

def description : MachineDescription where
  stateCount := 31
  start := 1
  halt := 0
  transitions :=
    [ transition 1 none none Direction.right 1
    , transition 1 (some false) (some false) Direction.right 2
    , transition 2 (some true) (some true) Direction.right 3
    , transition 3 (some false) (some true) Direction.right 4
    , transition 3 (some true) (some true) Direction.right 5
    , transition 4 (some false) (some true) Direction.left 22
    , transition 4 (some true) (some true) Direction.left 23
    , transition 5 (some false) (some true) Direction.left 24

    , transition 22 (some true) (some true) Direction.left 25
    , transition 23 (some true) (some true) Direction.left 26
    , transition 24 (some true) (some true) Direction.left 27
    , transition 25 (some true) (some true) Direction.left 28
    , transition 26 (some true) (some true) Direction.left 29
    , transition 27 (some true) (some true) Direction.left 30
    , transition 28 (some false) (some false) Direction.left 6
    , transition 29 (some false) (some false) Direction.left 7
    , transition 30 (some false) (some false) Direction.left 8

    , transition 6 none none Direction.left 6
    , transition 7 none none Direction.left 7
    , transition 8 none none Direction.left 8
    , transition 6 (some false) (some false) Direction.right 10
    , transition 6 (some true) (some true) Direction.right 10
    , transition 7 (some false) (some false) Direction.right 11
    , transition 7 (some true) (some true) Direction.right 11
    , transition 8 (some false) (some false) Direction.right 12
    , transition 8 (some true) (some true) Direction.right 12

    , transition 10 none (some false) Direction.right 13
    , transition 11 none (some false) Direction.right 14
    , transition 12 none (some false) Direction.right 15
    , transition 13 none (some true) Direction.right 16
    , transition 14 none (some true) Direction.right 17
    , transition 15 none (some true) Direction.right 18
    , transition 16 none (some false) Direction.right 19
    , transition 17 none (some false) Direction.right 20
    , transition 18 none (some true) Direction.right 21
    , transition 19 none (some false) Direction.right 0
    , transition 20 none (some true) Direction.right 0
    , transition 21 none (some false) Direction.right 0 ]

theorem description_subroutineReady : description.SubroutineReady :=
  machineDescription_subroutineReady_of_transition_checks
    description (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

private theorem run_scan_blanks (n : Nat)
    (left right : List (Option Bool)) :
    description.runConfig (n + 1)
        { state := description.start
          tape := tapeAtCells left
            (none ::
              List.append (List.replicate n (none : Option Bool)) right) } =
      { state := description.start
        tape := tapeAtCells
          (List.append (List.replicate (n + 1) (none : Option Bool)) left)
          right } := by
  induction n generalizing left with
  | zero =>
      cases right <;>
        simp [description, runConfig, stepConfig, lookupTransition,
          Matches, transition, tapeAtCells, Tape.read, Tape.write,
          Tape.move, Tape.moveRight]
  | succ n ih =>
      rw [show n + 1 + 1 = 1 + (n + 1) by lia]
      rw [runConfig_add]
      rw [show List.replicate (n + 1) (none : Option Bool) =
          none :: List.replicate n none by rfl]
      have hstep :
          description.runConfig 1
              { state := description.start
                tape := tapeAtCells left
                  (none ::
                    List.append (none :: List.replicate n none) right) } =
            { state := description.start
              tape := tapeAtCells (none :: left)
                (List.append (none :: List.replicate n none) right) } := by
        simp [description, runConfig, stepConfig, lookupTransition,
          Matches, transition, tapeAtCells, Tape.read, Tape.write,
          Tape.move, Tape.moveRight]
      rw [hstep]
      have ih' :
          description.runConfig (n + 1)
              { state := description.start
                tape := tapeAtCells (none :: left)
                  (List.append (none :: List.replicate n none) right) } =
            { state := description.start
              tape := tapeAtCells
                (List.append (List.replicate (n + 1) none)
                  (none :: left)) right } := by
        simpa using ih (none :: left)
      rw [ih']
      rw [replicate_none_append_none_cons]
      rw [show List.replicate (1 + (n + 1)) (none : Option Bool) =
          none :: List.replicate (n + 1) none by
        rw [show 1 + (n + 1) = Nat.succ (n + 1) by lia]
        rfl]
      rfl

private theorem run_read_cell (x y : Bool)
    (hvalid : (x, y) ≠ (true, true))
    (left right : List (Option Bool)) :
    description.runConfig 7
        { state := description.start
          tape := tapeAtCells (none :: left)
            (some false :: some true :: some x :: some y :: right) } =
      { state := returnState x y
        tape := tapeAtCells left
          (none :: List.append ([false, true, true, true].map some) right) } := by
  cases x <;> cases y
  · cases right <;>
      simp [description, returnState, runConfig, stepConfig,
        lookupTransition, Matches, transition, tapeAtCells,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
  · cases right <;>
      simp [description, returnState, runConfig, stepConfig,
        lookupTransition, Matches, transition, tapeAtCells,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
  · cases right <;>
      simp [description, returnState, runConfig, stepConfig,
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
      · cases right <;>
          simp [description, returnState, runConfig, stepConfig,
            lookupTransition, Matches, transition, tapeAtCells,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      · cases right <;>
          simp [description, returnState, runConfig, stepConfig,
            lookupTransition, Matches, transition, tapeAtCells,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      · cases right <;>
          simp [description, returnState, runConfig, stepConfig,
            lookupTransition, Matches, transition, tapeAtCells,
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
        · cases right <;>
            simp [description, returnState, runConfig, stepConfig,
              lookupTransition, Matches, transition, tapeAtCells,
              Tape.read, Tape.write, Tape.move, Tape.moveLeft]
        · cases right <;>
            simp [description, returnState, runConfig, stepConfig,
              lookupTransition, Matches, transition, tapeAtCells,
              Tape.read, Tape.write, Tape.move, Tape.moveLeft]
        · cases right <;>
            simp [description, returnState, runConfig, stepConfig,
              lookupTransition, Matches, transition, tapeAtCells,
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

private theorem run_boundary (x y boundary : Bool)
    (base right : List (Option Bool))
    (hvalid : (x, y) ≠ (true, true)) :
    description.runConfig 1
        { state := returnState x y
          tape := tapeAtCells base
            (some boundary :: none :: right) } =
      { state := writeZeroState x y
        tape := tapeAtCells (some boundary :: base)
          (none :: right) } := by
  cases x <;> cases y <;> cases boundary
  all_goals
    simp_all [description, returnState, writeZeroState,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]

private theorem run_write_cell (x y : Bool)
    (left right : List (Option Bool))
    (hvalid : (x, y) ≠ (true, true)) :
    description.runConfig 4
        { state := writeZeroState x y
          tape := tapeAtCells left
            (none :: none :: none :: none :: right) } =
      { state := description.halt
        tape := tapeAtCells
          (some y :: some x :: some true :: some false :: left) right } := by
  cases x <;> cases y
  · cases right <;>
      simp [description, writeZeroState, writeOneState,
        writeXState, writeYState, runConfig, stepConfig,
        lookupTransition, Matches, transition, tapeAtCells,
        Tape.read, Tape.write, Tape.move, Tape.moveRight]
  · cases right <;>
      simp [description, writeZeroState, writeOneState,
        writeXState, writeYState, runConfig, stepConfig,
        lookupTransition, Matches, transition, tapeAtCells,
        Tape.read, Tape.write, Tape.move, Tape.moveRight]
  · cases right <;>
      simp [description, writeZeroState, writeOneState,
        writeXState, writeYState, runConfig, stepConfig,
        lookupTransition, Matches, transition, tapeAtCells,
        Tape.read, Tape.write, Tape.move, Tape.moveRight]
  · exact False.elim (hvalid rfl)

def sourceTape (emitted : Word Bool) (scratch : Nat)
    (x y : Bool) (remaining : List (Bool × Bool))
    (right : List (Option Bool)) : Tape Bool :=
  tapeAtCells (emitted.reverse.map some)
    (none ::
      List.append (List.replicate (scratch + 4) (none : Option Bool))
        (List.append
          ((quotedPairBits ((x, y) :: remaining)).map some)
          (none :: right)))

def targetTape (emitted : Word Bool) (scratch : Nat)
    (x y : Bool) (remaining : List (Bool × Bool))
    (right : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    ((List.append emitted [false, true, x, y]).reverse.map some)
    (none ::
      List.append (List.replicate scratch (none : Option Bool))
        (List.append ([false, true, true, true].map some)
          (List.append ((quotedPairBits remaining).map some)
            (none :: right))))

theorem description_haltsFromTape
    (emitted : Word Bool) (scratch : Nat)
    (x y : Bool) (remaining : List (Bool × Bool))
    (right : List (Option Bool))
    (hemitted : emitted ≠ [])
    (hvalid : (x, y) ≠ (true, true)) :
    description.HaltsFromTape
      (sourceTape emitted scratch x y remaining right)
      (targetTape emitted scratch x y remaining right) := by
  change (emitted : List Bool) ≠ [] at hemitted
  cases hrev : emitted.reverse with
  | nil =>
      cases emitted with
      | nil => exact False.elim (hemitted rfl)
      | cons bit rest => simp at hrev
  | cons boundary baseBits =>
      let tail : List (Option Bool) :=
        List.append ((quotedPairBits remaining).map some) (none :: right)
      have hscan := run_scan_blanks (scratch + 4)
        (emitted.reverse.map some)
        (some false :: some true :: some x :: some y :: tail)
      have hrepScan :
          List.replicate (scratch + 4 + 1) (none : Option Bool) =
            none :: List.replicate (scratch + 4) none := by
        rw [show scratch + 4 + 1 = Nat.succ (scratch + 4) by lia]
        rfl
      have hread :=
        run_read_cell x y hvalid
          (List.append (List.replicate (scratch + 4) none)
            (emitted.reverse.map some)) tail
      have hread' :
          description.runConfig 7
              { state := description.start
                tape := tapeAtCells
                  (List.append
                    (List.replicate (scratch + 4 + 1) none)
                    (emitted.reverse.map some))
                  (some false :: some true :: some x :: some y :: tail) } =
            { state := returnState x y
              tape := tapeAtCells
                (List.append (List.replicate (scratch + 4) none)
                  (emitted.reverse.map some))
                (none ::
                  List.append ([false, true, true, true].map some) tail) } := by
        simpa [hrepScan, List.append_assoc] using hread
      have hreturn :=
        run_return_blanks x y (scratch + 4) boundary
          (baseBits.map some)
          (List.append ([false, true, true, true].map some) tail)
          hvalid
      have hreturn' :
          description.runConfig (scratch + 4 + 1)
              { state := returnState x y
                tape := tapeAtCells
                  (List.append (List.replicate (scratch + 4) none)
                    (emitted.reverse.map some))
                  (none ::
                    List.append ([false, true, true, true].map some) tail) } =
            { state := returnState x y
              tape := tapeAtCells (baseBits.map some)
                (some boundary ::
                  List.append (List.replicate (scratch + 4 + 1) none)
                    (List.append ([false, true, true, true].map some)
                      tail)) } := by
        simpa [hrev, List.append_assoc] using hreturn
      have hboundary :=
        run_boundary x y boundary (baseBits.map some)
          (List.append (List.replicate (scratch + 4) none)
            (List.append ([false, true, true, true].map some) tail))
          hvalid
      have hrepBoundary :
          List.replicate (scratch + 4 + 1) (none : Option Bool) =
            none :: List.replicate (scratch + 4) none := by
        rw [show scratch + 4 + 1 = Nat.succ (scratch + 4) by lia]
        rfl
      have hboundary' :
          description.runConfig 1
              { state := returnState x y
                tape := tapeAtCells (baseBits.map some)
                  (some boundary ::
                    List.append (List.replicate (scratch + 4 + 1) none)
                      (List.append ([false, true, true, true].map some)
                        tail)) } =
            { state := writeZeroState x y
              tape := tapeAtCells
                (some boundary :: baseBits.map some)
                (none ::
                  List.append (List.replicate (scratch + 4) none)
                    (List.append ([false, true, true, true].map some)
                      tail)) } := by
        simpa [hrepBoundary, List.append_assoc] using hboundary
      have hwrite :=
        run_write_cell x y
          (some boundary :: baseBits.map some)
          (none ::
            List.append (List.replicate scratch none)
              (List.append ([false, true, true, true].map some) tail))
          hvalid
      have hrepWrite :
          List.replicate (scratch + 4) (none : Option Bool) =
            none :: none :: none :: none :: List.replicate scratch none := by
        rw [show scratch + 4 =
          Nat.succ (Nat.succ (Nat.succ (Nat.succ scratch))) by lia]
        rfl
      have hwrite' :
          description.runConfig 4
              { state := writeZeroState x y
                tape := tapeAtCells
                  (some boundary :: baseBits.map some)
                  (none ::
                    List.append (List.replicate (scratch + 4) none)
                      (List.append ([false, true, true, true].map some)
                        tail)) } =
            { state := description.halt
              tape := tapeAtCells
                (some y :: some x :: some true :: some false ::
                  some boundary :: baseBits.map some)
                (none ::
                  List.append (List.replicate scratch none)
                    (List.append ([false, true, true, true].map some)
                      tail)) } := by
        rw [hrepWrite]
        simpa [List.append_assoc] using hwrite
      have hsourcePayload :
          List.append
              ((quotedPairBits ((x, y) :: remaining)).map some)
              (none :: right) =
            some false :: some true :: some x :: some y :: tail := by
        rfl
      refine
        ⟨(scratch + 4 + 1) +
            (7 + ((scratch + 4 + 1) + (1 + 4))), ?_⟩
      have hfull :
          description.runConfig
              ((scratch + 4 + 1) +
                (7 + ((scratch + 4 + 1) + (1 + 4))))
              { state := description.start
                tape := sourceTape emitted scratch x y remaining right } =
            { state := description.halt
              tape := targetTape emitted scratch x y remaining right } := by
        rw [runConfig_add]
        unfold sourceTape
        rw [hsourcePayload]
        rw [hscan]
        rw [runConfig_add]
        rw [hread']
        rw [runConfig_add]
        rw [hreturn']
        rw [runConfig_add]
        rw [hboundary']
        rw [hwrite']
        simp [targetTape, tail, hrev, List.reverse_append,
          List.map_append, List.replicate_succ, List.append_assoc]
      constructor
      · simpa using congrArg Configuration.state hfull
      · simpa using congrArg Configuration.tape hfull

def headExtractedTape (emitted : Word Bool) (scratch : Nat)
    (T : Tape Bool) (padding : List (Option Bool)) : Tape Bool :=
  targetTape emitted scratch
    (logicalCellPair T.head).1 (logicalCellPair T.head).2
    (T.right.map logicalCellPair) padding

theorem description_haltsFrom_separator_cellList
    (emitted : Word Bool) (scratch : Nat)
    (T : Tape Bool) (padding : List (Option Bool))
    (hemitted : emitted ≠ []) :
    description.HaltsFromTape
      (rawBoundaryLengthCursorSeparatorTape emitted (scratch + 3)
        (List.append
          ((quotedPairBits
            (logicalCellPair T.head ::
              T.right.map logicalCellPair)).map some)
          (none :: padding)))
      (headExtractedTape emitted scratch T padding) := by
  have hvalid : logicalCellPair T.head ≠ (true, true) := by
    cases T.head with
    | none => decide
    | some bit => cases bit <;> decide
  have hrun :=
    description_haltsFromTape emitted scratch
      (logicalCellPair T.head).1 (logicalCellPair T.head).2
      (T.right.map logicalCellPair) padding hemitted hvalid
  simpa [headExtractedTape, sourceTape,
    rawBoundaryLengthCursorSeparatorTape, quotedPairBits,
    List.replicate_succ, List.map_append, List.append_assoc] using hrun

end GuardedEgress.HeadCellExtractorScratch
end FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore

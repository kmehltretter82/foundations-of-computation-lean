import FoC.Computability.Compiler.ClosedCfg.ProjTail.StructuredPrefixEraserHandoff.Impl.PairParityEraser

set_option doc.verso true

/-!
# Marker-preserving pair-parity prefix eraser

This variant of the guarded two-tape prefix eraser retains the final two
represented prefix cells as the collision-safe {lit}`[true, false]` sentinel.
The sentinel is skipped during the rightward return because decoder footprint
pairs never contain adjacent represented cells; the existing
{lit}`[true, true]` right-end marker remains independently recognizable.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup
namespace LiveIngress
namespace MarkerHandoff

def description : MachineDescription where
  stateCount := 12
  start := 0
  halt := 10
  transitions :=
    [ transition 0 none (some true) Direction.left 1
    , transition 1 none (some true) Direction.left 2
    , transition 2 none none Direction.left 3
    , transition 2 (some false) (some false) Direction.left 3
    , transition 2 (some true) (some true) Direction.left 3
    , transition 3 none none Direction.left 2
    , transition 3 (some false) (some false) Direction.left 11
    , transition 3 (some true) (some false) Direction.left 11
    , transition 11 (some false) (some true) Direction.left 4
    , transition 11 (some true) (some true) Direction.left 4
    , transition 4 (some false) none Direction.left 4
    , transition 4 (some true) none Direction.left 4
    , transition 4 none none Direction.left 5
    , transition 5 (some false) none Direction.left 6
    , transition 5 (some true) none Direction.left 6
    , transition 6 (some false) none Direction.left 6
    , transition 6 (some true) none Direction.left 6
    , transition 6 none none Direction.right 7
    , transition 7 none none Direction.right 7
    , transition 7 (some false) (some false) Direction.right 8
    , transition 7 (some true) (some true) Direction.right 8
    , transition 8 none none Direction.right 7
    , transition 8 (some false) (some false) Direction.right 7
    , transition 8 (some true) none Direction.left 9
    , transition 9 (some true) none Direction.right 10 ]

theorem description_wellFormed : description.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := description.transitions)
      (stateCount := description.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := description.transitions)
      (by decide)

theorem description_haltTransitionFree : description.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := description.transitions)
    (state := description.halt)
    (by decide)

theorem description_subroutineReady : description.SubroutineReady :=
  ⟨description_wellFormed, description_haltTransitionFree⟩

theorem run_mark (x : Option Bool) (rest : List (Option Bool)) :
    description.runConfig 2
        { state := 0
          tape :=
            { left := none :: x :: rest
              head := none
              right := [] } } =
      { state := 2
        tape :=
          { left := rest
            head := x
            right := [some true, some true] } } := by
  simp [description, runConfig, stepConfig, lookupTransition, Matches,
    transition, Tape.read, Tape.write, Tape.move, Tape.moveLeft]

theorem run_scan
    (rev : List (Option Bool)) (c e : Option Bool)
    (leftRest right : List (Option Bool)) :
    description.runConfig (2 * rev.length + 2)
        { state := 2
          tape :=
            { left := none ::
                (pairParityEraserPairFlattenRev rev ++ (e :: leftRest))
              head := c
              right := right } } =
      { state := 2
        tape :=
          { left := leftRest
            head := e
            right := (pairParityEraserPairFlattenRev rev).reverse ++
              (none :: c :: right) } } := by
  induction rev generalizing c right with
  | nil =>
      cases c with
      | none =>
          simp [pairParityEraserPairFlattenRev, description, runConfig,
            stepConfig, lookupTransition, Matches, transition, Tape.read,
            Tape.write, Tape.move, Tape.moveLeft]
      | some bit =>
          cases bit <;>
            simp [pairParityEraserPairFlattenRev, description, runConfig,
              stepConfig, lookupTransition, Matches, transition, Tape.read,
              Tape.write, Tape.move, Tape.moveLeft]
  | cons d rest ih =>
      rw [show 2 * (d :: rest).length + 2 = 2 +
          (2 * rest.length + 2) by simp; lia]
      rw [runConfig_add]
      have hstep :
          description.runConfig 2
              { state := 2
                tape :=
                  { left :=
                      none :: (pairParityEraserPairFlattenRev (d :: rest) ++
                        (e :: leftRest))
                    head := c
                    right := right } } =
            { state := 2
              tape :=
                { left := none ::
                    (pairParityEraserPairFlattenRev rest ++ (e :: leftRest))
                  head := d
                  right := none :: c :: right } } := by
        cases c with
        | none =>
            simp [pairParityEraserPairFlattenRev, description, runConfig,
              stepConfig, lookupTransition, Matches, transition, Tape.read,
              Tape.write, Tape.move, Tape.moveLeft]
        | some bit =>
            cases bit <;>
              simp [pairParityEraserPairFlattenRev, description, runConfig,
                stepConfig, lookupTransition, Matches, transition, Tape.read,
                Tape.write, Tape.move, Tape.moveLeft]
      rw [hstep]
      simpa [pairParityEraserPairFlattenRev, List.append_assoc] using
        ih d (none :: c :: right)

theorem run_enterMarker_cons
    (t u current : Bool) (w : List Bool) (e : Option Bool)
    (leftRest right : List (Option Bool)) :
    description.runConfig 3
        { state := 2
          tape :=
            { left := some t :: some u ::
                ((current :: w).map some ++ (none :: e :: leftRest))
              head := none
              right := right } } =
      { state := 4
        tape :=
          { left := w.map some ++ (none :: e :: leftRest)
            head := some current
            right := [some true, some false, none] ++ right } } := by
  cases t <;> cases u <;>
    simp [description, runConfig, stepConfig, lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move, Tape.moveLeft]

theorem run_erase4
    (w : List Bool) (current : Bool) (e : Option Bool)
    (leftRest right : List (Option Bool)) :
    description.runConfig (w.length + 2)
        { state := 4
          tape :=
            { left := w.map some ++ (none :: e :: leftRest)
              head := some current
              right := right } } =
      { state := 5
        tape :=
          { left := leftRest
            head := e
            right := List.replicate (w.length + 2) none ++ right } } := by
  induction w generalizing current right with
  | nil =>
      cases current <;>
        simp [description, runConfig, stepConfig, lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          List.replicate_succ]
  | cons next rest ih =>
      rw [show (next :: rest).length + 2 = 1 + (rest.length + 2) by
        simp
        lia]
      rw [runConfig_add]
      have hstep :
          description.runConfig 1
              { state := 4
                tape :=
                  { left := (next :: rest).map some ++
                      (none :: e :: leftRest)
                    head := some current
                    right := right } } =
            { state := 4
              tape :=
                { left := rest.map some ++ (none :: e :: leftRest)
                  head := some next
                  right := none :: right } } := by
        cases current <;>
          simp [description, runConfig, stepConfig, lookupTransition,
            Matches, transition, Tape.read, Tape.write, Tape.move,
            Tape.moveLeft]
      rw [hstep]
      simpa [pairParityEraserReplicate_none_middle, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using ih next (none :: right)

theorem run_secondField
    (w : List Bool) (t u : Bool) (e : Option Bool)
    (leftRest right : List (Option Bool)) :
    description.runConfig (w.length + 4)
        { state := 2
          tape :=
            { left := some t :: some u ::
                (w.map some ++ (none :: e :: leftRest))
              head := none
              right := right } } =
      { state := 5
        tape :=
          { left := leftRest
            head := e
            right := List.replicate (w.length + 1) none ++
              [some true, some false, none] ++ right } } := by
  cases w with
  | nil =>
      cases t <;> cases u <;>
        simp [description, runConfig, stepConfig, lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          List.replicate_succ]
  | cons current rest =>
      rw [show (current :: rest).length + 4 =
          3 + (rest.length + 2) by simp; lia]
      rw [runConfig_add]
      rw [run_enterMarker_cons]
      simpa [pairParityEraserReplicate_none_middle, List.append_assoc] using
        run_erase4 rest current e leftRest
          ([some true, some false, none] ++ right)

theorem run_gap
    (s v : Bool) (leftRest right : List (Option Bool)) :
    description.runConfig 1
        { state := 5
          tape :=
            { left := some v :: leftRest
              head := some s
              right := right } } =
      { state := 6
        tape :=
          { left := leftRest
            head := some v
            right := none :: right } } := by
  cases s <;>
    simp [description, runConfig, stepConfig, lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move, Tape.moveLeft]

theorem run_erase6
    (w : List Bool) (current : Bool) (right : List (Option Bool)) :
    description.runConfig (w.length + 2)
        { state := 6
          tape :=
            { left := w.map some ++ [none]
              head := some current
              right := right } } =
      { state := 7
        tape :=
          { left := [none]
            head := none
            right := List.replicate w.length none ++ right } } := by
  induction w generalizing current right with
  | nil =>
      cases current <;>
        simp [description, runConfig, stepConfig, lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          Tape.moveRight]
  | cons next rest ih =>
      rw [show (next :: rest).length + 2 = 1 + (rest.length + 2) by
        simp
        lia]
      rw [runConfig_add]
      have hstep :
          description.runConfig 1
              { state := 6
                tape :=
                  { left := (next :: rest).map some ++ [none]
                    head := some current
                    right := right } } =
            { state := 6
              tape :=
                { left := rest.map some ++ [none]
                  head := some next
                  right := none :: right } } := by
        cases current <;>
          simp [description, runConfig, stepConfig, lookupTransition,
            Matches, transition, Tape.read, Tape.write, Tape.move,
            Tape.moveLeft]
      rw [hstep]
      simpa [pairParityEraserReplicate_none_middle, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using ih next (none :: right)

theorem run_skip7
    (n : Nat) (left : List (Option Bool)) (cell : Option Bool)
    (right : List (Option Bool)) :
    description.runConfig (n + 1)
        { state := 7
          tape :=
            { left := left
              head := none
              right := List.replicate n none ++ (cell :: right) } } =
      { state := 7
        tape :=
          { left := List.replicate (n + 1) none ++ left
            head := cell
            right := right } } := by
  induction n generalizing left with
  | zero =>
      simp [description, runConfig, stepConfig, lookupTransition, Matches,
        transition, Tape.read, Tape.write, Tape.move, Tape.moveRight,
        List.replicate_succ]
  | succ n ih =>
      rw [show n + 1 + 1 = 1 + (n + 1) by lia]
      rw [runConfig_add]
      have hstep :
          description.runConfig 1
              { state := 7
                tape :=
                  { left := left
                    head := none
                    right := List.replicate (n + 1) none ++
                      (cell :: right) } } =
            { state := 7
              tape :=
                { left := none :: left
                  head := none
                  right := List.replicate n none ++ (cell :: right) } } := by
        simp [description, runConfig, stepConfig, lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move, Tape.moveRight,
          List.replicate_succ]
      rw [hstep]
      simpa [pairParityEraserReplicate_none_middle, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using ih (none :: left)

theorem run_handoff
    (left : List (Option Bool)) (cell : Option Bool)
    (right : List (Option Bool)) :
    description.runConfig 3
        { state := 7
          tape :=
            { left := left
              head := some true
              right := some false :: none :: cell :: right } } =
      { state := 7
        tape :=
          { left := [none, some false, some true] ++ left
            head := cell
            right := right } } := by
  simp [description, runConfig, stepConfig, lookupTransition, Matches,
    transition, Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem run_ret
    (cells : List (Option Bool)) (h current : Option Bool)
    (left : List (Option Bool)) (next : Option Bool)
    (right : List (Option Bool)) :
    description.runConfig (2 * cells.length + 2)
        { state := pairParityEraserScanState h
          tape :=
            { left := left
              head := none
              right :=
                (current :: pairParityEraserPairFlatten cells) ++
                  (next :: right) } } =
      { state :=
          pairParityEraserScanState
            (pairParityEraserLastCell cells current)
        tape :=
          { left :=
              (pairParityEraserPairFlatten (current :: cells)).reverse ++
                left
            head := next
            right := right } } := by
  induction cells generalizing h current left with
  | nil =>
      cases h with
      | none =>
          cases current with
          | none =>
              simp [pairParityEraserScanState, pairParityEraserLastCell,
                pairParityEraserPairFlatten, description, runConfig,
                stepConfig, lookupTransition, Matches, transition,
                Tape.read, Tape.write, Tape.move, Tape.moveRight]
          | some bit =>
              cases bit <;>
                simp [pairParityEraserScanState, pairParityEraserLastCell,
                  pairParityEraserPairFlatten, description, runConfig,
                  stepConfig, lookupTransition, Matches, transition,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight]
      | some hb =>
          cases current with
          | none =>
              simp [pairParityEraserScanState, pairParityEraserLastCell,
                pairParityEraserPairFlatten, description, runConfig,
                stepConfig, lookupTransition, Matches, transition,
                Tape.read, Tape.write, Tape.move, Tape.moveRight]
          | some bit =>
              cases bit <;>
                simp [pairParityEraserScanState, pairParityEraserLastCell,
                  pairParityEraserPairFlatten, description, runConfig,
                  stepConfig, lookupTransition, Matches, transition,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight]
  | cons candidate rest ih =>
      rw [show 2 * (candidate :: rest).length + 2 =
          2 + (2 * rest.length + 2) by simp; lia]
      rw [runConfig_add]
      have hstep :
          description.runConfig 2
              { state := pairParityEraserScanState h
                tape :=
                  { left := left
                    head := none
                    right :=
                      (current ::
                        pairParityEraserPairFlatten (candidate :: rest)) ++
                        (next :: right) } } =
            { state := pairParityEraserScanState current
              tape :=
                { left := current :: none :: left
                  head := none
                  right :=
                    (candidate :: pairParityEraserPairFlatten rest) ++
                      (next :: right) } } := by
        cases h with
        | none =>
            cases current with
            | none =>
                simp [pairParityEraserScanState,
                  pairParityEraserPairFlatten, description, runConfig,
                  stepConfig, lookupTransition, Matches, transition,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight]
            | some bit =>
                cases bit <;>
                  simp [pairParityEraserScanState,
                    pairParityEraserPairFlatten, description, runConfig,
                    stepConfig, lookupTransition, Matches, transition,
                    Tape.read, Tape.write, Tape.move, Tape.moveRight]
        | some hb =>
            cases current with
            | none =>
                simp [pairParityEraserScanState,
                  pairParityEraserPairFlatten, description, runConfig,
                  stepConfig, lookupTransition, Matches, transition,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight]
            | some bit =>
                cases bit <;>
                  simp [pairParityEraserScanState,
                    pairParityEraserPairFlatten, description, runConfig,
                    stepConfig, lookupTransition, Matches, transition,
                    Tape.read, Tape.write, Tape.move, Tape.moveRight]
      rw [hstep]
      simpa [pairParityEraserPairFlatten, pairParityEraserLastCell,
        List.append_assoc] using
        ih current candidate (current :: none :: left)

theorem run_ret7
    (cells : List (Option Bool)) (current : Option Bool)
    (left : List (Option Bool)) (next : Option Bool)
    (right : List (Option Bool)) :
    description.runConfig (2 * cells.length + 2)
        { state := 7
          tape :=
            { left := left
              head := none
              right :=
                (current :: pairParityEraserPairFlatten cells) ++
                  (next :: right) } } =
      { state :=
          pairParityEraserScanState
            (pairParityEraserLastCell cells current)
        tape :=
          { left :=
              (pairParityEraserPairFlatten (current :: cells)).reverse ++
                left
            head := next
            right := right } } :=
  run_ret cells none current left next right

theorem run_finish (left : List (Option Bool)) :
    description.runConfig 3
        { state := 7
          tape :=
            { left := left
              head := some true
              right := [some true] } } =
      { state := 10
        tape :=
          { left := none :: left
            head := none
            right := [] } } := by
  simp [description, runConfig, stepConfig, lookupTransition, Matches,
    transition, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    Tape.moveRight]

theorem assemble_blank_prefix
    (n0 n1 : Nat) (tail : List (Option Bool)) :
    List.replicate n0 none ++
        (none :: (List.replicate (n1 + 1) none ++ tail)) =
      List.replicate (n0 + n1 + 2) none ++ tail := by
  rw [show (none : Option Bool) ::
      (List.replicate (n1 + 1) none ++ tail) =
    List.replicate 1 none ++
      (List.replicate (n1 + 1) none ++ tail) from rfl]
  rw [pairParityEraserReplicate_none_append n0 1]
  rw [pairParityEraserReplicate_none_append (n0 + 1) (n1 + 1)]
  congr 2
  lia

def actualTarget (J1 : List (Option Bool))
    (blankCount : Nat) : Tape Bool :=
  { left := none ::
      (pairParityEraserPairFlatten (none :: J1)).reverse ++
        [none, some false, some true] ++
          List.replicate blankCount none
    head := none
    right := [] }

def markerTarget (J1 : List (Option Bool)) : Tape Bool :=
  rightEndCompactionSourceTape
    ([some true, some false, none] ++
      pairParityEraserPairFlatten (none :: J1) ++ [none])

theorem actualTarget_equiv_markerTarget
    (J1 : List (Option Bool)) (blankCount : Nat) :
    Tape.Equiv (actualTarget J1 blankCount) (markerTarget J1) := by
  simp [actualTarget, markerTarget, rightEndCompactionSourceTape,
    tapeAtCells, Tape.Equiv, List.reverse_append,
    List.append_assoc]
  rw [show
      none ::
          ((pairParityEraserPairFlatten (none :: J1)).reverse ++
            none :: some false :: some true ::
              List.replicate blankCount none) =
        (none ::
          ((pairParityEraserPairFlatten (none :: J1)).reverse ++
            [none, some false, some true])) ++
          List.replicate blankCount none by
        simp [List.append_assoc]]
  rw [pairParityEraserDropTrailingNone_append_replicate]

def fullSource (J1 : List (Option Bool))
    (t u s v : Bool) (w1 w0 : List Bool) : Tape Bool :=
  { left := none ::
      ((pairParityEraserPairFlatten (none :: J1)).reverse ++
        (none :: (some t :: some u :: (w1.map some ++
          (none :: (some s :: some v :: (w0.map some ++ [none])))))))
    head := none
    right := [] }

theorem run_full
    (J1 zs : List (Option Bool))
    (hJ1 : J1 = zs ++ [none])
    (t u s v : Bool) (w1 w0 : List Bool) :
    description.HaltsFromTape
      (fullSource J1 t u s v w1 w0)
      (actualTarget J1 (w0.length + w1.length + 4)) := by
  have hFR : (pairParityEraserPairFlatten (none :: J1)).reverse =
      none :: none ::
        pairParityEraserPairFlattenRev (zs.reverse ++ [none]) := by
    rw [pairParityEraserPairFlatten_reverse, hJ1]
    simp [pairParityEraserPairFlattenRev,
      pairParityEraserPairFlattenRev_append, List.reverse_append]
  have hF : pairParityEraserPairFlatten (none :: J1) =
      (pairParityEraserPairFlattenRev (zs.reverse ++ [none])).reverse ++
        [none, none] := by
    have h := congrArg List.reverse hFR
    simpa [List.reverse_reverse, List.reverse_cons, List.append_assoc]
      using h
  have hstep1 :
      (pairParityEraserPairFlattenRev (zs.reverse ++ [none])).reverse ++
          (none :: none :: [some true, some true]) =
        none :: ((none :: pairParityEraserPairFlatten J1) ++
          [some true, some true]) := by
    have h2 : (none : Option Bool) ::
        ((none :: pairParityEraserPairFlatten J1) ++
          [some true, some true]) =
        pairParityEraserPairFlatten (none :: J1) ++
          [some true, some true] := by
      simp [pairParityEraserPairFlatten]
    rw [h2, hF]
    simp [List.append_assoc]
  have hblanks :
      List.replicate w0.length none ++
          (none :: (List.replicate (w1.length + 1) none ++
            ([some true, some false, none] ++
              ((pairParityEraserPairFlattenRev
                  (zs.reverse ++ [none])).reverse ++
                (none :: none :: [some true, some true]))))) =
        List.replicate (w0.length + w1.length + 2) none ++
          (some true :: some false :: none :: none ::
            ((none :: pairParityEraserPairFlatten J1) ++
              [some true, some true])) := by
    rw [hstep1]
    rw [assemble_blank_prefix]
    rfl
  have hlast : pairParityEraserLastCell J1 none = none := by
    rw [hJ1]
    exact pairParityEraserLastCell_append_none zs none
  let steps :=
    2 + ((2 * (zs.reverse ++ [none]).length + 2) +
      ((w1.length + 4) + (1 + ((w0.length + 2) +
        ((w0.length + w1.length + 2 + 1) +
          (3 + ((2 * J1.length + 2) + 3)))))))
  have hrun : description.runConfig steps
      { state := 0
        tape :=
          { left := none :: none :: none ::
              (pairParityEraserPairFlattenRev (zs.reverse ++ [none]) ++
                (none :: (some t :: some u :: (w1.map some ++
                  (none :: (some s :: some v ::
                    (w0.map some ++ [none])))))))
            head := none
            right := [] } } =
      { state := 10
        tape := actualTarget J1 (w0.length + w1.length + 4) } := by
    dsimp [steps]
    rw [runConfig_add, run_mark]
    rw [runConfig_add, run_scan]
    rw [runConfig_add, run_secondField]
    rw [runConfig_add, run_gap]
    rw [runConfig_add, run_erase6]
    simp only [List.append_assoc]
    rw [hblanks]
    rw [runConfig_add, run_skip7]
    rw [runConfig_add, run_handoff]
    rw [runConfig_add, run_ret7]
    rw [hlast]
    rw [show pairParityEraserScanState none = 7 from rfl]
    rw [run_finish]
    simp [actualTarget, pairParityEraserReplicate_none_middle,
      List.append_assoc]
  have hsource : fullSource J1 t u s v w1 w0 =
        { left := none :: none :: none ::
            (pairParityEraserPairFlattenRev (zs.reverse ++ [none]) ++
              (none :: (some t :: some u :: (w1.map some ++
                (none :: (some s :: some v ::
                  (w0.map some ++ [none])))))))
          head := none
          right := [] } := by
    rw [fullSource]
    rw [hFR]
    simp only [List.cons_append]
  refine ⟨steps, ?_, ?_⟩
  · rw [show description.start = 0 from rfl, hsource]
    exact congrArg Configuration.state hrun
  · rw [show description.start = 0 from rfl, hsource]
    exact congrArg Configuration.tape hrun

theorem haltsFrom_full_markerTarget
    (J1 zs : List (Option Bool))
    (hJ1 : J1 = zs ++ [none])
    (t u s v : Bool) (w1 w0 : List Bool) :
    description.HaltsFromTapeEquiv
      (fullSource J1 t u s v w1 w0)
      (markerTarget J1) := by
  exact
    ⟨actualTarget J1 (w0.length + w1.length + 4),
      run_full J1 zs hJ1 t u s v w1 w0,
      actualTarget_equiv_markerTarget J1
        (w0.length + w1.length + 4)⟩

def guardedMarkerTargetTape
    (bits : Word Bool) (padding : List (Option Bool)) : Tape Bool :=
  markerTarget
    (none :: none ::
      selectedSegmentLogicalTapeDecoderPayloadCells bits padding)

def GuardedMarkerHandoffSpec (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    forall (T0 T1 : Tape Bool) (bits : Word Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding)
        (guardedMarkerTargetTape bits padding)

theorem description_spec : GuardedMarkerHandoffSpec description := by
  refine ⟨description_subroutineReady, ?_⟩
  intro T0 T1 bits padding
  obtain ⟨t, u, w1, hw1⟩ :=
    pairParityEraserExists_two_cons
      (logicalTapeBits (guardLogicalTape T1)).reverse
      (by
        rw [List.length_reverse]
        exact pairParityEraserGuardedBits_two_le T1)
  obtain ⟨s, v, w0, hw0⟩ :=
    pairParityEraserExists_two_cons
      (logicalTapeBits (guardLogicalTape T0)).reverse
      (by
        rw [List.length_reverse]
        exact pairParityEraserGuardedBits_two_le T0)
  have hJ1 : (none :: none ::
      selectedSegmentLogicalTapeDecoderPayloadCells bits padding :
        List (Option Bool)) =
      (none :: none :: (bits.map some ++ (none :: padding))) ++
        [none] := by
    simp [selectedSegmentLogicalTapeDecoderPayloadCells, List.append_assoc]
  have hrun :=
    haltsFrom_full_markerTarget
      (none :: none ::
        selectedSegmentLogicalTapeDecoderPayloadCells bits padding)
      (none :: none :: (bits.map some ++ (none :: padding)))
      hJ1 t u s v w1 w0
  have hsource :
      guardedTwoTapeStructuredPrefixEraserSourceTape T0 T1 bits padding =
        fullSource
          (none :: none ::
            selectedSegmentLogicalTapeDecoderPayloadCells bits padding)
          t u s v w1 w0 := by
    rw [pairParityEraserSourceTape_shape]
    rw [pairParityEraserFootprint_eq_pairFlatten]
    rw [pairParityEraserPrefixCells_reverse]
    rw [hw1, hw0]
    simp [fullSource]
  rw [hsource]
  simpa [guardedMarkerTargetTape] using hrun

theorem guardedMarkerTargetTape_eq_markedFootprint
    (bits : Word Bool) (padding : List (Option Bool)) :
    guardedMarkerTargetTape bits padding =
      rightEndCompactionSourceTape
        ([some true, some false, none] ++
          selectedSegmentLogicalTapeDecoderDensifierFootprintCells
            bits padding ++ [none]) := by
  rw [guardedMarkerTargetTape, markerTarget]
  rw [pairParityEraserFootprint_eq_pairFlatten]

theorem guardedMarkerTargetTape_eq_liveSource
    (useAccept : Bool) (L : DovetailLayout) :
    guardedMarkerTargetTape (ParsedLayoutBits L)
        (postFieldDecodedPrefixScanPadding useAccept L) =
      countWindowPostFieldDecodedPrefixSelectedSegmentMarkedFootprintCompactorSourceTape
        useAccept L := by
  rw [guardedMarkerTargetTape_eq_markedFootprint]
  rfl

end MarkerHandoff
end LiveIngress
end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC

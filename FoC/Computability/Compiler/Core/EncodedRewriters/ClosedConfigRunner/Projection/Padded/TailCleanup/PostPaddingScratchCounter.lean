import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.PostPaddingRejectRoute

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncodedRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

/--
Temporary marker block used by the scratch-count extender.  The {lit}`false`
cells are counted markers and the final {lit}`true` cell is a moving right
sentinel.
-/
def scratchCounterMarkerBlock (markers : Nat) : List (Option Bool) :=
  List.append (List.replicate markers (some false : Option Bool))
    [some true, none]

theorem scratchCounterMarkerBlock_zero :
    scratchCounterMarkerBlock 0 = [some true, none] := by
  rfl

theorem scratchCounterMarkerBlock_succ (markers : Nat) :
    scratchCounterMarkerBlock (markers + 1) =
      some false :: scratchCounterMarkerBlock markers := by
  simp [scratchCounterMarkerBlock, List.replicate_succ]

theorem scratchCounter_replicate_false_append_cons
    (markers : Nat) (tail : List (Option Bool)) :
    List.append
        (List.replicate markers (some false : Option Bool))
        (some false :: tail) =
      List.append
        (List.replicate (markers + 1) (some false : Option Bool))
        tail := by
  induction markers with
  | zero =>
      rfl
  | succ markers ih =>
      calc
        List.append
            (List.replicate (markers + 1)
              (some false : Option Bool))
            (some false :: tail) =
          some false ::
            List.append
              (List.replicate markers (some false : Option Bool))
              (some false :: tail) := by
              simp [List.replicate_succ]
        _ =
          some false ::
            List.append
              (List.replicate (markers + 1)
                (some false : Option Bool))
              tail := by
              rw [ih]
        _ =
          List.append
            (List.replicate (markers + 1 + 1)
              (some false : Option Bool))
            tail := by
              simp [List.replicate_succ]

theorem scratchCounter_replicate_none_append_cons
    (markers : Nat) (tail : List (Option Bool)) :
    List.append
        (List.replicate markers (none : Option Bool))
        (none :: tail) =
      List.append
        (List.replicate (markers + 1) (none : Option Bool))
        tail := by
  induction markers with
  | zero =>
      rfl
  | succ markers ih =>
      calc
        List.append
            (List.replicate (markers + 1) (none : Option Bool))
            (none :: tail) =
          none ::
            List.append
              (List.replicate markers (none : Option Bool))
              (none :: tail) := by
              simp [List.replicate_succ]
        _ =
          none ::
            List.append
              (List.replicate (markers + 1) (none : Option Bool))
              tail := by
              rw [ih]
        _ =
          List.append
            (List.replicate (markers + 1 + 1) (none : Option Bool))
            tail := by
              simp [List.replicate_succ]

theorem tapeAtCells_moveRight_cons
    (leftRev : List (Option Bool)) (cell : Option Bool)
    (rest : List (Option Bool)) :
    Tape.moveRight (tapeAtCells leftRev (cell :: rest)) =
      tapeAtCells (cell :: leftRev) rest := by
  cases rest <;> rfl

/--
Preserve raw source cells while appending one temporary {lit}`false` marker
for each decoded/raw source bit.  The marker area is terminated by a moving
{lit}`true` sentinel so appending a marker grows the exact tape window.
-/
def scratchCounterPreservingMarkerAppendDescription :
    MachineDescription where
  stateCount := 50
  start := 0
  halt := 49
  transitions :=
    [ transition 0 (some false) none Direction.right 10
    , transition 0 (some true) none Direction.right 20
    , transition 0 none none Direction.right 49

    , transition 10 (some false) (some false) Direction.right 10
    , transition 10 (some true) (some true) Direction.right 10
    , transition 10 none none Direction.right 11
    , transition 11 (some false) (some false) Direction.right 11
    , transition 11 (some true) (some false) Direction.right 12
    , transition 12 none (some true) Direction.left 13
    , transition 13 (some false) (some false) Direction.left 13
    , transition 13 none none Direction.left 14
    , transition 14 (some false) (some false) Direction.left 14
    , transition 14 (some true) (some true) Direction.left 14
    , transition 14 none (some false) Direction.right 0

    , transition 20 (some false) (some false) Direction.right 20
    , transition 20 (some true) (some true) Direction.right 20
    , transition 20 none none Direction.right 21
    , transition 21 (some false) (some false) Direction.right 21
    , transition 21 (some true) (some false) Direction.right 22
    , transition 22 none (some true) Direction.left 23
    , transition 23 (some false) (some false) Direction.left 23
    , transition 23 none none Direction.left 24
    , transition 24 (some false) (some false) Direction.left 24
    , transition 24 (some true) (some true) Direction.left 24
    , transition 24 none (some true) Direction.right 0
    ]

private abbrev SCPMA :=
  scratchCounterPreservingMarkerAppendDescription

theorem scratchCounterPreservingMarkerAppendDescription_wellFormed :
    SCPMA.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := SCPMA.transitions)
      (stateCount := SCPMA.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := SCPMA.transitions)
      (by decide)

theorem scratchCounterPreservingMarkerAppendDescription_haltTransitionFree :
    SCPMA.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := SCPMA.transitions)
    (state := SCPMA.halt)
    (by decide)

theorem scratchCounterPreservingMarkerAppendDescription_subroutineReady :
    SCPMA.SubroutineReady :=
  ⟨scratchCounterPreservingMarkerAppendDescription_wellFormed,
    scratchCounterPreservingMarkerAppendDescription_haltTransitionFree⟩

theorem scratchCounterPreservingMarkerAppendDescription_run_scan_source_false
    (leftRev : List (Option Bool)) (rest : Word Bool)
    (right : List (Option Bool)) :
    SCPMA.runConfig rest.length
        { state := 10
          tape :=
            tapeAtCells leftRev
              (List.append (rest.map some) right) } =
      { state := 10
        tape :=
          tapeAtCells
            (List.append (rest.reverse.map some) leftRev)
            right } := by
  induction rest generalizing leftRev with
  | nil =>
      rfl
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        omega]
      rw [runConfig_add]
      have hstep :
          SCPMA.runConfig 1
              { state := 10
                tape :=
                  tapeAtCells leftRev
                    (List.append ((bit :: rest).map some) right) } =
            { state := 10
              tape :=
                tapeAtCells (some bit :: leftRev)
                  (List.append (rest.map some) right) } := by
        cases bit <;> cases rest <;> cases right <;>
          simp [SCPMA,
            scratchCounterPreservingMarkerAppendDescription,
            runConfig, stepConfig, lookupTransition, Matches,
            transition, tapeAtCells, Tape.read, Tape.write,
            Tape.move, Tape.moveRight]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: leftRev)

theorem scratchCounterPreservingMarkerAppendDescription_run_scan_source_true
    (leftRev : List (Option Bool)) (rest : Word Bool)
    (right : List (Option Bool)) :
    SCPMA.runConfig rest.length
        { state := 20
          tape :=
            tapeAtCells leftRev
              (List.append (rest.map some) right) } =
      { state := 20
        tape :=
          tapeAtCells
            (List.append (rest.reverse.map some) leftRev)
            right } := by
  induction rest generalizing leftRev with
  | nil =>
      rfl
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        omega]
      rw [runConfig_add]
      have hstep :
          SCPMA.runConfig 1
              { state := 20
                tape :=
                  tapeAtCells leftRev
                    (List.append ((bit :: rest).map some) right) } =
            { state := 20
              tape :=
                tapeAtCells (some bit :: leftRev)
                  (List.append (rest.map some) right) } := by
        cases bit <;> cases rest <;> cases right <;>
          simp [SCPMA,
            scratchCounterPreservingMarkerAppendDescription,
            runConfig, stepConfig, lookupTransition, Matches,
            transition, tapeAtCells, Tape.read, Tape.write,
            Tape.move, Tape.moveRight]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: leftRev)

theorem scratchCounterPreservingMarkerAppendDescription_run_scan_markers_false
    (leftRev : List (Option Bool)) (markers : Nat)
    (right : List (Option Bool)) :
    SCPMA.runConfig markers
        { state := 11
          tape :=
            tapeAtCells leftRev
              (List.append
                (List.replicate markers (some false : Option Bool))
                right) } =
      { state := 11
        tape :=
          tapeAtCells
            (List.append
              (List.replicate markers (some false : Option Bool))
              leftRev)
            right } := by
  induction markers generalizing leftRev with
  | zero =>
      rfl
  | succ markers ih =>
      rw [show markers + 1 = 1 + markers by omega]
      rw [runConfig_add]
      have hstep :
          SCPMA.runConfig 1
              { state := 11
                tape :=
                  tapeAtCells leftRev
                    (List.append
                      (List.replicate (1 + markers)
                        (some false : Option Bool))
                      right) } =
            { state := 11
              tape :=
                tapeAtCells (some false :: leftRev)
                  (List.append
                    (List.replicate markers
                      (some false : Option Bool))
                    right) } := by
        rw [show
            List.replicate (1 + markers)
                (some false : Option Bool) =
                some false ::
                List.replicate markers
                  (some false : Option Bool) by
          simp [Nat.add_comm, List.replicate_succ]]
        simp [SCPMA,
          scratchCounterPreservingMarkerAppendDescription,
          runConfig, stepConfig, lookupTransition, Matches,
          transition, tapeAtCells, Tape.read, Tape.write,
          Tape.move, Tape.moveRight]
        split <;> simp_all
      rw [hstep]
      calc
        SCPMA.runConfig markers
            { state := 11
              tape :=
                tapeAtCells (some false :: leftRev)
                  (List.append
                    (List.replicate markers
                      (some false : Option Bool))
                    right) } =
          { state := 11
            tape :=
              tapeAtCells
                (List.append
                  (List.replicate markers
                    (some false : Option Bool))
                  (some false :: leftRev))
                right } := by
            exact ih (some false :: leftRev)
        _ =
          { state := 11
            tape :=
              tapeAtCells
                (List.append
                  (List.replicate (1 + markers)
                    (some false : Option Bool))
                  leftRev)
                right } := by
            rw [scratchCounter_replicate_false_append_cons markers leftRev]
            simp [Nat.add_comm]

theorem scratchCounterPreservingMarkerAppendDescription_run_scan_markers_true
    (leftRev : List (Option Bool)) (markers : Nat)
    (right : List (Option Bool)) :
    SCPMA.runConfig markers
        { state := 21
          tape :=
            tapeAtCells leftRev
              (List.append
                (List.replicate markers (some false : Option Bool))
                right) } =
      { state := 21
        tape :=
          tapeAtCells
            (List.append
              (List.replicate markers (some false : Option Bool))
              leftRev)
            right } := by
  induction markers generalizing leftRev with
  | zero =>
      rfl
  | succ markers ih =>
      rw [show markers + 1 = 1 + markers by omega]
      rw [runConfig_add]
      have hstep :
          SCPMA.runConfig 1
              { state := 21
                tape :=
                  tapeAtCells leftRev
                    (List.append
                      (List.replicate (1 + markers)
                        (some false : Option Bool))
                      right) } =
            { state := 21
              tape :=
                tapeAtCells (some false :: leftRev)
                  (List.append
                    (List.replicate markers
                      (some false : Option Bool))
                    right) } := by
        rw [show
            List.replicate (1 + markers)
                (some false : Option Bool) =
                some false ::
                List.replicate markers
                  (some false : Option Bool) by
          simp [Nat.add_comm, List.replicate_succ]]
        simp [SCPMA,
          scratchCounterPreservingMarkerAppendDescription,
          runConfig, stepConfig, lookupTransition, Matches,
          transition, tapeAtCells, Tape.read, Tape.write,
          Tape.move, Tape.moveRight]
        split <;> simp_all
      rw [hstep]
      calc
        SCPMA.runConfig markers
            { state := 21
              tape :=
                tapeAtCells (some false :: leftRev)
                  (List.append
                    (List.replicate markers
                      (some false : Option Bool))
                    right) } =
          { state := 21
            tape :=
              tapeAtCells
                (List.append
                  (List.replicate markers
                    (some false : Option Bool))
                  (some false :: leftRev))
                right } := by
            exact ih (some false :: leftRev)
        _ =
          { state := 21
            tape :=
              tapeAtCells
                (List.append
                  (List.replicate (1 + markers)
                    (some false : Option Bool))
                  leftRev)
                right } := by
            rw [scratchCounter_replicate_false_append_cons markers leftRev]
            simp [Nat.add_comm]

theorem scratchCounterPreservingMarkerAppendDescription_run_extend_marker_false
    (leftRev : List (Option Bool)) (markers : Nat) :
    SCPMA.runConfig (markers + 2)
        { state := 11
          tape := tapeAtCells leftRev
            (scratchCounterMarkerBlock markers) } =
      { state := 13
        tape :=
          tapeAtCells
            (List.append
              (List.replicate markers (some false : Option Bool))
              leftRev)
            [some false, some true] } := by
  simp only [scratchCounterMarkerBlock]
  rw [runConfig_add]
  rw [scratchCounterPreservingMarkerAppendDescription_run_scan_markers_false]
  simp [SCPMA,
    scratchCounterPreservingMarkerAppendDescription,
    runConfig, stepConfig, lookupTransition, Matches, transition,
    tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    Tape.moveRight]

theorem scratchCounterPreservingMarkerAppendDescription_run_extend_marker_true
    (leftRev : List (Option Bool)) (markers : Nat) :
    SCPMA.runConfig (markers + 2)
        { state := 21
          tape := tapeAtCells leftRev
            (scratchCounterMarkerBlock markers) } =
      { state := 23
        tape :=
          tapeAtCells
            (List.append
              (List.replicate markers (some false : Option Bool))
              leftRev)
            [some false, some true] } := by
  simp only [scratchCounterMarkerBlock]
  rw [runConfig_add]
  rw [scratchCounterPreservingMarkerAppendDescription_run_scan_markers_true]
  simp [SCPMA,
    scratchCounterPreservingMarkerAppendDescription,
    runConfig, stepConfig, lookupTransition, Matches, transition,
    tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    Tape.moveRight]

theorem scratchCounterPreservingMarkerAppendDescription_run_extend_marker_false_withRight
    (leftRev : List (Option Bool)) (markers : Nat)
    (padding : List (Option Bool)) :
    SCPMA.runConfig (markers + 2)
        { state := 11
          tape :=
            tapeAtCells leftRev
              (List.append
                (List.replicate markers (some false : Option Bool))
                (some true :: none :: padding)) } =
      { state := 13
        tape :=
          tapeAtCells
            (List.append
              (List.replicate markers (some false : Option Bool))
              leftRev)
            (some false :: some true :: padding) } := by
  rw [runConfig_add]
  rw [scratchCounterPreservingMarkerAppendDescription_run_scan_markers_false]
  simp [SCPMA,
    scratchCounterPreservingMarkerAppendDescription,
    runConfig, stepConfig, lookupTransition, Matches, transition,
    tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    Tape.moveRight]

theorem scratchCounterPreservingMarkerAppendDescription_run_extend_marker_true_withRight
    (leftRev : List (Option Bool)) (markers : Nat)
    (padding : List (Option Bool)) :
    SCPMA.runConfig (markers + 2)
        { state := 21
          tape :=
            tapeAtCells leftRev
              (List.append
                (List.replicate markers (some false : Option Bool))
                (some true :: none :: padding)) } =
      { state := 23
        tape :=
          tapeAtCells
            (List.append
              (List.replicate markers (some false : Option Bool))
              leftRev)
            (some false :: some true :: padding) } := by
  rw [runConfig_add]
  rw [scratchCounterPreservingMarkerAppendDescription_run_scan_markers_true]
  simp [SCPMA,
    scratchCounterPreservingMarkerAppendDescription,
    runConfig, stepConfig, lookupTransition, Matches, transition,
    tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    Tape.moveRight]

theorem scratchCounterPreservingMarkerAppendDescription_run_rewind_markers_false
    (baseLeft right : List (Option Bool)) (markers : Nat) :
    SCPMA.runConfig (markers + 1)
        { state := 13
          tape :=
            tapeAtCells
              (List.append
                (List.replicate markers (some false : Option Bool))
                (none :: baseLeft))
              (some false :: right) } =
      { state := 13
        tape :=
          tapeAtCells baseLeft
            (none ::
              List.append
                (List.replicate (markers + 1)
                  (some false : Option Bool))
                right) } := by
  induction markers generalizing right with
  | zero =>
      cases baseLeft <;> cases right <;>
        simp [SCPMA,
          scratchCounterPreservingMarkerAppendDescription,
          runConfig, stepConfig, lookupTransition, Matches,
          transition, tapeAtCells, Tape.read, Tape.write,
          Tape.move, Tape.moveLeft]
  | succ markers ih =>
      rw [show markers + 1 + 1 = 1 + (markers + 1) by omega]
      rw [runConfig_add]
      have hstep :
          SCPMA.runConfig 1
              { state := 13
                tape :=
                  tapeAtCells
                    (List.append
                      (List.replicate (markers + 1)
                        (some false : Option Bool))
                      (none :: baseLeft))
                    (some false :: right) } =
            { state := 13
              tape :=
                tapeAtCells
                  (List.append
                    (List.replicate markers
                      (some false : Option Bool))
                    (none :: baseLeft))
                  (some false :: some false :: right) } := by
        rw [show
            List.replicate (markers + 1)
                (some false : Option Bool) =
              some false ::
                List.replicate markers
                  (some false : Option Bool) by
          simp [List.replicate_succ]]
        simp [SCPMA,
          scratchCounterPreservingMarkerAppendDescription,
          runConfig, stepConfig, lookupTransition, Matches,
          transition, tapeAtCells, Tape.read, Tape.write,
          Tape.move, Tape.moveLeft]
      rw [hstep]
      calc
        SCPMA.runConfig (markers + 1)
            { state := 13
              tape :=
                tapeAtCells
                  (List.append
                    (List.replicate markers
                      (some false : Option Bool))
                    (none :: baseLeft))
                  (some false :: some false :: right) } =
          { state := 13
            tape :=
              tapeAtCells baseLeft
                (none ::
                  List.append
                    (List.replicate (markers + 1)
                      (some false : Option Bool))
                    (some false :: right)) } := by
            exact ih (some false :: right)
        _ =
          { state := 13
            tape :=
              tapeAtCells baseLeft
                (none ::
                  List.append
                    (List.replicate (1 + (markers + 1))
                      (some false : Option Bool))
                    right) } := by
            rw [show 1 + (markers + 1) = markers + 1 + 1 by omega]
            rw [scratchCounter_replicate_false_append_cons
              (markers + 1) right]

theorem scratchCounterPreservingMarkerAppendDescription_run_rewind_markers_true
    (baseLeft right : List (Option Bool)) (markers : Nat) :
    SCPMA.runConfig (markers + 1)
        { state := 23
          tape :=
            tapeAtCells
              (List.append
                (List.replicate markers (some false : Option Bool))
                (none :: baseLeft))
              (some false :: right) } =
      { state := 23
        tape :=
          tapeAtCells baseLeft
            (none ::
              List.append
                (List.replicate (markers + 1)
                  (some false : Option Bool))
                right) } := by
  induction markers generalizing right with
  | zero =>
      cases baseLeft <;> cases right <;>
        simp [SCPMA,
          scratchCounterPreservingMarkerAppendDescription,
          runConfig, stepConfig, lookupTransition, Matches,
          transition, tapeAtCells, Tape.read, Tape.write,
          Tape.move, Tape.moveLeft]
  | succ markers ih =>
      rw [show markers + 1 + 1 = 1 + (markers + 1) by omega]
      rw [runConfig_add]
      have hstep :
          SCPMA.runConfig 1
              { state := 23
                tape :=
                  tapeAtCells
                    (List.append
                      (List.replicate (markers + 1)
                        (some false : Option Bool))
                      (none :: baseLeft))
                    (some false :: right) } =
            { state := 23
              tape :=
                tapeAtCells
                  (List.append
                    (List.replicate markers
                      (some false : Option Bool))
                    (none :: baseLeft))
                  (some false :: some false :: right) } := by
        rw [show
            List.replicate (markers + 1)
                (some false : Option Bool) =
              some false ::
                List.replicate markers
                  (some false : Option Bool) by
          simp [List.replicate_succ]]
        simp [SCPMA,
          scratchCounterPreservingMarkerAppendDescription,
          runConfig, stepConfig, lookupTransition, Matches,
          transition, tapeAtCells, Tape.read, Tape.write,
          Tape.move, Tape.moveLeft]
      rw [hstep]
      calc
        SCPMA.runConfig (markers + 1)
            { state := 23
              tape :=
                tapeAtCells
                  (List.append
                    (List.replicate markers
                      (some false : Option Bool))
                    (none :: baseLeft))
                  (some false :: some false :: right) } =
          { state := 23
            tape :=
              tapeAtCells baseLeft
                (none ::
                  List.append
                    (List.replicate (markers + 1)
                      (some false : Option Bool))
                    (some false :: right)) } := by
            exact ih (some false :: right)
        _ =
          { state := 23
            tape :=
              tapeAtCells baseLeft
                (none ::
                  List.append
                    (List.replicate (1 + (markers + 1))
                      (some false : Option Bool))
                    right) } := by
            rw [show 1 + (markers + 1) = markers + 1 + 1 by omega]
            rw [scratchCounter_replicate_false_append_cons
              (markers + 1) right]

theorem scratchCounterPreservingMarkerAppendDescription_run_restore_source_false_from_current
    (baseLeft : List (Option Bool)) (leftStack : Word Bool)
    (current : Bool) (right : List (Option Bool)) :
    SCPMA.runConfig (leftStack.length + 2)
        { state := 14
          tape :=
            tapeAtCells
              (List.append (leftStack.map some) (none :: baseLeft))
              (some current :: right) } =
      { state := 0
        tape :=
          tapeAtCells (some false :: baseLeft)
            (List.append
              ((List.append leftStack.reverse [current]).map some)
              right) } := by
  induction leftStack generalizing current right with
  | nil =>
      cases current <;> cases baseLeft <;> cases right <;>
        simp [SCPMA,
          scratchCounterPreservingMarkerAppendDescription,
          runConfig, stepConfig, lookupTransition, Matches,
          transition, tapeAtCells, Tape.read, Tape.write,
          Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons next rest ih =>
      rw [show (next :: rest).length + 2 =
          1 + (rest.length + 2) by
        simp
        omega]
      rw [runConfig_add]
      have hstep :
          SCPMA.runConfig 1
              { state := 14
                tape :=
                  tapeAtCells
                    (List.append ((next :: rest).map some)
                      (none :: baseLeft))
                    (some current :: right) } =
            { state := 14
              tape :=
                tapeAtCells
                  (List.append (rest.map some) (none :: baseLeft))
                  (some next :: some current :: right) } := by
        cases current <;> cases next <;>
          simp [SCPMA,
            scratchCounterPreservingMarkerAppendDescription,
            runConfig, stepConfig, lookupTransition, Matches,
            transition, tapeAtCells, Tape.read, Tape.write,
            Tape.move, Tape.moveLeft]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih next (some current :: right)

theorem scratchCounterPreservingMarkerAppendDescription_run_restore_source_false
    (baseLeft : List (Option Bool)) (leftStack : Word Bool)
    (right : List (Option Bool)) :
    SCPMA.runConfig (leftStack.length + 2)
        { state := 13
          tape :=
            tapeAtCells
              (List.append (leftStack.map some) (none :: baseLeft))
              (none :: right) } =
      { state := 0
        tape :=
          tapeAtCells (some false :: baseLeft)
            (List.append (leftStack.reverse.map some)
              (none :: right)) } := by
  cases leftStack with
  | nil =>
      cases baseLeft <;> cases right <;>
        simp [SCPMA,
          scratchCounterPreservingMarkerAppendDescription,
          runConfig, stepConfig, lookupTransition, Matches,
          transition, tapeAtCells, Tape.read, Tape.write,
          Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons current rest =>
      rw [show (current :: rest).length + 2 =
          1 + (rest.length + 2) by
        simp
        omega]
      rw [runConfig_add]
      have hstep :
          SCPMA.runConfig 1
              { state := 13
                tape :=
                  tapeAtCells
                    (List.append ((current :: rest).map some)
                      (none :: baseLeft))
                    (none :: right) } =
            { state := 14
              tape :=
                tapeAtCells
                  (List.append (rest.map some) (none :: baseLeft))
                  (some current :: none :: right) } := by
        cases current <;>
          simp [SCPMA,
            scratchCounterPreservingMarkerAppendDescription,
            runConfig, stepConfig, lookupTransition, Matches,
            transition, tapeAtCells, Tape.read, Tape.write,
            Tape.move, Tape.moveLeft]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        scratchCounterPreservingMarkerAppendDescription_run_restore_source_false_from_current
          baseLeft rest current (none :: right)

theorem scratchCounterPreservingMarkerAppendDescription_run_restore_source_true_from_current
    (baseLeft : List (Option Bool)) (leftStack : Word Bool)
    (current : Bool) (right : List (Option Bool)) :
    SCPMA.runConfig (leftStack.length + 2)
        { state := 24
          tape :=
            tapeAtCells
              (List.append (leftStack.map some) (none :: baseLeft))
              (some current :: right) } =
      { state := 0
        tape :=
          tapeAtCells (some true :: baseLeft)
            (List.append
              ((List.append leftStack.reverse [current]).map some)
              right) } := by
  induction leftStack generalizing current right with
  | nil =>
      cases current <;> cases baseLeft <;> cases right <;>
        simp [SCPMA,
          scratchCounterPreservingMarkerAppendDescription,
          runConfig, stepConfig, lookupTransition, Matches,
          transition, tapeAtCells, Tape.read, Tape.write,
          Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons next rest ih =>
      rw [show (next :: rest).length + 2 =
          1 + (rest.length + 2) by
        simp
        omega]
      rw [runConfig_add]
      have hstep :
          SCPMA.runConfig 1
              { state := 24
                tape :=
                  tapeAtCells
                    (List.append ((next :: rest).map some)
                      (none :: baseLeft))
                    (some current :: right) } =
            { state := 24
              tape :=
                tapeAtCells
                  (List.append (rest.map some) (none :: baseLeft))
                  (some next :: some current :: right) } := by
        cases current <;> cases next <;>
          simp [SCPMA,
            scratchCounterPreservingMarkerAppendDescription,
            runConfig, stepConfig, lookupTransition, Matches,
            transition, tapeAtCells, Tape.read, Tape.write,
            Tape.move, Tape.moveLeft]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih next (some current :: right)

theorem scratchCounterPreservingMarkerAppendDescription_run_restore_source_true
    (baseLeft : List (Option Bool)) (leftStack : Word Bool)
    (right : List (Option Bool)) :
    SCPMA.runConfig (leftStack.length + 2)
        { state := 23
          tape :=
            tapeAtCells
              (List.append (leftStack.map some) (none :: baseLeft))
              (none :: right) } =
      { state := 0
        tape :=
          tapeAtCells (some true :: baseLeft)
            (List.append (leftStack.reverse.map some)
              (none :: right)) } := by
  cases leftStack with
  | nil =>
      cases baseLeft <;> cases right <;>
        simp [SCPMA,
          scratchCounterPreservingMarkerAppendDescription,
          runConfig, stepConfig, lookupTransition, Matches,
          transition, tapeAtCells, Tape.read, Tape.write,
          Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons current rest =>
      rw [show (current :: rest).length + 2 =
          1 + (rest.length + 2) by
        simp
        omega]
      rw [runConfig_add]
      have hstep :
          SCPMA.runConfig 1
              { state := 23
                tape :=
                  tapeAtCells
                    (List.append ((current :: rest).map some)
                      (none :: baseLeft))
                    (none :: right) } =
            { state := 24
              tape :=
                tapeAtCells
                  (List.append (rest.map some) (none :: baseLeft))
                  (some current :: none :: right) } := by
        cases current <;>
          simp [SCPMA,
            scratchCounterPreservingMarkerAppendDescription,
            runConfig, stepConfig, lookupTransition, Matches,
            transition, tapeAtCells, Tape.read, Tape.write,
            Tape.move, Tape.moveLeft]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        scratchCounterPreservingMarkerAppendDescription_run_restore_source_true_from_current
          baseLeft rest current (none :: right)

theorem scratchCounterPreservingMarkerAppendDescription_run_cell_false_withRight
    (baseLeft : List (Option Bool)) (rest : Word Bool)
    (markers : Nat) (padding : List (Option Bool)) :
    SCPMA.runConfig
        (1 + (rest.length + (1 + ((markers + 2) +
          ((markers + 1) + (rest.length + 2))))))
        { state := 0
          tape :=
            tapeAtCells baseLeft
              (some false ::
                List.append (rest.map some)
                  (none ::
                    List.append
                      (List.replicate markers
                        (some false : Option Bool))
                      (some true :: none :: padding))) } =
      { state := 0
        tape :=
          tapeAtCells (some false :: baseLeft)
            (List.append (rest.map some)
              (none ::
                List.append
                  (List.replicate (markers + 1)
                    (some false : Option Bool))
                  (some true :: padding))) } := by
  rw [runConfig_add]
  have hstart :
      SCPMA.runConfig 1
          { state := 0
            tape :=
              tapeAtCells baseLeft
                (some false ::
                  List.append (rest.map some)
                    (none ::
                      List.append
                        (List.replicate markers
                          (some false : Option Bool))
                        (some true :: none :: padding))) } =
        { state := 10
          tape :=
            tapeAtCells (none :: baseLeft)
              (List.append (rest.map some)
                (none ::
                  List.append
                    (List.replicate markers
                      (some false : Option Bool))
                    (some true :: none :: padding))) } := by
    simp [SCPMA,
      scratchCounterPreservingMarkerAppendDescription,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]
    split <;> simp_all
  rw [hstart]
  rw [runConfig_add]
  rw [scratchCounterPreservingMarkerAppendDescription_run_scan_source_false]
  rw [runConfig_add]
  have hseparator :
      SCPMA.runConfig 1
          { state := 10
            tape :=
              tapeAtCells
                (List.append (rest.reverse.map some)
                  (none :: baseLeft))
                (none ::
                  List.append
                    (List.replicate markers
                      (some false : Option Bool))
                    (some true :: none :: padding)) } =
        { state := 11
          tape :=
            tapeAtCells
              (none ::
                List.append (rest.reverse.map some)
                  (none :: baseLeft))
              (List.append
                (List.replicate markers
                  (some false : Option Bool))
                (some true :: none :: padding)) } := by
    simp [SCPMA,
      scratchCounterPreservingMarkerAppendDescription,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]
    split <;> simp_all
  rw [hseparator]
  rw [runConfig_add]
  rw [scratchCounterPreservingMarkerAppendDescription_run_extend_marker_false_withRight]
  rw [runConfig_add]
  rw [scratchCounterPreservingMarkerAppendDescription_run_rewind_markers_false]
  simpa [List.reverse_reverse, List.map_append, List.append_assoc] using
    scratchCounterPreservingMarkerAppendDescription_run_restore_source_false
      baseLeft rest.reverse
      (List.append
        (List.replicate (markers + 1) (some false : Option Bool))
        (some true :: padding))

theorem scratchCounterPreservingMarkerAppendDescription_run_cell_true_withRight
    (baseLeft : List (Option Bool)) (rest : Word Bool)
    (markers : Nat) (padding : List (Option Bool)) :
    SCPMA.runConfig
        (1 + (rest.length + (1 + ((markers + 2) +
          ((markers + 1) + (rest.length + 2))))))
        { state := 0
          tape :=
            tapeAtCells baseLeft
              (some true ::
                List.append (rest.map some)
                  (none ::
                    List.append
                      (List.replicate markers
                        (some false : Option Bool))
                      (some true :: none :: padding))) } =
      { state := 0
        tape :=
          tapeAtCells (some true :: baseLeft)
            (List.append (rest.map some)
              (none ::
                List.append
                  (List.replicate (markers + 1)
                    (some false : Option Bool))
                  (some true :: padding))) } := by
  rw [runConfig_add]
  have hstart :
      SCPMA.runConfig 1
          { state := 0
            tape :=
              tapeAtCells baseLeft
                (some true ::
                  List.append (rest.map some)
                    (none ::
                      List.append
                        (List.replicate markers
                          (some false : Option Bool))
                        (some true :: none :: padding))) } =
        { state := 20
          tape :=
            tapeAtCells (none :: baseLeft)
              (List.append (rest.map some)
                (none ::
                  List.append
                    (List.replicate markers
                      (some false : Option Bool))
                    (some true :: none :: padding))) } := by
    simp [SCPMA,
      scratchCounterPreservingMarkerAppendDescription,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]
    split <;> simp_all
  rw [hstart]
  rw [runConfig_add]
  rw [scratchCounterPreservingMarkerAppendDescription_run_scan_source_true]
  rw [runConfig_add]
  have hseparator :
      SCPMA.runConfig 1
          { state := 20
            tape :=
              tapeAtCells
                (List.append (rest.reverse.map some)
                  (none :: baseLeft))
                (none ::
                  List.append
                    (List.replicate markers
                      (some false : Option Bool))
                    (some true :: none :: padding)) } =
        { state := 21
          tape :=
            tapeAtCells
              (none ::
                List.append (rest.reverse.map some)
                  (none :: baseLeft))
              (List.append
                (List.replicate markers
                  (some false : Option Bool))
                (some true :: none :: padding)) } := by
    simp [SCPMA,
      scratchCounterPreservingMarkerAppendDescription,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]
    split <;> simp_all
  rw [hseparator]
  rw [runConfig_add]
  rw [scratchCounterPreservingMarkerAppendDescription_run_extend_marker_true_withRight]
  rw [runConfig_add]
  rw [scratchCounterPreservingMarkerAppendDescription_run_rewind_markers_true]
  simpa [List.reverse_reverse, List.map_append, List.append_assoc] using
    scratchCounterPreservingMarkerAppendDescription_run_restore_source_true
      baseLeft rest.reverse
      (List.append
        (List.replicate (markers + 1) (some false : Option Bool))
        (some true :: padding))

def scratchCounterPreservingMarkerAppendWordSteps :
    Word Bool -> Nat -> Nat
  | [], _markers => 1
  | _bit :: rest, markers =>
      (1 + (rest.length + (1 + ((markers + 2) +
        ((markers + 1) + (rest.length + 2)))))) +
        scratchCounterPreservingMarkerAppendWordSteps rest (markers + 1)

theorem scratchCounterPreservingMarkerAppendDescription_run_word_withRight
    (baseLeft : List (Option Bool)) (source : Word Bool)
    (markers : Nat) (suffix : List (Option Bool)) :
    SCPMA.runConfig
        (scratchCounterPreservingMarkerAppendWordSteps source markers)
        { state := 0
          tape :=
            tapeAtCells baseLeft
              (List.append (source.map some)
                (none ::
                  List.append
                    (List.replicate markers
                      (some false : Option Bool))
                    (some true ::
                      List.append
                        (List.replicate source.length
                          (none : Option Bool))
                        suffix))) } =
      { state := SCPMA.halt
        tape :=
          tapeAtCells
            (none :: List.append (source.reverse.map some) baseLeft)
            (List.append
              (List.replicate (markers + source.length)
                (some false : Option Bool))
              (some true :: suffix)) } := by
  induction source generalizing baseLeft markers with
  | nil =>
      cases markers <;>
        simp [scratchCounterPreservingMarkerAppendWordSteps, SCPMA,
          scratchCounterPreservingMarkerAppendDescription,
          runConfig, stepConfig, lookupTransition, Matches, transition,
          tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight,
          List.replicate_succ]
  | cons bit rest ih =>
      simp only [scratchCounterPreservingMarkerAppendWordSteps]
      rw [runConfig_add]
      cases bit
      · have hcell :=
          scratchCounterPreservingMarkerAppendDescription_run_cell_false_withRight
            baseLeft rest markers
            (List.append
              (List.replicate rest.length (none : Option Bool))
              suffix)
        calc
          SCPMA.runConfig
              (scratchCounterPreservingMarkerAppendWordSteps rest
                (markers + 1))
              (SCPMA.runConfig
                (1 + (rest.length + (1 + ((markers + 2) +
                  ((markers + 1) + (rest.length + 2))))))
                { state := 0
                  tape :=
                    tapeAtCells baseLeft
                      (List.append ((false :: rest).map some)
                        (none ::
                          List.append
                            (List.replicate markers
                              (some false : Option Bool))
                            (some true ::
                              List.append
                                (List.replicate (false :: rest).length
                                  (none : Option Bool))
                                suffix))) }) =
            SCPMA.runConfig
              (scratchCounterPreservingMarkerAppendWordSteps rest
                (markers + 1))
              { state := 0
                tape :=
                  tapeAtCells (some false :: baseLeft)
                    (List.append (rest.map some)
                      (none ::
                        List.append
                          (List.replicate (markers + 1)
                            (some false : Option Bool))
                          (some true ::
                            List.append
                              (List.replicate rest.length
                                (none : Option Bool))
                              suffix))) } := by
              simpa [List.replicate_succ, List.append_assoc] using
                congrArg
                  (SCPMA.runConfig
                    (scratchCounterPreservingMarkerAppendWordSteps rest
                      (markers + 1)))
                  hcell
          _ =
            { state := SCPMA.halt
              tape :=
                tapeAtCells
                  (none ::
                    List.append ((false :: rest).reverse.map some)
                      baseLeft)
                  (List.append
                    (List.replicate
                      (markers + (false :: rest).length)
                      (some false : Option Bool))
                    (some true :: suffix)) } := by
              simpa [List.reverse_cons, List.map_append, List.append_assoc,
                Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                ih (some false :: baseLeft) (markers + 1)
      · have hcell :=
          scratchCounterPreservingMarkerAppendDescription_run_cell_true_withRight
            baseLeft rest markers
            (List.append
              (List.replicate rest.length (none : Option Bool))
              suffix)
        calc
          SCPMA.runConfig
              (scratchCounterPreservingMarkerAppendWordSteps rest
                (markers + 1))
              (SCPMA.runConfig
                (1 + (rest.length + (1 + ((markers + 2) +
                  ((markers + 1) + (rest.length + 2))))))
                { state := 0
                  tape :=
                    tapeAtCells baseLeft
                      (List.append ((true :: rest).map some)
                        (none ::
                          List.append
                            (List.replicate markers
                              (some false : Option Bool))
                            (some true ::
                              List.append
                                (List.replicate (true :: rest).length
                                  (none : Option Bool))
                                suffix))) }) =
            SCPMA.runConfig
              (scratchCounterPreservingMarkerAppendWordSteps rest
                (markers + 1))
              { state := 0
                tape :=
                  tapeAtCells (some true :: baseLeft)
                    (List.append (rest.map some)
                      (none ::
                        List.append
                          (List.replicate (markers + 1)
                            (some false : Option Bool))
                          (some true ::
                            List.append
                              (List.replicate rest.length
                                (none : Option Bool))
                              suffix))) } := by
              simpa [List.replicate_succ, List.append_assoc] using
                congrArg
                  (SCPMA.runConfig
                    (scratchCounterPreservingMarkerAppendWordSteps rest
                      (markers + 1)))
                  hcell
          _ =
            { state := SCPMA.halt
              tape :=
                tapeAtCells
                  (none ::
                    List.append ((true :: rest).reverse.map some)
                      baseLeft)
                  (List.append
                    (List.replicate
                      (markers + (true :: rest).length)
                      (some false : Option Bool))
                    (some true :: suffix)) } := by
              simpa [List.reverse_cons, List.map_append, List.append_assoc,
                Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                ih (some true :: baseLeft) (markers + 1)

/--
Erase a temporary counter-marker block after it has served as exact scratch
width evidence.  The pass turns all {lit}`false` markers and the final
{lit}`true` sentinel into blanks, preserving arbitrary right padding.
-/
def scratchCounterMarkerEraseDescription : MachineDescription where
  stateCount := 3
  start := 0
  halt := 2
  transitions :=
    [ transition 0 (some false) none Direction.right 0
    , transition 0 (some true) none Direction.right 2
    ]

private abbrev SCME := scratchCounterMarkerEraseDescription

theorem scratchCounterMarkerEraseDescription_wellFormed :
    SCME.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := SCME.transitions)
      (stateCount := SCME.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := SCME.transitions)
      (by decide)

theorem scratchCounterMarkerEraseDescription_haltTransitionFree :
    SCME.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := SCME.transitions)
    (state := SCME.halt)
    (by decide)

theorem scratchCounterMarkerEraseDescription_subroutineReady :
    SCME.SubroutineReady :=
  ⟨scratchCounterMarkerEraseDescription_wellFormed,
    scratchCounterMarkerEraseDescription_haltTransitionFree⟩

theorem scratchCounterMarkerEraseDescription_run_markers_withRight
    (leftRev : List (Option Bool)) (markers : Nat)
    (suffix : List (Option Bool)) :
    SCME.runConfig (markers + 1)
        { state := SCME.start
          tape :=
            tapeAtCells leftRev
              (List.append
                (List.replicate markers (some false : Option Bool))
                (some true :: suffix)) } =
      { state := SCME.halt
        tape :=
          tapeAtCells
            (List.append
              (List.replicate (markers + 1)
                (none : Option Bool))
              leftRev)
            suffix } := by
  induction markers generalizing leftRev with
  | zero =>
      cases suffix <;>
        simp [SCME, scratchCounterMarkerEraseDescription,
          runConfig, stepConfig, lookupTransition, Matches, transition,
          tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]
  | succ markers ih =>
      rw [show markers + 1 + 1 = 1 + (markers + 1) by omega]
      rw [runConfig_add]
      have hstep :
          SCME.runConfig 1
              { state := SCME.start
                tape :=
                  tapeAtCells leftRev
                    (List.append
                      (List.replicate (markers + 1)
                        (some false : Option Bool))
                      (some true :: suffix)) } =
            { state := SCME.start
              tape :=
                tapeAtCells (none :: leftRev)
                  (List.append
                    (List.replicate markers
                      (some false : Option Bool))
                    (some true :: suffix)) } := by
        rw [show
            List.replicate (markers + 1)
                (some false : Option Bool) =
              some false ::
                List.replicate markers
                  (some false : Option Bool) by
          simp [List.replicate_succ]]
        simp [SCME, scratchCounterMarkerEraseDescription,
          runConfig, stepConfig, lookupTransition, Matches, transition,
          tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]
        split <;> simp_all
      rw [hstep]
      calc
        SCME.runConfig (markers + 1)
            { state := SCME.start
              tape :=
                tapeAtCells (none :: leftRev)
                  (List.append
                    (List.replicate markers
                      (some false : Option Bool))
                    (some true :: suffix)) } =
          { state := SCME.halt
            tape :=
              tapeAtCells
                (List.append
                  (List.replicate (markers + 1)
                    (none : Option Bool))
                  (none :: leftRev))
                suffix } := by
            exact ih (none :: leftRev)
        _ =
          { state := SCME.halt
            tape :=
              tapeAtCells
                (List.append
                  (List.replicate (1 + (markers + 1))
                    (none : Option Bool))
                  leftRev)
                suffix } := by
            rw [show 1 + (markers + 1) = markers + 1 + 1 by omega]
            rw [scratchCounter_replicate_none_append_cons
              (markers + 1) leftRev]

theorem scratchCounterMarkerEraseDescription_haltsFrom_markers_withRight
    (leftRev : List (Option Bool)) (markers : Nat)
    (suffix : List (Option Bool)) :
    SCME.HaltsFromTape
      (tapeAtCells leftRev
        (List.append
          (List.replicate markers (some false : Option Bool))
          (some true :: suffix)))
      (tapeAtCells
        (List.append
          (List.replicate (markers + 1)
            (none : Option Bool))
          leftRev)
        suffix) := by
  refine ⟨markers + 1, ?_⟩
  constructor <;>
    rw [scratchCounterMarkerEraseDescription_run_markers_withRight]

/--
Initialize the moving {lit}`true` sentinel for the scratch counter.  The machine
preserves the raw source word, writes the sentinel into the first blank after
the source separator, and returns to the left boundary of the source word.
-/
def scratchCounterMarkerInitDescription : MachineDescription where
  stateCount := 5
  start := 0
  halt := 4
  transitions :=
    [ transition 0 (some false) (some false) Direction.right 0
    , transition 0 (some true) (some true) Direction.right 0
    , transition 0 none none Direction.right 1
    , transition 1 none (some true) Direction.left 2
    , transition 2 none none Direction.left 3
    , transition 3 (some false) (some false) Direction.left 3
    , transition 3 (some true) (some true) Direction.left 3
    , transition 3 none none Direction.right 4
    ]

private abbrev SCMI := scratchCounterMarkerInitDescription

theorem scratchCounterMarkerInitDescription_wellFormed :
    SCMI.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := SCMI.transitions)
      (stateCount := SCMI.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := SCMI.transitions)
      (by decide)

theorem scratchCounterMarkerInitDescription_haltTransitionFree :
    SCMI.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := SCMI.transitions)
    (state := SCMI.halt)
    (by decide)

theorem scratchCounterMarkerInitDescription_subroutineReady :
    SCMI.SubroutineReady :=
  ⟨scratchCounterMarkerInitDescription_wellFormed,
    scratchCounterMarkerInitDescription_haltTransitionFree⟩

def scratchCounterMarkerInitSteps (source : Word Bool) : Nat :=
  source.length + (1 + (1 + (1 + (source.length + 1))))

theorem scratchCounterMarkerInitDescription_run_scan_source
    (leftRev : List (Option Bool)) (source : Word Bool)
    (right : List (Option Bool)) :
    SCMI.runConfig source.length
        { state := 0
          tape :=
            tapeAtCells leftRev
              (List.append (source.map some) right) } =
      { state := 0
        tape :=
          tapeAtCells
            (List.append (source.reverse.map some) leftRev)
            right } := by
  induction source generalizing leftRev with
  | nil =>
      rfl
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        omega]
      rw [runConfig_add]
      have hstep :
          SCMI.runConfig 1
              { state := 0
                tape :=
                  tapeAtCells leftRev
                    (List.append ((bit :: rest).map some) right) } =
            { state := 0
              tape :=
                tapeAtCells (some bit :: leftRev)
                  (List.append (rest.map some) right) } := by
        cases bit <;> cases rest <;> cases right <;>
          simp [SCMI, scratchCounterMarkerInitDescription,
            runConfig, stepConfig, lookupTransition, Matches,
            transition, tapeAtCells, Tape.read, Tape.write,
            Tape.move, Tape.moveRight]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: leftRev)

theorem scratchCounterMarkerInitDescription_run_rewind_leftStack
    (baseLeft : List (Option Bool)) (sourceRev : Word Bool)
    (current : Option Bool) (rightTail : List (Option Bool)) :
    SCMI.runConfig (sourceRev.length + 1)
        { state := 3
          tape :=
            Tape.move Direction.left
              (tapeAtCells
                (List.append (sourceRev.map some) (none :: baseLeft))
                (current :: rightTail)) } =
      { state := SCMI.halt
        tape :=
          tapeAtCells (none :: baseLeft)
            (List.append (sourceRev.reverse.map some)
              (current :: rightTail)) } := by
  induction sourceRev generalizing current rightTail with
  | nil =>
      cases current <;> cases rightTail <;>
        simp [SCMI, scratchCounterMarkerInitDescription,
          runConfig, stepConfig, lookupTransition, Matches, transition,
          tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          Tape.moveRight]
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 1 = 1 + (rest.length + 1) by
        simp
        omega]
      rw [runConfig_add]
      have hstep :
          SCMI.runConfig 1
              { state := 3
                tape :=
                  Tape.move Direction.left
                    (tapeAtCells
                      (List.append ((bit :: rest).map some)
                        (none :: baseLeft))
                      (current :: rightTail)) } =
            { state := 3
              tape :=
                Tape.move Direction.left
                  (tapeAtCells
                    (List.append (rest.map some) (none :: baseLeft))
                    (some bit :: current :: rightTail)) } := by
        cases bit <;> cases current <;> cases rightTail <;>
          simp [SCMI, scratchCounterMarkerInitDescription,
            runConfig, stepConfig, lookupTransition, Matches, transition,
            tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit) (current :: rightTail)

theorem scratchCounterMarkerInitDescription_run_withRight
    (baseLeft : List (Option Bool)) (source : Word Bool)
    (suffix : List (Option Bool)) :
    SCMI.runConfig (scratchCounterMarkerInitSteps source)
        { state := SCMI.start
          tape :=
            tapeAtCells (none :: baseLeft)
              (List.append (source.map some) (none :: none :: suffix)) } =
      { state := SCMI.halt
        tape :=
          tapeAtCells (none :: baseLeft)
            (List.append (source.map some)
              (none :: some true :: suffix)) } := by
  rw [scratchCounterMarkerInitSteps]
  rw [runConfig_add]
  change
    SCMI.runConfig (1 + (1 + (1 + (source.length + 1))))
      (SCMI.runConfig source.length
        { state := 0
          tape :=
            tapeAtCells (none :: baseLeft)
              (List.append (source.map some) (none :: none :: suffix)) }) =
      { state := SCMI.halt
        tape :=
          tapeAtCells (none :: baseLeft)
            (List.append (source.map some)
              (none :: some true :: suffix)) }
  rw [scratchCounterMarkerInitDescription_run_scan_source]
  rw [runConfig_add]
  have hseparator :
      SCMI.runConfig 1
          { state := 0
            tape :=
              tapeAtCells
                (List.append (source.reverse.map some)
                  (none :: baseLeft))
                (none :: none :: suffix) } =
        { state := 1
          tape :=
            tapeAtCells
              (none :: List.append (source.reverse.map some)
                (none :: baseLeft))
              (none :: suffix) } := by
    cases suffix <;>
      simp [SCMI, scratchCounterMarkerInitDescription,
        runConfig, stepConfig, lookupTransition, Matches, transition,
        tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]
  rw [hseparator]
  rw [runConfig_add]
  have hwrite :
      SCMI.runConfig 1
          { state := 1
            tape :=
              tapeAtCells
                (none :: List.append (source.reverse.map some)
                  (none :: baseLeft))
                (none :: suffix) } =
        { state := 2
          tape :=
            tapeAtCells
              (List.append (source.reverse.map some)
                (none :: baseLeft))
              (none :: some true :: suffix) } := by
    cases suffix <;>
      simp [SCMI, scratchCounterMarkerInitDescription,
        runConfig, stepConfig, lookupTransition, Matches, transition,
        tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft]
  rw [hwrite]
  rw [runConfig_add]
  have hleft :
      SCMI.runConfig 1
          { state := 2
            tape :=
              tapeAtCells
                (List.append (source.reverse.map some)
                  (none :: baseLeft))
                (none :: some true :: suffix) } =
        { state := 3
          tape :=
            Tape.move Direction.left
              (tapeAtCells
                (List.append (source.reverse.map some)
                  (none :: baseLeft))
                (none :: some true :: suffix)) } := by
    simp [SCMI, scratchCounterMarkerInitDescription,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      tapeAtCells, Tape.read, Tape.write]
  rw [hleft]
  simpa [List.length_reverse, List.reverse_reverse, List.append_assoc] using
    scratchCounterMarkerInitDescription_run_rewind_leftStack
      baseLeft source.reverse none (some true :: suffix)

theorem scratchCounterMarkerInitDescription_haltsFrom_withRight
    (baseLeft : List (Option Bool)) (source : Word Bool)
    (suffix : List (Option Bool)) :
    SCMI.HaltsFromTape
      (tapeAtCells (none :: baseLeft)
        (List.append (source.map some) (none :: none :: suffix)))
      (tapeAtCells (none :: baseLeft)
        (List.append (source.map some)
          (none :: some true :: suffix))) := by
  refine ⟨scratchCounterMarkerInitSteps source, ?_⟩
  constructor <;>
    rw [scratchCounterMarkerInitDescription_run_withRight]

end SelectedProjectionPaddedTailCleanup

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC

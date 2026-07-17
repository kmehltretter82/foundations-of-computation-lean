import FoC.Computability.Compiler.ClosedCfg.QuoteRest.LTStructuredLowererReadiness
import FoC.Computability.Compiler.ClosedCfg.QuoteRest.LTJoinerOutput
import FoC.Computability.Compiler.Core.StructuredConstructionTargets.OptionCellExpandAppendImpl
import FoC.Computability.Compiler.Structured.Lowering.StructuredRefresh
import FoC.Computability.Compiler.Structured.Lowering.ThreeTapeTactic

set_option maxRecDepth 10000

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionInputQuoterFiniteLeaf

open CommonGround.FiniteTransducers

/-!
# Direct joined quote-rest endpoint

The joined-output route removes the precomputed quote-rest suffix from the mixed
source and rewinds to the first bit of the contiguous full source word.
-/

def mixedSourceCanonicalizerDescription : MachineDescription where
  stateCount := 5
  start := 0
  halt := 4
  transitions :=
    [ transition 0 (some false) (some false) Direction.right 0
    , transition 0 (some true) (some true) Direction.right 0
    , transition 0 none none Direction.right 1
    , transition 1 (some false) none Direction.right 1
    , transition 1 (some true) none Direction.right 1
    , transition 1 none none Direction.left 2
    , transition 2 none none Direction.left 2
    , transition 2 (some false) (some false) Direction.left 3
    , transition 2 (some true) (some true) Direction.left 3
    , transition 3 (some false) (some false) Direction.left 3
    , transition 3 (some true) (some true) Direction.left 3
    , transition 3 none none Direction.right 4 ]

theorem mixedSourceCanonicalizerDescription_wellFormed :
    mixedSourceCanonicalizerDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := mixedSourceCanonicalizerDescription.transitions)
      (stateCount := mixedSourceCanonicalizerDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := mixedSourceCanonicalizerDescription.transitions)
      (by decide)

theorem mixedSourceCanonicalizerDescription_haltTransitionFree :
    mixedSourceCanonicalizerDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := mixedSourceCanonicalizerDescription.transitions)
    (state := mixedSourceCanonicalizerDescription.halt)
    (by decide)

theorem mixedSourceCanonicalizerDescription_subroutineReady :
    mixedSourceCanonicalizerDescription.SubroutineReady :=
  ⟨mixedSourceCanonicalizerDescription_wellFormed,
    mixedSourceCanonicalizerDescription_haltTransitionFree⟩

theorem mixedSourceCanonicalizer_run_scan_right
    (prefixRev remaining : Word Bool)
    (suffix : List (Option Bool)) :
    mixedSourceCanonicalizerDescription.runConfig remaining.length
        { state := 0
          tape := tapeAtCells
            (List.append (prefixRev.map some) [none])
            (List.append (remaining.map some) (none :: suffix)) } =
      { state := 0
        tape := tapeAtCells
          (List.append (remaining.reverse.map some)
            (List.append (prefixRev.map some) [none]))
          (none :: suffix) } := by
  induction remaining generalizing prefixRev with
  | nil =>
      simp [runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp [Nat.add_comm]]
      rw [runConfig_add]
      change mixedSourceCanonicalizerDescription.runConfig rest.length
          (mixedSourceCanonicalizerDescription.runConfig 1
            { state := 0
              tape := tapeAtCells
                (List.append (prefixRev.map some) [none])
                (some bit ::
                  List.append (rest.map some) (none :: suffix)) }) = _
      have hstep :
          mixedSourceCanonicalizerDescription.runConfig 1
              { state := 0
                tape := tapeAtCells
                  (List.append (prefixRev.map some) [none])
                  (some bit ::
                    List.append (rest.map some) (none :: suffix)) } =
            { state := 0
              tape := tapeAtCells
                (some bit :: List.append (prefixRev.map some) [none])
                (List.append (rest.map some) (none :: suffix)) } := by
        cases bit <;> cases rest <;>
          simp [mixedSourceCanonicalizerDescription,
            runConfig, stepConfig, lookupTransition, Matches, transition,
            tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (bit :: prefixRev)

theorem mixedSourceCanonicalizer_run_enter_erase
    (left suffix : List (Option Bool)) :
    mixedSourceCanonicalizerDescription.runConfig 1
        { state := 0
          tape := tapeAtCells left (none :: suffix) } =
      { state := 1
        tape := tapeAtCells (none :: left) suffix } := by
  cases suffix <;>
    simp [mixedSourceCanonicalizerDescription,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem mixedSourceCanonicalizer_run_erase
    (bits : Word Bool) (left right : List (Option Bool)) :
    mixedSourceCanonicalizerDescription.runConfig bits.length
        { state := 1
          tape := tapeAtCells left
            (List.append (bits.map some) (none :: right)) } =
      { state := 1
        tape := tapeAtCells
          (List.append (List.replicate bits.length none) left)
          (none :: right) } := by
  induction bits generalizing left with
  | nil =>
      simp [runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp [Nat.add_comm]]
      rw [runConfig_add]
      change mixedSourceCanonicalizerDescription.runConfig rest.length
          (mixedSourceCanonicalizerDescription.runConfig 1
            { state := 1
              tape := tapeAtCells left
                (some bit ::
                  List.append (rest.map some) (none :: right)) }) = _
      have hstep :
          mixedSourceCanonicalizerDescription.runConfig 1
              { state := 1
                tape := tapeAtCells left
                  (some bit ::
                    List.append (rest.map some) (none :: right)) } =
            { state := 1
              tape := tapeAtCells (none :: left)
                (List.append (rest.map some) (none :: right)) } := by
        cases bit <;> cases rest <;>
          simp [mixedSourceCanonicalizerDescription,
            runConfig, stepConfig, lookupTransition, Matches, transition,
            tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]
      rw [hstep]
      have htail :
          List.append (List.replicate rest.length (none : Option Bool))
              (none :: left) =
            none ::
              List.append (List.replicate rest.length (none : Option Bool))
                left :=
        list_replicate_append_cons_eq_cons_append
          (none : Option Bool) rest.length left
      have hih := ih (none :: left)
      rw [htail] at hih
      simpa [Nat.add_comm, List.replicate_succ, List.append_assoc] using hih

private def mixedSourceCanonicalizerRewindTape
    (remainingRev : Word Bool) (right : List (Option Bool)) : Tape Bool :=
  match remainingRev with
  | [] => tapeAtCells [] (none :: right)
  | bit :: rest =>
      tapeAtCells (List.append (rest.map some) [none])
        (some bit :: right)

private theorem mixedSourceCanonicalizer_run_rewind
    (remainingRev : Word Bool) (right : List (Option Bool)) :
    mixedSourceCanonicalizerDescription.runConfig (remainingRev.length + 1)
        { state := 3
          tape := mixedSourceCanonicalizerRewindTape remainingRev right } =
      { state := 4
        tape := tapeAtCells [none]
          (List.append (remainingRev.reverse.map some) right) } := by
  induction remainingRev generalizing right with
  | nil =>
      cases right <;>
        simp [mixedSourceCanonicalizerRewindTape,
          mixedSourceCanonicalizerDescription,
          runConfig, stepConfig, lookupTransition, Matches, transition,
          tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 1 = 1 + (rest.length + 1) by
        simp
        lia]
      rw [runConfig_add]
      have hstep :
          mixedSourceCanonicalizerDescription.runConfig 1
              { state := 3
                tape := mixedSourceCanonicalizerRewindTape
                  (bit :: rest) right } =
            { state := 3
              tape := mixedSourceCanonicalizerRewindTape rest
                (some bit :: right) } := by
        cases bit <;> cases rest <;> cases right <;>
          simp [mixedSourceCanonicalizerRewindTape,
            mixedSourceCanonicalizerDescription,
            runConfig, stepConfig, lookupTransition, Matches, transition,
            tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: right)

private theorem mixedSourceCanonicalizer_run_enter_rewind
    (remainingRev : Word Bool) (current : Bool)
    (right : List (Option Bool)) :
    mixedSourceCanonicalizerDescription.runConfig 1
        { state := 2
          tape := tapeAtCells
            (List.append (remainingRev.map some) [none])
            (some current :: right) } =
      { state := 3
        tape := mixedSourceCanonicalizerRewindTape remainingRev
          (some current :: right) } := by
  cases current <;> cases remainingRev <;> cases right <;>
    simp [mixedSourceCanonicalizerRewindTape,
      mixedSourceCanonicalizerDescription,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft]

private theorem mixedSourceCanonicalizer_run_rewind_from_last
    (remainingRev : Word Bool) (current : Bool)
    (right : List (Option Bool)) :
    mixedSourceCanonicalizerDescription.runConfig (remainingRev.length + 2)
        { state := 2
          tape := tapeAtCells
            (List.append (remainingRev.map some) [none])
            (some current :: right) } =
      { state := 4
        tape := tapeAtCells [none]
          (List.append
            ((List.append remainingRev.reverse [current]).map some)
            right) } := by
  rw [show remainingRev.length + 2 = 1 + (remainingRev.length + 1) by lia]
  rw [runConfig_add]
  rw [mixedSourceCanonicalizer_run_enter_rewind]
  simpa [List.map_append, List.append_assoc] using
    mixedSourceCanonicalizer_run_rewind remainingRev (some current :: right)

private theorem mixedSourceCanonicalizer_run_blank_rewind
    (blanks : Nat) (left right : List (Option Bool)) :
    mixedSourceCanonicalizerDescription.runConfig blanks
        { state := 2
          tape := tapeAtCells
            (List.append (List.replicate blanks none) left)
            (none :: right) } =
      { state := 2
        tape := tapeAtCells left
          (List.append (List.replicate (blanks + 1) none) right) } := by
  induction blanks generalizing right with
  | zero =>
      simp [runConfig]
  | succ blanks ih =>
      rw [show blanks + 1 = 1 + blanks by lia]
      rw [runConfig_add]
      rw [show 1 + blanks = blanks + 1 by lia]
      change mixedSourceCanonicalizerDescription.runConfig blanks
          (mixedSourceCanonicalizerDescription.runConfig 1
            { state := 2
              tape := tapeAtCells
                (List.append (List.replicate (blanks + 1) none) left)
                (none :: right) }) = _
      have hstep :
          mixedSourceCanonicalizerDescription.runConfig 1
              { state := 2
                tape := tapeAtCells
                  (List.append
                    (List.replicate (blanks + 1) none) left)
                  (none :: right) } =
            { state := 2
              tape := tapeAtCells
                (List.append (List.replicate blanks none) left)
                (none :: none :: right) } := by
        cases blanks <;> cases left <;> cases right <;>
          simp [List.replicate_succ,
            mixedSourceCanonicalizerDescription,
            runConfig, stepConfig, lookupTransition, Matches, transition,
            tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      rw [hstep]
      have hih := ih (none :: right)
      rw [hih]
      have htail :
          List.append
              (List.replicate (blanks + 1) (none : Option Bool))
              (none :: right) =
            none ::
              List.append
                (List.replicate (blanks + 1) (none : Option Bool))
                right :=
        list_replicate_append_cons_eq_cons_append
          (none : Option Bool) (blanks + 1) right
      rw [htail]
      simp [List.replicate_succ]

private theorem mixedSourceCanonicalizer_run_erase_done
    (blanks : Nat) (left : List (Option Bool)) :
    mixedSourceCanonicalizerDescription.runConfig 1
        { state := 1
          tape := tapeAtCells
            (List.append (List.replicate blanks none) (none :: left))
            [none] } =
      { state := 2
        tape := tapeAtCells
          (List.append (List.replicate blanks none) left)
          [none, none] } := by
  have hleft :
      List.append (List.replicate blanks (none : Option Bool))
          (none :: left) =
        none ::
          List.append (List.replicate blanks (none : Option Bool)) left :=
    list_replicate_append_cons_eq_cons_append
      (none : Option Bool) blanks left
  rw [hleft]
  cases left <;>
    simp [mixedSourceCanonicalizerDescription,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft]

private theorem mixedSourceCanonicalizer_run_cross_separator
    (left right : List (Option Bool)) :
    mixedSourceCanonicalizerDescription.runConfig 1
        { state := 2
          tape := tapeAtCells left (none :: right) } =
      { state := 2
        tape := Tape.move Direction.left
          (tapeAtCells left (none :: right)) } := by
  cases left <;> cases right <;>
    simp [mixedSourceCanonicalizerDescription,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft]

private theorem mixedSourceCanonicalizer_run_enter_source
    (remainingRev : Word Bool) (current : Bool)
    (right : List (Option Bool)) :
    mixedSourceCanonicalizerDescription.runConfig 1
        { state := 2
          tape := tapeAtCells
            (some current ::
              List.append (remainingRev.map some) [none])
            (none :: right) } =
      { state := 2
        tape := tapeAtCells
          (List.append (remainingRev.map some) [none])
          (some current :: none :: right) } := by
  cases current <;> cases remainingRev <;> cases right <;>
    simp [mixedSourceCanonicalizerDescription,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft]

def mixedSourceCanonicalizerSourceTape
    (prefixRev scan quoteRest : Word Bool) : Tape Bool :=
  tapeAtCells
    (List.append (prefixRev.map some) [none])
    (List.append (scan.map some)
      (none :: List.append (quoteRest.map some) [none]))

def mixedSourceCanonicalizerFuel
    (prefixRev scan quoteRest : Word Bool) : Nat :=
  scan.length + 1 + quoteRest.length + 1 + quoteRest.length + 1 +
    ((List.append prefixRev.reverse scan).length + 1)

private theorem mixedSourceCanonicalizer_run_layout
    (prefixRev scan quoteRest sourceInit : Word Bool) (last : Bool)
    (hsource :
      List.append prefixRev.reverse scan =
        List.append sourceInit [last]) :
    mixedSourceCanonicalizerDescription.runConfig
        (mixedSourceCanonicalizerFuel prefixRev scan quoteRest)
        { state := mixedSourceCanonicalizerDescription.start
          tape := mixedSourceCanonicalizerSourceTape
            prefixRev scan quoteRest } =
      { state := mixedSourceCanonicalizerDescription.halt
        tape := tapeAtCells [none]
          (List.append
            ((List.append sourceInit [last]).map some)
            (List.replicate (quoteRest.length + 2) none)) } := by
  have hfuel :
      mixedSourceCanonicalizerFuel prefixRev scan quoteRest =
        scan.length + 1 + quoteRest.length + 1 + quoteRest.length + 1 +
          (sourceInit.length + 2) := by
    rw [mixedSourceCanonicalizerFuel, hsource]
    simp
  rw [hfuel]
  have hassoc :
      scan.length + 1 + quoteRest.length + 1 + quoteRest.length + 1 +
          (sourceInit.length + 2) =
        scan.length +
          (1 + (quoteRest.length +
            (1 + (quoteRest.length +
              (1 + (sourceInit.length + 2)))))) := by
    lia
  rw [hassoc]
  rw [runConfig_add]
  change mixedSourceCanonicalizerDescription.runConfig
      (1 + (quoteRest.length +
        (1 + (quoteRest.length +
          (1 + (sourceInit.length + 2))))))
      (mixedSourceCanonicalizerDescription.runConfig scan.length
        { state := 0
          tape := tapeAtCells
            (List.append (prefixRev.map some) [none])
            (List.append (scan.map some)
              (none :: List.append (quoteRest.map some) [none])) }) = _
  rw [mixedSourceCanonicalizer_run_scan_right]
  rw [runConfig_add]
  rw [mixedSourceCanonicalizer_run_enter_erase]
  rw [runConfig_add]
  rw [mixedSourceCanonicalizer_run_erase]
  rw [runConfig_add]
  rw [show
      List.append (List.replicate quoteRest.length (none : Option Bool))
          (none ::
            List.append (scan.reverse.map some)
              (List.append (prefixRev.map some) [none])) =
        List.append (List.replicate quoteRest.length (none : Option Bool))
          (none ::
            List.append
              ((List.append sourceInit [last]).reverse.map some) [none]) by
    rw [← hsource]
    simp [List.reverse_append, List.map_append, List.append_assoc]]
  rw [mixedSourceCanonicalizer_run_erase_done]
  rw [runConfig_add]
  rw [mixedSourceCanonicalizer_run_blank_rewind]
  rw [runConfig_add]
  have hright :
      List.append
          (List.replicate (quoteRest.length + 1) (none : Option Bool))
          [none] =
        none ::
          List.replicate (quoteRest.length + 1) (none : Option Bool) :=
    by simpa using
      (list_replicate_append_cons_eq_cons_append
        (none : Option Bool) (quoteRest.length + 1) [])
  rw [hright]
  have hleft :
      List.append
          (List.map some
            (List.reverse (List.append sourceInit [last]))) [none] =
        some last ::
          List.append (List.map some (List.reverse sourceInit)) [none] := by
    simp [List.reverse_append]
  rw [hleft]
  rw [mixedSourceCanonicalizer_run_enter_source]
  rw [show List.length sourceInit = List.length (List.reverse sourceInit) by simp]
  rw [mixedSourceCanonicalizer_run_rewind_from_last]
  simp [mixedSourceCanonicalizerDescription, List.map_append,
    List.append_assoc, List.replicate_succ]

theorem mixedSourceCanonicalizerDescription_haltsFrom_layout
    (prefixRev scan quoteRest sourceInit : Word Bool) (last : Bool)
    (hsource :
      List.append prefixRev.reverse scan =
        List.append sourceInit [last]) :
    mixedSourceCanonicalizerDescription.HaltsFromTapeEquiv
      (mixedSourceCanonicalizerSourceTape prefixRev scan quoteRest)
      (Tape.input (List.append sourceInit [last])) := by
  let fuel := mixedSourceCanonicalizerFuel prefixRev scan quoteRest
  let actual := tapeAtCells [none]
    (List.append ((List.append sourceInit [last]).map some)
      (List.replicate (quoteRest.length + 2) none))
  refine ⟨actual, ⟨fuel, ?_, ?_⟩, ?_⟩
  · simpa [fuel, actual] using congrArg Configuration.state
      (mixedSourceCanonicalizer_run_layout
        prefixRev scan quoteRest sourceInit last hsource)
  · simpa [fuel, actual] using congrArg Configuration.tape
      (mixedSourceCanonicalizer_run_layout
        prefixRev scan quoteRest sourceInit last hsource)
  · dsimp [actual]
    cases sourceInit with
    | nil =>
        change
          Tape.dropTrailingNone [none] =
              Tape.dropTrailingNone [] ∧
            some last = some last ∧
              Tape.dropTrailingNone
                  (List.replicate (quoteRest.length + 2) none) =
                Tape.dropTrailingNone []
        exact
          ⟨by simp [Tape.dropTrailingNone],
            rfl,
            by simpa [Tape.dropTrailingNone] using
              (dropTrailingNone_replicate_none
                (symbol := Bool) (quoteRest.length + 2))⟩
    | cons first rest =>
        simp only [List.cons_append, List.map_cons, tapeAtCells,
          Tape.input, Tape.Equiv]
        refine
          ⟨by simp [Tape.dropTrailingNone],
            trivial, ?_⟩
        exact dropTrailingNone_append_replicate_none
          ((List.append rest [last]).map some) (quoteRest.length + 2)

/-! The shared option-cell expander materializes an unguarded logical tape 0.
The emitter's logical source carries one additional represented blank at each
far edge, so this tiny structured pass visits both edges and returns to the
first bit. -/

namespace DirectJoinedInnerGuard

open Structured.MultiTapeLowering.ThreeTape

def rowsForTape0Read
    (source : Nat) (read0 : Option Bool)
    (action0 : Structured.TapeAction) (target : Nat) :
    List Structured.Transition :=
  allReads2 fun read1 read2 =>
    row source read0 read1 read2 action0 keepS keepS target

def rows : List Structured.Transition :=
  List.flatten
    [ rowsForTape0Read 0 (some false) keepR 0
    , rowsForTape0Read 0 (some true) keepR 0
    , rowsForTape0Read 0 none keepL 1
    , rowsForTape0Read 1 (some false) keepL 1
    , rowsForTape0Read 1 (some true) keepL 1
    , rowsForTape0Read 1 none keepR 2 ]

def description : Structured.Description :=
  Structured.MultiTapeLowering.ThreeTape.description 3 0 2 rows

theorem description_supported :
    Structured.MultiTapeLowering.SupportsReadWriteRows3 description := by
  exact Structured.MultiTapeLowering.supportedReadWriteRows3_of_supports_eq_true
    (by decide)

theorem description_wellFormed : description.WellFormed := by
  exact structuredDescription_wellFormed_of_transition_checks description
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem description_haltTransitionFree : description.HaltTransitionFree :=
  structuredDescription_haltTransitionFree_of_transition_checks description
    (by decide)

theorem description_subroutineReady : description.SubroutineReady :=
  ⟨description_wellFormed, description_haltTransitionFree⟩

def scanRightTape
    (processedRev remaining : Word Bool) : Tape Bool :=
  tapeAtCells (processedRev.map some)
    (remaining.map some)

set_option maxHeartbeats 1000000 in
theorem run_scan_right
    (processedRev remaining : Word Bool)
    (tape1 tape2 : Tape Bool) :
    description.runConfig remaining.length
        (config 0 (scanRightTape processedRev remaining) tape1 tape2) =
      config 0
        (scanRightTape
          (List.append remaining.reverse processedRev) [])
        tape1 tape2 := by
  induction remaining generalizing processedRev with
  | nil =>
      simp [Structured.Description.runConfig, scanRightTape]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by simp; lia]
      rw [Structured.Description.runConfig_add]
      have hstep :
          description.runConfig 1
              (config 0
                (scanRightTape processedRev (bit :: rest)) tape1 tape2) =
            config 0 (scanRightTape (bit :: processedRev) rest)
              tape1 tape2 := by
        cases tape1 with
        | mk left1 head1 right1 =>
          cases tape2 with
          | mk left2 head2 right2 =>
            cases bit <;> cases rest <;> cases processedRev <;>
              cases head1 <;> (try cases ‹Bool›) <;>
                cases head2 <;> (try cases ‹Bool›) <;>
                  three_tape_step [description, rows, rowsForTape0Read,
                    allReads2, List.find?, scanRightTape]
      rw [hstep]
      simpa [List.reverse_cons, List.append_assoc] using
        ih (bit :: processedRev)

def rewindLeftTape
    (remainingRev processed : Word Bool) : Tape Bool :=
  match remainingRev with
  | [] =>
      tapeAtCells []
        (none :: List.append (processed.map some) [none])
  | bit :: rest =>
      tapeAtCells (rest.map some)
        (some bit :: List.append (processed.map some) [none])

set_option maxHeartbeats 1000000 in
theorem run_rewind_left
    (remainingRev processed : Word Bool)
    (tape1 tape2 : Tape Bool) :
    description.runConfig remainingRev.length
        (config 1 (rewindLeftTape remainingRev processed) tape1 tape2) =
      config 1
        (rewindLeftTape []
          (List.append remainingRev.reverse processed))
        tape1 tape2 := by
  induction remainingRev generalizing processed with
  | nil =>
      simp [Structured.Description.runConfig, rewindLeftTape]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by simp; lia]
      rw [Structured.Description.runConfig_add]
      have hstep :
          description.runConfig 1
              (config 1
                (rewindLeftTape (bit :: rest) processed) tape1 tape2) =
            config 1 (rewindLeftTape rest (bit :: processed))
              tape1 tape2 := by
        cases tape1 with
        | mk left1 head1 right1 =>
          cases tape2 with
          | mk left2 head2 right2 =>
            cases bit <;> cases rest <;> cases processed <;>
              cases head1 <;> (try cases ‹Bool›) <;>
                cases head2 <;> (try cases ‹Bool›) <;>
                  three_tape_step [description, rows, rowsForTape0Read,
                    allReads2, List.find?, rewindLeftTape]
      rw [hstep]
      simpa [List.reverse_cons, List.append_assoc] using
        ih (bit :: processed)

def fuel (bits : Word Bool) : Nat :=
  bits.length + 1 + bits.length + 1

theorem moveLeft_scanRightTape_reverse_cons
    (first : Bool) (rest : Word Bool) :
    Tape.move Direction.left
        (scanRightTape (first :: rest).reverse []) =
      rewindLeftTape (first :: rest).reverse [] := by
  cases hrest : rest.reverse <;>
    simp [scanRightTape, rewindLeftTape, tapeAtCells, Tape.move,
      Tape.moveLeft, hrest]

theorem wordListAppend_nil (bits : Word Bool) :
    List.append bits [] = bits :=
  List.append_nil bits

set_option maxHeartbeats 1000000 in
theorem run_nonempty
    (first : Bool) (rest : Word Bool)
    (tape1 tape2 : Tape Bool) :
    description.runConfig (fuel (first :: rest))
        (config 0 (Tape.input (first :: rest)) tape1 tape2) =
      config 2
        (Structured.MultiTapeLowering.guardLogicalTape
          (Tape.input (first :: rest)))
        tape1 tape2 := by
  rw [show fuel (first :: rest) =
      (first :: rest).length +
        (1 + ((first :: rest).length + 1)) by
    simp [fuel]; lia]
  rw [Structured.Description.runConfig_add]
  change description.runConfig (1 + ((first :: rest).length + 1))
      (description.runConfig (first :: rest).length
        (config 0 (scanRightTape [] (first :: rest)) tape1 tape2)) = _
  rw [run_scan_right]
  rw [Structured.Description.runConfig_add]
  have hturn :
      description.runConfig 1
          (config 0
            (scanRightTape
              (List.append (first :: rest).reverse []) []) tape1 tape2) =
        config 1
          (rewindLeftTape (first :: rest).reverse []) tape1 tape2 := by
    calc
      _ = config 1
          (Tape.move Direction.left
            (scanRightTape
              (List.append (first :: rest).reverse []) [])) tape1 tape2 := by
        cases tape1 with
        | mk left1 head1 right1 =>
          cases tape2 with
          | mk left2 head2 right2 =>
            cases rest <;>
              cases head1 <;> (try cases ‹Bool›) <;>
                cases head2 <;> (try cases ‹Bool›) <;>
                  three_tape_step [description, rows, rowsForTape0Read,
                    allReads2, List.find?, scanRightTape]
      _ = _ := by
        exact congrArg (fun tape0 => config 1 tape0 tape1 tape2)
          (by simpa only [wordListAppend_nil] using
            moveLeft_scanRightTape_reverse_cons first rest)
  rw [hturn]
  rw [Structured.Description.runConfig_add]
  rw [show (first :: rest).length =
      (first :: rest).reverse.length by simp]
  rw [run_rewind_left]
  have hfinish :
      description.runConfig 1
          (config 1
            (rewindLeftTape [] (first :: rest)) tape1 tape2) =
        config 2
          (Structured.MultiTapeLowering.guardLogicalTape
            (Tape.input (first :: rest))) tape1 tape2 := by
    cases tape1 with
    | mk left1 head1 right1 =>
      cases tape2 with
      | mk left2 head2 right2 =>
        cases rest <;>
          cases head1 <;> (try cases ‹Bool›) <;>
            cases head2 <;> (try cases ‹Bool›) <;>
              three_tape_step [description, rows, rowsForTape0Read,
                allReads2, List.find?, rewindLeftTape,
                Structured.MultiTapeLowering.guardLogicalTape, Tape.input]
  simpa only [List.reverse_reverse, wordListAppend_nil] using hfinish

end DirectJoinedInnerGuard

namespace DirectJoinedCloseout

open Structured.MultiTapeLowering.ThreeTape

def rowsForTape0Read
    (source : Nat) (read0 : Option Bool)
    (action0 action1 action2 : Structured.TapeAction)
    (target : Nat) : List Structured.Transition :=
  allReads2 fun read1 read2 =>
    row source read0 read1 read2 action0 action1 action2 target

def rowsForTape1Read
    (source : Nat) (read1 : Option Bool)
    (action0 action1 action2 : Structured.TapeAction)
    (target : Nat) : List Structured.Transition :=
  allReads2 fun read0 read2 =>
    row source read0 read1 read2 action0 action1 action2 target

def rows : List Structured.Transition :=
  List.flatten
    [ allReadRows3 0 1 keepL keepS keepS
    , rowsForTape0Read 1 (some false) keepL keepS keepS 1
    , rowsForTape0Read 1 (some true) keepL keepS keepS 1
    , rowsForTape0Read 1 none keepR keepR keepS 3
    , rowsForTape0Read 20 (some false) keepL keepS keepS 20
    , rowsForTape0Read 20 (some true) keepL keepS keepS 20
    , rowsForTape0Read 20 none keepR keepS keepS 21
    , rowsForTape0Read 3 (some false) keepR (writeBitR true) keepS 4
    , rowsForTape0Read 3 (some true) keepR (writeBitR true) keepS 4
    , rowsForTape0Read 3 none keepS keepS keepS 11
    , allReadRows3 4 5 keepS (writeBitR true) keepS
    , allReadRows3 5 6 keepS (writeBitR true) keepS
    , allReadRows3 6 7 keepS (writeBitR true) keepS
    , allReadRows3 7 8 keepS (writeBitR true) keepS
    , allReadRows3 8 9 keepS (writeBitR true) keepS
    , allReadRows3 9 10 keepS (writeBitR true) keepS
    , allReadRows3 10 3 keepS (writeBitR true) keepS
    , allReadRows3 21 22 keepR keepS keepS
    , allReadRows3 22 23 keepR keepS keepS
    , allReadRows3 23 24 keepR keepS keepS
    , allReadRows3 24 25 keepR keepS keepS
    , allReadRows3 25 26 keepR keepS keepS
    , allReadRows3 26 27 keepR keepS keepS
    , allReadRows3 11 12 keepS (writeBitR true) keepS
    , allReadRows3 12 13 keepS (writeBitR true) keepS
    , allReadRows3 13 14 keepS (writeBitR true) keepS
    , allReadRows3 14 15 keepS (writeBitR true) keepS
    , allReadRows3 15 16 keepS (writeBitR true) keepS
    , allReadRows3 16 17 keepS (writeBitR true) keepS
    , allReadRows3 17 18 keepS (writeBitR true) keepS
    , allReadRows3 18 19 keepS (writeBitR true) keepS
    , allReadRows3 19 20 keepL keepR keepS
    , rowsForTape0Read 27 (some true) keepR keepS keepS 28
    , rowsForTape0Read 28 (some true) keepR keepL keepS 40
    , rowsForTape0Read 28 (some false) keepR keepS keepS 29
    , rowsForTape0Read 29 (some false) keepR keepS keepS 30
    , rowsForTape0Read 30 (some false) keepR keepS keepS 31
    , rowsForTape0Read 31 (some true) keepR keepS keepS 32
    , rowsForTape0Read 32 (some false) keepR (writeBitR false) keepS 29
    , rowsForTape0Read 32 (some true) keepR (writeBitR false) keepS 33
    , allReadRows3 33 34 keepS keepL keepS
    , rowsForTape1Read 34 (some false) keepR eraseL keepS 35
    , rowsForTape1Read 34 none keepS keepS keepS 40
    , allReadRows3 35 36 keepR keepS keepS
    , allReadRows3 36 37 keepR keepS keepS
    , allReadRows3 37 34 keepR keepS keepS
    , rowsForTape0Read 40 (some false)
        keepR (writeBitR true) (writeBitR false) 40
    , rowsForTape0Read 40 (some true)
        keepR (writeBitR true) (writeBitR true) 40
    , rowsForTape0Read 40 none keepS keepL keepL 41
    , rowsForTape1Read 41 (some true) keepS eraseL keepS 42
    , rowsForTape1Read 42 (some true) keepS eraseL keepL 42
    , rowsForTape1Read 42 none keepS keepS keepS 43 ]

def description : Structured.Description :=
  Structured.MultiTapeLowering.ThreeTape.description 44 0 43 rows

theorem run_rewind_bit
    (left right : List (Option Bool)) (bit : Bool)
    (tape1 tape2 : Tape Bool) :
    description.runConfig 1
        (config 1 (tapeAtCells left (some bit :: right)) tape1 tape2) =
      config 1
        (Tape.move Direction.left
          (tapeAtCells left (some bit :: right))) tape1 tape2 := by
  cases tape1 with
  | mk left1 head1 right1 =>
    cases tape2 with
    | mk left2 head2 right2 =>
      cases bit <;>
        cases head1 <;> (try cases ‹Bool›) <;>
          cases head2 <;> (try cases ‹Bool›) <;>
            three_tape_step [description, rows, rowsForTape0Read,
              rowsForTape1Read, allReadRows3, allReads3, allReads2,
              List.find?]

theorem run_rewind20_bit
    (left right : List (Option Bool)) (bit : Bool)
    (tape1 tape2 : Tape Bool) :
    description.runConfig 1
        (config 20 (tapeAtCells left (some bit :: right)) tape1 tape2) =
      config 20
        (Tape.move Direction.left
          (tapeAtCells left (some bit :: right))) tape1 tape2 := by
  cases tape1 with
  | mk left1 head1 right1 =>
    cases tape2 with
    | mk left2 head2 right2 =>
      cases bit <;>
        cases head1 <;> (try cases ‹Bool›) <;>
          cases head2 <;> (try cases ‹Bool›) <;>
            three_tape_step [description, rows, rowsForTape0Read,
              rowsForTape1Read, allReadRows3, allReads3, allReads2,
              List.find?]

def sourceRewindTape
    (leftRev : Word Bool) (current : Bool)
    (processed : Word Bool) : Tape Bool :=
  tapeAtCells (List.append (leftRev.map some) [none])
    (some current ::
      List.append (processed.map some) [none])

def sourceLeftGuardTape
    (bits : Word Bool) : Tape Bool :=
  tapeAtCells []
    (none :: List.append (bits.map some) [none])

def sourceScanTape
    (processedRev remaining : Word Bool) : Tape Bool :=
  tapeAtCells (List.append (processedRev.map some) [none])
    (List.append (remaining.map some) [none])

theorem run_rewind_loop
    (state : Nat)
    (hstate : state = 1 ∨ state = 20)
    (leftRev : Word Bool) (current : Bool)
    (processed : Word Bool) (tape1 tape2 : Tape Bool) :
    description.runConfig (leftRev.length + 1)
        (config state (sourceRewindTape leftRev current processed)
          tape1 tape2) =
      config state
        (sourceLeftGuardTape
          (List.append leftRev.reverse (current :: processed)))
        tape1 tape2 := by
  rcases hstate with rfl | rfl
  · induction leftRev generalizing current processed with
    | nil =>
        simpa [sourceRewindTape, sourceLeftGuardTape,
          tapeAtCells, Tape.move, Tape.moveLeft] using
          run_rewind_bit [none] (List.append (processed.map some) [none])
            current tape1 tape2
    | cons next rest ih =>
        rw [show (next :: rest).length + 1 =
            1 + (rest.length + 1) by simp; lia]
        rw [Structured.Description.runConfig_add]
        change description.runConfig (rest.length + 1)
            (description.runConfig 1
              (config 1
                (sourceRewindTape (next :: rest) current processed)
                tape1 tape2)) = _
        rw [show sourceRewindTape (next :: rest) current processed =
            tapeAtCells
              (some next :: List.append (rest.map some) [none])
              (some current ::
                List.append (processed.map some) [none]) by
          simp [sourceRewindTape]]
        rw [run_rewind_bit]
        change description.runConfig (rest.length + 1)
            (config 1 (sourceRewindTape rest next (current :: processed))
              tape1 tape2) = _
        rw [ih]
        rw [show List.append rest.reverse (next :: current :: processed) =
            List.append (next :: rest).reverse (current :: processed) by
          simp [List.reverse_cons, List.append_assoc]]
  · induction leftRev generalizing current processed with
    | nil =>
        simpa [sourceRewindTape, sourceLeftGuardTape,
          tapeAtCells, Tape.move, Tape.moveLeft] using
          run_rewind20_bit [none]
            (List.append (processed.map some) [none]) current tape1 tape2
    | cons next rest ih =>
        rw [show (next :: rest).length + 1 =
            1 + (rest.length + 1) by simp; lia]
        rw [Structured.Description.runConfig_add]
        change description.runConfig (rest.length + 1)
            (description.runConfig 1
              (config 20
                (sourceRewindTape (next :: rest) current processed)
                tape1 tape2)) = _
        rw [show sourceRewindTape (next :: rest) current processed =
            tapeAtCells
              (some next :: List.append (rest.map some) [none])
              (some current ::
                List.append (processed.map some) [none]) by
          simp [sourceRewindTape]]
        rw [run_rewind20_bit]
        change description.runConfig (rest.length + 1)
            (config 20
              (sourceRewindTape rest next (current :: processed))
              tape1 tape2) = _
        rw [ih]
        rw [show List.append rest.reverse (next :: current :: processed) =
            List.append (next :: rest).reverse (current :: processed) by
          simp [List.reverse_cons, List.append_assoc]]

theorem run_start_left
    (tape0 tape1 tape2 : Tape Bool) :
    description.runConfig 1 (config 0 tape0 tape1 tape2) =
      config 1 (Tape.move Direction.left tape0) tape1 tape2 := by
  cases tape0 with
  | mk left0 head0 right0 =>
    cases tape1 with
    | mk left1 head1 right1 =>
      cases tape2 with
      | mk left2 head2 right2 =>
        cases head0 <;> (try cases ‹Bool›) <;>
          cases head1 <;> (try cases ‹Bool›) <;>
            cases head2 <;> (try cases ‹Bool›) <;>
              three_tape_step [description, rows, rowsForTape0Read,
                rowsForTape1Read, allReadRows3, allReads3, allReads2,
                List.find?]

theorem run_rewind_exit1
    (bits : Word Bool) (tape1 tape2 : Tape Bool) :
    description.runConfig 1
        (config 1 (sourceLeftGuardTape bits) tape1 tape2) =
      config 3 (sourceScanTape [] bits)
        (Tape.move Direction.right tape1) tape2 := by
  cases tape1 with
  | mk left1 head1 right1 =>
    cases tape2 with
    | mk left2 head2 right2 =>
      cases bits <;>
        cases head1 <;> (try cases ‹Bool›) <;>
          cases head2 <;> (try cases ‹Bool›) <;>
            three_tape_step [description, rows, rowsForTape0Read,
              rowsForTape1Read, allReadRows3, allReads3, allReads2,
              List.find?, sourceLeftGuardTape, sourceScanTape]

theorem run_rewind_exit20
    (bits : Word Bool) (tape1 tape2 : Tape Bool) :
    description.runConfig 1
        (config 20 (sourceLeftGuardTape bits) tape1 tape2) =
      config 21 (sourceScanTape [] bits) tape1 tape2 := by
  cases tape1 with
  | mk left1 head1 right1 =>
    cases tape2 with
    | mk left2 head2 right2 =>
      cases bits <;>
        cases head1 <;> (try cases ‹Bool›) <;>
          cases head2 <;> (try cases ‹Bool›) <;>
            three_tape_step [description, rows, rowsForTape0Read,
              rowsForTape1Read, allReadRows3, allReads3, allReads2,
              List.find?, sourceLeftGuardTape, sourceScanTape]

theorem run_rewind0_to_count
    (sourceInit : Word Bool) (last : Bool)
    (tape1 tape2 : Tape Bool) :
    description.runConfig (sourceInit.length + 3)
        (config 0
          (sourceScanTape (List.append sourceInit [last]).reverse [])
          tape1 tape2) =
      config 3
        (sourceScanTape [] (List.append sourceInit [last]))
        (Tape.move Direction.right tape1) tape2 := by
  rw [show sourceInit.length + 3 =
      1 + ((sourceInit.reverse.length + 1) + 1) by simp; lia]
  rw [Structured.Description.runConfig_add]
  rw [run_start_left]
  rw [show Tape.move Direction.left
        (sourceScanTape (List.append sourceInit [last]).reverse []) =
      sourceRewindTape sourceInit.reverse last [] by
    simp [sourceScanTape, sourceRewindTape, tapeAtCells,
      Tape.move, Tape.moveLeft, List.reverse_append, List.map_reverse]]
  change description.runConfig (sourceInit.reverse.length + 1 + 1)
      (config 1 (sourceRewindTape sourceInit.reverse last [])
        tape1 tape2) = _
  rw [Structured.Description.runConfig_add]
  rw [run_rewind_loop 1 (Or.inl rfl)]
  simp only [List.reverse_reverse]
  exact run_rewind_exit1 (List.append sourceInit [last]) tape1 tape2

theorem run_rewind20_to_prefix
    (sourceInit : Word Bool) (last : Bool)
    (tape1 tape2 : Tape Bool) :
    description.runConfig (sourceInit.length + 2)
        (config 20 (sourceRewindTape sourceInit.reverse last [])
          tape1 tape2) =
      config 21
        (sourceScanTape [] (List.append sourceInit [last]))
        tape1 tape2 := by
  rw [show sourceInit.length + 2 =
      (sourceInit.reverse.length + 1) + 1 by simp]
  rw [Structured.Description.runConfig_add]
  rw [run_rewind_loop 20 (Or.inr rfl)]
  simp only [List.reverse_reverse]
  exact run_rewind_exit20 (List.append sourceInit [last]) tape1 tape2

def markerBuildTape
    (markers : Nat) (baseLeft : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append (List.replicate markers (some true)) baseLeft) []

set_option maxHeartbeats 1500000 in
theorem run_count_source_bit
    (left baseLeft : List (Option Bool)) (markers : Nat) (bit : Bool)
    (right : List (Option Bool)) (tape2 : Tape Bool) :
    description.runConfig 8
        (config 3 (tapeAtCells left (some bit :: right))
          (markerBuildTape markers baseLeft) tape2) =
      config 3
        (Tape.move Direction.right
          (tapeAtCells left (some bit :: right)))
        (markerBuildTape (markers + 8) baseLeft) tape2 := by
  have hmarkers4 :
      some true :: some true :: some true :: some true ::
          (List.replicate markers (some true) ++ baseLeft) =
        List.replicate (markers + 4) (some true) ++ baseLeft := by
    rw [show markers + 4 = 4 + markers by lia]
    simpa using (list_replicate_add_append
      (some true : Option Bool) 4 markers baseLeft).symm
  have hmarkers6 :
      some true :: some true ::
          (List.replicate (markers + 4) (some true) ++ baseLeft) =
        List.replicate (markers + 6) (some true) ++ baseLeft := by
    rw [show markers + 6 = 2 + (markers + 4) by lia]
    simpa using (list_replicate_add_append
      (some true : Option Bool) 2 (markers + 4) baseLeft).symm
  have hmarkers7 :
      some true ::
          (List.replicate (markers + 6) (some true) ++ baseLeft) =
        List.replicate (markers + 7) (some true) ++ baseLeft := by
    rw [show markers + 7 = 1 + (markers + 6) by lia]
    simpa using (list_replicate_add_append
      (some true : Option Bool) 1 (markers + 6) baseLeft).symm
  have hmarkers8 :
      some true ::
          (List.replicate (markers + 7) (some true) ++ baseLeft) =
        List.replicate (markers + 8) (some true) ++ baseLeft := by
    rw [show markers + 8 = 1 + (markers + 7) by lia]
    simpa using (list_replicate_add_append
      (some true : Option Bool) 1 (markers + 7) baseLeft).symm
  rw [show 8 = 4 + 4 by rfl, Structured.Description.runConfig_add]
  have hfirst :
      description.runConfig 4
          (config 3 (tapeAtCells left (some bit :: right))
            (markerBuildTape markers baseLeft) tape2) =
        config 7
          (Tape.move Direction.right
            (tapeAtCells left (some bit :: right)))
          (markerBuildTape (markers + 4) baseLeft) tape2 := by
    cases right with
    | nil =>
      cases tape2 with
      | mk left2 head2 right2 =>
        cases bit <;> cases head2 <;> (try cases ‹Bool›) <;>
          three_tape_step [description, rows, rowsForTape0Read,
            rowsForTape1Read, allReadRows3, allReads3, allReads2,
            List.find?, markerBuildTape, hmarkers4]
    | cons next tail =>
      cases tape2 with
      | mk left2 head2 right2 =>
        cases bit <;> cases next <;> (try cases ‹Bool›) <;>
          cases head2 <;> (try cases ‹Bool›) <;>
            three_tape_step [description, rows, rowsForTape0Read,
              rowsForTape1Read, allReadRows3, allReads3, allReads2,
              List.find?, markerBuildTape, hmarkers4]
  rw [hfirst]
  rw [show 4 = 2 + 2 by rfl, Structured.Description.runConfig_add]
  have hmiddle :
      description.runConfig 2
          (config 7
            (Tape.move Direction.right
              (tapeAtCells left (some bit :: right)))
            (markerBuildTape (markers + 4) baseLeft) tape2) =
        config 9
          (Tape.move Direction.right
            (tapeAtCells left (some bit :: right)))
          (markerBuildTape (markers + 6) baseLeft) tape2 := by
    cases right with
    | nil =>
      cases tape2 with
      | mk left2 head2 right2 =>
        cases head2 <;> (try cases ‹Bool›) <;>
          three_tape_step [description, rows, rowsForTape0Read,
            rowsForTape1Read, allReadRows3, allReads3, allReads2,
            List.find?, markerBuildTape, hmarkers6]
    | cons next tail =>
      cases tape2 with
      | mk left2 head2 right2 =>
        cases next <;> (try cases ‹Bool›) <;>
          cases head2 <;> (try cases ‹Bool›) <;>
            three_tape_step [description, rows, rowsForTape0Read,
              rowsForTape1Read, allReadRows3, allReads3, allReads2,
              List.find?, markerBuildTape, hmarkers6]
  rw [hmiddle]
  rw [show 2 = 1 + 1 by rfl, Structured.Description.runConfig_add]
  have hpenultimate :
      description.runConfig 1
          (config 9
            (Tape.move Direction.right
              (tapeAtCells left (some bit :: right)))
            (markerBuildTape (markers + 6) baseLeft) tape2) =
        config 10
          (Tape.move Direction.right
            (tapeAtCells left (some bit :: right)))
          (markerBuildTape (markers + 7) baseLeft) tape2 := by
    cases right with
    | nil =>
      cases tape2 with
      | mk left2 head2 right2 =>
        cases head2 <;> (try cases ‹Bool›) <;>
          three_tape_step [description, rows, rowsForTape0Read,
            rowsForTape1Read, allReadRows3, allReads3, allReads2,
            List.find?, markerBuildTape, hmarkers7]
    | cons next tail =>
      cases tape2 with
      | mk left2 head2 right2 =>
        cases next <;> (try cases ‹Bool›) <;>
          cases head2 <;> (try cases ‹Bool›) <;>
            three_tape_step [description, rows, rowsForTape0Read,
              rowsForTape1Read, allReadRows3, allReads3, allReads2,
              List.find?, markerBuildTape, hmarkers7]
  rw [hpenultimate]
  cases right with
  | nil =>
    cases tape2 with
    | mk left2 head2 right2 =>
      cases head2 <;> (try cases ‹Bool›) <;>
        three_tape_step [description, rows, rowsForTape0Read,
          rowsForTape1Read, allReadRows3, allReads3, allReads2,
          List.find?, markerBuildTape, hmarkers8]
  | cons next tail =>
    cases tape2 with
    | mk left2 head2 right2 =>
      cases next <;> (try cases ‹Bool›) <;>
        cases head2 <;> (try cases ‹Bool›) <;>
          three_tape_step [description, rows, rowsForTape0Read,
            rowsForTape1Read, allReadRows3, allReads3, allReads2,
            List.find?, markerBuildTape, hmarkers8]

def cursorTape
    (leftRev : List (Option Bool)) (remaining : Word Bool) : Tape Bool :=
  tapeAtCells leftRev
    (List.append (remaining.map some) [none])

def fixedSourcePrefix : Word Bool :=
  [false, false, false, true, false, false]

def parserMarkerBuildTape
    (markers : Nat) (prefixLeft : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append (List.replicate markers (some false))
      (none :: prefixLeft)) []

def skipCounterTape
    (remaining : Nat) (prefixLeft rightPadding : List (Option Bool)) :
    Tape Bool :=
  match remaining with
  | 0 => tapeAtCells prefixLeft (none :: rightPadding)
  | remaining' + 1 =>
      tapeAtCells
        (List.append (List.replicate remaining' (some false))
          (none :: prefixLeft))
        (some false :: rightPadding)

end DirectJoinedCloseout

end SelectedProjectionInputQuoterFiniteLeaf
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC

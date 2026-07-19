import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorDeterminismGate
import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorSuffixGate
import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorTokenGate
import FoC.Computability.Compiler.StuckExecution

set_option doc.verso true

/-!
# Exact-code validator: Boolean closeout

This module completes a halt-stable validator recognizer into a Boolean
decider.  Every missing transition at a nonhalt state enters the rejecting
erase-and-emit tail; reaching the recognizer halt enters the accepting tail.
Both tails first rewind across the contiguous encoded input, erase it, emit one
answer bit, and stop in a fresh transition-free halt state.

The completion is structural: existing rows remain first in the table, and a
fallback row is generated only when the original lookup is absent.  Thus the
wrapper preserves every recognizer step and gives its formerly stuck endpoints
an explicit finite rejecting route.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer
namespace ValidatorBooleanCloseout

open Languages
open MachineDescription
open FoC.Computability.DovetailInitialLayoutInitializer

private def cellValues : List (Option Bool) :=
  [none, some false, some true]

@[simp] private theorem mem_cellValues (cell : Option Bool) :
    cell ∈ cellValues := by
  cases cell with
  | none => simp [cellValues]
  | some bit => cases bit <;> simp [cellValues]

/-- State that rewinds a rejecting run to the left encoded boundary. -/
def rejectRewindState (D : MachineDescription) : Nat := D.stateCount

/-- State that erases the encoded input and emits {lit}`false`. -/
def rejectEraseState (D : MachineDescription) : Nat := D.stateCount + 1

/-- State that rewinds an accepting run to the left encoded boundary. -/
def acceptRewindState (D : MachineDescription) : Nat := D.stateCount + 2

/-- State that erases the encoded input and emits {lit}`true`. -/
def acceptEraseState (D : MachineDescription) : Nat := D.stateCount + 3

/-- Fresh public halt state shared by both answer tails. -/
def answerHaltState (D : MachineDescription) : Nat := D.stateCount + 4

private def preserveLeftRow
    (source : Nat) (read : Option Bool) (target : Nat) :
    TransitionDescription :=
  transition source read read Direction.left target

private def preserveRightRow
    (source : Nat) (read : Option Bool) (target : Nat) :
    TransitionDescription :=
  transition source read read Direction.right target

/-- Optional row completing one original state/read key. -/
def completionRow?
    (D : MachineDescription) (state : Nat) (read : Option Bool) :
    Option TransitionDescription :=
  if state = D.halt then
    some (preserveLeftRow state read (acceptRewindState D))
  else
    match D.lookupTransition state read with
    | none => some (preserveLeftRow state read (rejectRewindState D))
    | some _ => none

private def completionRowsAt
    (D : MachineDescription) (state : Nat) :
    List TransitionDescription :=
  cellValues.filterMap (completionRow? D state)

/-- All missing-key rows in the original state block. -/
def completionRows (D : MachineDescription) :
    List TransitionDescription :=
  (List.range D.stateCount).flatMap (completionRowsAt D)

private def rewindRows
    (rewind erase : Nat) : List TransitionDescription :=
  [ preserveRightRow rewind none erase
  , preserveLeftRow rewind (some false) rewind
  , preserveLeftRow rewind (some true) rewind
  ]

private def eraseRows
    (erase halt : Nat) (answer : Bool) : List TransitionDescription :=
  [ transition erase none (some answer) Direction.right halt
  , transition erase (some false) none Direction.right erase
  , transition erase (some true) none Direction.right erase
  ]

/-- Fixed rejecting and accepting rewind/erase/emit rows. -/
def answerRows (D : MachineDescription) :
    List TransitionDescription :=
  rewindRows (rejectRewindState D) (rejectEraseState D) ++
    eraseRows (rejectEraseState D) (answerHaltState D) false ++
    rewindRows (acceptRewindState D) (acceptEraseState D) ++
    eraseRows (acceptEraseState D) (answerHaltState D) true

/-- Complete a recognizer by routing every stuck key to {lit}`false` and its
successful halt to {lit}`true`. -/
def Description (D : MachineDescription) : MachineDescription where
  stateCount := D.stateCount + 5
  start := D.start
  halt := answerHaltState D
  transitions := D.transitions ++ completionRows D ++ answerRows D

/-!
## Completion-row structure
-/

@[simp] theorem completionRow?_halt
    (D : MachineDescription) (read : Option Bool) :
    completionRow? D D.halt read =
      some (preserveLeftRow D.halt read (acceptRewindState D)) := by
  simp [completionRow?]

theorem completionRow?_missing
    (D : MachineDescription) (state : Nat) (read : Option Bool)
    (hstate : state ≠ D.halt)
    (hlookup : D.lookupTransition state read = none) :
    completionRow? D state read =
      some (preserveLeftRow state read (rejectRewindState D)) := by
  simp [completionRow?, hstate, hlookup]

theorem completionRow?_present
    (D : MachineDescription) (state : Nat) (read : Option Bool)
    (hstate : state ≠ D.halt)
    {row : TransitionDescription}
    (hlookup : D.lookupTransition state read = some row) :
    completionRow? D state read = none := by
  simp [completionRow?, hstate, hlookup]

private theorem completion_row_mem
    (D : MachineDescription) (state : Nat) (read : Option Bool)
    {row : TransitionDescription}
    (hstate : state < D.stateCount)
    (hrow : completionRow? D state read = some row) :
    row ∈ completionRows D := by
  rw [completionRows, List.mem_flatMap]
  refine ⟨state, List.mem_range.mpr hstate, ?_⟩
  rw [completionRowsAt, List.mem_filterMap]
  exact ⟨read, mem_cellValues read, hrow⟩

/-- The accepting completion row exists at every possible halt-state read. -/
theorem accept_row_mem
    (D : MachineDescription) (hhalt : D.halt < D.stateCount)
    (read : Option Bool) :
    preserveLeftRow D.halt read (acceptRewindState D) ∈
      completionRows D :=
  completion_row_mem D D.halt read hhalt
    (completionRow?_halt D read)

/-- A missing nonhalt lookup has its rejecting completion row. -/
theorem reject_row_mem
    (D : MachineDescription) (state : Nat) (read : Option Bool)
    (hbound : state < D.stateCount) (hstate : state ≠ D.halt)
    (hlookup : D.lookupTransition state read = none) :
    preserveLeftRow state read (rejectRewindState D) ∈
      completionRows D :=
  completion_row_mem D state read hbound
    (completionRow?_missing D state read hstate hlookup)

private theorem mem_completion_rows
    {D : MachineDescription} {row : TransitionDescription}
    (hrow : row ∈ completionRows D) :
    exists state : Nat, exists read : Option Bool,
      state < D.stateCount ∧
        completionRow? D state read = some row := by
  rw [completionRows, List.mem_flatMap] at hrow
  rcases hrow with ⟨state, hstate, hrow⟩
  rw [completionRowsAt, List.mem_filterMap] at hrow
  rcases hrow with ⟨read, _hread, hrow⟩
  exact ⟨state, read, List.mem_range.mp hstate, hrow⟩

private theorem completion_row_source_read
    {D : MachineDescription} {state : Nat} {read : Option Bool}
    {row : TransitionDescription}
    (hrow : completionRow? D state read = some row) :
    row.source = state ∧ row.read = read := by
  unfold completionRow? at hrow
  split at hrow
  · have hkey : state = row.source ∧ read = row.read := by
      simpa [preserveLeftRow, transition] using
        congrArg (fun value => Option.map
          (fun r : TransitionDescription => (r.source, r.read)) value) hrow
    exact ⟨hkey.1.symm, hkey.2.symm⟩
  · split at hrow
    · have hkey : state = row.source ∧ read = row.read := by
        simpa [preserveLeftRow, transition] using
          congrArg (fun value => Option.map
            (fun r : TransitionDescription => (r.source, r.read)) value) hrow
      exact ⟨hkey.1.symm, hkey.2.symm⟩
    · simp at hrow

private theorem completion_rows_source_lt
    {D : MachineDescription} {row : TransitionDescription}
    (hrow : row ∈ completionRows D) :
    row.source < D.stateCount := by
  rcases mem_completion_rows hrow with
    ⟨state, read, hstate, hcompletion⟩
  exact (completion_row_source_read hcompletion).1.symm ▸ hstate

private theorem completion_rows_lookup
    {D : MachineDescription} {row : TransitionDescription}
    (hrow : row ∈ completionRows D) :
    row.source = D.halt ∨
      D.lookupTransition row.source row.read = none := by
  rcases mem_completion_rows hrow with
    ⟨state, read, _hstate, hcompletion⟩
  have hkey := completion_row_source_read hcompletion
  by_cases hhalt : state = D.halt
  · exact Or.inl (hkey.1.trans hhalt)
  · right
    unfold completionRow? at hcompletion
    simp [hhalt] at hcompletion
    cases hlookup : D.lookupTransition state read with
    | none => simpa [hkey.1, hkey.2] using hlookup
    | some base => simp [hlookup] at hcompletion

private theorem completion_rows_target
    {D : MachineDescription} {row : TransitionDescription}
    (hrow : row ∈ completionRows D) :
    row.target = rejectRewindState D ∨
      row.target = acceptRewindState D := by
  rcases mem_completion_rows hrow with
    ⟨state, read, _hstate, hcompletion⟩
  unfold completionRow? at hcompletion
  split at hcompletion
  · right
    have hrowEq := Option.some.inj hcompletion
    rw [← hrowEq]
    rfl
  · split at hcompletion
    · left
      have hrowEq := Option.some.inj hcompletion
      rw [← hrowEq]
      rfl
    · simp at hcompletion

private theorem completion_rows_wellFormed
    {D : MachineDescription} {row : TransitionDescription}
    (hrow : row ∈ completionRows D) :
    row.WellFormed (D.stateCount + 5) := by
  constructor
  · exact Nat.lt_trans (completion_rows_source_lt hrow) (by lia)
  · rcases completion_rows_target hrow with hreject | haccept
    · rw [hreject]
      simp [rejectRewindState]
    · rw [haccept]
      simp [acceptRewindState]

private theorem completion_rows_deterministic
    {D : MachineDescription}
    {left right : TransitionDescription}
    (hleft : left ∈ completionRows D)
    (hright : right ∈ completionRows D)
    (hkey : TransitionDescription.SameKey left right) :
    TransitionDescription.SameAction left right := by
  rcases mem_completion_rows hleft with
    ⟨leftState, leftRead, _hleftState, hleftRow⟩
  rcases mem_completion_rows hright with
    ⟨rightState, rightRead, _hrightState, hrightRow⟩
  have hleftKey := completion_row_source_read hleftRow
  have hrightKey := completion_row_source_read hrightRow
  have hstate : leftState = rightState := by
    rw [← hleftKey.1, ← hrightKey.1]
    exact hkey.1
  have hread : leftRead = rightRead := by
    rw [← hleftKey.2, ← hrightKey.2]
    exact hkey.2
  subst rightState
  subst rightRead
  rw [hleftRow] at hrightRow
  have hrow : left = right := Option.some.inj hrightRow
  subst right
  exact ⟨rfl, rfl, rfl⟩

/-!
## Answer-row structure
-/

private theorem answer_rows_source_ge
    {D : MachineDescription} {row : TransitionDescription}
    (hrow : row ∈ answerRows D) :
    D.stateCount ≤ row.source := by
  simp [answerRows, rewindRows, eraseRows, preserveLeftRow,
    preserveRightRow, transition] at hrow
  rcases hrow with
      rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [rejectRewindState, rejectEraseState, acceptRewindState,
      acceptEraseState]

private theorem answer_rows_wellFormed
    {D : MachineDescription} {row : TransitionDescription}
    (hrow : row ∈ answerRows D) :
    row.WellFormed (D.stateCount + 5) := by
  simp [answerRows, rewindRows, eraseRows, preserveLeftRow,
    preserveRightRow, transition] at hrow
  rcases hrow with
      rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [TransitionDescription.WellFormed, rejectRewindState,
      rejectEraseState, acceptRewindState, acceptEraseState,
      answerHaltState] <;> lia

private theorem answer_rows_deterministic
    {D : MachineDescription}
    {left right : TransitionDescription}
    (hleft : left ∈ answerRows D)
    (hright : right ∈ answerRows D)
    (hkey : TransitionDescription.SameKey left right) :
    TransitionDescription.SameAction left right := by
  simp [answerRows, rewindRows, eraseRows, preserveLeftRow,
    preserveRightRow, transition] at hleft hright
  rcases hleft with
      rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hright with
      rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [TransitionDescription.SameKey,
      TransitionDescription.SameAction, rejectRewindState,
      rejectEraseState, acceptRewindState, acceptEraseState,
      answerHaltState] at hkey ⊢ <;> lia

private theorem answer_rows_source_ne_halt
    {D : MachineDescription} {row : TransitionDescription}
    (hrow : row ∈ answerRows D) :
    row.source ≠ answerHaltState D := by
  simp [answerRows, rewindRows, eraseRows, preserveLeftRow,
    preserveRightRow, transition] at hrow
  rcases hrow with
      rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [rejectRewindState, rejectEraseState, acceptRewindState,
      acceptEraseState, answerHaltState] <;> lia

private theorem base_completion_deterministic
    {D : MachineDescription} (hD : D.SubroutineReady)
    {base completed : TransitionDescription}
    (hbase : base ∈ D.transitions)
    (hcompleted : completed ∈ completionRows D)
    (hkey : TransitionDescription.SameKey base completed) :
    TransitionDescription.SameAction base completed := by
  rcases completion_rows_lookup hcompleted with hhalt | hmissing
  · exfalso
    exact (hD.2 base hbase) (hkey.1.trans hhalt)
  · have hlookup :
        D.lookupTransition base.source base.read = some base :=
      lookupTransition_eq_some_of_mem_deterministic
        hD.1.2.2.2.2 hbase
    rw [← hkey.1, ← hkey.2, hlookup] at hmissing
    contradiction

private theorem completion_base_deterministic
    {D : MachineDescription} (hD : D.SubroutineReady)
    {completed base : TransitionDescription}
    (hcompleted : completed ∈ completionRows D)
    (hbase : base ∈ D.transitions)
    (hkey : TransitionDescription.SameKey completed base) :
    TransitionDescription.SameAction completed base := by
  have haction := base_completion_deterministic hD hbase hcompleted
    ⟨hkey.1.symm, hkey.2.symm⟩
  exact ⟨haction.1.symm, haction.2.1.symm, haction.2.2.symm⟩

private theorem source_separation_deterministic
    {D : MachineDescription}
    {early late : TransitionDescription}
    (hearly : early.source < D.stateCount)
    (hlate : D.stateCount ≤ late.source)
    (hkey : TransitionDescription.SameKey early late) :
    TransitionDescription.SameAction early late := by
  exfalso
  rw [hkey.1] at hearly
  exact Nat.not_lt_of_ge hlate hearly

private theorem source_separation_deterministic_rev
    {D : MachineDescription}
    {late early : TransitionDescription}
    (hlate : D.stateCount ≤ late.source)
    (hearly : early.source < D.stateCount)
    (hkey : TransitionDescription.SameKey late early) :
    TransitionDescription.SameAction late early := by
  exfalso
  rw [hkey.1] at hlate
  exact Nat.not_le_of_lt hearly hlate

/-!
## Structural readiness
-/

/-- Completion preserves finite-description well-formedness. -/
theorem description_wellFormed
    {D : MachineDescription} (hD : D.SubroutineReady) :
    (Description D).WellFormed := by
  have hWF := hD.1
  constructor
  · simp [Description]
  constructor
  · exact Nat.lt_trans hWF.2.1 (by simp [Description])
  constructor
  · simp [Description, answerHaltState]
  constructor
  · intro row hrow
    change row ∈
      (D.transitions ++ completionRows D) ++ answerRows D at hrow
    change row.WellFormed (D.stateCount + 5)
    rw [List.mem_append] at hrow
    rcases hrow with hfront | hanswer
    · rw [List.mem_append] at hfront
      rcases hfront with hbase | hcompletion
      · have hbaseWF := hWF.2.2.2.1 row hbase
        exact
          ⟨Nat.lt_trans hbaseWF.1 (by lia),
            Nat.lt_trans hbaseWF.2 (by lia)⟩
      · exact completion_rows_wellFormed hcompletion
    · exact answer_rows_wellFormed hanswer
  · intro left right hleft hright hkey
    change left ∈
      (D.transitions ++ completionRows D) ++ answerRows D at hleft
    change right ∈
      (D.transitions ++ completionRows D) ++ answerRows D at hright
    rw [List.mem_append] at hleft hright
    rcases hleft with hleftFront | hleftAnswer
    · rw [List.mem_append] at hleftFront
      rcases hleftFront with hleftBase | hleftCompletion
      · rcases hright with hrightFront | hrightAnswer
        · rw [List.mem_append] at hrightFront
          rcases hrightFront with hrightBase | hrightCompletion
          · exact hWF.2.2.2.2 left right
              hleftBase hrightBase hkey
          · exact base_completion_deterministic hD
              hleftBase hrightCompletion hkey
        · exact source_separation_deterministic
            (hWF.2.2.2.1 left hleftBase).1
            (answer_rows_source_ge hrightAnswer) hkey
      · rcases hright with hrightFront | hrightAnswer
        · rw [List.mem_append] at hrightFront
          rcases hrightFront with hrightBase | hrightCompletion
          · exact completion_base_deterministic hD
              hleftCompletion hrightBase hkey
          · exact completion_rows_deterministic
              hleftCompletion hrightCompletion hkey
        · exact source_separation_deterministic
            (completion_rows_source_lt hleftCompletion)
            (answer_rows_source_ge hrightAnswer) hkey
    · rcases hright with hrightFront | hrightAnswer
      · rw [List.mem_append] at hrightFront
        rcases hrightFront with hrightBase | hrightCompletion
        · exact source_separation_deterministic_rev
            (answer_rows_source_ge hleftAnswer)
            (hWF.2.2.2.1 right hrightBase).1 hkey
        · exact source_separation_deterministic_rev
            (answer_rows_source_ge hleftAnswer)
            (completion_rows_source_lt hrightCompletion) hkey
      · exact answer_rows_deterministic hleftAnswer hrightAnswer hkey

/-- The fresh answer halt has no outgoing transition. -/
theorem description_haltTransitionFree
    {D : MachineDescription} (hD : D.SubroutineReady) :
    (Description D).HaltTransitionFree := by
  intro row hrow
  change row ∈
    (D.transitions ++ completionRows D) ++ answerRows D at hrow
  rw [List.mem_append] at hrow
  rcases hrow with hfront | hanswer
  · rw [List.mem_append] at hfront
    rcases hfront with hbase | hcompletion
    · have hsource := (hD.1.2.2.2.1 row hbase).1
      simp [Description, answerHaltState]
      lia
    · have hsource := completion_rows_source_lt hcompletion
      simp [Description, answerHaltState]
      lia
  · simpa [Description] using answer_rows_source_ne_halt hanswer

/-- The Boolean completion is ready for further finite-table composition. -/
theorem description_subroutineReady
    {D : MachineDescription} (hD : D.SubroutineReady) :
    (Description D).SubroutineReady :=
  ⟨description_wellFormed hD, description_haltTransitionFree hD⟩

/-!
## Step preservation and branch entry
-/

private theorem base_row_mem_description
    {D : MachineDescription} {row : TransitionDescription}
    (hrow : row ∈ D.transitions) :
    row ∈ (Description D).transitions := by
  simp [Description, hrow]

private theorem completion_row_mem_description
    {D : MachineDescription} {row : TransitionDescription}
    (hrow : row ∈ completionRows D) :
    row ∈ (Description D).transitions := by
  simp [Description, hrow]

private theorem answer_row_mem_description
    {D : MachineDescription} {row : TransitionDescription}
    (hrow : row ∈ answerRows D) :
    row ∈ (Description D).transitions := by
  simp [Description, hrow]

/-- Every concrete original step is unchanged by Boolean completion. -/
theorem stepConfig_of_base_step
    {D : MachineDescription} (hD : D.SubroutineReady)
    {source target : Configuration}
    (hstep : D.stepConfig source = some target) :
    (Description D).stepConfig source = some target := by
  unfold MachineDescription.stepConfig at hstep ⊢
  cases hlookup :
      D.lookupTransition source.state (Tape.read source.tape) with
  | none => simp [hlookup] at hstep
  | some row =>
      have hrow : row ∈ D.transitions :=
        MachineDescription.lookupTransition_mem hlookup
      have hlookupCompleted :
          (Description D).lookupTransition row.source row.read = some row :=
        lookupTransition_eq_some_of_mem_deterministic
          (description_wellFormed hD).2.2.2.2
          (base_row_mem_description hrow)
      have hmatches := MachineDescription.lookupTransition_matches hlookup
      have hlookupCompleted' :
          (Description D).lookupTransition source.state
              (Tape.read source.tape) = some row := by
        simpa [hmatches.1, hmatches.2] using hlookupCompleted
      rw [hlookupCompleted']
      rw [hlookup] at hstep
      exact hstep

private theorem lookup_completion_row
    {D : MachineDescription} (hD : D.SubroutineReady)
    {row : TransitionDescription}
    (hrow : row ∈ completionRows D) :
    (Description D).lookupTransition row.source row.read = some row :=
  lookupTransition_eq_some_of_mem_deterministic
    (description_wellFormed hD).2.2.2.2
    (completion_row_mem_description hrow)

private theorem lookup_answer_row
    {D : MachineDescription} (hD : D.SubroutineReady)
    {row : TransitionDescription}
    (hrow : row ∈ answerRows D) :
    (Description D).lookupTransition row.source row.read = some row :=
  lookupTransition_eq_some_of_mem_deterministic
    (description_wellFormed hD).2.2.2.2
    (answer_row_mem_description hrow)

/-- Reaching the original halt enters the accepting rewind tail in one step. -/
theorem runConfig_one_accept
    {D : MachineDescription} (hD : D.SubroutineReady)
    (T : Tape Bool) :
    (Description D).runConfig 1
        { state := D.halt, tape := T } =
      { state := acceptRewindState D
        tape := Tape.move Direction.left T } := by
  let row := preserveLeftRow D.halt (Tape.read T) (acceptRewindState D)
  have hrow : row ∈ completionRows D :=
    accept_row_mem D hD.1.2.2.1 (Tape.read T)
  have hlookup := lookup_completion_row hD hrow
  have hlookup' :
      (Description D).lookupTransition D.halt (Tape.read T) = some row := by
    simpa [row, preserveLeftRow, transition] using hlookup
  simp [MachineDescription.runConfig, MachineDescription.stepConfig,
    hlookup', row, preserveLeftRow, transition,
    Tape.write_read_eq_self]

/-- A missing bounded nonhalt key enters the rejecting rewind tail. -/
theorem runConfig_one_reject
    {D : MachineDescription} (hD : D.SubroutineReady)
    {state : Nat} (hbound : state < D.stateCount)
    (hstate : state ≠ D.halt) (T : Tape Bool)
    (hlookup : D.lookupTransition state (Tape.read T) = none) :
    (Description D).runConfig 1
        { state := state, tape := T } =
      { state := rejectRewindState D
        tape := Tape.move Direction.left T } := by
  let row := preserveLeftRow state (Tape.read T) (rejectRewindState D)
  have hrow : row ∈ completionRows D :=
    reject_row_mem D state (Tape.read T)
      hbound hstate hlookup
  have hlookupCompleted := lookup_completion_row hD hrow
  have hlookupCompleted' :
      (Description D).lookupTransition state (Tape.read T) = some row := by
    simpa [row, preserveLeftRow, transition] using hlookupCompleted
  simp [MachineDescription.runConfig, MachineDescription.stepConfig,
    hlookupCompleted', row, preserveLeftRow, transition,
    Tape.write_read_eq_self]

private theorem reaches_reject_of_runConfig_stuck
    {D : MachineDescription} (hD : D.SubroutineReady)
    {steps : Nat} {source : Configuration} {state : Nat}
    {stuck : Tape Bool}
    (hsource : source.state < D.stateCount)
    (hrun : D.runConfig steps source =
      { state := state, tape := stuck })
    (hstep : D.stepConfig { state := state, tape := stuck } = none)
    (hstate : state ≠ D.halt) :
    exists completedSteps : Nat,
      (Description D).runConfig completedSteps source =
        { state := rejectRewindState D
          tape := Tape.move Direction.left stuck } := by
  induction steps generalizing source with
  | zero =>
      have hsourceEq : source = { state := state, tape := stuck } := by
        simpa [MachineDescription.runConfig] using hrun
      rw [hsourceEq] at hsource ⊢
      exact ⟨1, runConfig_one_reject hD hsource hstate stuck
        (lookupTransition_eq_none_of_stepConfig_eq_none hstep)⟩
  | succ steps ih =>
      cases hsourceStep : D.stepConfig source with
      | none =>
          have hstay :=
            MachineDescription.runConfig_of_stepConfig_none
              hsourceStep (Nat.succ steps)
          have hsourceEq :
              source = { state := state, tape := stuck } :=
            hstay.symm.trans hrun
          have hlookup :=
            lookupTransition_eq_none_of_stepConfig_eq_none hsourceStep
          have hsourceState : source.state ≠ D.halt := by
            simpa [hsourceEq] using hstate
          refine ⟨1, ?_⟩
          simpa [hsourceEq] using
            runConfig_one_reject hD hsource hsourceState source.tape hlookup
      | some next =>
          have hrunNext :
              D.runConfig steps next =
                { state := state, tape := stuck } := by
            simpa [MachineDescription.runConfig, hsourceStep] using hrun
          have hnextBound : next.state < D.stateCount :=
            MachineDescription.stepConfig_state_bound hD.1 hsourceStep
          rcases ih hnextBound hrunNext with
            ⟨completedSteps, hcompleted⟩
          refine ⟨completedSteps + 1, ?_⟩
          have hcompletedStep := stepConfig_of_base_step hD hsourceStep
          simpa [MachineDescription.runConfig, hcompletedStep] using hcompleted

private theorem runConfig_to_first_halt
    {D : MachineDescription} (hD : D.SubroutineReady)
    {n : Nat} {source : Configuration} {T : Tape Bool}
    (hrun : D.runConfig n source = { state := D.halt, tape := T })
    (hfirst : forall k : Nat, k < n ->
      (D.runConfig k source).state ≠ D.halt) :
    (Description D).runConfig n source =
      { state := D.halt, tape := T } := by
  induction n generalizing source T with
  | zero =>
      simpa [MachineDescription.runConfig] using hrun
  | succ n ih =>
      have hsource : source.state ≠ D.halt := by
        have hzero := hfirst 0 (Nat.zero_lt_succ n)
        simpa [MachineDescription.runConfig] using hzero
      cases hstep : D.stepConfig source with
      | none =>
          have hstay :=
            MachineDescription.runConfig_of_stepConfig_none hstep (n + 1)
          have hsourceEq :
              source = { state := D.halt, tape := T } := by
            exact hstay.symm.trans hrun
          exact False.elim
            (hsource (congrArg Configuration.state hsourceEq))
      | some next =>
          have hrunNext :
              D.runConfig n next = { state := D.halt, tape := T } := by
            simpa [MachineDescription.runConfig, hstep] using hrun
          have hfirstNext : forall k : Nat, k < n ->
              (D.runConfig k next).state ≠ D.halt := by
            intro k hk
            have hnext := hfirst (k + 1) (by lia)
            simpa [MachineDescription.runConfig, hstep] using hnext
          have ihNext := ih hrunNext hfirstNext
          have hstepCompleted := stepConfig_of_base_step hD hstep
          simpa [MachineDescription.runConfig, hstepCompleted] using ihNext

/-- Every original halt reaches the accepting rewind state with the original
output tape moved one cell left. -/
theorem reaches_accept_of_haltsFromTape
    {D : MachineDescription} (hD : D.SubroutineReady)
    {input output : Tape Bool}
    (hhalts : D.HaltsFromTape input output) :
    exists steps : Nat,
      (Description D).runConfig steps
          { state := (Description D).start, tape := input } =
        { state := acceptRewindState D
          tape := Tape.move Direction.left output } := by
  rcases MachineDescription.runConfig_eq_halt_of_haltsFromTape hhalts with
    ⟨n, hrun⟩
  rcases MachineDescription.firstReaches_halt_of_runConfig_eq hD.2 hrun with
    ⟨first, _hfirstLe, hfirstRun, hfirstMinimal⟩
  have hcompleted :=
    runConfig_to_first_halt hD hfirstRun hfirstMinimal
  refine ⟨first + 1, ?_⟩
  rw [MachineDescription.runConfig_add]
  change
    (Description D).runConfig 1
        ((Description D).runConfig first
          { state := D.start, tape := input }) = _
  rw [hcompleted]
  simpa [Description] using runConfig_one_accept hD output

/-!
## Rewind and erase/emit tails
-/

/-- Answer-indexed rewind state. -/
def answerRewindState (D : MachineDescription) : Bool -> Nat
  | false => rejectRewindState D
  | true => acceptRewindState D

/-- Answer-indexed erase/emit state. -/
def answerEraseState (D : MachineDescription) : Bool -> Nat
  | false => rejectEraseState D
  | true => acceptEraseState D

private theorem rewind_blank_row_mem
    (D : MachineDescription) (answer : Bool) :
    preserveRightRow (answerRewindState D answer) none
        (answerEraseState D answer) ∈ answerRows D := by
  cases answer <;>
    simp [answerRewindState, answerEraseState, answerRows,
      rewindRows, eraseRows]

private theorem rewind_bit_row_mem
    (D : MachineDescription) (answer bit : Bool) :
    preserveLeftRow (answerRewindState D answer) (some bit)
        (answerRewindState D answer) ∈ answerRows D := by
  cases answer <;> cases bit <;>
    simp [answerRewindState, answerRows, rewindRows, eraseRows]

private theorem erase_blank_row_mem
    (D : MachineDescription) (answer : Bool) :
    transition (answerEraseState D answer) none (some answer)
        Direction.right (answerHaltState D) ∈ answerRows D := by
  cases answer <;>
    simp [answerEraseState, answerRows, rewindRows, eraseRows]

private theorem erase_bit_row_mem
    (D : MachineDescription) (answer bit : Bool) :
    transition (answerEraseState D answer) (some bit) none
        Direction.right (answerEraseState D answer) ∈ answerRows D := by
  cases answer <;> cases bit <;>
    simp [answerEraseState, answerRows, rewindRows, eraseRows]

private theorem runConfig_one_rewind_blank
    {D : MachineDescription} (hD : D.SubroutineReady)
    (answer : Bool) (T : Tape Bool) (hread : Tape.read T = none) :
    (Description D).runConfig 1
        { state := answerRewindState D answer, tape := T } =
      { state := answerEraseState D answer
        tape := Tape.move Direction.right T } := by
  let row := preserveRightRow (answerRewindState D answer) none
    (answerEraseState D answer)
  have hrow : row ∈ answerRows D := rewind_blank_row_mem D answer
  have hlookup := lookup_answer_row hD hrow
  have hlookup' :
      (Description D).lookupTransition (answerRewindState D answer)
          (Tape.read T) = some row := by
    simpa [row, preserveRightRow, transition, hread] using hlookup
  have hwrite : Tape.write none T = T := by
    rw [← hread]
    exact Tape.write_read_eq_self T
  simp [MachineDescription.runConfig, MachineDescription.stepConfig,
    hlookup', row, preserveRightRow, transition, hwrite]

private theorem runConfig_one_rewind_bit
    {D : MachineDescription} (hD : D.SubroutineReady)
    (answer bit : Bool) (T : Tape Bool)
    (hread : Tape.read T = some bit) :
    (Description D).runConfig 1
        { state := answerRewindState D answer, tape := T } =
      { state := answerRewindState D answer
        tape := Tape.move Direction.left T } := by
  let row := preserveLeftRow (answerRewindState D answer) (some bit)
    (answerRewindState D answer)
  have hrow : row ∈ answerRows D := rewind_bit_row_mem D answer bit
  have hlookup := lookup_answer_row hD hrow
  have hlookup' :
      (Description D).lookupTransition (answerRewindState D answer)
          (Tape.read T) = some row := by
    simpa [row, preserveLeftRow, transition, hread] using hlookup
  have hwrite : Tape.write (some bit) T = T := by
    rw [← hread]
    exact Tape.write_read_eq_self T
  simp [MachineDescription.runConfig, MachineDescription.stepConfig,
    hlookup', row, preserveLeftRow, transition, hwrite]

private theorem runConfig_one_erase_blank
    {D : MachineDescription} (hD : D.SubroutineReady)
    (answer : Bool) (T : Tape Bool) (hread : Tape.read T = none) :
    (Description D).runConfig 1
        { state := answerEraseState D answer, tape := T } =
      { state := answerHaltState D
        tape := Tape.move Direction.right (Tape.write (some answer) T) } := by
  let row := transition (answerEraseState D answer) none (some answer)
    Direction.right (answerHaltState D)
  have hrow : row ∈ answerRows D := erase_blank_row_mem D answer
  have hlookup := lookup_answer_row hD hrow
  have hlookup' :
      (Description D).lookupTransition (answerEraseState D answer)
          (Tape.read T) = some row := by
    simpa [row, transition, hread] using hlookup
  simp [MachineDescription.runConfig, MachineDescription.stepConfig,
    hlookup', row, transition]

private theorem runConfig_one_erase_bit
    {D : MachineDescription} (hD : D.SubroutineReady)
    (answer bit : Bool) (T : Tape Bool)
    (hread : Tape.read T = some bit) :
    (Description D).runConfig 1
        { state := answerEraseState D answer, tape := T } =
      { state := answerEraseState D answer
        tape := Tape.move Direction.right (Tape.write none T) } := by
  let row := transition (answerEraseState D answer) (some bit) none
    Direction.right (answerEraseState D answer)
  have hrow : row ∈ answerRows D := erase_bit_row_mem D answer bit
  have hlookup := lookup_answer_row hD hrow
  have hlookup' :
      (Description D).lookupTransition (answerEraseState D answer)
          (Tape.read T) = some row := by
    simpa [row, transition, hread] using hlookup
  simp [MachineDescription.runConfig, MachineDescription.stepConfig,
    hlookup', row, transition]

private def eraseTape
    (erased : Nat) (right : Word Bool) (padding : Nat) : Tape Bool :=
  tapeAtCells
    (List.append
      (List.replicate erased (none : Option Bool)) [none])
    (List.append (right.map some)
      (List.replicate (padding + 1) (none : Option Bool)))

/-- Exact final tape after erasing a contiguous word and emitting one answer. -/
def answerTape
    (answer : Bool) (erased padding : Nat) : Tape Bool :=
  tapeAtCells
    (some answer ::
      List.append
        (List.replicate erased (none : Option Bool)) [none])
    (List.replicate padding (none : Option Bool))

/-- The answer tail exposes exactly one normalized Boolean cell. -/
theorem answerTape_normalizedOutput
    (answer : Bool) (erased padding : Nat) :
    Tape.normalizedOutput (answerTape answer erased padding) = [answer] := by
  cases padding <;>
    simp [answerTape, tapeAtCells, Tape.normalizedOutput, Tape.cells,
      List.replicate_succ]

private theorem runConfig_rewind
    {D : MachineDescription} (hD : D.SubroutineReady)
    (answer : Bool) (leftRev right : Word Bool) (padding : Nat) :
    (Description D).runConfig (leftRev.length + 1)
        { state := answerRewindState D answer
          tape := Tape.move Direction.left
            (splitTape leftRev right padding) } =
      { state := answerEraseState D answer
        tape := splitTape []
          (List.append leftRev.reverse right) padding } := by
  induction leftRev generalizing right with
  | nil =>
      have hread :
          Tape.read
              (Tape.move Direction.left (splitTape [] right padding)) =
            none := by
        cases right <;>
          simp [splitTape, Tape.read, Tape.move,
            Tape.moveLeft, List.replicate_succ]
      have hstep := runConfig_one_rewind_blank hD answer
        (Tape.move Direction.left (splitTape [] right padding)) hread
      cases right <;>
        simpa [splitTape, tapeAtCells, Tape.move, Tape.moveLeft,
          Tape.moveRight, List.replicate_succ] using hstep
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 1 = 1 + (rest.length + 1) by
        simp
        lia]
      rw [MachineDescription.runConfig_add]
      have hread :
          Tape.read
              (Tape.move Direction.left
                (splitTape (bit :: rest) right padding)) = some bit := by
        cases right <;>
          simp [splitTape, Tape.read, Tape.move,
            Tape.moveLeft, List.replicate_succ]
      rw [runConfig_one_rewind_bit hD answer bit _ hread]
      have htail := ih (bit :: right)
      cases right <;>
        simpa [splitTape, tapeAtCells, Tape.move, Tape.moveLeft,
          List.reverse_cons, List.append_assoc, List.replicate_succ]
          using htail

private theorem runConfig_erase
    {D : MachineDescription} (hD : D.SubroutineReady)
    (answer : Bool) (erased : Nat) (right : Word Bool) (padding : Nat) :
    (Description D).runConfig (right.length + 1)
        { state := answerEraseState D answer
          tape := eraseTape erased right padding } =
      { state := answerHaltState D
        tape := answerTape answer (erased + right.length) padding } := by
  induction right generalizing erased with
  | nil =>
      have hread : Tape.read (eraseTape erased [] padding) = none := by
        simp [eraseTape, tapeAtCells, Tape.read, List.replicate_succ]
      have hstep := runConfig_one_erase_blank hD answer
        (eraseTape erased [] padding) hread
      cases padding <;>
        simpa [eraseTape, answerTape, tapeAtCells, Tape.move,
          Tape.moveRight, Tape.write, List.replicate_succ,
          List.append_assoc] using hstep
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 1 = 1 + (rest.length + 1) by
        simp
        lia]
      rw [MachineDescription.runConfig_add]
      have hread :
          Tape.read (eraseTape erased (bit :: rest) padding) = some bit := by
        simp [eraseTape, tapeAtCells, Tape.read, List.replicate_succ]
      rw [runConfig_one_erase_bit hD answer bit _ hread]
      have htail := ih (erased + 1)
      have herased :
          erased + 1 + rest.length = erased + (rest.length + 1) := by
        lia
      rw [herased] at htail
      cases rest <;>
        simpa [eraseTape, tapeAtCells, Tape.move, Tape.moveRight,
          Tape.write, List.replicate_succ, List.append_assoc] using htail

private theorem runConfig_answer_tail
    {D : MachineDescription} (hD : D.SubroutineReady)
    (answer : Bool) (leftRev right : Word Bool) (padding : Nat) :
    (Description D).runConfig
        ((leftRev.length + 1) +
          ((List.append leftRev.reverse right).length + 1))
        { state := answerRewindState D answer
          tape := Tape.move Direction.left
            (splitTape leftRev right padding) } =
      { state := answerHaltState D
        tape := answerTape answer
          (List.append leftRev.reverse right).length padding } := by
  rw [MachineDescription.runConfig_add]
  rw [runConfig_rewind hD]
  have herase := runConfig_erase hD answer 0
    (List.append leftRev.reverse right) padding
  have htape :
      splitTape [] (List.append leftRev.reverse right) padding =
        eraseTape 0 (List.append leftRev.reverse right) padding := by
    cases List.append leftRev.reverse right with
    | nil =>
        cases padding <;>
          rfl
    | cons bit rest =>
        simp [splitTape, eraseTape, tapeAtCells]
  rw [htape]
  simpa using herase

private theorem haltsFromTape_of_reaches_rewind
    {D : MachineDescription} (hD : D.SubroutineReady)
    {input : Tape Bool} (answer : Bool)
    (leftRev right : Word Bool) (padding : Nat)
    (hreach : exists prefixSteps : Nat,
      (Description D).runConfig prefixSteps
          { state := (Description D).start, tape := input } =
        { state := answerRewindState D answer
          tape := Tape.move Direction.left
            (splitTape leftRev right padding) }) :
    (Description D).HaltsFromTape input
      (answerTape answer
        (List.append leftRev.reverse right).length padding) := by
  rcases hreach with ⟨prefixSteps, hprefix⟩
  let tailSteps :=
    (leftRev.length + 1) +
      ((List.append leftRev.reverse right).length + 1)
  have hrun :
      (Description D).runConfig (prefixSteps + tailSteps)
          { state := (Description D).start, tape := input } =
        { state := answerHaltState D
          tape := answerTape answer
            (List.append leftRev.reverse right).length padding } := by
    rw [MachineDescription.runConfig_add, hprefix]
    exact runConfig_answer_tail hD answer leftRev right padding
  refine ⟨prefixSteps + tailSteps, ?_, ?_⟩
  · simpa [Description] using congrArg Configuration.state hrun
  · exact congrArg Configuration.tape hrun

/-- If the original recognizer halts on a contiguous encoded split, completion
erases that window and returns the accepting bit. -/
theorem haltsFromTape_accept
    {D : MachineDescription} (hD : D.SubroutineReady)
    {input : Tape Bool} (leftRev right : Word Bool) (padding : Nat)
    (hhalts : D.HaltsFromTape input
      (splitTape leftRev right padding)) :
    (Description D).HaltsFromTape input
      (answerTape true
        (List.append leftRev.reverse right).length padding) := by
  apply haltsFromTape_of_reaches_rewind hD true leftRev right padding
  rcases reaches_accept_of_haltsFromTape hD hhalts with
    ⟨steps, hreach⟩
  exact ⟨steps, by simpa [answerRewindState] using hreach⟩

/-- If completion reaches a bounded missing nonhalt key on a contiguous encoded
split, it erases that window and returns the rejecting bit. -/
theorem haltsFromTape_reject_of_missing
    {D : MachineDescription} (hD : D.SubroutineReady)
    {input : Tape Bool} {state : Nat}
    (leftRev right : Word Bool) (padding : Nat)
    (hbound : state < D.stateCount) (hstate : state ≠ D.halt)
    (hlookup : D.lookupTransition state
      (Tape.read (splitTape leftRev right padding)) = none)
    (hreach : exists prefixSteps : Nat,
      (Description D).runConfig prefixSteps
          { state := (Description D).start, tape := input } =
        { state := state
          tape := splitTape leftRev right padding }) :
    (Description D).HaltsFromTape input
      (answerTape false
        (List.append leftRev.reverse right).length padding) := by
  apply haltsFromTape_of_reaches_rewind hD false leftRev right padding
  rcases hreach with ⟨prefixSteps, hprefix⟩
  refine ⟨prefixSteps + 1, ?_⟩
  rw [MachineDescription.runConfig_add, hprefix]
  simpa [answerRewindState] using
    runConfig_one_reject hD hbound hstate
      (splitTape leftRev right padding) hlookup

/-- Exact stuck-run evidence on a contiguous encoded split enters the rejecting
answer tail. -/
theorem haltsFromTape_reject_of_stuck
    {D : MachineDescription} (hD : D.SubroutineReady)
    {input : Tape Bool} (leftRev right : Word Bool) (padding : Nat)
    (hstuck : D.StuckFromTape input
      (splitTape leftRev right padding)) :
    (Description D).HaltsFromTape input
      (answerTape false
        (List.append leftRev.reverse right).length padding) := by
  apply haltsFromTape_of_reaches_rewind hD false leftRev right padding
  rcases hstuck with ⟨steps, state, hrun, hstep, hstate⟩
  rcases reaches_reject_of_runConfig_stuck hD hD.1.2.1
      hrun hstep hstate with ⟨completedSteps, hcompleted⟩
  exact ⟨completedSteps, by
    simpa [Description, answerRewindState] using hcompleted⟩

/-- Normalized accepting-output contract for a successful recognizer run. -/
theorem haltsFromTapeWithOutput_accept
    {D : MachineDescription} (hD : D.SubroutineReady)
    {input : Tape Bool} (leftRev right : Word Bool) (padding : Nat)
    (hhalts : D.HaltsFromTape input
      (splitTape leftRev right padding)) :
    (Description D).HaltsFromTapeWithOutput input [true] := by
  have houtput :=
    MachineDescription.haltsFromTapeWithOutput_of_haltsFromTape
      (haltsFromTape_accept hD leftRev right padding hhalts)
  simpa [answerTape_normalizedOutput] using houtput

/-- Normalized rejecting-output contract for a reached missing key. -/
theorem haltsFromTapeWithOutput_reject_of_missing
    {D : MachineDescription} (hD : D.SubroutineReady)
    {input : Tape Bool} {state : Nat}
    (leftRev right : Word Bool) (padding : Nat)
    (hbound : state < D.stateCount) (hstate : state ≠ D.halt)
    (hlookup : D.lookupTransition state
      (Tape.read (splitTape leftRev right padding)) = none)
    (hreach : exists prefixSteps : Nat,
      (Description D).runConfig prefixSteps
          { state := (Description D).start, tape := input } =
        { state := state
          tape := splitTape leftRev right padding }) :
    (Description D).HaltsFromTapeWithOutput input [false] := by
  have houtput :=
    MachineDescription.haltsFromTapeWithOutput_of_haltsFromTape
      (haltsFromTape_reject_of_missing hD leftRev right padding
        hbound hstate hlookup hreach)
  simpa [answerTape_normalizedOutput] using houtput

/-- Normalized rejecting-output contract for exact stuck-run evidence. -/
theorem haltsFromTapeWithOutput_reject_of_stuck
    {D : MachineDescription} (hD : D.SubroutineReady)
    {input : Tape Bool} (leftRev right : Word Bool) (padding : Nat)
    (hstuck : D.StuckFromTape input
      (splitTape leftRev right padding)) :
    (Description D).HaltsFromTapeWithOutput input [false] := by
  have houtput :=
    MachineDescription.haltsFromTapeWithOutput_of_haltsFromTape
      (haltsFromTape_reject_of_stuck hD leftRev right padding hstuck)
  simpa [answerTape_normalizedOutput] using houtput

/-- The conventional reject and accept answers are distinct. -/
theorem answerBits_ne : (false : Bool) ≠ true := by decide

end ValidatorBooleanCloseout
end SelfHaltingRecognizer
end Computability
end FoC

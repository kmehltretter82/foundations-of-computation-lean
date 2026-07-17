import FoC.Computability.Compiler.Core.Language

set_option doc.verso true

/-!
# Section 5.2: Contract Guardrails

This page records counterexamples that constrain the book-facing computability
contracts. They are proof obligations for API repair, not examples of the
intended textbook definitions.

The legacy
{name (full := FoC.Computability.TuringDecidable)}`TuringDecidable` predicate permits its two answer symbols to
coincide. A well-formed constant-output description therefore witnesses that
predicate for every language. The witness below also disables transitions out
of its halt state, showing that halt stability alone does not repair the
contract: distinguishable answers are essential.
-/

namespace FoC
namespace Book
namespace Chapter05
namespace Section02

open Computability
open Languages

private abbrev LegacyCollapseDescription : MachineDescription :=
  MachineDescription.BoolOutputDescription false

private theorem legacyCollapseDescription_haltsWithFalse
    (w : Word Bool) :
    TuringMachine.HaltsWithOutput
      LegacyCollapseDescription.toTuringMachine w [false] := by
  exact (MachineDescription.toTuringMachine_haltsWithOutput_iff
    (MachineDescription.boolOutputDescription_wellFormed false) w [false]).2
    (MachineDescription.boolOutputDescription_haltsWithOutput false w)

/-- Every language satisfies the legacy predicate because its answers may coincide. -/
theorem every_language_turingDecidable_under_legacy_contract
    (L : Language input) :
    TuringDecidable L := by
  refine ⟨Bool, Fin (LegacyCollapseDescription.stateCount + 1),
    LegacyCollapseDescription.toTuringMachine, fun _ => false,
    false, false, ?_⟩
  intro w
  exact ⟨fun _ => legacyCollapseDescription_haltsWithFalse _,
    fun _ => legacyCollapseDescription_haltsWithFalse _⟩

/-- The collapse witness already has no outgoing transition from its halt state. -/
theorem legacy_collapse_witness_haltingTransitionsDisabled :
    TuringMachine.HaltingTransitionsDisabled
      LegacyCollapseDescription.toTuringMachine := by
  intro cell
  cases cell
  all_goals
    simp [LegacyCollapseDescription, MachineDescription.toTuringMachine,
      MachineDescription.BoolOutputDescription,
      MachineDescription.lookupTransition, MachineDescription.stateOfNat,
      MachineDescription.transition, MachineDescription.Matches]

/-!
The finite-description decision predicate already fixes the two output words
to the distinct Boolean singletons.  Its remaining compatibility defect is
instead temporal: reaching the designated halt state does not stop the
executable runner when the transition table contains a matching row there.
-/

/--
A concrete decider-shaped table that first halts with {lit}`true`, leaves its
halt state, rewrites that answer, and returns to the same halt with
{lit}`false`.
-/
def HaltReentryDeciderDescription : MachineDescription where
  stateCount := 3
  start := 0
  halt := 1
  transitions :=
    [ MachineDescription.transition 0 none (some true) Direction.right 1
    , MachineDescription.transition 0 (some false) none Direction.right 0
    , MachineDescription.transition 0 (some true) none Direction.right 0
    , MachineDescription.transition 1 none none Direction.left 2
    , MachineDescription.transition 2 (some true) (some false) Direction.right 1 ]

theorem haltReentryDeciderDescription_wellFormed :
    HaltReentryDeciderDescription.WellFormed := by
  refine ⟨by simp [HaltReentryDeciderDescription],
    by simp [HaltReentryDeciderDescription],
    by simp [HaltReentryDeciderDescription], ?_, ?_⟩
  · intro t ht
    simp [HaltReentryDeciderDescription, MachineDescription.transition,
      TransitionDescription.WellFormed] at ht ⊢
    rcases ht with rfl | rfl | rfl | rfl | rfl <;> simp
  · intro t u ht hu hkey
    simp [HaltReentryDeciderDescription, MachineDescription.transition] at ht hu
    rcases ht with rfl | rfl | rfl | rfl | rfl <;>
      rcases hu with rfl | rfl | rfl | rfl | rfl <;>
        simp [TransitionDescription.SameKey,
          TransitionDescription.SameAction] at hkey ⊢

private theorem haltReentryDeciderDescription_step_nonempty
    (erased : Nat) (b : Bool) (rest : Word Bool) :
    HaltReentryDeciderDescription.stepConfig
        { state := 0,
          tape := MachineDescription.eraseRightTape erased (b :: rest) } =
      some
        { state := 0,
          tape := MachineDescription.eraseRightTape (erased + 1) rest } := by
  cases b
  all_goals cases rest
  all_goals
    simp [HaltReentryDeciderDescription, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read,
      MachineDescription.eraseRightTape, Tape.write, Tape.move,
      Tape.moveRight, List.replicate_succ]

private theorem haltReentryDeciderDescription_run_scan
    (erased : Nat) (w : Word Bool) :
    HaltReentryDeciderDescription.runConfig w.length
        { state := 0,
          tape := MachineDescription.eraseRightTape erased w } =
      { state := 0,
        tape := MachineDescription.eraseRightTape (erased + w.length) [] } := by
  induction w generalizing erased with
  | nil => rfl
  | cons b rest ih =>
      simp [MachineDescription.runConfig,
        haltReentryDeciderDescription_step_nonempty, ih]
      congr 1 <;> lia

private theorem haltReentryDeciderDescription_step_empty
    (erased : Nat) :
    HaltReentryDeciderDescription.stepConfig
        { state := 0,
          tape := MachineDescription.eraseRightTape erased [] } =
      some
        { state := 1,
          tape := MachineDescription.boolOutputTape erased true } := by
  simp [HaltReentryDeciderDescription, MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition, Tape.read,
    MachineDescription.eraseRightTape, MachineDescription.boolOutputTape,
    Tape.write, Tape.move, Tape.moveRight]

private theorem haltReentryDeciderDescription_run_first_halt
    (w : Word Bool) :
    HaltReentryDeciderDescription.runConfig (w.length + 1)
        (HaltReentryDeciderDescription.initial w) =
      { state := 1,
        tape := MachineDescription.boolOutputTape w.length true } := by
  rw [MachineDescription.runConfig_add]
  have hscan :
      HaltReentryDeciderDescription.runConfig w.length
          (HaltReentryDeciderDescription.initial w) =
        { state := 0,
          tape := MachineDescription.eraseRightTape w.length [] } := by
    simpa [MachineDescription.initial, HaltReentryDeciderDescription,
      MachineDescription.eraseRightTape_zero_eq_input,
      Nat.zero_add] using haltReentryDeciderDescription_run_scan 0 w
  rw [hscan]
  simp [MachineDescription.runConfig,
    haltReentryDeciderDescription_step_empty]

theorem haltReentryDeciderDescription_haltsWithTrue
    (w : Word Bool) :
    HaltReentryDeciderDescription.HaltsWithOutput w [true] := by
  exists w.length + 1
  constructor
  · rw [haltReentryDeciderDescription_run_first_halt]
    rfl
  · rw [haltReentryDeciderDescription_run_first_halt]
    exact MachineDescription.boolOutputTape_normalizedOutput w.length true

/-- The witness has an enabled transition whose source is the designated halt. -/
theorem haltReentryDeciderDescription_not_haltTransitionFree :
    ¬ HaltReentryDeciderDescription.HaltTransitionFree := by
  simp [MachineDescription.HaltTransitionFree,
    HaltReentryDeciderDescription, MachineDescription.transition]

/-- The enabled halt row moves the actual first-answer configuration to state 2. -/
theorem haltReentryDeciderDescription_run_leaves_halt
    (erased : Nat) :
    (HaltReentryDeciderDescription.runConfig 1
        { state := HaltReentryDeciderDescription.halt,
          tape := MachineDescription.boolOutputTape erased true }).state = 2 := by
  simp [MachineDescription.runConfig, HaltReentryDeciderDescription,
    MachineDescription.stepConfig, MachineDescription.lookupTransition,
    MachineDescription.Matches, MachineDescription.transition,
    MachineDescription.boolOutputTape, Tape.read, Tape.write, Tape.move,
    Tape.moveLeft]

/-- Two more steps replace the first answer and return to the designated halt. -/
theorem haltReentryDeciderDescription_run_reenters_halt
    (erased : Nat) :
    HaltReentryDeciderDescription.runConfig 2
        { state := HaltReentryDeciderDescription.halt,
          tape := MachineDescription.boolOutputTape erased true } =
      { state := HaltReentryDeciderDescription.halt,
        tape := MachineDescription.boolOutputTape erased false } := by
  simp [MachineDescription.runConfig, HaltReentryDeciderDescription,
    MachineDescription.stepConfig, MachineDescription.lookupTransition,
    MachineDescription.Matches, MachineDescription.transition,
    MachineDescription.boolOutputTape, Tape.read, Tape.write, Tape.move,
    Tape.moveLeft, Tape.moveRight]

private theorem haltReentryDeciderDescription_run_second_halt
    (w : Word Bool) :
    HaltReentryDeciderDescription.runConfig (w.length + 3)
        (HaltReentryDeciderDescription.initial w) =
      { state := HaltReentryDeciderDescription.halt,
        tape := MachineDescription.boolOutputTape w.length false } := by
  rw [show w.length + 3 = (w.length + 1) + 2 by lia,
    MachineDescription.runConfig_add,
    haltReentryDeciderDescription_run_first_halt]
  exact haltReentryDeciderDescription_run_reenters_halt w.length

theorem haltReentryDeciderDescription_haltsWithFalse
    (w : Word Bool) :
    HaltReentryDeciderDescription.HaltsWithOutput w [false] := by
  exists w.length + 3
  constructor
  · rw [haltReentryDeciderDescription_run_second_halt]
  · rw [haltReentryDeciderDescription_run_second_halt]
    exact MachineDescription.boolOutputTape_normalizedOutput w.length false

/--
Without {name}`MachineDescription.HaltTransitionFree`, the finite-description
decision contract collapses even though {lit}`false` and {lit}`true` are
distinct: its two existential output observations may select different visits
to the designated halt state.
-/
theorem every_language_machineDescriptionDecidesLanguage_under_halt_reentry
    (L : Language Bool) :
    MachineDescriptionDecidesLanguage HaltReentryDeciderDescription L := by
  constructor
  · exact haltReentryDeciderDescription_wellFormed
  · intro w
    exact
      ⟨fun _ => haltReentryDeciderDescription_haltsWithTrue w,
        fun _ => haltReentryDeciderDescription_haltsWithFalse w⟩

end Section02
end Chapter05
end Book
end FoC

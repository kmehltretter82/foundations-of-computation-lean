import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorTransitionScanner

set_option doc.verso true

/-!
# Exact-code validator: suffix-emptiness gate

This module closes leaf 4 of the exact-code validator roadmap. The transition
scanner leaves the first suffix bit under the head, or a blank when its decoded
suffix is empty. The finite gate tests that cell, then bounces left and right so
the successful handoff tape is preserved exactly.

The head-cell test is also the collision audit: an empty suffix and a nonempty
suffix have different current cells, so equivalent sources never demand both a
successful and a rejecting outcome.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer

open Languages
open MachineDescription

open FoC.Computability.DovetailInitialLayoutInitializer

/-- Every transition-scanner handoff is one contiguous encoded window. -/
theorem validatorTransitionScannerHandoffTape_contiguous
    (stateCount start halt transitionCount : Nat)
    (transitions : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    ContiguousTape
      (validatorTransitionScannerHandoffTape
        stateCount start halt transitionCount transitions suffix) := by
  refine ⟨(encodeCodeWordAsInput
      (validatorTransitionScannerPrefix
        stateCount start halt transitionCount transitions)).reverse,
    encodeCodeWordAsInput suffix, 0, ?_⟩
  unfold validatorTransitionScannerHandoffTape
  cases encodeCodeWordAsInput suffix <;>
    simp [splitTape, tapeAtCells]

/-- Every transition-scanner handoff has a nonempty left context, so the
same-head sequencing bounce cancels exactly. -/
theorem validatorTransitionScannerHandoffTape_move_right_left
    (stateCount start halt transitionCount : Nat)
    (transitions : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (validatorTransitionScannerHandoffTape
            stateCount start halt transitionCount transitions suffix)) =
      validatorTransitionScannerHandoffTape
        stateCount start halt transitionCount transitions suffix := by
  unfold validatorTransitionScannerHandoffTape
  exact
    CommonGround.FiniteTransducers.tapeAtCells_move_right_move_left_append_singleton
      (((encodeCodeWordAsInput
        (validatorTransitionScannerPrefix
          stateCount start halt transitionCount transitions)).reverse).map
            some)
      none
      (List.append ((encodeCodeWordAsInput suffix).map some) [none])

/-!
## Detectable boundary
-/

/-- At the transition-scanner handoff, a blank head is exactly an empty suffix. -/
theorem validatorTransitionScannerHandoffTape_read_eq_none_iff
    (stateCount start halt transitionCount : Nat)
    (transitions : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    Iff
      (Tape.read
        (validatorTransitionScannerHandoffTape
          stateCount start halt transitionCount transitions suffix) = none)
      (suffix = []) := by
  cases suffix
  · simp [validatorTransitionScannerHandoffTape, tapeAtCells, Tape.read,
      encodeCodeWordAsInput]
  · rename_i symbol rest
    cases symbol
    all_goals
      simp [validatorTransitionScannerHandoffTape, tapeAtCells, Tape.read,
        encodeCodeWordAsInput, encodeCodeSymbolAsInput]

/-- Empty and nonempty suffix handoffs are physically distinct at the head. -/
theorem validatorTransitionScannerHandoffTape_nil_ne_cons
    (stateCount start halt transitionCount : Nat)
    (transitions : List TransitionDescription)
    (symbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    Not
      (validatorTransitionScannerHandoffTape
          stateCount start halt transitionCount transitions [] =
        validatorTransitionScannerHandoffTape
          stateCount start halt transitionCount transitions
            (symbol :: rest)) := by
  intro heq
  have hread := congrArg Tape.read heq
  have hnil :
      Tape.read
          (validatorTransitionScannerHandoffTape
            stateCount start halt transitionCount transitions []) = none :=
    (validatorTransitionScannerHandoffTape_read_eq_none_iff
      stateCount start halt transitionCount transitions []).2 rfl
  have hcons :
      Not
        (Tape.read
            (validatorTransitionScannerHandoffTape
              stateCount start halt transitionCount transitions
                (symbol :: rest)) = none) := by
    intro hnone
    have hempty :=
      (validatorTransitionScannerHandoffTape_read_eq_none_iff
        stateCount start halt transitionCount transitions
          (symbol :: rest)).1 hnone
    simp at hempty
  exact hcons (hread.symm.trans hnil)

/-!
## Concrete machine

State 0 admits only a blank current cell. State 1 accepts every left neighbor
and returns right, so on the nonempty left context supplied by leaf 3 the final
tape is definitionally the original handoff.
-/

/-- Three-state same-head gate for an empty decoded suffix. -/
def ExactCodeValidatorSuffixGateDescription : MachineDescription where
  stateCount := 3
  start := 0
  halt := 2
  transitions :=
    [ transition 0 none none Direction.left 1
    , transition 1 none none Direction.right 2
    , transition 1 (some false) (some false) Direction.right 2
    , transition 1 (some true) (some true) Direction.right 2
    ]

private abbrev VSG := ExactCodeValidatorSuffixGateDescription

/-- The suffix gate's finite table satisfies all description invariants. -/
theorem exactCodeValidatorSuffixGateDescription_wellFormed :
    VSG.WellFormed := by
  constructor
  · decide
  · constructor
    · decide
    · constructor
      · decide
      · constructor
        · exact transition_wellFormed_of_all
            (l := VSG.transitions) (stateCount := VSG.stateCount) (by decide)
        · exact transition_deterministic_of_all
            (l := VSG.transitions) (by decide)

/-- The suffix gate has no outgoing transition from its halt state. -/
theorem exactCodeValidatorSuffixGateDescription_haltTransitionFree :
    VSG.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := VSG.transitions) (state := VSG.halt) (by decide)

/-- The suffix gate is well formed and halt-stable. -/
theorem exactCodeValidatorSuffixGateDescription_subroutineReady :
    VSG.SubroutineReady :=
  And.intro
    exactCodeValidatorSuffixGateDescription_wellFormed
    exactCodeValidatorSuffixGateDescription_haltTransitionFree

private theorem suffixGate_runConfig_blank_bounce
    (T : Tape Bool)
    (hread : Tape.read T = none)
    (hleft : Not (T.left = [])) :
    VSG.runConfig 2 { state := VSG.start, tape := T } =
      { state := VSG.halt, tape := T } := by
  cases T
  rename_i left head right
  cases head
  · cases left
    · simp at hleft
    · rename_i cell rest
      cases cell
      · simp [VSG, ExactCodeValidatorSuffixGateDescription,
          runConfig, stepConfig, lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, Tape.moveRight]
      · rename_i bit
        cases bit
        all_goals
          simp [VSG, ExactCodeValidatorSuffixGateDescription,
            runConfig, stepConfig, lookupTransition, Matches,
            transition, Tape.read, Tape.write, Tape.move,
            Tape.moveLeft, Tape.moveRight]
  · simp [Tape.read] at hread

/-- An empty suffix takes exactly two steps and preserves the handoff tape. -/
theorem exactCodeValidatorSuffixGateDescription_haltsFromTape_nil
    (stateCount start halt transitionCount : Nat)
    (transitions : List TransitionDescription) :
    VSG.HaltsFromTape
      (validatorTransitionScannerHandoffTape
        stateCount start halt transitionCount transitions [])
      (validatorTransitionScannerHandoffTape
        stateCount start halt transitionCount transitions []) := by
  let T := validatorTransitionScannerHandoffTape
    stateCount start halt transitionCount transitions []
  have hread : Tape.read T = none := by
    exact
      (validatorTransitionScannerHandoffTape_read_eq_none_iff
        stateCount start halt transitionCount transitions []).2 rfl
  have hleft : Not (T.left = []) := by
    simp [T, validatorTransitionScannerHandoffTape, tapeAtCells,
      encodeCodeWordAsInput]
  have hrun := suffixGate_runConfig_blank_bounce T hread hleft
  apply Exists.intro 2
  change
    And
      ((VSG.runConfig 2 { state := VSG.start, tape := T }).state = VSG.halt)
      ((VSG.runConfig 2 { state := VSG.start, tape := T }).tape = T)
  rw [hrun]
  constructor
  · rfl
  · rfl

/-- Any halt of the gate certifies that its initial current cell was blank. -/
theorem exactCodeValidatorSuffixGateDescription_read_eq_none_of_haltsFromTape
    {input output : Tape Bool}
    (hhalts : VSG.HaltsFromTape input output) :
    Tape.read input = none := by
  cases hread : Tape.read input
  · rfl
  · rename_i bit
    have hstep :
        VSG.stepConfig { state := VSG.start, tape := input } = none := by
      cases bit
      all_goals
        simp [VSG, ExactCodeValidatorSuffixGateDescription,
          stepConfig, lookupTransition, Matches, transition, hread]
    have hex := MachineDescription.runConfig_eq_halt_of_haltsFromTape hhalts
    cases hex
    rename_i n hrun
    rw [MachineDescription.runConfig_of_stepConfig_none hstep n] at hrun
    have hstate := congrArg MachineDescription.Configuration.state hrun
    simp [VSG, ExactCodeValidatorSuffixGateDescription] at hstate

/-- Exact closed characterization on every transition-scanner suffix handoff. -/
theorem exactCodeValidatorSuffixGateDescription_haltsFromTape_iff
    (stateCount start halt transitionCount : Nat)
    (transitions : List TransitionDescription)
    (suffix : Word MachineCodeSymbol)
    (output : Tape Bool) :
    Iff
      (VSG.HaltsFromTape
        (validatorTransitionScannerHandoffTape
          stateCount start halt transitionCount transitions suffix)
        output)
      (And
        (suffix = [])
        (output = validatorTransitionScannerHandoffTape
          stateCount start halt transitionCount transitions [])) := by
  constructor
  · intro hhalts
    have hsuffix : suffix = [] :=
      (validatorTransitionScannerHandoffTape_read_eq_none_iff
        stateCount start halt transitionCount transitions suffix).1
        (exactCodeValidatorSuffixGateDescription_read_eq_none_of_haltsFromTape
          hhalts)
    apply And.intro hsuffix
    subst suffix
    have hcanonical :=
      exactCodeValidatorSuffixGateDescription_haltsFromTape_nil
        stateCount start halt transitionCount transitions
    exact MachineDescription.haltsFromTape_functional_of_haltTransitionFree
      exactCodeValidatorSuffixGateDescription_haltTransitionFree
      hhalts hcanonical
  · intro haccept
    have hsuffix := haccept.left
    have houtput := haccept.right
    subst suffix
    subst output
    exact exactCodeValidatorSuffixGateDescription_haltsFromTape_nil
      stateCount start halt transitionCount transitions

/-- A nonempty decoded suffix is rejected at the gate's missing start-state
bit transition. -/
theorem exactCodeValidatorSuffixGateDescription_stuckFromTape_cons
    (stateCount start halt transitionCount : Nat)
    (transitions : List TransitionDescription)
    (symbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    VSG.StuckFromTape
      (validatorTransitionScannerHandoffTape
        stateCount start halt transitionCount transitions (symbol :: rest))
      (validatorTransitionScannerHandoffTape
        stateCount start halt transitionCount transitions (symbol :: rest)) := by
  let input := validatorTransitionScannerHandoffTape
    stateCount start halt transitionCount transitions (symbol :: rest)
  have hreadNe : Tape.read input ≠ none := by
    intro hread
    have hempty :=
      (validatorTransitionScannerHandoffTape_read_eq_none_iff
        stateCount start halt transitionCount transitions
          (symbol :: rest)).1 hread
    simp at hempty
  refine ⟨0, VSG.start, rfl, ?_, by decide⟩
  cases hread : Tape.read input with
  | none => exact False.elim (hreadNe hread)
  | some bit =>
      change VSG.stepConfig { state := VSG.start, tape := input } = none
      simp only [MachineDescription.stepConfig, hread]
      cases bit <;>
        simp [VSG, ExactCodeValidatorSuffixGateDescription,
          MachineDescription.lookupTransition,
          MachineDescription.Matches, MachineDescription.transition]

/-- Every canonical transition-scanner handoff either succeeds exactly or
reaches a contiguous concrete missing suffix-gate row. -/
theorem exactCodeValidatorSuffixGateDescription_haltsOrContiguousStuckFromTape
    (stateCount start halt transitionCount : Nat)
    (transitions : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    (exists output : Tape Bool,
      VSG.HaltsFromTape
        (validatorTransitionScannerHandoffTape
          stateCount start halt transitionCount transitions suffix) output) ∨
    (exists stuck : Tape Bool,
      VSG.StuckFromTape
          (validatorTransitionScannerHandoffTape
            stateCount start halt transitionCount transitions suffix) stuck ∧
        ContiguousTape stuck) := by
  cases suffix with
  | nil =>
      exact Or.inl ⟨_,
        exactCodeValidatorSuffixGateDescription_haltsFromTape_nil
          stateCount start halt transitionCount transitions⟩
  | cons symbol rest =>
      exact Or.inr ⟨_,
        exactCodeValidatorSuffixGateDescription_stuckFromTape_cons
          stateCount start halt transitionCount transitions symbol rest,
        validatorTransitionScannerHandoffTape_contiguous
          stateCount start halt transitionCount transitions (symbol :: rest)⟩

/-- Every canonical transition-scanner handoff either succeeds exactly or
reaches a concrete missing suffix-gate row. -/
theorem exactCodeValidatorSuffixGateDescription_haltsOrStuckFromTape
    (stateCount start halt transitionCount : Nat)
    (transitions : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    (exists output : Tape Bool,
      VSG.HaltsFromTape
        (validatorTransitionScannerHandoffTape
          stateCount start halt transitionCount transitions suffix) output) ∨
    (exists stuck : Tape Bool,
      VSG.StuckFromTape
        (validatorTransitionScannerHandoffTape
          stateCount start halt transitionCount transitions suffix) stuck) := by
  rcases exactCodeValidatorSuffixGateDescription_haltsOrContiguousStuckFromTape
      stateCount start halt transitionCount transitions suffix with
    hhalts | hstuck
  · exact Or.inl hhalts
  · rcases hstuck with ⟨stuck, hstuck, _hcontiguous⟩
    exact Or.inr ⟨stuck, hstuck⟩

end SelfHaltingRecognizer
end Computability
end FoC

import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.FixedStep

set_option doc.verso true

/-!
# Fixed-description state classification

The terminal run-config emitter parses an arbitrary encoded configuration
state, but its fixed-step kernel can put only finitely many values in control.
This module isolates the exact classification boundary.  States mentioned by
the fixed description become witnessed finite-control values; every remaining
natural number takes one generic {lit}`other` branch and keeps its raw unary
encoding available on tape.

This is deliberately a parser-facing semantic seam rather than a claim that
an arbitrary natural number fits in finite control.  The finite enumeration
below can be embedded in a typed parser table, while the residual-code API
specifies what that parser must leave behind for the generic branch.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace RunConfigEmitterCore

/-- Finite-control result of classifying a parsed configuration state.

The proof carried by {lit}`known` is the currency required by the fixed-step
table.  The {lit}`other` constructor intentionally carries no natural number:
an unmatched value remains represented by its encoding on tape. -/
inductive StateClass (D : MachineDescription) where
  | known (state : Nat) (member : state ∈ fixedStepValues D)
  | other
deriving DecidableEq

/-- Executably classify an arbitrary parsed state against the fixed list. -/
def classifyState (D : MachineDescription) (state : Nat) : StateClass D :=
  if hstate : state ∈ fixedStepValues D then
    .known state hstate
  else
    .other

/-- All finite-control classification results.  Duplicate description values
are harmless because typed tables use first-occurrence state identifiers. -/
def stateClasses (D : MachineDescription) : List (StateClass D) :=
  List.append
    ((fixedStepValues D).attach.map fun state =>
      StateClass.known state.val state.property)
    [.other]

theorem known_mem_stateClasses
    {D : MachineDescription} {state : Nat}
    (hstate : state ∈ fixedStepValues D) :
    StateClass.known state hstate ∈ stateClasses D := by
  simp [stateClasses]
  exact hstate

theorem other_mem_stateClasses (D : MachineDescription) :
    (StateClass.other : StateClass D) ∈ stateClasses D := by
  simp [stateClasses]

/-- The list is a complete finite enumeration of parser control outcomes. -/
theorem mem_stateClasses (D : MachineDescription) (tag : StateClass D) :
    tag ∈ stateClasses D := by
  cases tag with
  | known state hstate =>
      exact known_mem_stateClasses hstate
  | other =>
      exact other_mem_stateClasses D

@[simp] theorem classifyState_of_mem
    {D : MachineDescription} {state : Nat}
    (hstate : state ∈ fixedStepValues D) :
    classifyState D state = StateClass.known state hstate := by
  simp [classifyState, hstate]

@[simp] theorem classifyState_of_not_mem
    {D : MachineDescription} {state : Nat}
    (hstate : state ∉ fixedStepValues D) :
    classifyState D state = StateClass.other := by
  simp [classifyState, hstate]

@[simp] theorem classifyState_eq_other_iff
    (D : MachineDescription) (state : Nat) :
    classifyState D state = StateClass.other ↔
      state ∉ fixedStepValues D := by
  by_cases hstate : state ∈ fixedStepValues D
  · simp [hstate]
  · simp [hstate]

/-- A known classification exposes exactly the membership witness required by
the fixed-step dispatcher. -/
theorem exists_classifyState_eq_known_iff
    (D : MachineDescription) (state : Nat) :
    (exists hstate : state ∈ fixedStepValues D,
      classifyState D state = StateClass.known state hstate) ↔
      state ∈ fixedStepValues D := by
  constructor
  · rintro ⟨hstate, _⟩
    exact hstate
  · intro hstate
    exact ⟨hstate, classifyState_of_mem hstate⟩

@[simp] theorem classifyState_eq_known_iff
    {D : MachineDescription} {state known : Nat}
    (hknown : known ∈ fixedStepValues D) :
    classifyState D state = StateClass.known known hknown ↔
      state = known := by
  constructor
  · intro hclass
    unfold classifyState at hclass
    split at hclass
    · injection hclass
    · contradiction
  · intro hstate
    subst hstate
    exact classifyState_of_mem hknown

theorem classifyState_mem_stateClasses
    (D : MachineDescription) (state : Nat) :
    classifyState D state ∈ stateClasses D := by
  exact mem_stateClasses D (classifyState D state)

/-!
## Residual state encoding
-/

/-- State-field code left for the next phase.  A known state has been absorbed
into finite control, whereas the generic branch retains the complete unary
encoding of its arbitrary raw value. -/
def StateClass.residualStateCode
    {D : MachineDescription} (tag : StateClass D)
    (rawState : Nat) (suffix : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  match tag with
  | .known _ _ => suffix
  | .other => encodeNatAppend rawState suffix

@[simp] theorem StateClass.residualStateCode_known
    {D : MachineDescription} {state : Nat}
    (hstate : state ∈ fixedStepValues D)
    (rawState : Nat) (suffix : Word MachineCodeSymbol) :
    (StateClass.known state hstate).residualStateCode rawState suffix =
      suffix := by
  rfl

@[simp] theorem StateClass.residualStateCode_other
    {D : MachineDescription} (rawState : Nat)
    (suffix : Word MachineCodeSymbol) :
    (StateClass.other : StateClass D).residualStateCode rawState suffix =
      encodeNatAppend rawState suffix := by
  rfl

theorem residualStateCode_classify_of_mem
    {D : MachineDescription} {state : Nat}
    (hstate : state ∈ fixedStepValues D)
    (suffix : Word MachineCodeSymbol) :
    (classifyState D state).residualStateCode state suffix = suffix := by
  rw [classifyState_of_mem hstate]
  rfl

/-- The generic parser branch preserves the raw state field byte-for-byte. -/
theorem residualStateCode_classify_of_not_mem
    {D : MachineDescription} {state : Nat}
    (hstate : state ∉ fixedStepValues D)
    (suffix : Word MachineCodeSymbol) :
    (classifyState D state).residualStateCode state suffix =
      encodeNatAppend state suffix := by
  rw [classifyState_of_not_mem hstate]
  rfl

/-- Configuration-specialized form: the unmatched branch leaves the complete
state-and-tape encoding unchanged. -/
theorem residualStateCode_classify_of_not_mem_eq_encodeConfigurationAppend
    {D : MachineDescription} {state : Nat}
    (hstate : state ∉ fixedStepValues D)
    (T : Tape Bool) (suffix : Word MachineCodeSymbol) :
    (classifyState D state).residualStateCode state
        (encodeTapeAppend T suffix) =
      encodeConfigurationAppend { state := state, tape := T } suffix := by
  rw [residualStateCode_classify_of_not_mem hstate]
  rfl

/-!
## Semantic dispatch
-/

/-- If the parser selected {lit}`other`, the fixed description stutters for
every remaining unary-stage iteration. -/
theorem runConfig_eq_self_of_classifyState_other
    {D : MachineDescription} {state : Nat}
    (hclass : classifyState D state = StateClass.other)
    (T : Tape Bool) (fuel : Nat) :
    D.runConfig fuel { state := state, tape := T } =
      { state := state, tape := T } := by
  apply runConfig_eq_self_of_not_mem_fixedStepValues
  exact (classifyState_eq_other_iff D state).mp hclass

/-- Total semantic case split exposed to the field parser.  The known
branch recovers the exact parsed state; the unmatched branch has the complete
stuttering behavior needed to skip the remaining counter. -/
theorem classifyState_semantics
    (D : MachineDescription) (state : Nat)
    (T : Tape Bool) (fuel : Nat) :
    match classifyState D state with
    | .known known _ => known = state
    | .other =>
        D.runConfig fuel { state := state, tape := T } =
          { state := state, tape := T } := by
  by_cases hstate : state ∈ fixedStepValues D
  · rw [classifyState_of_mem hstate]
  · rw [classifyState_of_not_mem hstate]
    exact runConfig_eq_self_of_not_mem_fixedStepValues hstate T fuel

end RunConfigEmitterCore
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC

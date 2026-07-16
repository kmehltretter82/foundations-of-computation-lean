import FoC.Computability.Compiler.Structured.Lowering.TypedStateTable
import FoC.Computability.Compiler.Structured.Lowering.ConcreteRefresh

set_option doc.verso true

/-!
# Fixed-description one-step execution core

The terminal run-config emitter must execute a description baked into finite
control while the simulated configuration remains on logical tapes.  This
module isolates the executable one-step transition kernel. Its state and tape
functions perform exactly the write, move, and target update selected by the
fixed description's transition lookup, or stutter when lookup fails.

The integrated known-state loop consumes these functions directly and carries
the dispatch result through its typed {lit}`done` state into the combined
dispatcher.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace RunConfigEmitterCore

open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape

/-- Translate an ordinary description head move to the structured action
currency. -/
def headMoveOfDirection : Direction -> HeadMove
  | .left => .left
  | .right => .right

/-- Execute the write and movement prescribed by one baked-in transition. -/
def transitionTapeAction (t : TransitionDescription) : TapeAction :=
  TapeAction.writeMove t.write (headMoveOfDirection t.move)

@[simp] theorem transitionTapeAction_apply
    (t : TransitionDescription) (T : Tape Bool) :
    (transitionTapeAction t).apply T =
      Tape.move t.move (Tape.write t.write T) := by
  rcases t with ⟨source, read, write, move, target⟩
  cases move <;> rfl

/-- State selected by one ordinary lookup, with failed lookup stuttering. -/
def fixedStepTargetState
    (D : MachineDescription) (state : Nat) (read : Option Bool) : Nat :=
  match D.lookupTransition state read with
  | none => state
  | some t => t.target

/-- Tape action selected by one ordinary lookup, with failed lookup preserving
the logical tape exactly. -/
def fixedStepTapeAction
    (D : MachineDescription) (state : Nat) (read : Option Bool) : TapeAction :=
  match D.lookupTransition state read with
  | none => keepS
  | some t => transitionTapeAction t

/-- Sources and targets mentioned by the fixed transition block, together
with its public start and halt states. -/
def fixedStepValues (D : MachineDescription) : List Nat :=
  D.start :: D.halt ::
    List.append (D.transitions.map TransitionDescription.source)
      (D.transitions.map TransitionDescription.target)

theorem start_mem_fixedStepValues (D : MachineDescription) :
    D.start ∈ fixedStepValues D := by
  simp [fixedStepValues]

theorem halt_mem_fixedStepValues (D : MachineDescription) :
    D.halt ∈ fixedStepValues D := by
  simp [fixedStepValues]

theorem source_mem_fixedStepValues
    {D : MachineDescription} {t : TransitionDescription}
    (ht : t ∈ D.transitions) :
    t.source ∈ fixedStepValues D := by
  unfold fixedStepValues
  simp only [List.mem_cons]
  exact
    Or.inr
      (Or.inr
        (List.mem_append.mpr
          (Or.inl (List.mem_map.mpr ⟨t, ht, rfl⟩))))

theorem target_mem_fixedStepValues
    {D : MachineDescription} {t : TransitionDescription}
    (ht : t ∈ D.transitions) :
    t.target ∈ fixedStepValues D := by
  unfold fixedStepValues
  simp only [List.mem_cons]
  exact
    Or.inr
      (Or.inr
        (List.mem_append.mpr
          (Or.inr (List.mem_map.mpr ⟨t, ht, rfl⟩))))

theorem fixedStepTargetState_mem
    {D : MachineDescription} {state : Nat}
    (hstate : state ∈ fixedStepValues D)
    (read : Option Bool) :
    fixedStepTargetState D state read ∈ fixedStepValues D := by
  cases hlookup : D.lookupTransition state read with
  | none =>
      simpa [fixedStepTargetState, hlookup] using hstate
  | some t =>
      have ht : t ∈ D.transitions :=
        MachineDescription.lookupTransition_mem hlookup
      simpa [fixedStepTargetState, hlookup] using
        (target_mem_fixedStepValues ht)

/-- A raw state not represented by the fixed transition block has no matching
transition.  The field parser can route precisely this case to one generic
{lit}`other` branch without assuming that arbitrary encoded states are bounded
by {name}`MachineDescription.stateCount`. -/
theorem lookupTransition_eq_none_of_not_mem_fixedStepValues
    {D : MachineDescription} {state : Nat}
    (hstate : state ∉ fixedStepValues D)
    (read : Option Bool) :
    D.lookupTransition state read = none := by
  cases hlookup : D.lookupTransition state read with
  | none => rfl
  | some t =>
      exfalso
      have ht : t ∈ D.transitions :=
        MachineDescription.lookupTransition_mem hlookup
      have hsource : t.source = state :=
        (MachineDescription.lookupTransition_matches hlookup).left
      apply hstate
      rw [← hsource]
      exact source_mem_fixedStepValues ht

/-- The generic unmatched-state branch may preserve the encoded configuration
for every remaining unary-stage iteration. -/
theorem runConfig_eq_self_of_not_mem_fixedStepValues
    {D : MachineDescription} {state : Nat}
    (hstate : state ∉ fixedStepValues D)
    (T : Tape Bool) (fuel : Nat) :
    D.runConfig fuel { state := state, tape := T } =
      { state := state, tape := T } := by
  apply MachineDescription.runConfig_of_stepConfig_none
  simp [MachineDescription.stepConfig,
    lookupTransition_eq_none_of_not_mem_fixedStepValues
      hstate (Tape.read T)]

/-!
## Exact one-step semantics
-/

/-- The typed target state and tape action are exactly one ordinary
{name}`MachineDescription.runConfig` iteration. -/
theorem fixedStep_selected_eq_runConfig_one
    (D : MachineDescription) (state : Nat) (T : Tape Bool) :
    ({ state := fixedStepTargetState D state (Tape.read T)
       tape := (fixedStepTapeAction D state (Tape.read T)).apply T } :
        MachineDescription.Configuration) =
      D.runConfig 1 { state := state, tape := T } := by
  cases hlookup : D.lookupTransition state (Tape.read T) with
  | none =>
      rw [runConfig_one_of_lookupTransition_none hlookup]
      simp [fixedStepTargetState, fixedStepTapeAction, hlookup,
        keepS, TapeAction.stay, TapeAction.apply, HeadMove.apply]
  | some t =>
      rw [runConfig_one_of_lookupTransition_some hlookup]
      simp [fixedStepTargetState, fixedStepTapeAction, hlookup]

theorem fixedStepTargetState_eq_runConfig_one_state
    (D : MachineDescription) (state : Nat) (T : Tape Bool) :
    fixedStepTargetState D state (Tape.read T) =
      (D.runConfig 1 { state := state, tape := T }).state := by
  exact congrArg MachineDescription.Configuration.state
    (fixedStep_selected_eq_runConfig_one D state T)

theorem fixedStepTapeAction_apply_eq_runConfig_one_tape
    (D : MachineDescription) (state : Nat) (T : Tape Bool) :
    (fixedStepTapeAction D state (Tape.read T)).apply T =
      (D.runConfig 1 { state := state, tape := T }).tape := by
  exact congrArg MachineDescription.Configuration.tape
    (fixedStep_selected_eq_runConfig_one D state T)

end RunConfigEmitterCore
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC

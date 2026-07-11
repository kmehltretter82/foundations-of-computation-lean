import FoC.Computability.Compiler.Structured.Lowering.TypedStateTable
import FoC.Computability.Compiler.Structured.Lowering.ConcreteRefresh

set_option doc.verso true

/-!
# Fixed-description one-step execution core

The terminal run-config emitter must execute a description baked into finite
control while the simulated configuration remains on logical tapes.  This
module isolates the executable one-step microkernel.  A dispatch state carries
one of the finitely relevant description states; one structured step performs
exactly the write, move, and target update selected by the fixed description's
transition lookup, or stutters when lookup fails.

The resulting {lit}`done` state deliberately retains the next
simulated state in typed control.  A surrounding unary-stage loop can therefore
reuse the transition function before eventually re-encoding the final
configuration.
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

/-- Typed control of the fixed-step microkernel. -/
inductive FixedStepState where
  | dispatch (state : Nat)
  | done (state : Nat)
  | halt
deriving DecidableEq, Repr

/-- Sources and targets mentioned by the fixed transition block, together
with its public start and halt states. -/
def fixedStepValues (D : MachineDescription) : List Nat :=
  D.start :: D.halt ::
    List.append (D.transitions.map TransitionDescription.source)
      (D.transitions.map TransitionDescription.target)

/-- Finite typed-state enumeration used by the generated table. -/
def fixedStepStates (D : MachineDescription) : List FixedStepState :=
  List.append
    (fixedStepValues D |>.map FixedStepState.dispatch)
    (List.append
      (fixedStepValues D |>.map FixedStepState.done)
      [FixedStepState.halt])

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

theorem dispatch_mem_fixedStepStates
    {D : MachineDescription} {state : Nat}
    (hstate : state ∈ fixedStepValues D) :
    FixedStepState.dispatch state ∈ fixedStepStates D := by
  apply List.mem_append.mpr
  exact Or.inl (List.mem_map.mpr ⟨state, hstate, rfl⟩)

theorem done_mem_fixedStepStates
    {D : MachineDescription} {state : Nat}
    (hstate : state ∈ fixedStepValues D) :
    FixedStepState.done state ∈ fixedStepStates D := by
  apply List.mem_append.mpr
  apply Or.inr
  apply List.mem_append.mpr
  exact Or.inl (List.mem_map.mpr ⟨state, hstate, rfl⟩)

theorem halt_mem_fixedStepStates (D : MachineDescription) :
    FixedStepState.halt ∈ fixedStepStates D := by
  simp [fixedStepStates]

theorem fixedStepValues_of_dispatch_mem
    {D : MachineDescription} {state : Nat}
    (hstate : FixedStepState.dispatch state ∈ fixedStepStates D) :
    state ∈ fixedStepValues D := by
  simpa [fixedStepStates] using hstate

theorem fixedStepValues_of_done_mem
    {D : MachineDescription} {state : Nat}
    (hstate : FixedStepState.done state ∈ fixedStepStates D) :
    state ∈ fixedStepValues D := by
  simpa [fixedStepStates] using hstate

/-- One typed micro-step.  Logical tape 0 is the simulated tape; logical tapes
1 and 2 are preserved for the surrounding counter and emitter phases. -/
def fixedStepNext (D : MachineDescription) :
    FixedStepState -> Option Bool -> Option Bool -> Option Bool ->
      Option (TypedStep FixedStepState)
  | .dispatch state, read, _, _ =>
      some
        { target := .done (fixedStepTargetState D state read)
          action0 := fixedStepTapeAction D state read
          action1 := keepS
          action2 := keepS }
  | .done _, _, _, _ =>
      some
        { target := .halt
          action0 := keepS
          action1 := keepS
          action2 := keepS }
  | .halt, _, _, _ => none

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

theorem fixedStepTargetState_of_not_mem
    {D : MachineDescription} {state : Nat}
    (hstate : state ∉ fixedStepValues D)
    (read : Option Bool) :
    fixedStepTargetState D state read = state := by
  simp [fixedStepTargetState,
    lookupTransition_eq_none_of_not_mem_fixedStepValues hstate read]

theorem fixedStepTapeAction_of_not_mem
    {D : MachineDescription} {state : Nat}
    (hstate : state ∉ fixedStepValues D)
    (read : Option Bool) :
    fixedStepTapeAction D state read = keepS := by
  simp [fixedStepTapeAction,
    lookupTransition_eq_none_of_not_mem_fixedStepValues hstate read]

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

theorem fixedStepNext_target_mem (D : MachineDescription) :
    forall s : FixedStepState, s ∈ fixedStepStates D ->
      forall (r0 r1 r2 : Option Bool) (st : TypedStep FixedStepState),
        fixedStepNext D s r0 r1 r2 = some st ->
          st.target ∈ fixedStepStates D := by
  intro s hs r0 r1 r2 st hnext
  cases s with
  | dispatch state =>
      simp only [fixedStepNext] at hnext
      cases hnext
      apply done_mem_fixedStepStates
      exact fixedStepTargetState_mem
        (fixedStepValues_of_dispatch_mem hs) r0
  | done state =>
      simp only [fixedStepNext] at hnext
      cases hnext
      exact halt_mem_fixedStepStates D
  | halt =>
      simp [fixedStepNext] at hnext

/-- Generated typed table for one baked-in description. -/
def fixedStepTable (D : MachineDescription) :
    TypedStateTable FixedStepState :=
  TypedStateTable.ofList
    (fixedStepStates D)
    (.dispatch D.start)
    .halt
    (fixedStepNext D)
    (dispatch_mem_fixedStepStates (start_mem_fixedStepValues D))
    (halt_mem_fixedStepStates D)
    (by intro r0 r1 r2; rfl)
    (fixedStepNext_target_mem D)

/-- The executable structured three-tape microkernel. -/
def fixedStepDescription (D : MachineDescription) : Description :=
  (fixedStepTable D).description

theorem fixedStepDescription_wellFormed (D : MachineDescription) :
    (fixedStepDescription D).WellFormed := by
  exact (fixedStepTable D).description_wellFormed

theorem fixedStepDescription_haltTransitionFree (D : MachineDescription) :
    (fixedStepDescription D).HaltTransitionFree := by
  exact (fixedStepTable D).description_haltTransitionFree

theorem fixedStepDescription_supportsReadWriteRows3
    (D : MachineDescription) :
    SupportsReadWriteRows3 (fixedStepDescription D) := by
  exact (fixedStepTable D).description_supportsReadWriteRows3

theorem fixedStepDescription_subroutineReady (D : MachineDescription) :
    (fixedStepDescription D).SubroutineReady :=
  ⟨fixedStepDescription_wellFormed D,
    fixedStepDescription_haltTransitionFree D⟩

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

@[simp] theorem fixedStepNext_dispatch
    (D : MachineDescription) (state : Nat)
    (r0 r1 r2 : Option Bool) :
    fixedStepNext D (.dispatch state) r0 r1 r2 =
      some
        { target := .done (fixedStepTargetState D state r0)
          action0 := fixedStepTapeAction D state r0
          action1 := keepS
          action2 := keepS } := by
  rfl

@[simp] theorem fixedStepNext_done
    (D : MachineDescription) (state : Nat)
    (r0 r1 r2 : Option Bool) :
    fixedStepNext D (.done state) r0 r1 r2 =
      some
        { target := .halt
          action0 := keepS
          action1 := keepS
          action2 := keepS } := by
  rfl

@[simp] theorem fixedStepNext_halt
    (D : MachineDescription) (r0 r1 r2 : Option Bool) :
    fixedStepNext D .halt r0 r1 r2 = none := by
  rfl

/-- Exact structured step from a typed dispatch state. -/
theorem fixedStepDescription_stepConfig_dispatch
    (D : MachineDescription) (state : Nat)
    (hstate : state ∈ fixedStepValues D)
    (T0 T1 T2 : Tape Bool) :
    (fixedStepDescription D).stepConfig
        (ThreeTape.config
          ((fixedStepTable D).stateId (.dispatch state))
          T0 T1 T2) =
      some
        (ThreeTape.config
          ((fixedStepTable D).stateId
            (.done (fixedStepTargetState D state (Tape.read T0))))
          ((fixedStepTapeAction D state (Tape.read T0)).apply T0)
          T1 T2) := by
  unfold fixedStepDescription
  rw [(fixedStepTable D).stepConfig_config
    (dispatch_mem_fixedStepStates hstate) T0 T1 T2]
  change
    (fixedStepNext D (.dispatch state)
      (Tape.read T0) (Tape.read T1) (Tape.read T2)).map _ = _
  rw [fixedStepNext_dispatch]
  simp [keepS, TapeAction.stay, TapeAction.apply, HeadMove.apply]

/-- The bookkeeping step exposes the typed next state before entering the
common halt state. -/
theorem fixedStepDescription_stepConfig_done
    (D : MachineDescription) (state : Nat)
    (hstate : state ∈ fixedStepValues D)
    (T0 T1 T2 : Tape Bool) :
    (fixedStepDescription D).stepConfig
        (ThreeTape.config
          ((fixedStepTable D).stateId (.done state))
          T0 T1 T2) =
      some
        (ThreeTape.config
          ((fixedStepTable D).stateId .halt)
          T0 T1 T2) := by
  unfold fixedStepDescription
  rw [(fixedStepTable D).stepConfig_config
    (done_mem_fixedStepStates hstate) T0 T1 T2]
  change
    (fixedStepNext D (.done state)
      (Tape.read T0) (Tape.read T1) (Tape.read T2)).map _ = _
  rw [fixedStepNext_done]
  simp [keepS, TapeAction.stay, TapeAction.apply, HeadMove.apply]

/-- Two structured iterations execute one simulated step and then enter the
common halt state. -/
theorem fixedStepDescription_runConfig_two_dispatch
    (D : MachineDescription) (state : Nat)
    (hstate : state ∈ fixedStepValues D)
    (T0 T1 T2 : Tape Bool) :
    (fixedStepDescription D).runConfig 2
        (ThreeTape.config
          ((fixedStepTable D).stateId (.dispatch state))
          T0 T1 T2) =
      ThreeTape.config
        ((fixedStepTable D).stateId .halt)
        ((fixedStepTapeAction D state (Tape.read T0)).apply T0)
        T1 T2 := by
  change
    (match
        (fixedStepDescription D).stepConfig
          (ThreeTape.config
            ((fixedStepTable D).stateId (.dispatch state))
            T0 T1 T2) with
      | none =>
          ThreeTape.config
            ((fixedStepTable D).stateId (.dispatch state))
            T0 T1 T2
      | some next => (fixedStepDescription D).runConfig 1 next) = _
  rw [fixedStepDescription_stepConfig_dispatch D state hstate T0 T1 T2]
  change
    (match
        (fixedStepDescription D).stepConfig
          (ThreeTape.config
            ((fixedStepTable D).stateId
              (.done (fixedStepTargetState D state (Tape.read T0))))
            ((fixedStepTapeAction D state (Tape.read T0)).apply T0)
            T1 T2) with
      | none =>
          ThreeTape.config
            ((fixedStepTable D).stateId
              (.done (fixedStepTargetState D state (Tape.read T0))))
            ((fixedStepTapeAction D state (Tape.read T0)).apply T0)
            T1 T2
      | some next => (fixedStepDescription D).runConfig 0 next) = _
  rw [fixedStepDescription_stepConfig_done D
    (fixedStepTargetState D state (Tape.read T0))
    (fixedStepTargetState_mem hstate (Tape.read T0))
    ((fixedStepTapeAction D state (Tape.read T0)).apply T0) T1 T2]
  rfl

/-- Consumer-facing one-step equation: the intermediate typed state and tape
are the ordinary fixed-description run result. -/
theorem fixedStepDescription_stepConfig_dispatch_eq_runConfig_one
    (D : MachineDescription) (state : Nat)
    (hstate : state ∈ fixedStepValues D)
    (T0 T1 T2 : Tape Bool) :
    (fixedStepDescription D).stepConfig
        (ThreeTape.config
          ((fixedStepTable D).stateId (.dispatch state))
          T0 T1 T2) =
      some
        (ThreeTape.config
          ((fixedStepTable D).stateId
            (.done
              (D.runConfig 1 { state := state, tape := T0 }).state))
          (D.runConfig 1 { state := state, tape := T0 }).tape
          T1 T2) := by
  rw [← fixedStepTargetState_eq_runConfig_one_state D state T0]
  rw [← fixedStepTapeAction_apply_eq_runConfig_one_tape D state T0]
  exact fixedStepDescription_stepConfig_dispatch
    D state hstate T0 T1 T2

/-- Consumer-facing halting equation for the complete two-iteration
microkernel. -/
theorem fixedStepDescription_runConfig_two_eq_runConfig_one
    (D : MachineDescription) (state : Nat)
    (hstate : state ∈ fixedStepValues D)
    (T0 T1 T2 : Tape Bool) :
    (fixedStepDescription D).runConfig 2
        (ThreeTape.config
          ((fixedStepTable D).stateId (.dispatch state))
          T0 T1 T2) =
      ThreeTape.config
        ((fixedStepTable D).stateId .halt)
        (D.runConfig 1 { state := state, tape := T0 }).tape
        T1 T2 := by
  rw [← fixedStepTapeAction_apply_eq_runConfig_one_tape D state T0]
  exact fixedStepDescription_runConfig_two_dispatch
    D state hstate T0 T1 T2

/-!
## Standalone lowering seam
-/

/-- The ordinary one-tape lowering of the reusable structured microkernel. -/
def loweredFixedStepDescription (D : MachineDescription) :
    MachineDescription :=
  lowerStructured3Description (fixedStepDescription D)

theorem loweredFixedStepDescription_wellFormed
    (D : MachineDescription) :
    (loweredFixedStepDescription D).WellFormed := by
  exact lowerStructured3Description_wellFormed
    (fixedStepDescription_wellFormed D)
    (fixedStepDescription_supportsReadWriteRows3 D)

theorem loweredFixedStepDescription_subroutineReady
    (D : MachineDescription) :
    (loweredFixedStepDescription D).SubroutineReady := by
  exact lowerStructured3Description_subroutineReady
    (fixedStepDescription_wellFormed D)
    (fixedStepDescription_supportsReadWriteRows3 D)

/-- The structured machine started at the baked description's start state
halts with exactly the tape produced by one ordinary iteration. -/
theorem fixedStepDescription_haltsWithTapes_start
    (D : MachineDescription) (T0 T1 T2 : Tape Bool) :
    (fixedStepDescription D).HaltsWithTapes
        (ThreeTape.config (fixedStepDescription D).start T0 T1 T2)
        [ (D.runConfig 1 { state := D.start, tape := T0 }).tape
        , T1
        , T2 ] := by
  refine ⟨2, ?_⟩
  change
    (fixedStepDescription D).runConfig 2
        (ThreeTape.config
          ((fixedStepTable D).stateId (.dispatch D.start))
          T0 T1 T2) =
      ThreeTape.config
        ((fixedStepTable D).stateId .halt)
        (D.runConfig 1 { state := D.start, tape := T0 }).tape
        T1 T2
  exact fixedStepDescription_runConfig_two_eq_runConfig_one
    D D.start (start_mem_fixedStepValues D) T0 T1 T2

/-- Lowered physical behavior of the standalone fixed-step microkernel. -/
theorem loweredFixedStepDescription_haltsFromTapeEquiv
    (D : MachineDescription) (T0 T1 T2 : Tape Bool) :
    (loweredFixedStepDescription D).HaltsFromTapeEquiv
        (encodedGuardedStructuredTapes [T0, T1, T2])
        (encodedGuardedStructuredTapes
          [ (D.runConfig 1 { state := D.start, tape := T0 }).tape
          , T1
          , T2 ]) := by
  unfold loweredFixedStepDescription
  apply lowerStructured3Description_haltsFromConfigWithTapes
    (fixedStepDescription_wellFormed D)
    (fixedStepDescription_haltTransitionFree D)
    (fixedStepDescription_supportsReadWriteRows3 D)
    (c := ThreeTape.config (fixedStepDescription D).start T0 T1 T2)
  · rfl
  · simp [fixedStepDescription]
  · exact fixedStepDescription_haltsWithTapes_start D T0 T1 T2

end RunConfigEmitterCore
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC

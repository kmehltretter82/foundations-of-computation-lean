import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.LoopDispatcher

set_option doc.verso true

/-!
# Done-witness closeout for the classified loop dispatcher

The classified dispatcher stops with the final known state in typed control.
This module extends that same typed table, preserving every dispatcher state
identifier, and appends the required self-delimiting witness on logical tape
2 before entering the common halt state.

This is an endpoint splice, not an entry classifier.  Its exact source is the
classified structured configuration {lit}`loopDispatcherSourceConfig`; that
state is generally not the fixed start state of the description.  The field
decomposer must still select the appropriate D-specific classified entry.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace RunConfigEmitterCore

open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape

/-!
## Finite suffix control
-/

/-- All suffixes of a finite list, including the list itself and the empty
suffix. -/
def closeoutSuffixes {α : Type} : List α -> List (List α)
  | [] => [[]]
  | x :: xs => (x :: xs) :: closeoutSuffixes xs

theorem self_mem_closeoutSuffixes {α : Type}
    (xs : List α) : xs ∈ closeoutSuffixes xs := by
  cases xs <;> simp [closeoutSuffixes]
  done

theorem nil_mem_closeoutSuffixes {α : Type}
    (xs : List α) : [] ∈ closeoutSuffixes xs := by
  induction xs with
  | nil => simp [closeoutSuffixes]
  | cons x xs ih => simp [closeoutSuffixes, ih]
  done

theorem tail_mem_closeoutSuffixes_of_cons_mem {α : Type}
    {x : α} {xs source : List α}
    (h : x :: xs ∈ closeoutSuffixes source) :
    xs ∈ closeoutSuffixes source := by
  induction source with
  | nil => simp [closeoutSuffixes] at h
  | cons y ys ih =>
      simp only [closeoutSuffixes, List.mem_cons] at h ⊢
      rcases h with hself | htail
      · cases hself
        exact Or.inr (self_mem_closeoutSuffixes xs)
      · exact Or.inr (ih htail)
  done

/-!
## Extended typed state space
-/

/-- Dispatcher states retain their numeric identifiers.  The closeout
constructors occupy a fresh block above the dispatcher state count. -/
inductive LoopDispatcherCloseoutState (D : MachineDescription) where
  | base (state : LoopDispatcherState D)
  | skip (witness : LoopDispatcherDoneWitness)
  | emit (witness : LoopDispatcherDoneWitness) (remaining : Word Bool)
  | rewind (witness : LoopDispatcherDoneWitness) (remaining : Word Bool)
  | finish (witness : LoopDispatcherDoneWitness)
deriving DecidableEq

/-- Finite branch witnesses baked into the description. -/
def loopDispatcherCloseoutWitnesses
    (D : MachineDescription) : List LoopDispatcherDoneWitness :=
  List.append
    ((fixedStepValues D).map LoopDispatcherDoneWitness.known)
    [.other]

theorem known_mem_loopDispatcherCloseoutWitnesses
    {D : MachineDescription} {state : Nat}
    (hstate : state ∈ fixedStepValues D) :
    LoopDispatcherDoneWitness.known state ∈
      loopDispatcherCloseoutWitnesses D := by
  simp [loopDispatcherCloseoutWitnesses, hstate]
  done

theorem other_mem_loopDispatcherCloseoutWitnesses
    (D : MachineDescription) :
    LoopDispatcherDoneWitness.other ∈
      loopDispatcherCloseoutWitnesses D := by
  simp [loopDispatcherCloseoutWitnesses]
  done

/-- Fresh emission and rewind states for one witness. -/
def loopDispatcherCloseoutStatesFor
    {D : MachineDescription} (witness : LoopDispatcherDoneWitness) :
    List (LoopDispatcherCloseoutState D) :=
  LoopDispatcherCloseoutState.skip witness ::
    List.append
      ((closeoutSuffixes witness.bits).map
        (LoopDispatcherCloseoutState.emit witness))
      (List.append
        ((closeoutSuffixes witness.bits.reverse).map
          (LoopDispatcherCloseoutState.rewind witness))
        [LoopDispatcherCloseoutState.finish witness])

/-- Fresh state block, disjoint by constructor from the embedded dispatcher. -/
def loopDispatcherCloseoutInternalStates
    (D : MachineDescription) : List (LoopDispatcherCloseoutState D) :=
  (loopDispatcherCloseoutWitnesses D).flatMap
    loopDispatcherCloseoutStatesFor

/-- Complete extended state enumeration. -/
def loopDispatcherCloseoutStates
    (D : MachineDescription) : List (LoopDispatcherCloseoutState D) :=
  List.append
    ((loopDispatcherStates D).map LoopDispatcherCloseoutState.base)
    (loopDispatcherCloseoutInternalStates D)

theorem base_mem_loopDispatcherCloseoutStates
    {D : MachineDescription} {state : LoopDispatcherState D}
    (hstate : state ∈ loopDispatcherStates D) :
    LoopDispatcherCloseoutState.base state ∈
      loopDispatcherCloseoutStates D := by
  simp [loopDispatcherCloseoutStates, hstate]
  done

theorem dispatcher_mem_of_base_mem_closeoutStates
    {D : MachineDescription} {state : LoopDispatcherState D}
    (hstate :
      LoopDispatcherCloseoutState.base state ∈
        loopDispatcherCloseoutStates D) :
    state ∈ loopDispatcherStates D := by
  rcases List.mem_append.mp hstate with hbase | hinternal
  · simpa using hbase
  · unfold loopDispatcherCloseoutInternalStates at hinternal
    rcases List.mem_flatMap.mp hinternal with
      ⟨witness, _, hwitness⟩
    simp [loopDispatcherCloseoutStatesFor] at hwitness
  done

theorem internal_mem_loopDispatcherCloseoutStates
    {D : MachineDescription} {state : LoopDispatcherCloseoutState D}
    (hstate : state ∈ loopDispatcherCloseoutInternalStates D) :
    state ∈ loopDispatcherCloseoutStates D := by
  exact List.mem_append.mpr (Or.inr hstate)
  done

theorem internal_mem_of_nonbase_mem_closeoutStates
    {D : MachineDescription} {state : LoopDispatcherCloseoutState D}
    (hstate : state ∈ loopDispatcherCloseoutStates D)
    (hbase : forall base, state ≠ .base base) :
    state ∈ loopDispatcherCloseoutInternalStates D := by
  rcases List.mem_append.mp hstate with hleft | hright
  · rcases List.mem_map.mp hleft with ⟨base, _, hbaseEq⟩
    exact absurd hbaseEq.symm (hbase base)
  · exact hright
  done

theorem stateFor_mem_internal
    {D : MachineDescription} {witness : LoopDispatcherDoneWitness}
    (hwitness : witness ∈ loopDispatcherCloseoutWitnesses D)
    {state : LoopDispatcherCloseoutState D}
    (hstate : state ∈ loopDispatcherCloseoutStatesFor witness) :
    state ∈ loopDispatcherCloseoutInternalStates D := by
  exact List.mem_flatMap.mpr ⟨witness, hwitness, hstate⟩
  done

theorem skip_mem_loopDispatcherCloseoutStates
    {D : MachineDescription} {witness : LoopDispatcherDoneWitness}
    (hwitness : witness ∈ loopDispatcherCloseoutWitnesses D) :
    LoopDispatcherCloseoutState.skip witness ∈
      loopDispatcherCloseoutStates D := by
  apply internal_mem_loopDispatcherCloseoutStates
  apply stateFor_mem_internal hwitness
  simp [loopDispatcherCloseoutStatesFor]
  done

theorem emit_mem_loopDispatcherCloseoutStates
    {D : MachineDescription} {witness : LoopDispatcherDoneWitness}
    (hwitness : witness ∈ loopDispatcherCloseoutWitnesses D)
    {remaining : Word Bool}
    (hremaining : remaining ∈ closeoutSuffixes witness.bits) :
    LoopDispatcherCloseoutState.emit witness remaining ∈
      loopDispatcherCloseoutStates D := by
  apply internal_mem_loopDispatcherCloseoutStates
  apply stateFor_mem_internal hwitness
  simp [loopDispatcherCloseoutStatesFor]
  exact hremaining
  done

theorem rewind_mem_loopDispatcherCloseoutStates
    {D : MachineDescription} {witness : LoopDispatcherDoneWitness}
    (hwitness : witness ∈ loopDispatcherCloseoutWitnesses D)
    {remaining : Word Bool}
    (hremaining : remaining ∈ closeoutSuffixes witness.bits.reverse) :
    LoopDispatcherCloseoutState.rewind witness remaining ∈
      loopDispatcherCloseoutStates D := by
  apply internal_mem_loopDispatcherCloseoutStates
  apply stateFor_mem_internal hwitness
  simp [loopDispatcherCloseoutStatesFor]
  exact hremaining
  done

theorem finish_mem_loopDispatcherCloseoutStates
    {D : MachineDescription} {witness : LoopDispatcherDoneWitness}
    (hwitness : witness ∈ loopDispatcherCloseoutWitnesses D) :
    LoopDispatcherCloseoutState.finish witness ∈
      loopDispatcherCloseoutStates D := by
  apply internal_mem_loopDispatcherCloseoutStates
  apply stateFor_mem_internal hwitness
  simp [loopDispatcherCloseoutStatesFor]
  done

/-!
## State identifiers preserving the dispatcher block
-/

def loopDispatcherCloseoutStateId (D : MachineDescription) :
    LoopDispatcherCloseoutState D -> Nat
  | .base state => (loopDispatcherTable D).stateId state
  | state =>
      (loopDispatcherTable D).stateCount +
        listIndexOf (loopDispatcherCloseoutInternalStates D) state

theorem loopDispatcherCloseoutStateId_base
    (D : MachineDescription) (state : LoopDispatcherState D) :
    loopDispatcherCloseoutStateId D (.base state) =
      (loopDispatcherTable D).stateId state := by
  rfl

theorem loopDispatcherCloseoutStateId_lt
    (D : MachineDescription) :
    forall state : LoopDispatcherCloseoutState D,
      state ∈ loopDispatcherCloseoutStates D ->
        loopDispatcherCloseoutStateId D state <
          (loopDispatcherTable D).stateCount +
            (loopDispatcherCloseoutInternalStates D).length := by
  intro state hstate
  by_cases hbase :
      exists base : LoopDispatcherState D, state = .base base
  · rcases hbase with ⟨base, rfl⟩
    exact Nat.lt_of_lt_of_le
      ((loopDispatcherTable D).stateId_lt base
        (dispatcher_mem_of_base_mem_closeoutStates hstate))
      (Nat.le_add_right _ _)
  · have hinternal :
        state ∈ loopDispatcherCloseoutInternalStates D :=
      internal_mem_of_nonbase_mem_closeoutStates hstate
        (by
          intro base heq
          exact hbase ⟨base, heq⟩)
    have hindex := listIndexOf_lt_length hinternal
    have hid :
        loopDispatcherCloseoutStateId D state =
          (loopDispatcherTable D).stateCount +
            listIndexOf (loopDispatcherCloseoutInternalStates D) state := by
      cases state <;> simp_all [loopDispatcherCloseoutStateId]
    rw [hid]
    exact Nat.add_lt_add_left hindex _
  done

theorem loopDispatcherCloseoutStateId_inj
    (D : MachineDescription) :
    forall state : LoopDispatcherCloseoutState D,
      state ∈ loopDispatcherCloseoutStates D ->
      forall target : LoopDispatcherCloseoutState D,
        target ∈ loopDispatcherCloseoutStates D ->
        loopDispatcherCloseoutStateId D state =
          loopDispatcherCloseoutStateId D target ->
        state = target := by
  intro state hstate target htarget hid
  by_cases hstateBase :
      exists base : LoopDispatcherState D, state = .base base
  · rcases hstateBase with ⟨base, rfl⟩
    by_cases htargetBase :
        exists targetBase : LoopDispatcherState D,
          target = .base targetBase
    · rcases htargetBase with ⟨targetBase, rfl⟩
      have hbaseEq :=
        (loopDispatcherTable D).stateId_inj
          base (dispatcher_mem_of_base_mem_closeoutStates hstate)
          targetBase (dispatcher_mem_of_base_mem_closeoutStates htarget)
          hid
      cases hbaseEq
      rfl
    · exfalso
      have htargetInternal :
          target ∈ loopDispatcherCloseoutInternalStates D :=
        internal_mem_of_nonbase_mem_closeoutStates htarget
          (by
            intro targetBase heq
            exact htargetBase ⟨targetBase, heq⟩)
      have htargetId :
          loopDispatcherCloseoutStateId D target =
            (loopDispatcherTable D).stateCount +
              listIndexOf (loopDispatcherCloseoutInternalStates D) target := by
        cases target <;> simp_all [loopDispatcherCloseoutStateId]
      have hbaseLt :=
        (loopDispatcherTable D).stateId_lt base
          (dispatcher_mem_of_base_mem_closeoutStates hstate)
      rw [htargetId] at hid
      simp only [loopDispatcherCloseoutStateId] at hid
      have hge :
          (loopDispatcherTable D).stateCount ≤
            (loopDispatcherTable D).stateId base := by
        rw [hid]
        exact Nat.le_add_right _ _
      exact (Nat.not_le_of_lt hbaseLt) hge
  · by_cases htargetBase :
        exists base : LoopDispatcherState D, target = .base base
    · rcases htargetBase with ⟨targetBase, rfl⟩
      exfalso
      have hstateInternal :
          state ∈ loopDispatcherCloseoutInternalStates D :=
        internal_mem_of_nonbase_mem_closeoutStates hstate
          (by
            intro base heq
            exact hstateBase ⟨base, heq⟩)
      have hstateId :
          loopDispatcherCloseoutStateId D state =
            (loopDispatcherTable D).stateCount +
              listIndexOf (loopDispatcherCloseoutInternalStates D) state := by
        cases state <;> simp_all [loopDispatcherCloseoutStateId]
      have htargetLt :=
        (loopDispatcherTable D).stateId_lt targetBase
          (dispatcher_mem_of_base_mem_closeoutStates htarget)
      rw [hstateId] at hid
      simp only [loopDispatcherCloseoutStateId] at hid
      have hge :
          (loopDispatcherTable D).stateCount ≤
            (loopDispatcherTable D).stateId targetBase := by
        rw [← hid]
        exact Nat.le_add_right _ _
      exact (Nat.not_le_of_lt htargetLt) hge
    · have hstateInternal :
          state ∈ loopDispatcherCloseoutInternalStates D :=
        internal_mem_of_nonbase_mem_closeoutStates hstate
          (by
            intro base heq
            exact hstateBase ⟨base, heq⟩)
      have htargetInternal :
          target ∈ loopDispatcherCloseoutInternalStates D :=
        internal_mem_of_nonbase_mem_closeoutStates htarget
          (by
            intro base heq
            exact htargetBase ⟨base, heq⟩)
      have hstateId :
          loopDispatcherCloseoutStateId D state =
            (loopDispatcherTable D).stateCount +
              listIndexOf (loopDispatcherCloseoutInternalStates D) state := by
        cases state <;> simp_all [loopDispatcherCloseoutStateId]
      have htargetId :
          loopDispatcherCloseoutStateId D target =
            (loopDispatcherTable D).stateCount +
              listIndexOf (loopDispatcherCloseoutInternalStates D) target := by
        cases target <;> simp_all [loopDispatcherCloseoutStateId]
      rw [hstateId, htargetId] at hid
      exact listIndexOf_inj hstateInternal htargetInternal
        (Nat.add_left_cancel hid)
  done

/-!
## Combined transition function
-/

def liftDispatcherStep {D : MachineDescription}
    (step : TypedStep (LoopDispatcherState D)) :
    TypedStep (LoopDispatcherCloseoutState D) :=
  { target := .base step.target
    action0 := step.action0
    action1 := step.action1
    action2 := step.action2 }

def loopDispatcherCloseoutNext (D : MachineDescription) :
    LoopDispatcherCloseoutState D ->
      Option Bool -> Option Bool -> Option Bool ->
      Option (TypedStep (LoopDispatcherCloseoutState D))
  | .base (.known (.done state)), _, _, _ =>
      some
        { target := .skip (.known state)
          action0 := keepS
          action1 := keepS
          action2 := keepR }
  | .base (.other .done), _, _, _ =>
      some
        { target := .skip .other
          action0 := keepS
          action1 := keepS
          action2 := keepR }
  | .base state, r0, r1, r2 =>
      (loopDispatcherNext D state r0 r1 r2).map liftDispatcherStep
  | .skip witness, _, _, _ =>
      some
        { target := .emit witness witness.bits
          action0 := keepS
          action1 := keepS
          action2 := keepR }
  | .emit witness (bit :: rest), _, _, _ =>
      some
        { target := .emit witness rest
          action0 := keepS
          action1 := keepS
          action2 := writeBitR bit }
  | .emit witness [], _, _, _ =>
      some
        { target := .rewind witness witness.bits.reverse
          action0 := keepS
          action1 := keepS
          action2 := keepL }
  | .rewind witness (_ :: rest), _, _, _ =>
      some
        { target := .rewind witness rest
          action0 := keepS
          action1 := keepS
          action2 := keepL }
  | .rewind witness [], _, _, _ =>
      some
        { target := .finish witness
          action0 := keepS
          action1 := keepS
          action2 := keepL }
  | .finish _, _, _, _ =>
      some
        { target := .base .halt
          action0 := keepS
          action1 := keepS
          action2 := keepS }

theorem witness_mem_of_skip_mem_closeoutStates
    {D : MachineDescription} {witness : LoopDispatcherDoneWitness}
    (hstate :
      LoopDispatcherCloseoutState.skip witness ∈
        loopDispatcherCloseoutStates D) :
    witness ∈ loopDispatcherCloseoutWitnesses D := by
  simpa [loopDispatcherCloseoutStates,
    loopDispatcherCloseoutInternalStates,
    loopDispatcherCloseoutStatesFor] using hstate
  done

theorem witness_suffix_of_emit_mem_closeoutStates
    {D : MachineDescription} {witness : LoopDispatcherDoneWitness}
    {remaining : Word Bool}
    (hstate :
      LoopDispatcherCloseoutState.emit witness remaining ∈
        loopDispatcherCloseoutStates D) :
    witness ∈ loopDispatcherCloseoutWitnesses D ∧
      remaining ∈ closeoutSuffixes witness.bits := by
  have h := hstate
  simp [loopDispatcherCloseoutStates,
    loopDispatcherCloseoutInternalStates,
    loopDispatcherCloseoutStatesFor] at h
  exact ⟨h.left, h.right⟩
  done

theorem witness_suffix_of_rewind_mem_closeoutStates
    {D : MachineDescription} {witness : LoopDispatcherDoneWitness}
    {remaining : Word Bool}
    (hstate :
      LoopDispatcherCloseoutState.rewind witness remaining ∈
        loopDispatcherCloseoutStates D) :
    witness ∈ loopDispatcherCloseoutWitnesses D ∧
      remaining ∈ closeoutSuffixes witness.bits.reverse := by
  have h := hstate
  simp [loopDispatcherCloseoutStates,
    loopDispatcherCloseoutInternalStates,
    loopDispatcherCloseoutStatesFor] at h
  exact ⟨h.left, h.right⟩
  done

theorem witness_mem_of_finish_mem_closeoutStates
    {D : MachineDescription} {witness : LoopDispatcherDoneWitness}
    (hstate :
      LoopDispatcherCloseoutState.finish witness ∈
        loopDispatcherCloseoutStates D) :
    witness ∈ loopDispatcherCloseoutWitnesses D := by
  simpa [loopDispatcherCloseoutStates,
    loopDispatcherCloseoutInternalStates,
    loopDispatcherCloseoutStatesFor] using hstate
  done

theorem loopDispatcherCloseoutNext_target_mem
    (D : MachineDescription) :
    forall state : LoopDispatcherCloseoutState D,
      state ∈ loopDispatcherCloseoutStates D ->
      forall (r0 r1 r2 : Option Bool)
        (step : TypedStep (LoopDispatcherCloseoutState D)),
        loopDispatcherCloseoutNext D state r0 r1 r2 = some step ->
          step.target ∈ loopDispatcherCloseoutStates D := by
  intro state hstate r0 r1 r2 step hnext
  cases state with
  | base state =>
      have hdispatcher := dispatcher_mem_of_base_mem_closeoutStates hstate
      cases state with
      | dispatch tag =>
          cases hinner :
              loopDispatcherNext D (.dispatch tag) r0 r1 r2 with
          | none => simp [loopDispatcherCloseoutNext, hinner] at hnext
          | some inner =>
              simp only [loopDispatcherCloseoutNext, hinner,
                Option.map_some] at hnext
              cases hnext
              exact base_mem_loopDispatcherCloseoutStates
                (loopDispatcherNext_target_mem D (.dispatch tag)
                  hdispatcher r0 r1 r2 inner hinner)
      | known state =>
          cases state with
          | done state =>
              simp only [loopDispatcherCloseoutNext] at hnext
              cases hnext
              apply skip_mem_loopDispatcherCloseoutStates
              apply known_mem_loopDispatcherCloseoutWitnesses
              exact fixedStepValues_of_knownStateLoopDone_mem
                (knownStateLoopStates_of_known_mem hdispatcher)
          | seed state =>
              cases hinner :
                  loopDispatcherNext D (.known (.seed state)) r0 r1 r2 with
              | none =>
                  simp [loopDispatcherCloseoutNext, hinner] at hnext
              | some inner =>
                  simp only [loopDispatcherCloseoutNext, hinner,
                    Option.map_some] at hnext
                  cases hnext
                  exact base_mem_loopDispatcherCloseoutStates
                    (loopDispatcherNext_target_mem D
                      (.known (.seed state)) hdispatcher
                      r0 r1 r2 inner hinner)
          | loop state =>
              cases hinner :
                  loopDispatcherNext D (.known (.loop state)) r0 r1 r2 with
              | none =>
                  simp [loopDispatcherCloseoutNext, hinner] at hnext
              | some inner =>
                  simp only [loopDispatcherCloseoutNext, hinner,
                    Option.map_some] at hnext
                  cases hnext
                  exact base_mem_loopDispatcherCloseoutStates
                    (loopDispatcherNext_target_mem D
                      (.known (.loop state)) hdispatcher
                      r0 r1 r2 inner hinner)
          | halt =>
              simp [loopDispatcherCloseoutNext,
                loopDispatcherNext, knownStateLoopNext] at hnext
      | other state =>
          cases state with
          | done =>
              simp only [loopDispatcherCloseoutNext] at hnext
              cases hnext
              exact skip_mem_loopDispatcherCloseoutStates
                (other_mem_loopDispatcherCloseoutWitnesses D)
          | loop =>
              cases hinner :
                  loopDispatcherNext D (.other .loop) r0 r1 r2 with
              | none =>
                  simp [loopDispatcherCloseoutNext, hinner] at hnext
              | some inner =>
                  simp only [loopDispatcherCloseoutNext, hinner,
                    Option.map_some] at hnext
                  cases hnext
                  exact base_mem_loopDispatcherCloseoutStates
                    (loopDispatcherNext_target_mem D (.other .loop)
                      hdispatcher r0 r1 r2 inner hinner)
          | halt =>
              simp [loopDispatcherCloseoutNext,
                loopDispatcherNext, otherStateLoopNext] at hnext
      | halt =>
          simp [loopDispatcherCloseoutNext, loopDispatcherNext] at hnext
  | skip witness =>
      simp only [loopDispatcherCloseoutNext] at hnext
      cases hnext
      exact emit_mem_loopDispatcherCloseoutStates
        (witness_mem_of_skip_mem_closeoutStates hstate)
        (self_mem_closeoutSuffixes witness.bits)
  | emit witness remaining =>
      have hwitness := witness_suffix_of_emit_mem_closeoutStates hstate
      cases remaining with
      | nil =>
          simp only [loopDispatcherCloseoutNext] at hnext
          cases hnext
          exact rewind_mem_loopDispatcherCloseoutStates hwitness.left
            (self_mem_closeoutSuffixes witness.bits.reverse)
      | cons bit rest =>
          simp only [loopDispatcherCloseoutNext] at hnext
          cases hnext
          exact emit_mem_loopDispatcherCloseoutStates hwitness.left
            (tail_mem_closeoutSuffixes_of_cons_mem hwitness.right)
  | rewind witness remaining =>
      have hwitness := witness_suffix_of_rewind_mem_closeoutStates hstate
      cases remaining with
      | nil =>
          simp only [loopDispatcherCloseoutNext] at hnext
          cases hnext
          exact finish_mem_loopDispatcherCloseoutStates hwitness.left
      | cons bit rest =>
          simp only [loopDispatcherCloseoutNext] at hnext
          cases hnext
          exact rewind_mem_loopDispatcherCloseoutStates hwitness.left
            (tail_mem_closeoutSuffixes_of_cons_mem hwitness.right)
  | finish witness =>
      simp only [loopDispatcherCloseoutNext] at hnext
      cases hnext
      exact base_mem_loopDispatcherCloseoutStates
        (halt_mem_loopDispatcherStates D)
  done

/-- One typed table containing the dispatcher and witness closeout. -/
def loopDispatcherCloseoutTable (D : MachineDescription) :
    TypedStateTable (LoopDispatcherCloseoutState D) where
  states := loopDispatcherCloseoutStates D
  stateCount :=
    (loopDispatcherTable D).stateCount +
      (loopDispatcherCloseoutInternalStates D).length
  stateId := loopDispatcherCloseoutStateId D
  start := .base (loopDispatcherTable D).start
  halt := .base .halt
  next := loopDispatcherCloseoutNext D
  start_mem :=
    base_mem_loopDispatcherCloseoutStates
      (loopDispatcherTable D).start_mem
  halt_mem :=
    base_mem_loopDispatcherCloseoutStates
      (halt_mem_loopDispatcherStates D)
  stateId_lt := loopDispatcherCloseoutStateId_lt D
  stateId_inj := loopDispatcherCloseoutStateId_inj D
  halt_next := by intro r0 r1 r2; rfl
  next_target_mem := loopDispatcherCloseoutNext_target_mem D

/-- Combined classified dispatcher and done-witness closeout description. -/
def loopDispatcherCloseoutDescription
    (D : MachineDescription) : Description :=
  (loopDispatcherCloseoutTable D).description

theorem loopDispatcherCloseoutDescription_wellFormed
    (D : MachineDescription) :
    (loopDispatcherCloseoutDescription D).WellFormed := by
  exact (loopDispatcherCloseoutTable D).description_wellFormed
  done

theorem loopDispatcherCloseoutDescription_haltTransitionFree
    (D : MachineDescription) :
    (loopDispatcherCloseoutDescription D).HaltTransitionFree := by
  exact (loopDispatcherCloseoutTable D).description_haltTransitionFree
  done

theorem loopDispatcherCloseoutDescription_supportsReadWriteRows3
    (D : MachineDescription) :
    SupportsReadWriteRows3 (loopDispatcherCloseoutDescription D) := by
  exact (loopDispatcherCloseoutTable D).description_supportsReadWriteRows3
  done

theorem loopDispatcherCloseoutDescription_subroutineReady
    (D : MachineDescription) :
    (loopDispatcherCloseoutDescription D).SubroutineReady := by
  exact (loopDispatcherCloseoutTable D).description_subroutineReady
  done

/-!
## Exact closeout tape shapes
-/

/-- Tape 2 while the witness is being emitted.  The head is the first blank
after {lit}`written`; the reverse of {lit}`written` is therefore the newest
part of the left context. -/
def loopDispatcherCloseoutEmissionTape
    (L : SimulatorLayout) (hit : Bool) (written : Word Bool) : Tape Bool :=
  tapeAtCells
    (List.append (written.reverse.map some)
      (none :: some hit ::
        (FieldDecomposition.metadataPrefixCells L).reverse))
    []

/-- The separator position reached immediately after leaving a dispatcher
done state. -/
def loopDispatcherCloseoutSeparatorTape
    (L : SimulatorLayout) (hit : Bool) : Tape Bool :=
  tapeAtCells
    (some hit :: (FieldDecomposition.metadataPrefixCells L).reverse)
    []

/-- Tape 2 while moving back over an emitted witness.  {lit}`remaining` is the
suffix of the reversed witness that is still at or left of the head, while
{lit}`processed` is already restored in forward order to the right. -/
def loopDispatcherCloseoutRewindTape
    (L : SimulatorLayout) (hit : Bool)
    (remaining processed : Word Bool) : Tape Bool :=
  match remaining with
  | [] =>
      tapeAtCells
        (some hit :: (FieldDecomposition.metadataPrefixCells L).reverse)
        (none :: List.append (processed.map some) [none])
  | bit :: rest =>
      tapeAtCells
        (List.append (rest.map some)
          (none :: some hit ::
            (FieldDecomposition.metadataPrefixCells L).reverse))
        (some bit :: List.append (processed.map some) [none])

/-- Generic exact target for one branch witness and one final hit value. -/
def loopDispatcherCloseoutWitnessTape
    (L : SimulatorLayout) (hit : Bool)
    (witness : LoopDispatcherDoneWitness) : Tape Bool :=
  tapeAtCells
    (FieldDecomposition.metadataPrefixCells L).reverse
    (some hit :: none ::
      List.append (witness.bits.map some) [none])

/-- Both branch encodings contain at least the four bits of their Boolean
tag. -/
theorem LoopDispatcherDoneWitness.bits_ne_nil
    (witness : LoopDispatcherDoneWitness) : witness.bits ≠ [] := by
  cases witness with
  | known state =>
      simp [LoopDispatcherDoneWitness.bits,
        LoopDispatcherDoneWitness.code, encodeBoolAppend,
        encodeCellAppend, encodeCell, encodeCodeWordAsInput,
        encodeCodeSymbolAsInput]
  | other =>
      simp [LoopDispatcherDoneWitness.bits,
        LoopDispatcherDoneWitness.code, encodeBoolAppend,
        encodeCellAppend, encodeCell, encodeCodeWordAsInput,
        encodeCodeSymbolAsInput]
  done

/-!
## Exact primitive executions
-/

/-- One row of the extended typed table executes as one structured step. -/
theorem loopDispatcherCloseoutDescription_runConfig_one
    (D : MachineDescription) (state : LoopDispatcherCloseoutState D)
    (hstate : state ∈ loopDispatcherCloseoutStates D)
    (T0 T1 T2 : Tape Bool)
    (step : TypedStep (LoopDispatcherCloseoutState D))
    (hnext :
      loopDispatcherCloseoutNext D state
          (Tape.read T0) (Tape.read T1) (Tape.read T2) = some step) :
    (loopDispatcherCloseoutDescription D).runConfig 1
        (ThreeTape.config
          (loopDispatcherCloseoutStateId D state) T0 T1 T2) =
      ThreeTape.config
        (loopDispatcherCloseoutStateId D step.target)
        (step.action0.apply T0)
        (step.action1.apply T1)
        (step.action2.apply T2) := by
  change
    (loopDispatcherCloseoutTable D).description.runConfig (0 + 1)
        (ThreeTape.config
          ((loopDispatcherCloseoutTable D).stateId state) T0 T1 T2) =
      ThreeTape.config
        ((loopDispatcherCloseoutTable D).stateId step.target)
        (step.action0.apply T0)
        (step.action1.apply T1)
        (step.action2.apply T2)
  rw [(loopDispatcherCloseoutTable D).runConfig_succ_config
    hstate hnext 0]
  rfl
  done

theorem loopDispatcherCloseoutDescription_runConfig_one_known_done
    (D : MachineDescription) (state : Nat)
    (hstate : state ∈ fixedStepValues D)
    (T0 T1 : Tape Bool) (L : SimulatorLayout) (hit : Bool) :
    (loopDispatcherCloseoutDescription D).runConfig 1
        (ThreeTape.config
          ((loopDispatcherTable D).stateId (.known (.done state)))
          T0 T1 (loopDispatcherHitTape L hit)) =
      ThreeTape.config
        (loopDispatcherCloseoutStateId D (.skip (.known state)))
        T0 T1 (loopDispatcherCloseoutSeparatorTape L hit) := by
  have hnext :
      loopDispatcherCloseoutNext D (.base (.known (.done state)))
          (Tape.read T0) (Tape.read T1)
          (Tape.read (loopDispatcherHitTape L hit)) =
        some
          { target := .skip (.known state)
            action0 := keepS
            action1 := keepS
            action2 := keepR } := by
    rfl
  have hrun :=
    loopDispatcherCloseoutDescription_runConfig_one D
      (.base (.known (.done state)))
      (base_mem_loopDispatcherCloseoutStates
        (known_mem_loopDispatcherStates
          (done_mem_knownStateLoopStates hstate)))
      T0 T1 (loopDispatcherHitTape L hit)
      { target := .skip (.known state)
        action0 := keepS
        action1 := keepS
        action2 := keepR }
      hnext
  simpa [loopDispatcherCloseoutStateId_base,
    loopDispatcherHitTape,
    FieldDecomposition.metadataHitTapeWithHit,
    loopDispatcherCloseoutSeparatorTape, tapeAtCells,
    keepS, keepR, TapeAction.stay, TapeAction.apply,
    HeadMove.apply, Tape.move, Tape.moveRight] using hrun
  done

theorem loopDispatcherCloseoutDescription_runConfig_one_other_done
    (D : MachineDescription) (T0 T1 : Tape Bool)
    (L : SimulatorLayout) (hit : Bool) :
    (loopDispatcherCloseoutDescription D).runConfig 1
        (ThreeTape.config
          ((loopDispatcherTable D).stateId (.other .done))
          T0 T1 (loopDispatcherHitTape L hit)) =
      ThreeTape.config
        (loopDispatcherCloseoutStateId D (.skip .other))
        T0 T1 (loopDispatcherCloseoutSeparatorTape L hit) := by
  have hnext :
      loopDispatcherCloseoutNext D (.base (.other .done))
          (Tape.read T0) (Tape.read T1)
          (Tape.read (loopDispatcherHitTape L hit)) =
        some
          { target := .skip .other
            action0 := keepS
            action1 := keepS
            action2 := keepR } := by
    rfl
  have hrun :=
    loopDispatcherCloseoutDescription_runConfig_one D
      (.base (.other .done))
      (base_mem_loopDispatcherCloseoutStates
        (other_mem_loopDispatcherStates done_mem_otherStateLoopStates))
      T0 T1 (loopDispatcherHitTape L hit)
      { target := .skip .other
        action0 := keepS
        action1 := keepS
        action2 := keepR }
      hnext
  simpa [loopDispatcherCloseoutStateId_base,
    loopDispatcherHitTape,
    FieldDecomposition.metadataHitTapeWithHit,
    loopDispatcherCloseoutSeparatorTape, tapeAtCells,
    keepS, keepR, TapeAction.stay, TapeAction.apply,
    HeadMove.apply, Tape.move, Tape.moveRight] using hrun
  done

theorem loopDispatcherCloseoutDescription_runConfig_one_skip
    (D : MachineDescription) (witness : LoopDispatcherDoneWitness)
    (hwitness : witness ∈ loopDispatcherCloseoutWitnesses D)
    (T0 T1 : Tape Bool) (L : SimulatorLayout) (hit : Bool) :
    (loopDispatcherCloseoutDescription D).runConfig 1
        (ThreeTape.config
          (loopDispatcherCloseoutStateId D (.skip witness))
          T0 T1 (loopDispatcherCloseoutSeparatorTape L hit)) =
      ThreeTape.config
        (loopDispatcherCloseoutStateId D
          (.emit witness witness.bits))
        T0 T1 (loopDispatcherCloseoutEmissionTape L hit []) := by
  have hnext :
      loopDispatcherCloseoutNext D (.skip witness)
          (Tape.read T0) (Tape.read T1)
          (Tape.read (loopDispatcherCloseoutSeparatorTape L hit)) =
        some
          { target := .emit witness witness.bits
            action0 := keepS
            action1 := keepS
            action2 := keepR } := by
    rfl
  have hrun :=
    loopDispatcherCloseoutDescription_runConfig_one D
      (.skip witness)
      (skip_mem_loopDispatcherCloseoutStates hwitness)
      T0 T1 (loopDispatcherCloseoutSeparatorTape L hit)
      { target := .emit witness witness.bits
        action0 := keepS
        action1 := keepS
        action2 := keepR }
      hnext
  simpa [loopDispatcherCloseoutSeparatorTape,
    loopDispatcherCloseoutEmissionTape, tapeAtCells,
    keepS, keepR, TapeAction.stay, TapeAction.apply,
    HeadMove.apply, Tape.move, Tape.moveRight] using hrun
  done

theorem loopDispatcherCloseoutDescription_runConfig_one_emit_cons
    (D : MachineDescription) (witness : LoopDispatcherDoneWitness)
    (hwitness : witness ∈ loopDispatcherCloseoutWitnesses D)
    (bit : Bool) (rest written : Word Bool)
    (hremaining : bit :: rest ∈ closeoutSuffixes witness.bits)
    (T0 T1 : Tape Bool) (L : SimulatorLayout) (hit : Bool) :
    (loopDispatcherCloseoutDescription D).runConfig 1
        (ThreeTape.config
          (loopDispatcherCloseoutStateId D
            (.emit witness (bit :: rest)))
          T0 T1 (loopDispatcherCloseoutEmissionTape L hit written)) =
      ThreeTape.config
        (loopDispatcherCloseoutStateId D (.emit witness rest))
        T0 T1
        (loopDispatcherCloseoutEmissionTape L hit
          (List.append written [bit])) := by
  have hnext :
      loopDispatcherCloseoutNext D (.emit witness (bit :: rest))
          (Tape.read T0) (Tape.read T1)
          (Tape.read (loopDispatcherCloseoutEmissionTape L hit written)) =
        some
          { target := .emit witness rest
            action0 := keepS
            action1 := keepS
            action2 := writeBitR bit } := by
    rfl
  have hrun :=
    loopDispatcherCloseoutDescription_runConfig_one D
      (.emit witness (bit :: rest))
      (emit_mem_loopDispatcherCloseoutStates hwitness hremaining)
      T0 T1 (loopDispatcherCloseoutEmissionTape L hit written)
      { target := .emit witness rest
        action0 := keepS
        action1 := keepS
        action2 := writeBitR bit }
      hnext
  simpa [loopDispatcherCloseoutEmissionTape, tapeAtCells,
    keepS, writeBitR, writeR, TapeAction.stay, TapeAction.apply,
    HeadMove.apply, Tape.write, Tape.move, Tape.moveRight,
    List.reverse_append, List.map_append, List.append_assoc] using hrun
  done

theorem loopDispatcherCloseoutDescription_runConfig_one_emit_nil
    (D : MachineDescription) (witness : LoopDispatcherDoneWitness)
    (hwitness : witness ∈ loopDispatcherCloseoutWitnesses D)
    (T0 T1 : Tape Bool) (L : SimulatorLayout) (hit : Bool) :
    (loopDispatcherCloseoutDescription D).runConfig 1
        (ThreeTape.config
          (loopDispatcherCloseoutStateId D (.emit witness []))
          T0 T1
          (loopDispatcherCloseoutEmissionTape L hit witness.bits)) =
      ThreeTape.config
        (loopDispatcherCloseoutStateId D
          (.rewind witness witness.bits.reverse))
        T0 T1
        (loopDispatcherCloseoutRewindTape L hit
          witness.bits.reverse []) := by
  have hnext :
      loopDispatcherCloseoutNext D (.emit witness [])
          (Tape.read T0) (Tape.read T1)
          (Tape.read
            (loopDispatcherCloseoutEmissionTape L hit witness.bits)) =
        some
          { target := .rewind witness witness.bits.reverse
            action0 := keepS
            action1 := keepS
            action2 := keepL } := by
    rfl
  have hrun :=
    loopDispatcherCloseoutDescription_runConfig_one D
      (.emit witness [])
      (emit_mem_loopDispatcherCloseoutStates hwitness
        (nil_mem_closeoutSuffixes witness.bits))
      T0 T1 (loopDispatcherCloseoutEmissionTape L hit witness.bits)
      { target := .rewind witness witness.bits.reverse
        action0 := keepS
        action1 := keepS
        action2 := keepL }
      hnext
  cases hreverse : witness.bits.reverse with
  | nil =>
      exfalso
      apply witness.bits_ne_nil
      unfold Word
      have := congrArg List.reverse hreverse
      simpa using this
  | cons bit rest =>
      simpa [hreverse, loopDispatcherCloseoutEmissionTape,
        loopDispatcherCloseoutRewindTape, tapeAtCells,
        keepS, keepL, TapeAction.stay, TapeAction.apply,
        HeadMove.apply, Tape.move, Tape.moveLeft,
        List.append_assoc] using hrun
  done

/-- Emit every bit in {lit}`remaining`, accumulating it after
{lit}`written`. -/
theorem loopDispatcherCloseoutDescription_runConfig_emit
    (D : MachineDescription) (witness : LoopDispatcherDoneWitness)
    (hwitness : witness ∈ loopDispatcherCloseoutWitnesses D)
    (remaining written : Word Bool)
    (hremaining : remaining ∈ closeoutSuffixes witness.bits)
    (hparts : witness.bits = List.append written remaining)
    (T0 T1 : Tape Bool) (L : SimulatorLayout) (hit : Bool) :
    (loopDispatcherCloseoutDescription D).runConfig remaining.length
        (ThreeTape.config
          (loopDispatcherCloseoutStateId D (.emit witness remaining))
          T0 T1 (loopDispatcherCloseoutEmissionTape L hit written)) =
      ThreeTape.config
        (loopDispatcherCloseoutStateId D (.emit witness []))
        T0 T1
        (loopDispatcherCloseoutEmissionTape L hit witness.bits) := by
  induction remaining generalizing written with
  | nil =>
      simp only [List.length_nil]
      rw [Structured.Description.runConfig]
      simpa using congrArg
        (fun bits =>
          ThreeTape.config
            (loopDispatcherCloseoutStateId D (.emit witness []))
            T0 T1 (loopDispatcherCloseoutEmissionTape L hit bits))
        hparts.symm
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp [Nat.add_comm]]
      rw [Structured.Description.runConfig_add]
      rw [loopDispatcherCloseoutDescription_runConfig_one_emit_cons
        D witness hwitness bit rest written hremaining T0 T1 L hit]
      apply ih (List.append written [bit])
      · exact tail_mem_closeoutSuffixes_of_cons_mem hremaining
      · simpa [List.append_assoc] using hparts
  done

theorem loopDispatcherCloseoutDescription_runConfig_one_rewind_cons
    (D : MachineDescription) (witness : LoopDispatcherDoneWitness)
    (hwitness : witness ∈ loopDispatcherCloseoutWitnesses D)
    (bit : Bool) (rest processed : Word Bool)
    (hremaining :
      bit :: rest ∈ closeoutSuffixes witness.bits.reverse)
    (T0 T1 : Tape Bool) (L : SimulatorLayout) (hit : Bool) :
    (loopDispatcherCloseoutDescription D).runConfig 1
        (ThreeTape.config
          (loopDispatcherCloseoutStateId D
            (.rewind witness (bit :: rest)))
          T0 T1
          (loopDispatcherCloseoutRewindTape L hit
            (bit :: rest) processed)) =
      ThreeTape.config
        (loopDispatcherCloseoutStateId D (.rewind witness rest))
        T0 T1
        (loopDispatcherCloseoutRewindTape L hit rest
          (bit :: processed)) := by
  have hnext :
      loopDispatcherCloseoutNext D
          (.rewind witness (bit :: rest))
          (Tape.read T0) (Tape.read T1)
          (Tape.read
            (loopDispatcherCloseoutRewindTape L hit
              (bit :: rest) processed)) =
        some
          { target := .rewind witness rest
            action0 := keepS
            action1 := keepS
            action2 := keepL } := by
    rfl
  have hrun :=
    loopDispatcherCloseoutDescription_runConfig_one D
      (.rewind witness (bit :: rest))
      (rewind_mem_loopDispatcherCloseoutStates hwitness hremaining)
      T0 T1
      (loopDispatcherCloseoutRewindTape L hit
        (bit :: rest) processed)
      { target := .rewind witness rest
        action0 := keepS
        action1 := keepS
        action2 := keepL }
      hnext
  cases rest with
  | nil =>
      simpa [loopDispatcherCloseoutRewindTape, tapeAtCells,
        keepS, keepL, TapeAction.stay, TapeAction.apply,
        HeadMove.apply, Tape.move, Tape.moveLeft,
        List.append_assoc] using hrun
  | cons next rest =>
      simpa [loopDispatcherCloseoutRewindTape, tapeAtCells,
        keepS, keepL, TapeAction.stay, TapeAction.apply,
        HeadMove.apply, Tape.move, Tape.moveLeft,
        List.append_assoc] using hrun
  done

/-- Rewind over every cell in {lit}`remaining`, rebuilding forward-order bits
on the right of the head. -/
theorem loopDispatcherCloseoutDescription_runConfig_rewind
    (D : MachineDescription) (witness : LoopDispatcherDoneWitness)
    (hwitness : witness ∈ loopDispatcherCloseoutWitnesses D)
    (remaining processed : Word Bool)
    (hremaining :
      remaining ∈ closeoutSuffixes witness.bits.reverse)
    (T0 T1 : Tape Bool) (L : SimulatorLayout) (hit : Bool) :
    (loopDispatcherCloseoutDescription D).runConfig remaining.length
        (ThreeTape.config
          (loopDispatcherCloseoutStateId D
            (.rewind witness remaining))
          T0 T1
          (loopDispatcherCloseoutRewindTape L hit
            remaining processed)) =
      ThreeTape.config
        (loopDispatcherCloseoutStateId D (.rewind witness []))
        T0 T1
        (loopDispatcherCloseoutRewindTape L hit []
          (List.append remaining.reverse processed)) := by
  induction remaining generalizing processed with
  | nil =>
      simp [Structured.Description.runConfig]
      done
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp [Nat.add_comm]]
      rw [Structured.Description.runConfig_add]
      rw [loopDispatcherCloseoutDescription_runConfig_one_rewind_cons
        D witness hwitness bit rest processed hremaining T0 T1 L hit]
      simpa [List.reverse_cons, List.append_assoc] using
        (ih (bit :: processed)
          (tail_mem_closeoutSuffixes_of_cons_mem hremaining))
  done

theorem loopDispatcherCloseoutDescription_runConfig_one_rewind_nil
    (D : MachineDescription) (witness : LoopDispatcherDoneWitness)
    (hwitness : witness ∈ loopDispatcherCloseoutWitnesses D)
    (T0 T1 : Tape Bool) (L : SimulatorLayout) (hit : Bool) :
    (loopDispatcherCloseoutDescription D).runConfig 1
        (ThreeTape.config
          (loopDispatcherCloseoutStateId D (.rewind witness []))
          T0 T1
          (loopDispatcherCloseoutRewindTape L hit [] witness.bits)) =
      ThreeTape.config
        (loopDispatcherCloseoutStateId D (.finish witness))
        T0 T1 (loopDispatcherCloseoutWitnessTape L hit witness) := by
  have hnext :
      loopDispatcherCloseoutNext D (.rewind witness [])
          (Tape.read T0) (Tape.read T1)
          (Tape.read
            (loopDispatcherCloseoutRewindTape L hit [] witness.bits)) =
        some
          { target := .finish witness
            action0 := keepS
            action1 := keepS
            action2 := keepL } := by
    rfl
  have hrun :=
    loopDispatcherCloseoutDescription_runConfig_one D
      (.rewind witness [])
      (rewind_mem_loopDispatcherCloseoutStates hwitness
        (nil_mem_closeoutSuffixes witness.bits.reverse))
      T0 T1
      (loopDispatcherCloseoutRewindTape L hit [] witness.bits)
      { target := .finish witness
        action0 := keepS
        action1 := keepS
        action2 := keepL }
      hnext
  simpa [loopDispatcherCloseoutRewindTape,
    loopDispatcherCloseoutWitnessTape, tapeAtCells,
    keepS, keepL, TapeAction.stay, TapeAction.apply,
    HeadMove.apply, Tape.move, Tape.moveLeft,
    List.append_assoc] using hrun
  done

theorem loopDispatcherCloseoutDescription_runConfig_one_finish
    (D : MachineDescription) (witness : LoopDispatcherDoneWitness)
    (hwitness : witness ∈ loopDispatcherCloseoutWitnesses D)
    (T0 T1 T2 : Tape Bool) :
    (loopDispatcherCloseoutDescription D).runConfig 1
        (ThreeTape.config
          (loopDispatcherCloseoutStateId D (.finish witness))
          T0 T1 T2) =
      ThreeTape.config
        (loopDispatcherCloseoutStateId D (.base .halt))
        T0 T1 T2 := by
  have hnext :
      loopDispatcherCloseoutNext D (.finish witness)
          (Tape.read T0) (Tape.read T1) (Tape.read T2) =
        some
          { target := .base .halt
            action0 := keepS
            action1 := keepS
            action2 := keepS } := by
    rfl
  have hrun :=
    loopDispatcherCloseoutDescription_runConfig_one D
      (.finish witness)
      (finish_mem_loopDispatcherCloseoutStates hwitness)
      T0 T1 T2
      { target := .base .halt
        action0 := keepS
        action1 := keepS
        action2 := keepS }
      hnext
  simpa [keepS, TapeAction.stay, TapeAction.apply,
    HeadMove.apply] using hrun
  done

/-!
## Complete endpoint closeout
-/

/-- Exact number of rows from a dispatcher done endpoint through the witness
emitter and into the common halt. -/
def loopDispatcherCloseoutSteps
    (witness : LoopDispatcherDoneWitness) : Nat :=
  2 * witness.bits.length + 5

/-- Shared closeout after the branch-specific done row has reached the
{lit}`skip` control. -/
theorem loopDispatcherCloseoutDescription_runConfig_from_skip
    (D : MachineDescription) (witness : LoopDispatcherDoneWitness)
    (hwitness : witness ∈ loopDispatcherCloseoutWitnesses D)
    (T0 T1 : Tape Bool) (L : SimulatorLayout) (hit : Bool) :
    (loopDispatcherCloseoutDescription D).runConfig
        (2 * witness.bits.length + 4)
        (ThreeTape.config
          (loopDispatcherCloseoutStateId D (.skip witness))
          T0 T1 (loopDispatcherCloseoutSeparatorTape L hit)) =
      ThreeTape.config
        (loopDispatcherCloseoutStateId D (.base .halt))
        T0 T1 (loopDispatcherCloseoutWitnessTape L hit witness) := by
  rw [show 2 * witness.bits.length + 4 =
      1 + (witness.bits.length +
        (1 + (witness.bits.length + (1 + 1)))) by lia]
  rw [Structured.Description.runConfig_add]
  rw [loopDispatcherCloseoutDescription_runConfig_one_skip
    D witness hwitness T0 T1 L hit]
  rw [Structured.Description.runConfig_add]
  rw [loopDispatcherCloseoutDescription_runConfig_emit
    D witness hwitness witness.bits []
    (self_mem_closeoutSuffixes witness.bits)
    (by simp) T0 T1 L hit]
  rw [Structured.Description.runConfig_add]
  rw [loopDispatcherCloseoutDescription_runConfig_one_emit_nil
    D witness hwitness T0 T1 L hit]
  rw [show witness.bits.length = witness.bits.reverse.length by simp]
  rw [Structured.Description.runConfig_add]
  rw [loopDispatcherCloseoutDescription_runConfig_rewind
    D witness hwitness witness.bits.reverse []
    (self_mem_closeoutSuffixes witness.bits.reverse)
    T0 T1 L hit]
  simp
  rw [show 2 = 1 + 1 by rfl]
  rw [Structured.Description.runConfig_add]
  rw [loopDispatcherCloseoutDescription_runConfig_one_rewind_nil
    D witness hwitness T0 T1 L hit]
  exact loopDispatcherCloseoutDescription_runConfig_one_finish
    D witness hwitness T0 T1
      (loopDispatcherCloseoutWitnessTape L hit witness)
  done

theorem loopDispatcherCloseoutDescription_runConfig_known_done
    (D : MachineDescription) (state : Nat)
    (hstate : state ∈ fixedStepValues D)
    (T0 T1 : Tape Bool) (L : SimulatorLayout) (hit : Bool) :
    (loopDispatcherCloseoutDescription D).runConfig
        (loopDispatcherCloseoutSteps (.known state))
        (ThreeTape.config
          ((loopDispatcherTable D).stateId (.known (.done state)))
          T0 T1 (loopDispatcherHitTape L hit)) =
      ThreeTape.config
        (loopDispatcherCloseoutStateId D (.base .halt))
        T0 T1
        (loopDispatcherCloseoutWitnessTape L hit (.known state)) := by
  rw [show loopDispatcherCloseoutSteps (.known state) =
      1 + (2 * (LoopDispatcherDoneWitness.known state).bits.length + 4) by
    unfold loopDispatcherCloseoutSteps
    lia]
  rw [Structured.Description.runConfig_add]
  rw [loopDispatcherCloseoutDescription_runConfig_one_known_done
    D state hstate T0 T1 L hit]
  exact loopDispatcherCloseoutDescription_runConfig_from_skip
    D (.known state)
      (known_mem_loopDispatcherCloseoutWitnesses hstate)
      T0 T1 L hit
  done

theorem loopDispatcherCloseoutDescription_runConfig_other_done
    (D : MachineDescription) (T0 T1 : Tape Bool)
    (L : SimulatorLayout) (hit : Bool) :
    (loopDispatcherCloseoutDescription D).runConfig
        (loopDispatcherCloseoutSteps .other)
        (ThreeTape.config
          ((loopDispatcherTable D).stateId (.other .done))
          T0 T1 (loopDispatcherHitTape L hit)) =
      ThreeTape.config
        (loopDispatcherCloseoutStateId D (.base .halt))
        T0 T1 (loopDispatcherCloseoutWitnessTape L hit .other) := by
  rw [show loopDispatcherCloseoutSteps .other =
      1 + (2 * LoopDispatcherDoneWitness.other.bits.length + 4) by
    unfold loopDispatcherCloseoutSteps
    lia]
  rw [Structured.Description.runConfig_add]
  rw [loopDispatcherCloseoutDescription_runConfig_one_other_done
    D T0 T1 L hit]
  exact loopDispatcherCloseoutDescription_runConfig_from_skip
    D .other (other_mem_loopDispatcherCloseoutWitnesses D)
      T0 T1 L hit
  done

/-- The exact semantic dispatcher endpoint closes to the requested witness
tapes.  The source is intentionally the classified endpoint, not the fixed
description start. -/
theorem loopDispatcherCloseoutDescription_runConfig_endpoint
    (D : MachineDescription) (L : SimulatorLayout) :
    (loopDispatcherCloseoutDescription D).runConfig
        (loopDispatcherCloseoutSteps (loopDispatcherDoneWitness D L))
        (loopDispatcherEndpointConfig D L) =
      { state := (loopDispatcherCloseoutDescription D).halt
        tapes := loopDispatcherDoneWitnessTapes D L } := by
  by_cases hstate : L.config.state ∈ fixedStepValues D
  · have hclass := classifyState_of_mem hstate
    have hfinal :
        (SimulatorLayout.run D L.stage L).config.state ∈
          fixedStepValues D := by
      rw [← RunConfigEmitterTheory.iterateStep_seedHit_eq_run]
      exact iterateStep_config_state_mem_fixedStepValues D
        (RunConfigEmitterTheory.seedHit D L)
        (by simpa [RunConfigEmitterTheory.seedHit] using hstate)
        L.stage
    have hrun :=
      loopDispatcherCloseoutDescription_runConfig_known_done D
        (SimulatorLayout.run D L.stage L).config.state hfinal
        (SimulatorLayout.run D L.stage L).config.tape
        (loopDispatcherConsumedStageCounterTape L.stage)
        L (SimulatorLayout.run D L.stage L).hit
    simpa [loopDispatcherEndpointConfig,
      loopDispatcherEndpointState, loopDispatcherDoneWitness,
      loopDispatcherDoneWitnessTapes,
      loopDispatcherDoneWitnessTape,
      loopDispatcherCloseoutWitnessTape,
      loopDispatcherCloseoutDescription,
      loopDispatcherCloseoutTable,
      ThreeTape.config,
      hclass] using hrun
  · have hclass := classifyState_of_not_mem hstate
    have hrun :=
      loopDispatcherCloseoutDescription_runConfig_other_done D
        (SimulatorLayout.run D L.stage L).config.tape
        (loopDispatcherConsumedStageCounterTape L.stage)
        L (SimulatorLayout.run D L.stage L).hit
    simpa [loopDispatcherEndpointConfig,
      loopDispatcherEndpointState, loopDispatcherDoneWitness,
      loopDispatcherDoneWitnessTapes,
      loopDispatcherDoneWitnessTape,
      loopDispatcherCloseoutWitnessTape,
      loopDispatcherCloseoutDescription,
      loopDispatcherCloseoutTable,
      ThreeTape.config,
      hclass] using hrun
  done

theorem loopDispatcherCloseoutDescription_haltsWithTapes
    (D : MachineDescription) (L : SimulatorLayout) :
    (loopDispatcherCloseoutDescription D).HaltsWithTapes
      (loopDispatcherEndpointConfig D L)
      (loopDispatcherDoneWitnessTapes D L) := by
  exact
    ⟨loopDispatcherCloseoutSteps (loopDispatcherDoneWitness D L),
      loopDispatcherCloseoutDescription_runConfig_endpoint D L⟩
  done

/-- The concrete finite table discharges the exact closeout specification. -/
theorem loopDispatcherCloseoutDescription_spec
    (D : MachineDescription) :
    LoopDispatcherDoneWitnessCloseoutSpec D
      (loopDispatcherCloseoutDescription D) := by
  exact
    ⟨loopDispatcherCloseoutDescription_wellFormed D,
      loopDispatcherCloseoutDescription_haltTransitionFree D,
      loopDispatcherCloseoutDescription_supportsReadWriteRows3 D,
      loopDispatcherCloseoutDescription_haltsWithTapes D⟩
  done

/-- The combined typed dispatcher/closeout table supplies the done-witness
closeout obligation. -/
theorem loopDispatcherDoneWitnessCloseoutObligation :
    LoopDispatcherDoneWitnessCloseoutObligation := by
  intro D
  exact
    ⟨loopDispatcherCloseoutDescription D,
      loopDispatcherCloseoutDescription_spec D⟩
  done

/-- Safe composition seam for the entry selector.  The source is
the L-dependent classified configuration; no claim is made that it is the
fixed description start. -/
theorem loopDispatcherCloseoutDescription_safe_splice
    (D : MachineDescription) (L : SimulatorLayout) (prefixSteps : Nat)
    (hprefix :
      (loopDispatcherCloseoutDescription D).runConfig prefixSteps
          (loopDispatcherSourceConfig D L) =
        loopDispatcherEndpointConfig D L) :
    (loopDispatcherCloseoutDescription D).runConfig
        (prefixSteps +
          loopDispatcherCloseoutSteps (loopDispatcherDoneWitness D L))
        (loopDispatcherSourceConfig D L) =
      { state := (loopDispatcherCloseoutDescription D).halt
        tapes := loopDispatcherDoneWitnessTapes D L } := by
  rw [Structured.Description.runConfig_add]
  rw [hprefix]
  exact loopDispatcherCloseoutDescription_runConfig_endpoint D L
  done

end RunConfigEmitterCore
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC

import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.MasterLoop
import FoC.Computability.Compiler.Structured.Lowering.DivergenceTransfer

set_option doc.verso true

/-!
# Master-loop progress

Every active master-loop transition changes state or moves at least one logical tape head, yielding divergence transfer for the lowered machine.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape

namespace BoundedFuelPairSearch
namespace U12MasterProgress

open StructuredConstructionTargets
open StructuredConstructionTargets.FuelSimulatorCore
open StructuredConstructionTargets.FusedLayoutEmission
open StructuredConstructionTargets.RawLayoutPreparation

theorem rawLayoutPreparation_next_progress
    (state : RawLayoutPreparation.State)
    (r0 r1 r2 : Option Bool)
    (st : TypedStep RawLayoutPreparation.State)
    (hnext : RawLayoutPreparation.next state r0 r1 r2 = some st) :
    st.target ≠ state \/
      st.action0.move ≠ HeadMove.stay \/
        st.action1.move ≠ HeadMove.stay \/
          st.action2.move ≠ HeadMove.stay := by
  cases state <;> simp only [RawLayoutPreparation.next] at hnext
  all_goals repeat' split at hnext
  all_goals try simp only [RawLayoutPreparation.step] at hnext
  all_goals try cases hnext
  all_goals simp [keepS, keepL, keepR, eraseL, TapeAction.stay]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem fuelSimulatorCore_next_progress
    (start : Nat) (state : FuelSimulatorCore.State)
    (r0 r1 r2 : Option Bool)
    (st : TypedStep FuelSimulatorCore.State)
    (hnext : FuelSimulatorCore.next start state r0 r1 r2 = some st) :
    st.target ≠ state \/
      st.action0.move ≠ HeadMove.stay \/
        st.action1.move ≠ HeadMove.stay \/
          st.action2.move ≠ HeadMove.stay := by
  cases state
  all_goals simp only [FuelSimulatorCore.next] at hnext
  all_goals repeat' split at hnext
  all_goals try simp only [FuelSimulatorCore.copyBit,
    FuelSimulatorCore.stream, FuelSimulatorCore.step] at hnext
  all_goals try cases hnext
  all_goals simp [keepS, keepL, keepR, FuelSimulatorCore.emitAction,
    FuelSimulatorCore.flushAction, delayedLeftEmitAction,
    delayedLeftFlushAction, TapeAction.stay]

theorem fusedNext_progress
    (start : Nat) (state : FusedLayoutEmission.FusedState)
    (r0 r1 r2 : Option Bool)
    (st : TypedStep FusedLayoutEmission.FusedState)
    (hnext : FusedLayoutEmission.fusedNext start state r0 r1 r2 = some st) :
    st.target ≠ state \/
      st.action0.move ≠ HeadMove.stay \/
        st.action1.move ≠ HeadMove.stay \/
          st.action2.move ≠ HeadMove.stay := by
  cases state with
  | inl state =>
      by_cases hhalt : state = RawLayoutPreparation.State.halt
      · change (if state = RawLayoutPreparation.State.halt then _ else _) =
          some st at hnext
        rw [if_pos hhalt] at hnext
        injection hnext with hst
        subst st
        simp
      · change (if state = RawLayoutPreparation.State.halt then _ else _) =
          some st at hnext
        rw [if_neg hhalt] at hnext
        cases hlocal : RawLayoutPreparation.next state r0 r1 r2 with
        | none => rw [hlocal] at hnext; simp at hnext
        | some localStep =>
            rw [hlocal] at hnext
            simp only [Option.map_some] at hnext
            injection hnext with hst
            subst st
            rcases localStep with ⟨target, a0, a1, a2⟩
            change Sum.inl target ≠ Sum.inl state \/
              a0.move ≠ HeadMove.stay \/
                a1.move ≠ HeadMove.stay \/ a2.move ≠ HeadMove.stay
            simpa using rawLayoutPreparation_next_progress
              state r0 r1 r2 ⟨target, a0, a1, a2⟩ hlocal
  | inr state =>
      change
        (FuelSimulatorCore.next start state r0 r1 r2).map
            (fun x =>
              ⟨Sum.inr x.target, x.action0,
                x.action1, x.action2⟩) = some st at hnext
      cases hlocal : FuelSimulatorCore.next start state r0 r1 r2 with
      | none => rw [hlocal] at hnext; simp at hnext
      | some localStep =>
          rw [hlocal] at hnext
          simp only [Option.map_some] at hnext
          injection hnext with hst
          subst st
          rcases localStep with ⟨target, a0, a1, a2⟩
          change Sum.inr target ≠ Sum.inr state \/
            a0.move ≠ HeadMove.stay \/
              a1.move ≠ HeadMove.stay \/ a2.move ≠ HeadMove.stay
          simpa using fuelSimulatorCore_next_progress start state r0 r1 r2
            ⟨target, a0, a1, a2⟩ hlocal

theorem tape01Swap_next_progress
    {sigma : Type} (M : TypedStateTable sigma)
    (hprogress : forall state r0 r1 r2 (st : TypedStep sigma),
      M.next state r0 r1 r2 = some st ->
        st.target ≠ state \/
          st.action0.move ≠ HeadMove.stay \/
            st.action1.move ≠ HeadMove.stay \/
              st.action2.move ≠ HeadMove.stay)
    (state : sigma) (r0 r1 r2 : Option Bool) (st : TypedStep sigma)
    (hnext : Tape01Swap.next M state r0 r1 r2 = some st) :
    st.target ≠ state \/
      st.action0.move ≠ HeadMove.stay \/
        st.action1.move ≠ HeadMove.stay \/
          st.action2.move ≠ HeadMove.stay := by
  unfold Tape01Swap.next at hnext
  cases hlocal : M.next state r1 r0 r2 with
  | none => rw [hlocal] at hnext; simp at hnext
  | some localStep =>
      rw [hlocal] at hnext
      simp only [Option.map_some] at hnext
      injection hnext with hst
      subst st
      rcases localStep with ⟨target, a0, a1, a2⟩
      change target ≠ state \/
        a1.move ≠ HeadMove.stay \/
          a0.move ≠ HeadMove.stay \/ a2.move ≠ HeadMove.stay
      rcases hprogress state r1 r0 r2 ⟨target, a0, a1, a2⟩ hlocal with
        htarget | hmove0 | hmove1 | hmove2
      · exact Or.inl htarget
      · exact Or.inr (Or.inr (Or.inl hmove0))
      · exact Or.inr (Or.inl hmove1)
      · exact Or.inr (Or.inr (Or.inr hmove2))

theorem mappedNext_progress
    {sigma tau : Type} (f : sigma -> tau) (hf : Function.Injective f)
    (localNext : sigma -> Option Bool -> Option Bool -> Option Bool ->
      Option (TypedStep sigma))
    (hprogress : forall state r0 r1 r2 (st : TypedStep sigma),
      localNext state r0 r1 r2 = some st ->
        st.target ≠ state \/
          st.action0.move ≠ HeadMove.stay \/
            st.action1.move ≠ HeadMove.stay \/
              st.action2.move ≠ HeadMove.stay)
    (state : sigma) (r0 r1 r2 : Option Bool) (st : TypedStep tau)
    (hnext : (localNext state r0 r1 r2).map
      (U12PhaseFusion.mapStep f) = some st) :
    st.target ≠ f state \/
      st.action0.move ≠ HeadMove.stay \/
        st.action1.move ≠ HeadMove.stay \/
          st.action2.move ≠ HeadMove.stay := by
  cases hlocal : localNext state r0 r1 r2 with
  | none => rw [hlocal] at hnext; simp at hnext
  | some localStep =>
      rw [hlocal] at hnext
      simp only [Option.map_some] at hnext
      injection hnext with hst
      subst st
      rcases localStep with ⟨target, a0, a1, a2⟩
      change f target ≠ f state \/
        a0.move ≠ HeadMove.stay \/
          a1.move ≠ HeadMove.stay \/ a2.move ≠ HeadMove.stay
      rcases hprogress state r0 r1 r2 ⟨target, a0, a1, a2⟩ hlocal with
        htarget | hmove0 | hmove1 | hmove2
      · exact Or.inl (fun heq => htarget (hf heq))
      · exact Or.inr (Or.inl hmove0)
      · exact Or.inr (Or.inr (Or.inl hmove1))
      · exact Or.inr (Or.inr (Or.inr hmove2))

theorem swappedFusedNext_progress
    (start : Nat) (state : FusedLayoutEmission.FusedState)
    (r0 r1 r2 : Option Bool)
    (st : TypedStep FusedLayoutEmission.FusedState)
    (hnext : (SwappedLayoutEmission.swappedFusedTable start).next
      state r0 r1 r2 = some st) :
    st.target ≠ state \/
      st.action0.move ≠ HeadMove.stay \/
        st.action1.move ≠ HeadMove.stay \/
          st.action2.move ≠ HeadMove.stay := by
  exact tape01Swap_next_progress (FusedLayoutEmission.fusedTable start)
    (fusedNext_progress start) state r0 r1 r2 st hnext

set_option maxRecDepth 10000 in
theorem zeroBootstrap_next_progress
    (state : U12ZeroBootstrap.State) (r0 r1 r2 : Option Bool)
    (st : TypedStep U12ZeroBootstrap.State)
    (hnext : U12ZeroBootstrap.next state r0 r1 r2 = some st) :
    st.target ≠ state \/
      st.action0.move ≠ HeadMove.stay \/
        st.action1.move ≠ HeadMove.stay \/
          st.action2.move ≠ HeadMove.stay := by
  cases state
  all_goals simp only [U12ZeroBootstrap.next] at hnext
  all_goals repeat' split at hnext
  all_goals try simp only [U12ZeroBootstrap.step] at hnext
  all_goals try cases hnext
  all_goals simp [keepS, keepL, keepR, writeBitR,
    eraseR, TapeAction.stay]

theorem hitBranch_next_progress
    (b : Bool) (state : U12HitBranch.State)
    (r0 r1 r2 : Option Bool) (st : TypedStep U12HitBranch.State)
    (hnext : U12HitBranch.next b state r0 r1 r2 = some st) :
    st.target ≠ state \/
      st.action0.move ≠ HeadMove.stay \/
        st.action1.move ≠ HeadMove.stay \/
          st.action2.move ≠ HeadMove.stay := by
  cases state
  all_goals simp only [U12HitBranch.next] at hnext
  all_goals repeat' split at hnext
  all_goals try simp only [U12HitBranch.step] at hnext
  all_goals try cases hnext
  all_goals simp [keepS, keepL, writeBitR,
    eraseL, TapeAction.stay]

theorem persistentRestaging_next_progress
    (state : PersistentRestaging.State)
    (r0 r1 r2 : Option Bool) (st : TypedStep PersistentRestaging.State)
    (hnext : PersistentRestaging.next state r0 r1 r2 = some st) :
    st.target ≠ state \/
      st.action0.move ≠ HeadMove.stay \/
        st.action1.move ≠ HeadMove.stay \/
          st.action2.move ≠ HeadMove.stay := by
  cases state
  all_goals simp only [PersistentRestaging.next] at hnext
  all_goals repeat' split at hnext
  all_goals try simp only [PersistentRestaging.step] at hnext
  all_goals try cases hnext
  all_goals simp [keepS, keepL, keepR, writeBitL,
    eraseR, TapeAction.stay]

set_option maxRecDepth 10000 in
theorem diagonalAdvance_next_progress
    (state : U12DiagonalAdvance.State)
    (r0 r1 r2 : Option Bool) (st : TypedStep U12DiagonalAdvance.State)
    (hnext : U12DiagonalAdvance.next state r0 r1 r2 = some st) :
    st.target ≠ state \/
      st.action0.move ≠ HeadMove.stay \/
        st.action1.move ≠ HeadMove.stay \/
          st.action2.move ≠ HeadMove.stay := by
  cases state
  all_goals simp only [U12DiagonalAdvance.next] at hnext
  all_goals repeat' split at hnext
  all_goals try simp only [U12DiagonalAdvance.step2] at hnext
  all_goals try cases hnext
  all_goals simp [keepS, keepL, keepR, writeBitL, TapeAction.stay]

set_option maxRecDepth 10000 in
theorem candidateRollover_next_progress
    (state : U12CandidateRollover.State)
    (r0 r1 r2 : Option Bool) (st : TypedStep U12CandidateRollover.State)
    (hnext : U12CandidateRollover.next state r0 r1 r2 = some st) :
    st.target ≠ state \/
      st.action0.move ≠ HeadMove.stay \/
        st.action1.move ≠ HeadMove.stay \/
          st.action2.move ≠ HeadMove.stay := by
  cases state
  all_goals simp only [U12CandidateRollover.next] at hnext
  all_goals repeat' split at hnext
  all_goals try simp only [U12CandidateRollover.step] at hnext
  all_goals try cases hnext
  all_goals simp [keepS, keepL, keepR, writeBitL, writeBitR,
    eraseL, TapeAction.stay]

set_option maxRecDepth 10000 in
theorem sourceRollover_next_progress
    (state : U12SourceRollover.State)
    (r0 r1 r2 : Option Bool) (st : TypedStep U12SourceRollover.State)
    (hnext : U12SourceRollover.next state r0 r1 r2 = some st) :
    st.target ≠ state \/
      st.action0.move ≠ HeadMove.stay \/
        st.action1.move ≠ HeadMove.stay \/
          st.action2.move ≠ HeadMove.stay := by
  cases state
  all_goals simp only [U12SourceRollover.next] at hnext
  all_goals repeat' split at hnext
  all_goals try simp only [U12SourceRollover.step] at hnext
  all_goals try cases hnext
  all_goals simp [keepS, keepL, keepR, writeBitL, writeBitR,
    eraseR, TapeAction.stay]

set_option maxRecDepth 10000 in
theorem checkerRollover_next_progress
    (state : U12CheckerRollover.State)
    (r0 r1 r2 : Option Bool) (st : TypedStep U12CheckerRollover.State)
    (hnext : U12CheckerRollover.next state r0 r1 r2 = some st) :
    st.target ≠ state \/
      st.action0.move ≠ HeadMove.stay \/
        st.action1.move ≠ HeadMove.stay \/
          st.action2.move ≠ HeadMove.stay := by
  cases state
  all_goals simp only [U12CheckerRollover.next] at hnext
  all_goals repeat' split at hnext
  all_goals try simp only [U12CheckerRollover.step] at hnext
  all_goals try cases hnext
  all_goals simp [keepS, keepL, keepR, writeBitL, writeBitR,
    eraseR, TapeAction.stay]

theorem positiveState_eq_positive_implies
    (target state : U12DiagonalAdvance.State)
    (h : U12DispatchBootstrap.positiveState target =
      U12DispatchBootstrap.State.positive state) :
    target = state := by
  cases target <;> simp [U12DispatchBootstrap.positiveState] at h ⊢
  all_goals exact h

theorem candidateState_eq_candidate_implies
    (target state : U12CandidateRollover.State)
    (h : U12DispatchBootstrap.candidateState target =
      U12DispatchBootstrap.State.candidate state) :
    target = state := by
  cases target <;> simp [U12DispatchBootstrap.candidateState] at h ⊢
  all_goals exact h

theorem sourceState_eq_source_implies
    (target state : U12SourceRollover.State)
    (h : U12DispatchBootstrap.sourceState target =
      U12DispatchBootstrap.State.source state) :
    target = state := by
  cases target <;> simp [U12DispatchBootstrap.sourceState] at h ⊢
  all_goals exact h

theorem checkerState_eq_checker_implies
    (target state : U12CheckerRollover.State)
    (h : U12DispatchBootstrap.checkerState target =
      U12DispatchBootstrap.State.checker state) :
    target = state := by
  cases target <;> simp [U12DispatchBootstrap.checkerState] at h ⊢
  all_goals exact h

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem dispatchBootstrap_next_progress
    (state : U12DispatchBootstrap.State)
    (r0 r1 r2 : Option Bool) (st : TypedStep U12DispatchBootstrap.State)
    (hnext : U12DispatchBootstrap.next state r0 r1 r2 = some st) :
    st.target ≠ state \/
      st.action0.move ≠ HeadMove.stay \/
        st.action1.move ≠ HeadMove.stay \/
          st.action2.move ≠ HeadMove.stay := by
  cases state
  all_goals simp only [U12DispatchBootstrap.next] at hnext
  all_goals repeat' split at hnext
  all_goals try simp only [U12DispatchBootstrap.step] at hnext
  all_goals try cases hnext
  all_goals try simp [keepS, keepL, keepR, TapeAction.stay]
  case positive state =>
    cases hlocal : U12DiagonalAdvance.next state r0 r1 r2 with
    | none => rw [hlocal] at hnext; simp at hnext
    | some localStep =>
        rw [hlocal] at hnext
        simp only [Option.map_some] at hnext
        injection hnext with hst
        subst st
        rcases localStep with ⟨target, a0, a1, a2⟩
        change U12DispatchBootstrap.positiveState target ≠
            U12DispatchBootstrap.State.positive state \/
          a0.move ≠ HeadMove.stay \/
            a1.move ≠ HeadMove.stay \/ a2.move ≠ HeadMove.stay
        rcases diagonalAdvance_next_progress state r0 r1 r2
            ⟨target, a0, a1, a2⟩ hlocal with
          htarget | hmove0 | hmove1 | hmove2
        · left
          intro heq
          exact htarget (positiveState_eq_positive_implies target state heq)
        · exact Or.inr (Or.inl hmove0)
        · exact Or.inr (Or.inr (Or.inl hmove1))
        · exact Or.inr (Or.inr (Or.inr hmove2))
  case candidate state =>
    cases hlocal : U12CandidateRollover.next state r0 r1 r2 with
    | none => rw [hlocal] at hnext; simp at hnext
    | some localStep =>
        rw [hlocal] at hnext
        simp only [Option.map_some] at hnext
        injection hnext with hst
        subst st
        rcases localStep with ⟨target, a0, a1, a2⟩
        change U12DispatchBootstrap.candidateState target ≠
            U12DispatchBootstrap.State.candidate state \/
          a0.move ≠ HeadMove.stay \/
            a1.move ≠ HeadMove.stay \/ a2.move ≠ HeadMove.stay
        rcases candidateRollover_next_progress state r0 r1 r2
            ⟨target, a0, a1, a2⟩ hlocal with
          htarget | hmove0 | hmove1 | hmove2
        · left
          intro heq
          exact htarget (candidateState_eq_candidate_implies target state heq)
        · exact Or.inr (Or.inl hmove0)
        · exact Or.inr (Or.inr (Or.inl hmove1))
        · exact Or.inr (Or.inr (Or.inr hmove2))
  case source state =>
    cases hlocal : U12SourceRollover.next state r0 r1 r2 with
    | none => rw [hlocal] at hnext; simp at hnext
    | some localStep =>
        rw [hlocal] at hnext
        simp only [Option.map_some] at hnext
        injection hnext with hst
        subst st
        rcases localStep with ⟨target, a0, a1, a2⟩
        change U12DispatchBootstrap.sourceState target ≠
            U12DispatchBootstrap.State.source state \/
          a0.move ≠ HeadMove.stay \/
            a1.move ≠ HeadMove.stay \/ a2.move ≠ HeadMove.stay
        rcases sourceRollover_next_progress state r0 r1 r2
            ⟨target, a0, a1, a2⟩ hlocal with
          htarget | hmove0 | hmove1 | hmove2
        · left
          intro heq
          exact htarget (sourceState_eq_source_implies target state heq)
        · exact Or.inr (Or.inl hmove0)
        · exact Or.inr (Or.inr (Or.inl hmove1))
        · exact Or.inr (Or.inr (Or.inr hmove2))
  case checker state =>
    cases hlocal : U12CheckerRollover.next state r0 r1 r2 with
    | none => rw [hlocal] at hnext; simp at hnext
    | some localStep =>
        rw [hlocal] at hnext
        simp only [Option.map_some] at hnext
        injection hnext with hst
        subst st
        rcases localStep with ⟨target, a0, a1, a2⟩
        change U12DispatchBootstrap.checkerState target ≠
            U12DispatchBootstrap.State.checker state \/
          a0.move ≠ HeadMove.stay \/
            a1.move ≠ HeadMove.stay \/ a2.move ≠ HeadMove.stay
        rcases checkerRollover_next_progress state r0 r1 r2
            ⟨target, a0, a1, a2⟩ hlocal with
          htarget | hmove0 | hmove1 | hmove2
        · left
          intro heq
          exact htarget (checkerState_eq_checker_implies target state heq)
        · exact Or.inr (Or.inl hmove0)
        · exact Or.inr (Or.inr (Or.inl hmove1))
        · exact Or.inr (Or.inr (Or.inr hmove2))

theorem tape2SubroutineLift_next_progress
    (D : MachineDescription) (state : Nat)
    (r0 r1 r2 : Option Bool) (st : TypedStep Nat)
    (hnext : Tape2SubroutineLift.next D state r0 r1 r2 = some st) :
    st.target ≠ state \/
      st.action0.move ≠ HeadMove.stay \/
        st.action1.move ≠ HeadMove.stay \/
          st.action2.move ≠ HeadMove.stay := by
  unfold Tape2SubroutineLift.next at hnext
  cases hlookup : D.lookupTransition state r2 with
  | none => simp [hlookup] at hnext
  | some transition =>
      rw [hlookup] at hnext
      injection hnext with hst
      subst st
      right
      right
      right
      cases transition.move <;>
        simp [Tape2SubroutineLift.headMoveOfDirection]

set_option maxRecDepth 10000 in
theorem master_next_progress
    (source sourceSimulator recognizer checkerSimulator : MachineDescription)
    (b : Bool)
    (hsourceSimulator : sourceSimulator.SubroutineReady)
    (hcheckerSimulator : checkerSimulator.SubroutineReady)
    (state : U12MasterLoop.State) (r0 r1 r2 : Option Bool)
    (st : TypedStep U12MasterLoop.State)
    (hnext : U12MasterLoop.next source sourceSimulator recognizer
      checkerSimulator b hsourceSimulator hcheckerSimulator
      state r0 r1 r2 = some st) :
    st.target ≠ state \/
      st.action0.move ≠ HeadMove.stay \/
        st.action1.move ≠ HeadMove.stay \/
          st.action2.move ≠ HeadMove.stay := by
  cases state with
  | bootstrap state =>
      by_cases hhalt : state = U12ZeroBootstrap.State.halt
      · change (if state = U12ZeroBootstrap.State.halt then _ else _) =
          some st at hnext
        rw [if_pos hhalt] at hnext
        injection hnext with hst
        subst st
        simp
      · change (if state = U12ZeroBootstrap.State.halt then _ else _) =
          some st at hnext
        rw [if_neg hhalt] at hnext
        exact mappedNext_progress U12MasterLoop.State.bootstrap
          (by intro a c hac; injection hac)
          U12ZeroBootstrap.table.next
          (by
            intro s p0 p1 p2 step hstep
            exact zeroBootstrap_next_progress s p0 p1 p2 step hstep)
          state r0 r1 r2 st hnext
  | sourceEmit state =>
      by_cases hhalt : state =
          (FusedLayoutEmission.fusedTable source.start).halt
      · change (if state =
            (FusedLayoutEmission.fusedTable source.start).halt then _ else _) =
          some st at hnext
        rw [if_pos hhalt] at hnext
        injection hnext with hst
        subst st
        simp
      · change (if state =
            (FusedLayoutEmission.fusedTable source.start).halt then _ else _) =
          some st at hnext
        rw [if_neg hhalt] at hnext
        exact mappedNext_progress U12MasterLoop.State.sourceEmit
          (by intro a c hac; injection hac)
          (FusedLayoutEmission.fusedTable source.start).next
          (by
            intro s p0 p1 p2 step hstep
            exact fusedNext_progress source.start s p0 p1 p2 step hstep)
          state r0 r1 r2 st hnext
  | sourceSim state =>
      let phase := Tape2SubroutineLift.table
        sourceSimulator hsourceSimulator
      by_cases hhalt : state = phase.halt
      · change (if state = phase.halt then _ else _) = some st at hnext
        rw [if_pos hhalt] at hnext
        injection hnext with hst
        subst st
        simp
      · change (if state = phase.halt then _ else _) = some st at hnext
        rw [if_neg hhalt] at hnext
        exact mappedNext_progress U12MasterLoop.State.sourceSim
          (by intro a c hac; injection hac)
          phase.next
          (by
            intro s p0 p1 p2 step hstep
            exact tape2SubroutineLift_next_progress sourceSimulator
              s p0 p1 p2 step hstep)
          state r0 r1 r2 st hnext
  | checkerEmit state =>
      let phase := SwappedLayoutEmission.swappedFusedTable recognizer.start
      by_cases hhalt : state = phase.halt
      · change (if state = phase.halt then _ else _) = some st at hnext
        rw [if_pos hhalt] at hnext
        injection hnext with hst
        subst st
        simp
      · change (if state = phase.halt then _ else _) = some st at hnext
        rw [if_neg hhalt] at hnext
        exact mappedNext_progress U12MasterLoop.State.checkerEmit
          (by intro a c hac; injection hac)
          phase.next
          (by
            intro s p0 p1 p2 step hstep
            exact swappedFusedNext_progress recognizer.start
              s p0 p1 p2 step hstep)
          state r0 r1 r2 st hnext
  | checkerSim state =>
      let phase := Tape2SubroutineLift.table
        checkerSimulator hcheckerSimulator
      by_cases hhalt : state = phase.halt
      · change (if state = phase.halt then _ else _) = some st at hnext
        rw [if_pos hhalt] at hnext
        injection hnext with hst
        subst st
        simp
      · change (if state = phase.halt then _ else _) = some st at hnext
        rw [if_neg hhalt] at hnext
        exact mappedNext_progress U12MasterLoop.State.checkerSim
          (by intro a c hac; injection hac)
          phase.next
          (by
            intro s p0 p1 p2 step hstep
            exact tape2SubroutineLift_next_progress checkerSimulator
              s p0 p1 p2 step hstep)
          state r0 r1 r2 st hnext
  | hitExtract state =>
      let phase := Tape2SubroutineLift.table
        SimulatorHitExtractorDescription
        simulatorHitExtractorDescription_subroutineReady
      by_cases hhalt : state = phase.halt
      · change (if state = phase.halt then _ else _) = some st at hnext
        rw [if_pos hhalt] at hnext
        injection hnext with hst
        subst st
        simp
      · change (if state = phase.halt then _ else _) = some st at hnext
        rw [if_neg hhalt] at hnext
        exact mappedNext_progress U12MasterLoop.State.hitExtract
          (by intro a c hac; injection hac)
          phase.next
          (by
            intro s p0 p1 p2 step hstep
            exact tape2SubroutineLift_next_progress
              SimulatorHitExtractorDescription s p0 p1 p2 step hstep)
          state r0 r1 r2 st hnext
  | hitBranch state =>
      by_cases hsuccess : state = U12HitBranch.State.successHalt
      · change (if state = U12HitBranch.State.successHalt then _ else _) =
          some st at hnext
        rw [if_pos hsuccess] at hnext
        injection hnext with hst
        subst st
        simp
      · by_cases hfailure : state = U12HitBranch.State.failureExit
        · change (if state = U12HitBranch.State.successHalt then _ else _) =
            some st at hnext
          rw [if_neg hsuccess, if_pos hfailure] at hnext
          injection hnext with hst
          subst st
          simp
        · change (if state = U12HitBranch.State.successHalt then _ else _) =
            some st at hnext
          rw [if_neg hsuccess, if_neg hfailure] at hnext
          exact mappedNext_progress U12MasterLoop.State.hitBranch
            (by intro a c hac; injection hac)
            (U12HitBranch.table b).next
            (by
              intro s p0 p1 p2 step hstep
              exact hitBranch_next_progress b s p0 p1 p2 step hstep)
            state r0 r1 r2 st hnext
  | restage state =>
      by_cases hhalt : state = PersistentRestaging.table.halt
      · change (if state = PersistentRestaging.table.halt then _ else _) =
          some st at hnext
        rw [if_pos hhalt] at hnext
        injection hnext with hst
        subst st
        simp
      · change (if state = PersistentRestaging.table.halt then _ else _) =
          some st at hnext
        rw [if_neg hhalt] at hnext
        exact mappedNext_progress U12MasterLoop.State.restage
          (by intro a c hac; injection hac)
          PersistentRestaging.table.next
          (by
            intro s p0 p1 p2 step hstep
            exact persistentRestaging_next_progress
              s p0 p1 p2 step hstep)
          state r0 r1 r2 st hnext
  | dispatch state =>
      by_cases hhalt : state = U12DispatchBootstrap.table.halt
      · change (if state = U12DispatchBootstrap.table.halt then _ else _) =
          some st at hnext
        rw [if_pos hhalt] at hnext
        injection hnext with hst
        subst st
        simp
      · change (if state = U12DispatchBootstrap.table.halt then _ else _) =
          some st at hnext
        rw [if_neg hhalt] at hnext
        exact mappedNext_progress U12MasterLoop.State.dispatch
          (by intro a c hac; injection hac)
          U12DispatchBootstrap.table.next
          (by
            intro s p0 p1 p2 step hstep
            exact dispatchBootstrap_next_progress s p0 p1 p2 step hstep)
          state r0 r1 r2 st hnext
  | halt => simp [U12MasterLoop.next] at hnext

theorem master_transition_changes_state_or_some_action_moves
    (source sourceSimulator recognizer checkerSimulator : MachineDescription)
    (b : Bool)
    (hsourceSimulator : sourceSimulator.SubroutineReady)
    (hcheckerSimulator : checkerSimulator.SubroutineReady) :
    let M := U12MasterLoop.table source sourceSimulator recognizer
      checkerSimulator b hsourceSimulator hcheckerSimulator
    forall tr, tr ∈ M.description.transitions ->
      exists a0 a1 a2 : TapeAction,
        tr.actions = [a0, a1, a2] ∧
          (tr.target ≠ tr.source \/
            a0.move ≠ HeadMove.stay \/
              a1.move ≠ HeadMove.stay \/
                a2.move ≠ HeadMove.stay) := by
  dsimp only
  let M := U12MasterLoop.table source sourceSimulator recognizer
    checkerSimulator b hsourceSimulator hcheckerSimulator
  intro tr htr
  rcases M.mem_transitions htr with ⟨state, hstate, hrow⟩
  rcases M.mem_rowsFor hrow with
    ⟨r0, r1, r2, st, hnext, rfl⟩
  change U12MasterLoop.next source sourceSimulator recognizer
    checkerSimulator b hsourceSimulator hcheckerSimulator
    state r0 r1 r2 = some st at hnext
  have hchange := master_next_progress source sourceSimulator recognizer
    checkerSimulator b hsourceSimulator hcheckerSimulator
    state r0 r1 r2 st hnext
  refine ⟨st.action0, st.action1, st.action2, rfl, ?_⟩
  rcases hchange with htarget | hmoves
  · left
    simp only [TypedStateTable.rowOf, ThreeTape.row]
    intro hid
    have htargetMem : st.target ∈ M.states :=
      M.next_target_mem state hstate r0 r1 r2 st hnext
    apply htarget
    exact M.stateId_inj st.target htargetMem state hstate hid
  · exact Or.inr hmoves

theorem master_stepConfig_progress
    (source sourceSimulator recognizer checkerSimulator : MachineDescription)
    (b : Bool)
    (hsourceSimulator : sourceSimulator.SubroutineReady)
    (hcheckerSimulator : checkerSimulator.SubroutineReady) :
    let M := U12MasterLoop.table source sourceSimulator recognizer
      checkerSimulator b hsourceSimulator hcheckerSimulator
    forall {a c : CommonGround.FiniteTransducers.Structured.Configuration},
      M.description.stepConfig a = some c ->
        a.state ≠ c.state \/ a.tapes ≠ c.tapes := by
  dsimp only
  let M := U12MasterLoop.table source sourceSimulator recognizer
    checkerSimulator b hsourceSimulator hcheckerSimulator
  intro a c hstep
  exact stepConfig_state_ne_or_tapes_ne_of_state_or_action_moves
    M.description_tapeCount
    (master_transition_changes_state_or_some_action_moves
      source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator)
    hstep

end U12MasterProgress
end BoundedFuelPairSearch
end Computability
end FoC

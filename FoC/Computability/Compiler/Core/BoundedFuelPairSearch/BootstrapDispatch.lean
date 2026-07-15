import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.ZeroBootstrap
import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.DispatchBootstrap
import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.FusedLayoutEmission

set_option doc.verso true

/-!
# Bootstrap-to-dispatch composition

The exact zero bootstrap hands its finite three-tape state to the rollover dispatcher.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open DovetailInitialLayoutInitializer.StageInputMarkedScanner

namespace BoundedFuelPairSearch

namespace U12ZeroBootstrap
def D : Description := table.description
end U12ZeroBootstrap

namespace U12BootstrapDispatch

open U12ZeroBootstrap
open U12DispatchBootstrap

/-- The checker-zero dispatch only inspects the finite field at the current
head of tape 1.  Its proof therefore does not need the large left padding
installed by persistent restaging. -/
theorem leads_dispatchChecker_generic
    (w : Word Bool) (padding : List (Option Bool))
    (T0 : Tape Bool) (left right : List (Option Bool)) :
    U12DispatchBootstrap.table.Leads
      (U12DispatchBootstrap.table.config .length0 T0
        (tapeAtCells left
          (none :: some false :: some false :: some true ::
            some true :: right))
        (U12DispatchBootstrap.cursorTape []
          (CandidateInputBits w 0 0) padding))
      (U12DispatchBootstrap.table.config (.checker .seekRight) T0
        (tapeAtCells left
          (none :: some false :: some false :: some true ::
            some true :: right))
        (U12DispatchBootstrap.cursorTape []
          (CandidateInputBits w 0 0) padding)) := by
  let T1 := tapeAtCells left
    (none :: some false :: some false :: some true :: some true :: right)
  change
    U12DispatchBootstrap.table.Leads
      (U12DispatchBootstrap.table.config .length0 T0 T1
        (U12DispatchBootstrap.cursorTape []
          (CandidateInputBits w 0 0) padding))
      (U12DispatchBootstrap.table.config (.checker .seekRight) T0 T1
        (U12DispatchBootstrap.cursorTape []
          (CandidateInputBits w 0 0) padding))
  apply TypedStateTable.Leads.trans
    (by
      simpa [U12DiagonalAdvance.candidateInputBits_eq_fields,
        List.append_assoc] using
        U12DispatchBootstrap.leads_prefixToLimit w
          (true :: true :: List.append (stageNatBits 0) [])
          padding T0 T1)
  apply TypedStateTable.Leads.trans
    (U12DispatchBootstrap.leads_limitZero
      (false :: false :: U12DispatchBootstrap.prefixLeftRev w)
      (stageNatBits 0) padding T0 T1)
  apply TypedStateTable.Leads.trans
    (by
      simpa [stageNatBits, encodeNat, doneBits,
        encodeCodeWordAsInput, encodeCodeSymbolAsInput] using
        U12DispatchBootstrap.leads_candidateZero
          (true :: true :: false :: false ::
            U12DispatchBootstrap.prefixLeftRev w)
          [] padding T0 T1)
  apply TypedStateTable.Leads.trans
    (by
      have hT1 :
          T1 = tapeAtCells left
            (none :: some false :: some false :: some true ::
              some true :: right) := rfl
      have hmove :
          keepR.apply T1 =
            tapeAtCells (none :: left)
              (some false :: some false :: some true :: some true :: right) := by
        rw [show T1 = tapeAtCells left
          (none :: some false :: some false :: some true ::
            some true :: right) by rfl]
        exact keepR_apply_tapeAtCells _ _ _
      have hprobe := U12DispatchBootstrap.leads_sourceProbe true left right T0
        (U12DispatchBootstrap.cursorTape
          (true :: false :: false :: true :: true :: false :: false ::
            U12DispatchBootstrap.prefixLeftRev w)
          [true] padding)
      rw [← hmove, ← hT1] at hprobe
      simpa only [U12DispatchBootstrap.sourceBranch, keepR,
        TapeAction.preserveMove] using hprobe)
  simpa [U12DispatchBootstrap.branchStart,
    U12DispatchBootstrap.prefixLeftRev,
    U12DiagonalAdvance.candidateInputBits_eq_fields,
    List.reverse_append, List.append_assoc] using
    U12DispatchBootstrap.leads_rewind .checker
      (true :: false :: false :: true :: true :: false :: false ::
        U12DispatchBootstrap.prefixLeftRev w)
      [] true padding T0 T1

abbrev State := Sum U12ZeroBootstrap.State U12DispatchBootstrap.State

private def mapBootstrapStep
    (st : TypedStep U12ZeroBootstrap.State) : TypedStep State :=
  ⟨Sum.inl st.target, st.action0, st.action1, st.action2⟩

private def mapDispatchStep
    (st : TypedStep U12DispatchBootstrap.State) : TypedStep State :=
  ⟨Sum.inr st.target, st.action0, st.action1, st.action2⟩

def next : State -> Option Bool -> Option Bool -> Option Bool ->
    Option (TypedStep State)
  | .inl state => fun r0 r1 r2 =>
      if state = U12ZeroBootstrap.State.halt then
        some ⟨Sum.inr U12DispatchBootstrap.State.length0,
          keepS, keepS, keepS⟩
      else
        (U12ZeroBootstrap.next state r0 r1 r2).map mapBootstrapStep
  | .inr state => fun r0 r1 r2 =>
      (U12DispatchBootstrap.next state r0 r1 r2).map mapDispatchStep

def states : List State :=
  List.append (U12ZeroBootstrap.states.map Sum.inl)
    (U12DispatchBootstrap.states.map Sum.inr)

theorem state_mem : forall state : State, state ∈ states
  | .inl state => by
      simpa [states] using U12ZeroBootstrap.state_mem state
  | .inr state => by
      simpa [states] using U12DispatchBootstrap.state_mem state

theorem next_target_mem :
    forall state : State, state ∈ states ->
      forall r0 r1 r2 st, next state r0 r1 r2 = some st ->
        st.target ∈ states := by
  intro state _hstate r0 r1 r2 st hnext
  cases state with
  | inl state =>
      by_cases hhalt : state = U12ZeroBootstrap.State.halt
      · simp [next, hhalt] at hnext
        subst st
        exact state_mem _
      · simp [next, hhalt] at hnext
        cases hlocal : U12ZeroBootstrap.next state r0 r1 r2 with
        | none => simp [hlocal] at hnext
        | some localStep =>
            simp [hlocal] at hnext
            subst st
            exact state_mem _
  | inr state =>
      simp [next] at hnext
      cases hlocal : U12DispatchBootstrap.next state r0 r1 r2 with
      | none => simp [hlocal] at hnext
      | some localStep =>
          simp [hlocal] at hnext
          subst st
          exact state_mem _

def table : TypedStateTable State :=
  TypedStateTable.ofList states
    (Sum.inl U12ZeroBootstrap.State.lengthScan)
    (Sum.inr U12DispatchBootstrap.State.halt)
    next (state_mem _) (state_mem _) (by intros; rfl) next_target_mem

def D : Description := table.description

set_option maxRecDepth 10000 in
theorem bridge_step (T0 T1 T2 : Tape Bool) :
    D.runConfig 1
        (table.config (Sum.inl U12ZeroBootstrap.State.halt) T0 T1 T2) =
      table.config (Sum.inr U12DispatchBootstrap.State.length0) T0 T1 T2 := by
  have hnext :
      table.next (Sum.inl U12ZeroBootstrap.State.halt)
          (Tape.read T0) (Tape.read T1) (Tape.read T2) =
        some ⟨Sum.inr U12DispatchBootstrap.State.length0,
          keepS, keepS, keepS⟩ := by
    rfl
  have h0 : keepS.apply T0 = T0 := rfl
  have h1 : keepS.apply T1 = T1 := rfl
  have h2 : keepS.apply T2 = T2 := rfl
  simpa only [D, TypedStateTable.config, Description.runConfig,
    h0, h1, h2] using
    table.runConfig_succ_config (state_mem _) hnext 0

theorem dispatch_embeds :
    U12DispatchBootstrap.TypedEmbedding.Embeds
      U12DispatchBootstrap.table table Sum.inr := by
  intro state r0 r1 r2
  rfl

theorem lift_dispatch_leads
    (source target : U12DispatchBootstrap.State)
    (T0 T1 T2 U0 U1 U2 : Tape Bool)
    (hleads :
      U12DispatchBootstrap.table.Leads
        (U12DispatchBootstrap.table.config source T0 T1 T2)
        (U12DispatchBootstrap.table.config target U0 U1 U2)) :
    table.Leads
      (table.config (Sum.inr source) T0 T1 T2)
      (table.config (Sum.inr target) U0 U1 U2) := by
  apply U12DispatchBootstrap.TypedEmbedding.lift_leads
    U12DispatchBootstrap.table table Sum.inr dispatch_embeds
    (fun state _ => state_mem (Sum.inr state))
    source target T0 T1 T2 U0 U1 U2
  · exact U12DispatchBootstrap.state_mem source
  · exact U12DispatchBootstrap.state_mem target
  · exact hleads

set_option maxRecDepth 10000 in
theorem run_bootstrap_to_bridge :
    forall (steps : Nat) (state : U12ZeroBootstrap.State),
      state ∈ U12ZeroBootstrap.table.states ->
      forall (T0 T1 T2 U0 U1 U2 : Tape Bool),
        U12ZeroBootstrap.D.runConfig steps
            (U12ZeroBootstrap.table.config state T0 T1 T2) =
          U12ZeroBootstrap.table.config U12ZeroBootstrap.State.halt
            U0 U1 U2 ->
        (forall k : Nat, k < steps ->
          (U12ZeroBootstrap.D.runConfig k
            (U12ZeroBootstrap.table.config state T0 T1 T2)).state ≠
              U12ZeroBootstrap.D.halt) ->
        D.runConfig steps
            (table.config (Sum.inl state) T0 T1 T2) =
          table.config (Sum.inl U12ZeroBootstrap.State.halt)
            U0 U1 U2 := by
  intro steps
  induction steps with
  | zero =>
      intro state hstate T0 T1 T2 U0 U1 U2 hfinal _hbefore
      change
        U12ZeroBootstrap.table.description.runConfig 0
            (ThreeTape.config (U12ZeroBootstrap.table.stateId state)
              T0 T1 T2) =
          ThreeTape.config
            (U12ZeroBootstrap.table.stateId U12ZeroBootstrap.State.halt)
            U0 U1 U2 at hfinal
      change
        table.description.runConfig 0
            (ThreeTape.config (table.stateId (Sum.inl state)) T0 T1 T2) =
          ThreeTape.config
            (table.stateId (Sum.inl U12ZeroBootstrap.State.halt))
            U0 U1 U2
      have hstateId := congrArg
        (fun c : CommonGround.FiniteTransducers.Structured.Configuration =>
          c.state) hfinal
      change U12ZeroBootstrap.table.stateId state =
        U12ZeroBootstrap.table.stateId U12ZeroBootstrap.State.halt at hstateId
      have hstateEq := U12ZeroBootstrap.table.stateId_inj
        state hstate U12ZeroBootstrap.State.halt
        U12ZeroBootstrap.table.halt_mem hstateId
      subst state
      have htapes := congrArg
        (fun c : CommonGround.FiniteTransducers.Structured.Configuration =>
          c.tapes) hfinal
      change [T0, T1, T2] = [U0, U1, U2] at htapes
      simp at htapes
      rcases htapes with ⟨rfl, rfl, rfl⟩
      rfl
  | succ steps ih =>
      intro state hstate T0 T1 T2 U0 U1 U2 hfinal hbefore
      change
        U12ZeroBootstrap.table.description.runConfig (steps + 1)
            (ThreeTape.config (U12ZeroBootstrap.table.stateId state)
              T0 T1 T2) =
          ThreeTape.config
            (U12ZeroBootstrap.table.stateId U12ZeroBootstrap.State.halt)
            U0 U1 U2 at hfinal
      change
        (forall k : Nat, k < steps + 1 ->
          (U12ZeroBootstrap.table.description.runConfig k
            (ThreeTape.config (U12ZeroBootstrap.table.stateId state)
              T0 T1 T2)).state ≠
              U12ZeroBootstrap.table.description.halt) at hbefore
      change
        table.description.runConfig (steps + 1)
            (ThreeTape.config (table.stateId (Sum.inl state)) T0 T1 T2) =
          ThreeTape.config
            (table.stateId (Sum.inl U12ZeroBootstrap.State.halt))
            U0 U1 U2
      have hsne : state ≠ U12ZeroBootstrap.State.halt := by
        intro hstateEq
        subst state
        exact hbefore 0 (Nat.succ_pos steps) rfl
      cases hnext : U12ZeroBootstrap.table.next state
          (Tape.read T0) (Tape.read T1) (Tape.read T2) with
      | none =>
          have hstepNone :=
            U12ZeroBootstrap.table.stepConfig_config_none hstate hnext
          simp only [Description.runConfig] at hfinal
          rw [hstepNone] at hfinal
          have hstateId := congrArg
            (fun c : CommonGround.FiniteTransducers.Structured.Configuration =>
              c.state) hfinal
          change U12ZeroBootstrap.table.stateId state =
            U12ZeroBootstrap.table.stateId U12ZeroBootstrap.State.halt
              at hstateId
          exact (hsne (U12ZeroBootstrap.table.stateId_inj
            state hstate U12ZeroBootstrap.State.halt
            U12ZeroBootstrap.table.halt_mem hstateId)).elim
      | some st =>
          have htarget := U12ZeroBootstrap.table.next_target_mem
            state hstate _ _ _ st hnext
          rw [U12ZeroBootstrap.table.runConfig_succ_config
            hstate hnext steps] at hfinal
          have hnextLocal := hnext
          change U12ZeroBootstrap.next state
            (Tape.read T0) (Tape.read T1) (Tape.read T2) = some st at hnextLocal
          have hcombinedNext :
              table.next (Sum.inl state)
                  (Tape.read T0) (Tape.read T1) (Tape.read T2) =
                some (mapBootstrapStep st) := by
            change next (Sum.inl state)
              (Tape.read T0) (Tape.read T1) (Tape.read T2) =
                some (mapBootstrapStep st)
            simp [next, hsne, hnextLocal]
          rw [table.runConfig_succ_config
            (state_mem (Sum.inl state)) hcombinedNext steps]
          apply ih st.target htarget
            (st.action0.apply T0) (st.action1.apply T1)
            (st.action2.apply T2) U0 U1 U2 hfinal
          intro k hk
          have h := hbefore (k + 1) (Nat.succ_lt_succ hk)
          rw [U12ZeroBootstrap.table.runConfig_succ_config
            hstate hnext k] at h
          exact h

theorem bootstrap_first_halt_run (raw : List Bool) :
    exists steps : Nat,
      U12ZeroBootstrap.D.runConfig steps
          (U12ZeroBootstrap.table.config U12ZeroBootstrap.State.lengthScan
            (Tape.input (show Word Bool from raw)) Tape.blank Tape.blank) =
        U12ZeroBootstrap.table.config U12ZeroBootstrap.State.halt
          (U12ZeroBootstrap.bootstrapFuelTape (raw.length + 2))
          (U12ZeroBootstrap.bootstrapFuelTape 1)
          (U12ZeroBootstrap.bootstrapCandidateTape raw) ∧
      forall k : Nat, k < steps ->
        (U12ZeroBootstrap.D.runConfig k
          (U12ZeroBootstrap.table.config U12ZeroBootstrap.State.lengthScan
            (Tape.input (show Word Bool from raw)) Tape.blank Tape.blank)).state ≠
          U12ZeroBootstrap.D.halt := by
  let source := U12ZeroBootstrap.table.config
    U12ZeroBootstrap.State.lengthScan
    (Tape.input (show Word Bool from raw)) Tape.blank Tape.blank
  let target := U12ZeroBootstrap.table.config U12ZeroBootstrap.State.halt
    (U12ZeroBootstrap.bootstrapFuelTape (raw.length + 2))
    (U12ZeroBootstrap.bootstrapFuelTape 1)
    (U12ZeroBootstrap.bootstrapCandidateTape raw)
  rcases (U12ZeroBootstrap.leads_initialized_to_exact_bootstrap raw).to_runConfig
    with ⟨someSteps, hsome⟩
  change U12ZeroBootstrap.D.runConfig someSteps source = target at hsome
  have hbounded : exists n : Nat, n ≤ someSteps ∧
      (U12ZeroBootstrap.D.runConfig n source).state =
        U12ZeroBootstrap.D.halt := by
    refine ⟨someSteps, Nat.le_refl _, ?_⟩
    rw [hsome]
    rfl
  rcases StructuredConstructionTargets.FusedLayoutEmission.exists_least_up_to
      someSteps hbounded with
    ⟨first, hle, hfirstState, hbefore⟩
  obtain ⟨extra, hsteps⟩ := Nat.exists_eq_add_of_le hle
  have hfirstConfig :
      U12ZeroBootstrap.D.runConfig first source = target := by
    have hstall := U12ZeroBootstrap.table.description.runConfig_halt
      U12ZeroBootstrap.table.description_haltTransitionFree
      (U12ZeroBootstrap.D.runConfig first source)
      hfirstState extra
    change U12ZeroBootstrap.D.runConfig extra
      (U12ZeroBootstrap.D.runConfig first source) =
        U12ZeroBootstrap.D.runConfig first source at hstall
    have hadd := U12ZeroBootstrap.D.runConfig_add first extra source
    rw [hstall] at hadd
    rw [hsteps] at hsome
    exact hadd.symm.trans hsome
  refine ⟨first, ?_, ?_⟩
  · exact hfirstConfig
  · intro k hk
    exact hbefore k hk

theorem leads_initialized_to_length0 (raw : List Bool) :
    table.Leads
      (table.config (Sum.inl U12ZeroBootstrap.State.lengthScan)
        (Tape.input (show Word Bool from raw)) Tape.blank Tape.blank)
      (table.config (Sum.inr U12DispatchBootstrap.State.length0)
        (U12ZeroBootstrap.bootstrapFuelTape (raw.length + 2))
        (U12ZeroBootstrap.bootstrapFuelTape 1)
        (U12ZeroBootstrap.bootstrapCandidateTape raw)) := by
  rcases bootstrap_first_halt_run raw with
    ⟨steps, hrun, hbefore⟩
  have hlift := run_bootstrap_to_bridge steps
    U12ZeroBootstrap.State.lengthScan
    U12ZeroBootstrap.table.start_mem
    (Tape.input (show Word Bool from raw)) Tape.blank Tape.blank
    (U12ZeroBootstrap.bootstrapFuelTape (raw.length + 2))
    (U12ZeroBootstrap.bootstrapFuelTape 1)
    (U12ZeroBootstrap.bootstrapCandidateTape raw)
    hrun hbefore
  exact TypedStateTable.Leads.trans
    (U12DispatchBootstrap.TypedEmbedding.leads_of_runConfig table hlift)
    (U12DispatchBootstrap.TypedEmbedding.leads_of_runConfig table
      (bridge_step
        (U12ZeroBootstrap.bootstrapFuelTape (raw.length + 2))
        (U12ZeroBootstrap.bootstrapFuelTape 1)
        (U12ZeroBootstrap.bootstrapCandidateTape raw)))

theorem bootstrapCandidateTape_eq_cursor (raw : List Bool) :
    U12ZeroBootstrap.bootstrapCandidateTape raw =
      U12DispatchBootstrap.cursorTape []
        (CandidateInputBits (show Word Bool from raw) 0 0) [none] := by
  exact (U12ZeroBootstrap.bootstrapCandidateTape_eq_restaged raw).trans
    (U12DispatchBootstrap.cursorTape_singleton_eq_restagedRawTape _).symm

theorem leads_initialized_to_checkerStart (raw : List Bool) :
    table.Leads
      (table.config (Sum.inl U12ZeroBootstrap.State.lengthScan)
        (Tape.input (show Word Bool from raw)) Tape.blank Tape.blank)
      (table.config
        (Sum.inr (U12DispatchBootstrap.State.checker
          U12CheckerRollover.State.seekRight))
        (U12ZeroBootstrap.bootstrapFuelTape (raw.length + 2))
        (U12ZeroBootstrap.bootstrapFuelTape 1)
        (U12ZeroBootstrap.bootstrapCandidateTape raw)) := by
  apply TypedStateTable.Leads.trans (leads_initialized_to_length0 raw)
  have hdispatch := leads_dispatchChecker_generic
    (show Word Bool from raw) [none]
    (U12ZeroBootstrap.bootstrapFuelTape (raw.length + 2)) [none] [none]
  have hlift := lift_dispatch_leads
    U12DispatchBootstrap.State.length0
    (U12DispatchBootstrap.State.checker U12CheckerRollover.State.seekRight)
    (U12ZeroBootstrap.bootstrapFuelTape (raw.length + 2))
    (U12ZeroBootstrap.bootstrapFuelTape 1)
    (U12ZeroBootstrap.bootstrapCandidateTape raw)
    (U12ZeroBootstrap.bootstrapFuelTape (raw.length + 2))
    (U12ZeroBootstrap.bootstrapFuelTape 1)
    (U12ZeroBootstrap.bootstrapCandidateTape raw)
    (by
      simpa [U12ZeroBootstrap.bootstrapFuelTape,
        bootstrapCandidateTape_eq_cursor] using hdispatch)
  exact hlift

end U12BootstrapDispatch
end BoundedFuelPairSearch
end Computability
end FoC

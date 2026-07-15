import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.FusedLayoutEmission
import FoC.Computability.Compiler.Structured.Lowering.TypedStateRuns

namespace FoC
namespace Computability

open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape

namespace BoundedFuelPairSearch
namespace U12PhaseFusion

set_option maxRecDepth 10000

def mapStep {sigma tau : Type}
    (f : sigma -> tau) (st : TypedStep sigma) : TypedStep tau :=
  ⟨f st.target, st.action0, st.action1, st.action2⟩

/-- A phase table agrees with the master table at every state before its local
halt.  The local halt itself is deliberately excluded because the master uses
it as a live bridge. -/
def EmbedsBeforeHalt
    {sigma tau : Type}
    (small : TypedStateTable sigma) (big : TypedStateTable tau)
    (f : sigma -> tau) : Prop :=
  forall state : sigma, state ≠ small.halt ->
    forall r0 r1 r2,
      big.next (f state) r0 r1 r2 =
        (small.next state r0 r1 r2).map (mapStep f)

/-- Lift an exact run up to its first local halt into a table that turns that
halt into a live bridge. -/
theorem lift_runConfig_to_first_halt
    {sigma tau : Type} [DecidableEq sigma] [DecidableEq tau]
    (small : TypedStateTable sigma) (big : TypedStateTable tau)
    (f : sigma -> tau)
    (hembeds : EmbedsBeforeHalt small big f)
    (hmem : forall state, state ∈ small.states -> f state ∈ big.states) :
    forall (steps : Nat) (state : sigma), state ∈ small.states ->
      forall (T0 T1 T2 U0 U1 U2 : Tape Bool),
        small.description.runConfig steps
            (small.config state T0 T1 T2) =
          small.config small.halt U0 U1 U2 ->
        (forall k : Nat, k < steps ->
          (small.description.runConfig k
            (small.config state T0 T1 T2)).state ≠
              small.description.halt) ->
        big.description.runConfig steps
            (big.config (f state) T0 T1 T2) =
          big.config (f small.halt) U0 U1 U2 := by
  intro steps
  induction steps with
  | zero =>
      intro state hstate T0 T1 T2 U0 U1 U2 hfinal _hbefore
      change
        small.description.runConfig 0
            (ThreeTape.config (small.stateId state) T0 T1 T2) =
          ThreeTape.config (small.stateId small.halt) U0 U1 U2 at hfinal
      change
        big.description.runConfig 0
            (ThreeTape.config (big.stateId (f state)) T0 T1 T2) =
          ThreeTape.config (big.stateId (f small.halt)) U0 U1 U2
      have hstateId := congrArg
        (fun c : CommonGround.FiniteTransducers.Structured.Configuration =>
          c.state) hfinal
      change small.stateId state = small.stateId small.halt at hstateId
      have hstateEq := small.stateId_inj
        state hstate small.halt small.halt_mem hstateId
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
        small.description.runConfig (steps + 1)
            (ThreeTape.config (small.stateId state) T0 T1 T2) =
          ThreeTape.config (small.stateId small.halt) U0 U1 U2 at hfinal
      change
        (forall k : Nat, k < steps + 1 ->
          (small.description.runConfig k
            (ThreeTape.config (small.stateId state) T0 T1 T2)).state ≠
              small.description.halt) at hbefore
      change
        big.description.runConfig (steps + 1)
            (ThreeTape.config (big.stateId (f state)) T0 T1 T2) =
          ThreeTape.config (big.stateId (f small.halt)) U0 U1 U2
      have hsne : state ≠ small.halt := by
        intro hstateEq
        subst state
        exact hbefore 0 (Nat.succ_pos steps) rfl
      cases hnext : small.next state
          (Tape.read T0) (Tape.read T1) (Tape.read T2) with
      | none =>
          have hstepNone := small.stepConfig_config_none hstate hnext
          simp only [Description.runConfig] at hfinal
          rw [hstepNone] at hfinal
          have hstateId := congrArg
            (fun c : CommonGround.FiniteTransducers.Structured.Configuration =>
              c.state) hfinal
          change small.stateId state = small.stateId small.halt at hstateId
          exact (hsne (small.stateId_inj
            state hstate small.halt small.halt_mem hstateId)).elim
      | some st =>
          have htarget := small.next_target_mem
            state hstate _ _ _ st hnext
          rw [small.runConfig_succ_config hstate hnext steps] at hfinal
          have hbigNext :
              big.next (f state)
                  (Tape.read T0) (Tape.read T1) (Tape.read T2) =
                some (mapStep f st) := by
            rw [hembeds state hsne]
            simp [hnext, mapStep]
          rw [big.runConfig_succ_config
            (hmem state hstate) hbigNext steps]
          apply ih st.target htarget
            (st.action0.apply T0) (st.action1.apply T1)
            (st.action2.apply T2) U0 U1 U2 hfinal
          intro k hk
          have h := hbefore (k + 1) (Nat.succ_lt_succ hk)
          rw [small.runConfig_succ_config hstate hnext k] at h
          exact h

/-- Any exact `Leads` endpoint at the local halt has a least such run.  At
that least time the entire configuration is the named deterministic endpoint,
not merely a configuration whose state is the halt state. -/
theorem first_halt_run_of_leads
    {sigma : Type} [DecidableEq sigma]
    (M : TypedStateTable sigma)
    (state : sigma) (T0 T1 T2 U0 U1 U2 : Tape Bool)
    (hleads :
      M.Leads (M.config state T0 T1 T2)
        (M.config M.halt U0 U1 U2)) :
    exists steps : Nat,
      M.description.runConfig steps (M.config state T0 T1 T2) =
        M.config M.halt U0 U1 U2 ∧
      forall k : Nat, k < steps ->
        (M.description.runConfig k
          (M.config state T0 T1 T2)).state ≠ M.description.halt := by
  let source := M.config state T0 T1 T2
  let target := M.config M.halt U0 U1 U2
  rcases hleads.to_runConfig with ⟨someSteps, hsome⟩
  change M.description.runConfig someSteps source = target at hsome
  have hbounded : exists n : Nat, n ≤ someSteps ∧
      (M.description.runConfig n source).state = M.description.halt := by
    refine ⟨someSteps, Nat.le_refl _, ?_⟩
    rw [hsome]
    rfl
  rcases StructuredConstructionTargets.FusedLayoutEmission.exists_least_up_to
      someSteps hbounded with
    ⟨first, hle, hfirstState, hbefore⟩
  obtain ⟨extra, hsteps⟩ := Nat.exists_eq_add_of_le hle
  have hfirstConfig : M.description.runConfig first source = target := by
    have hstall := M.description.runConfig_halt
      M.description_haltTransitionFree
      (M.description.runConfig first source) hfirstState extra
    change M.description.runConfig extra
      (M.description.runConfig first source) =
        M.description.runConfig first source at hstall
    have hadd := M.description.runConfig_add first extra source
    rw [hstall] at hadd
    rw [hsteps] at hsome
    exact hadd.symm.trans hsome
  exact ⟨first, hfirstConfig, hbefore⟩

theorem leads_of_runConfig
    {sigma : Type} (M : TypedStateTable sigma)
    {n : Nat}
    {c d : CommonGround.FiniteTransducers.Structured.Configuration}
    (hrun : M.description.runConfig n c = d) : M.Leads c d := by
  refine ⟨n, fun k => ?_⟩
  rw [Nat.add_comm, Description.runConfig_add, hrun]

/-- A one-step live bridge is enough to turn a first-halt phase run into a
master-table `Leads` fact. -/
theorem leads_via_first_halt_and_bridge
    {sigma tau : Type} [DecidableEq sigma] [DecidableEq tau]
    (small : TypedStateTable sigma) (big : TypedStateTable tau)
    (f : sigma -> tau)
    (hembeds : EmbedsBeforeHalt small big f)
    (hmem : forall state, state ∈ small.states -> f state ∈ big.states)
    (state : sigma) (hstate : state ∈ small.states)
    (T0 T1 T2 U0 U1 U2 : Tape Bool)
    (hleads :
      small.Leads (small.config state T0 T1 T2)
        (small.config small.halt U0 U1 U2))
    {target : tau} {V0 V1 V2 : Tape Bool}
    (hbridge :
      big.Leads (big.config (f small.halt) U0 U1 U2)
        (big.config target V0 V1 V2)) :
    big.Leads (big.config (f state) T0 T1 T2)
      (big.config target V0 V1 V2) := by
  rcases first_halt_run_of_leads small state
      T0 T1 T2 U0 U1 U2 hleads with
    ⟨steps, hrun, hbefore⟩
  have hlift := lift_runConfig_to_first_halt
    small big f hembeds hmem steps state
    hstate
    T0 T1 T2 U0 U1 U2 hrun hbefore
  exact TypedStateTable.Leads.trans
    (leads_of_runConfig big hlift)
    hbridge

/-- Transport an exact three-tape run across componentwise tape equivalence,
carrying the three actual endpoint representatives explicitly. -/
theorem runConfig_endpoint_of_equiv3
    {sigma : Type} [DecidableEq sigma]
    (M : TypedStateTable sigma)
    (steps : Nat) (state : sigma) (hstate : state ∈ M.states)
    (target : sigma)
    (T0 T1 T2 U0 U1 U2 V0 V1 V2 : Tape Bool)
    (h0 : Tape.Equiv T0 U0) (h1 : Tape.Equiv T1 U1)
    (h2 : Tape.Equiv T2 U2)
    (hcanonical :
      M.description.runConfig steps (M.config state U0 U1 U2) =
        M.config target V0 V1 V2) :
    exists A0 A1 A2 : Tape Bool,
      M.description.runConfig steps (M.config state T0 T1 T2) =
          M.config target A0 A1 A2 ∧
        Tape.Equiv A0 V0 ∧ Tape.Equiv A1 V1 ∧
          Tape.Equiv A2 V2 := by
  let actual :=
    M.description.runConfig steps (M.config state T0 T1 T2)
  have htransport :=
    StructuredConstructionTargets.FusedLayoutEmission.typed_runConfig_equiv3
      M steps state hstate T0 T1 T2 U0 U1 U2 h0 h1 h2
  have hstateEq : actual.state = M.stateId target := by
    have hs := htransport.1
    change actual.state =
      (M.description.runConfig steps (M.config state U0 U1 U2)).state at hs
    rw [hcanonical] at hs
    exact hs
  have htapes : LogicalTapeListEquiv actual.tapes [V0, V1, V2] := by
    have ht := htransport.2
    change LogicalTapeListEquiv actual.tapes
      (M.description.runConfig steps (M.config state U0 U1 U2)).tapes at ht
    rw [hcanonical] at ht
    exact ht
  have hlen : actual.tapes.length = 3 := by
    have h := logicalTapeListEquiv_length htapes
    simpa using h
  obtain ⟨A0, A1, A2, hactualTapes⟩ :
      exists A0 A1 A2 : Tape Bool, actual.tapes = [A0, A1, A2] := by
    cases hlist : actual.tapes with
    | nil => simp [hlist] at hlen
    | cons A0 rest =>
        cases hrest : rest with
        | nil => simp [hlist, hrest] at hlen
        | cons A1 rest =>
            cases hrest2 : rest with
            | nil => simp [hlist, hrest, hrest2] at hlen
            | cons A2 rest =>
                cases hrest3 : rest with
                | nil => exact ⟨A0, A1, A2, rfl⟩
                | cons extra rest =>
                    simp [hlist, hrest, hrest2, hrest3] at hlen
  rw [hactualTapes] at htapes
  change Tape.Equiv A0 V0 ∧ Tape.Equiv A1 V1 ∧
      Tape.Equiv A2 V2 ∧ True at htapes
  have hactualConfig : actual = M.config target A0 A1 A2 := by
    cases ha : actual with
    | mk actualState actualTapes =>
        have hs : actualState = M.stateId target := by
          simpa [ha] using hstateEq
        have ht : actualTapes = [A0, A1, A2] := by
          simpa [ha] using hactualTapes
        rw [hs, ht]
        rfl
  exact ⟨A0, A1, A2, hactualConfig, htapes.1,
    htapes.2.1, htapes.2.2.1⟩

/-- Step-count-free form of `runConfig_endpoint_of_equiv3`. -/
theorem leads_endpoint_of_equiv3
    {sigma : Type} [DecidableEq sigma]
    (M : TypedStateTable sigma)
    (state : sigma) (hstate : state ∈ M.states) (target : sigma)
    (T0 T1 T2 U0 U1 U2 V0 V1 V2 : Tape Bool)
    (h0 : Tape.Equiv T0 U0) (h1 : Tape.Equiv T1 U1)
    (h2 : Tape.Equiv T2 U2)
    (hcanonical :
      M.Leads (M.config state U0 U1 U2)
        (M.config target V0 V1 V2)) :
    exists A0 A1 A2 : Tape Bool,
      M.Leads (M.config state T0 T1 T2)
          (M.config target A0 A1 A2) ∧
        Tape.Equiv A0 V0 ∧ Tape.Equiv A1 V1 ∧
          Tape.Equiv A2 V2 := by
  rcases hcanonical.to_runConfig with ⟨steps, hrun⟩
  rcases runConfig_endpoint_of_equiv3 M steps state hstate target
      T0 T1 T2 U0 U1 U2 V0 V1 V2 h0 h1 h2 hrun with
    ⟨A0, A1, A2, hactual, hA0, hA1, hA2⟩
  exact ⟨A0, A1, A2,
    leads_of_runConfig M hactual,
    hA0, hA1, hA2⟩

end U12PhaseFusion
end BoundedFuelPairSearch
end Computability
end FoC

import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.RawLayoutEmission
import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.RawLayoutPreparation

namespace FoC
namespace Computability

open Languages

namespace StructuredConstructionTargets
namespace FusedLayoutEmission

open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape

theorem tapeAction_apply_equiv
    (action : TapeAction) {T U : Tape Bool}
    (h : Tape.Equiv T U) :
    Tape.Equiv (action.apply T) (action.apply U) := by
  cases action with
  | mk write move =>
      cases write with
      | none =>
          cases move with
          | stay => exact h
          | left => exact Tape.Equiv.move h Direction.left
          | right => exact Tape.Equiv.move h Direction.right
      | some cell =>
          have hw := Tape.Equiv.write h cell
          cases move with
          | stay => exact hw
          | left => exact Tape.Equiv.move hw Direction.left
          | right => exact Tape.Equiv.move hw Direction.right

/-- Typed structured runs cannot distinguish far-edge logical blank padding.
The theorem records the exact two runs while relating their three resulting
logical tape representatives pointwise. -/
theorem typed_runConfig_equiv3
    {σ : Type} [DecidableEq σ] (M : TypedStateTable σ) :
    forall (steps : Nat) (s : σ), s ∈ M.states ->
      forall (T0 T1 T2 U0 U1 U2 : Tape Bool),
        Tape.Equiv T0 U0 -> Tape.Equiv T1 U1 -> Tape.Equiv T2 U2 ->
        let actual := M.description.runConfig steps
          (ThreeTape.config (M.stateId s) T0 T1 T2)
        let expected := M.description.runConfig steps
          (ThreeTape.config (M.stateId s) U0 U1 U2)
        actual.state = expected.state ∧
          LogicalTapeListEquiv actual.tapes expected.tapes := by
  intro steps
  induction steps with
  | zero =>
      intro s hs T0 T1 T2 U0 U1 U2 h0 h1 h2
      exact ⟨rfl, h0, h1, h2, trivial⟩
  | succ steps ih =>
      intro s hs T0 T1 T2 U0 U1 U2 h0 h1 h2
      have hr0 : Tape.read T0 = Tape.read U0 := h0.read_eq
      have hr1 : Tape.read T1 = Tape.read U1 := h1.read_eq
      have hr2 : Tape.read T2 = Tape.read U2 := h2.read_eq
      cases hnext : M.next s (Tape.read T0) (Tape.read T1) (Tape.read T2) with
      | none =>
          have hnextU :
              M.next s (Tape.read U0) (Tape.read U1) (Tape.read U2) = none := by
            simpa [hr0, hr1, hr2] using hnext
          simp only [Description.runConfig]
          rw [M.stepConfig_config hs T0 T1 T2, hnext,
            M.stepConfig_config hs U0 U1 U2, hnextU]
          exact ⟨rfl, h0, h1, h2, trivial⟩
      | some st =>
          have hnextU :
              M.next s (Tape.read U0) (Tape.read U1) (Tape.read U2) =
                some st := by
            simpa [hr0, hr1, hr2] using hnext
          rw [M.runConfig_succ_config hs hnext steps,
            M.runConfig_succ_config hs hnextU steps]
          exact ih st.target
            (M.next_target_mem s hs _ _ _ st hnext)
            (st.action0.apply T0) (st.action1.apply T1)
            (st.action2.apply T2)
            (st.action0.apply U0) (st.action1.apply U1)
            (st.action2.apply U2)
            (tapeAction_apply_equiv st.action0 h0)
            (tapeAction_apply_equiv st.action1 h1)
            (tapeAction_apply_equiv st.action2 h2)

open FuelSimulatorCore
open FuelSimulatorCore.RawLayoutEmission
open RawLayoutPreparation

abbrev FusedState := Sum RawLayoutPreparation.State FuelSimulatorCore.State

private def mapLeftStep
    (st : TypedStep RawLayoutPreparation.State) :
    TypedStep FusedState :=
  ⟨Sum.inl st.target, st.action0, st.action1, st.action2⟩

private def mapRightStep
    (st : TypedStep FuelSimulatorCore.State) : TypedStep FusedState :=
  ⟨Sum.inr st.target, st.action0, st.action1, st.action2⟩

def fusedNext (start : Nat) :
    FusedState -> Option Bool -> Option Bool -> Option Bool ->
      Option (TypedStep FusedState)
  | .inl s => fun r0 r1 r2 =>
      if s = RawLayoutPreparation.State.halt then
        some ⟨Sum.inr (.outFalse0 none), keepS, keepS, keepS⟩
      else
        (RawLayoutPreparation.next s r0 r1 r2).map mapLeftStep
  | .inr s => fun r0 r1 r2 =>
      (FuelSimulatorCore.next start s r0 r1 r2).map mapRightStep

def fusedStates (start : Nat) : List FusedState :=
  List.append
    (RawLayoutPreparation.states.map Sum.inl)
    ((FuelSimulatorCore.states start).map Sum.inr)

theorem fusedNext_target_mem (start : Nat) :
    forall s : FusedState, s ∈ fusedStates start ->
      forall r0 r1 r2 : Option Bool, forall st : TypedStep FusedState,
        fusedNext start s r0 r1 r2 = some st ->
          st.target ∈ fusedStates start := by
  intro s hs r0 r1 r2 st hnext
  cases s with
  | inl s =>
      have hsLocal : s ∈ RawLayoutPreparation.states := by
        simpa [fusedStates] using hs
      by_cases hhalt : s = RawLayoutPreparation.State.halt
      · simp [fusedNext, hhalt] at hnext
        subst st
        have hstart := (rawEmissionTable start).start_mem
        change FuelSimulatorCore.State.outFalse0 none ∈
          FuelSimulatorCore.states start at hstart
        simpa [fusedStates] using hstart
      · simp [fusedNext, hhalt] at hnext
        cases hlocal : RawLayoutPreparation.next s r0 r1 r2 with
        | none => simp [hlocal] at hnext
        | some localStep =>
            simp [hlocal] at hnext
            subst st
            have htarget :=
              RawLayoutPreparation.next_target_mem s hsLocal
                r0 r1 r2 localStep hlocal
            simpa [fusedStates, mapLeftStep] using htarget
  | inr s =>
      have hsLocal : s ∈ FuelSimulatorCore.states start := by
        simpa [fusedStates] using hs
      simp [fusedNext] at hnext
      cases hlocal : FuelSimulatorCore.next start s r0 r1 r2 with
      | none => simp [hlocal] at hnext
      | some localStep =>
          simp [hlocal] at hnext
          subst st
          have htarget := FuelSimulatorCore.next_target_mem start s hsLocal
            r0 r1 r2 localStep hlocal
          simpa [fusedStates, mapRightStep] using htarget

def fusedTable (start : Nat) : TypedStateTable FusedState :=
  TypedStateTable.ofList (fusedStates start)
    (Sum.inl RawLayoutPreparation.State.seekRawEnd)
    (Sum.inr FuelSimulatorCore.State.halt)
    (fusedNext start)
    (by simp [fusedStates, RawLayoutPreparation.states])
    (by
      have hhalt := (rawEmissionTable start).halt_mem
      change FuelSimulatorCore.State.halt ∈ FuelSimulatorCore.states start at hhalt
      simpa [fusedStates] using hhalt)
    (by intros; rfl)
    (fusedNext_target_mem start)

def fusedD (start : Nat) : Description :=
  (fusedTable start).description

theorem fused_run_left_to_bridge
    (start : Nat) :
    forall (steps : Nat)
      (s : RawLayoutPreparation.State),
      s ∈ RawLayoutPreparation.table.states ->
      forall (T0 T1 T2 U0 U1 U2 : Tape Bool),
        RawLayoutPreparation.D.runConfig steps
            (RawLayoutPreparation.table.config s T0 T1 T2) =
          RawLayoutPreparation.table.config
            RawLayoutPreparation.State.halt U0 U1 U2 ->
        (forall k : Nat, k < steps ->
          (RawLayoutPreparation.D.runConfig k
            (RawLayoutPreparation.table.config s T0 T1 T2)).state ≠
              RawLayoutPreparation.D.halt) ->
        (fusedD start).runConfig steps
            ((fusedTable start).config (Sum.inl s) T0 T1 T2) =
          (fusedTable start).config
            (Sum.inl RawLayoutPreparation.State.halt) U0 U1 U2 := by
  intro steps
  induction steps with
  | zero =>
      intro s hs T0 T1 T2 U0 U1 U2 hfinal hbefore
      change
        RawLayoutPreparation.table.description.runConfig 0
            (ThreeTape.config (RawLayoutPreparation.table.stateId s)
              T0 T1 T2) =
          ThreeTape.config
            (RawLayoutPreparation.table.stateId
              RawLayoutPreparation.State.halt) U0 U1 U2 at hfinal
      change
        (fusedTable start).description.runConfig 0
            (ThreeTape.config ((fusedTable start).stateId (Sum.inl s))
              T0 T1 T2) =
          ThreeTape.config
            ((fusedTable start).stateId
              (Sum.inl RawLayoutPreparation.State.halt)) U0 U1 U2
      have hstate := congrArg
        (fun c : CommonGround.FiniteTransducers.Structured.Configuration => c.state)
        hfinal
      change RawLayoutPreparation.table.stateId s =
        RawLayoutPreparation.table.stateId
          RawLayoutPreparation.State.halt at hstate
      have hsEq := RawLayoutPreparation.table.stateId_inj
        s hs RawLayoutPreparation.State.halt
        RawLayoutPreparation.table.halt_mem hstate
      subst s
      have htapes := congrArg
        (fun c : CommonGround.FiniteTransducers.Structured.Configuration => c.tapes)
        hfinal
      change [T0, T1, T2] = [U0, U1, U2] at htapes
      simp at htapes
      rcases htapes with ⟨rfl, rfl, rfl⟩
      rfl
  | succ steps ih =>
      intro s hs T0 T1 T2 U0 U1 U2 hfinal hbefore
      change
        RawLayoutPreparation.table.description.runConfig (steps + 1)
            (ThreeTape.config (RawLayoutPreparation.table.stateId s)
              T0 T1 T2) =
          ThreeTape.config
            (RawLayoutPreparation.table.stateId
              RawLayoutPreparation.State.halt) U0 U1 U2 at hfinal
      change
        (forall k : Nat, k < steps + 1 ->
          (RawLayoutPreparation.table.description.runConfig k
            (ThreeTape.config (RawLayoutPreparation.table.stateId s)
              T0 T1 T2)).state ≠
              RawLayoutPreparation.table.description.halt) at hbefore
      change
        (fusedTable start).description.runConfig (steps + 1)
            (ThreeTape.config ((fusedTable start).stateId (Sum.inl s))
              T0 T1 T2) =
          ThreeTape.config
            ((fusedTable start).stateId
              (Sum.inl RawLayoutPreparation.State.halt)) U0 U1 U2
      have hsne : s ≠ RawLayoutPreparation.State.halt := by
        intro hsEq
        subst s
        exact hbefore 0 (Nat.succ_pos steps) rfl
      cases hnext : RawLayoutPreparation.table.next s
          (Tape.read T0) (Tape.read T1) (Tape.read T2) with
      | none =>
          have hstepNone :=
            RawLayoutPreparation.table.stepConfig_config_none hs hnext
          simp only [Description.runConfig] at hfinal
          rw [hstepNone] at hfinal
          have hstate := congrArg
            (fun c : CommonGround.FiniteTransducers.Structured.Configuration => c.state)
            hfinal
          change RawLayoutPreparation.table.stateId s =
            RawLayoutPreparation.table.stateId
              RawLayoutPreparation.State.halt at hstate
          exact (hsne (RawLayoutPreparation.table.stateId_inj
            s hs RawLayoutPreparation.State.halt
            RawLayoutPreparation.table.halt_mem hstate)).elim
      | some st =>
          have htarget := RawLayoutPreparation.table.next_target_mem
            s hs _ _ _ st hnext
          rw [RawLayoutPreparation.table.runConfig_succ_config
            hs hnext steps] at hfinal
          have hsLocal : s ∈ RawLayoutPreparation.states := by
            simpa [RawLayoutPreparation.table,
              TypedStateTable.ofList] using hs
          have hsfused : Sum.inl s ∈ (fusedTable start).states := by
            change Sum.inl s ∈ fusedStates start
            simpa [fusedStates] using hsLocal
          have hnextLocal := hnext
          change RawLayoutPreparation.next s
            (Tape.read T0) (Tape.read T1) (Tape.read T2) = some st at hnextLocal
          have hfnext :
              (fusedTable start).next (Sum.inl s)
                  (Tape.read T0) (Tape.read T1) (Tape.read T2) =
                some (mapLeftStep st) := by
            change fusedNext start (Sum.inl s)
              (Tape.read T0) (Tape.read T1) (Tape.read T2) =
                some (mapLeftStep st)
            simp [fusedNext, hsne, hnextLocal]
          rw [(fusedTable start).runConfig_succ_config
            hsfused hfnext steps]
          apply ih st.target htarget
            (st.action0.apply T0) (st.action1.apply T1)
            (st.action2.apply T2) U0 U1 U2 hfinal
          intro k hk
          have h := hbefore (k + 1) (Nat.succ_lt_succ hk)
          rw [RawLayoutPreparation.table.runConfig_succ_config
            hs hnext k] at h
          exact h

theorem exists_least_up_to
    {p : Nat -> Prop} [DecidablePred p] :
    forall bound : Nat,
      (exists n : Nat, n ≤ bound ∧ p n) ->
      exists first : Nat,
        first ≤ bound ∧ p first ∧
          forall k : Nat, k < first -> ¬ p k := by
  intro bound
  induction bound with
  | zero =>
      rintro ⟨n, hn, hp⟩
      have hn0 : n = 0 := by lia
      subst n
      exact ⟨0, Nat.le_refl 0, hp, by intros; lia⟩
  | succ bound ih =>
      intro hexists
      by_cases hprevious : exists n : Nat, n ≤ bound ∧ p n
      · rcases ih hprevious with ⟨first, hle, hp, hminimal⟩
        exact ⟨first, Nat.le_trans hle (Nat.le_succ bound), hp, hminimal⟩
      · rcases hexists with ⟨n, hn, hp⟩
        have hnEq : n = Nat.succ bound := by
          have hnNotLe : ¬ n ≤ bound := by
            intro hnLe
            exact hprevious ⟨n, hnLe, hp⟩
          lia
        subst n
        refine ⟨Nat.succ bound, Nat.le_refl _, hp, ?_⟩
        intro k hk hpk
        exact hprevious ⟨k, by lia, hpk⟩

theorem prep_first_halt_run
    (raw : Word Bool) (hraw : raw ≠ [])
    (fuel : Nat) (T0 : Tape Bool) :
    exists steps : Nat,
      RawLayoutPreparation.D.runConfig steps
          (RawLayoutPreparation.table.config
            RawLayoutPreparation.State.seekRawEnd T0
            (cursorFuelSourceTape fuel) (Tape.input raw)) =
        RawLayoutPreparation.table.config
          RawLayoutPreparation.State.halt T0
          (preparedEntryScratch raw fuel) (erasedRawTape raw) ∧
      forall k : Nat, k < steps ->
        (RawLayoutPreparation.D.runConfig k
          (RawLayoutPreparation.table.config
            RawLayoutPreparation.State.seekRawEnd T0
            (cursorFuelSourceTape fuel) (Tape.input raw))).state ≠
          RawLayoutPreparation.D.halt := by
  let source := RawLayoutPreparation.table.config
    RawLayoutPreparation.State.seekRawEnd T0
    (cursorFuelSourceTape fuel) (Tape.input raw)
  let target := RawLayoutPreparation.table.config
    RawLayoutPreparation.State.halt T0
    (preparedEntryScratch raw fuel) (erasedRawTape raw)
  rcases (leads_prepare_raw_emission raw hraw fuel T0).to_runConfig with
    ⟨someSteps, hsome⟩
  change RawLayoutPreparation.D.runConfig someSteps source = target at hsome
  have hbounded : exists n : Nat, n ≤ someSteps ∧
      (RawLayoutPreparation.D.runConfig n source).state =
        RawLayoutPreparation.D.halt := by
    refine ⟨someSteps, Nat.le_refl _, ?_⟩
    rw [hsome]
    rfl
  rcases exists_least_up_to someSteps hbounded with
    ⟨first, hle, hfirstState, hbefore⟩
  obtain ⟨extra, hsteps⟩ := Nat.exists_eq_add_of_le hle
  have hfirstConfig :
      RawLayoutPreparation.D.runConfig first source = target := by
    have hstall := RawLayoutPreparation.table.description.runConfig_halt
      RawLayoutPreparation.table.description_haltTransitionFree
      (RawLayoutPreparation.D.runConfig first source)
      hfirstState extra
    change RawLayoutPreparation.D.runConfig extra
      (RawLayoutPreparation.D.runConfig first source) =
        RawLayoutPreparation.D.runConfig first source at hstall
    have hadd := RawLayoutPreparation.D.runConfig_add first extra source
    rw [hstall] at hadd
    rw [hsteps] at hsome
    exact hadd.symm.trans hsome
  refine ⟨first, ?_, ?_⟩
  · exact hfirstConfig
  · intro k hk
    exact hbefore k hk

theorem fused_bridge_step
    (start : Nat) (T0 T1 T2 : Tape Bool) :
    (fusedD start).runConfig 1
        ((fusedTable start).config
          (Sum.inl RawLayoutPreparation.State.halt) T0 T1 T2) =
      (fusedTable start).config
        (Sum.inr (FuelSimulatorCore.State.outFalse0 none)) T0 T1 T2 := by
  have hlocal : RawLayoutPreparation.State.halt ∈
      RawLayoutPreparation.states := by
    simpa [RawLayoutPreparation.table,
      TypedStateTable.ofList] using RawLayoutPreparation.table.halt_mem
  have hs : Sum.inl RawLayoutPreparation.State.halt ∈
      (fusedTable start).states := by
    change Sum.inl RawLayoutPreparation.State.halt ∈ fusedStates start
    simpa [fusedStates] using hlocal
  have hnext :
      (fusedTable start).next
          (Sum.inl RawLayoutPreparation.State.halt)
          (Tape.read T0) (Tape.read T1) (Tape.read T2) =
        some ⟨Sum.inr (FuelSimulatorCore.State.outFalse0 none),
          keepS, keepS, keepS⟩ := by
    rfl
  have h0 : TapeAction.stay.apply T0 = T0 := rfl
  have h1 : TapeAction.stay.apply T1 = T1 := rfl
  have h2 : TapeAction.stay.apply T2 = T2 := rfl
  simpa [fusedD, TypedStateTable.config, Description.runConfig,
    h0, h1, h2] using
    (fusedTable start).runConfig_succ_config hs hnext 0

theorem fused_run_right
    (start : Nat) :
    forall (steps : Nat) (s : FuelSimulatorCore.State),
      s ∈ (rawEmissionTable start).states ->
      forall (target : FuelSimulatorCore.State),
        target ∈ (rawEmissionTable start).states ->
        forall (T0 T1 T2 U0 U1 U2 : Tape Bool),
          (rawEmissionD start).runConfig steps
              ((rawEmissionTable start).config s T0 T1 T2) =
            (rawEmissionTable start).config target U0 U1 U2 ->
          (fusedD start).runConfig steps
              ((fusedTable start).config (Sum.inr s) T0 T1 T2) =
            (fusedTable start).config (Sum.inr target) U0 U1 U2 := by
  intro steps
  induction steps with
  | zero =>
      intro s hs target ht T0 T1 T2 U0 U1 U2 hfinal
      change
        (rawEmissionTable start).description.runConfig 0
            (ThreeTape.config ((rawEmissionTable start).stateId s)
              T0 T1 T2) =
          ThreeTape.config ((rawEmissionTable start).stateId target)
            U0 U1 U2 at hfinal
      have hstate := congrArg
        (fun c : CommonGround.FiniteTransducers.Structured.Configuration => c.state)
        hfinal
      change (rawEmissionTable start).stateId s =
        (rawEmissionTable start).stateId target at hstate
      have hsEq := (rawEmissionTable start).stateId_inj
        s hs target ht hstate
      subst target
      have htapes := congrArg
        (fun c : CommonGround.FiniteTransducers.Structured.Configuration => c.tapes)
        hfinal
      change [T0, T1, T2] = [U0, U1, U2] at htapes
      simp at htapes
      rcases htapes with ⟨rfl, rfl, rfl⟩
      rfl
  | succ steps ih =>
      intro s hs target ht T0 T1 T2 U0 U1 U2 hfinal
      change
        (rawEmissionTable start).description.runConfig (steps + 1)
            (ThreeTape.config ((rawEmissionTable start).stateId s)
              T0 T1 T2) =
          ThreeTape.config ((rawEmissionTable start).stateId target)
            U0 U1 U2 at hfinal
      change
        (fusedTable start).description.runConfig (steps + 1)
            (ThreeTape.config ((fusedTable start).stateId (Sum.inr s))
              T0 T1 T2) =
          ThreeTape.config
            ((fusedTable start).stateId (Sum.inr target)) U0 U1 U2
      cases hnext : (rawEmissionTable start).next s
          (Tape.read T0) (Tape.read T1) (Tape.read T2) with
      | none =>
          have hlocalStep :=
            (rawEmissionTable start).stepConfig_config_none hs hnext
          simp only [Description.runConfig] at hfinal
          rw [hlocalStep] at hfinal
          have hstate := congrArg
            (fun c : CommonGround.FiniteTransducers.Structured.Configuration => c.state)
            hfinal
          change (rawEmissionTable start).stateId s =
            (rawEmissionTable start).stateId target at hstate
          have hsEq := (rawEmissionTable start).stateId_inj
            s hs target ht hstate
          subst target
          have htapes := congrArg
            (fun c : CommonGround.FiniteTransducers.Structured.Configuration => c.tapes)
            hfinal
          change [T0, T1, T2] = [U0, U1, U2] at htapes
          simp at htapes
          rcases htapes with ⟨rfl, rfl, rfl⟩
          have hsLocal : s ∈ FuelSimulatorCore.states start := by
            simpa [rawEmissionTable, TypedStateTable.ofList] using hs
          have hsfused : Sum.inr s ∈ (fusedTable start).states := by
            change Sum.inr s ∈ fusedStates start
            simpa [fusedStates] using hsLocal
          have hnextLocal := hnext
          change FuelSimulatorCore.next start s
            (Tape.read T0) (Tape.read T1) (Tape.read T2) = none at hnextLocal
          have hfnext :
              (fusedTable start).next (Sum.inr s)
                  (Tape.read T0) (Tape.read T1) (Tape.read T2) = none := by
            change fusedNext start (Sum.inr s)
              (Tape.read T0) (Tape.read T1) (Tape.read T2) = none
            simp [fusedNext, hnextLocal]
          have hfstep :=
            (fusedTable start).stepConfig_config_none hsfused hfnext
          simp [Description.runConfig, hfstep]
      | some st =>
          have htarget := (rawEmissionTable start).next_target_mem
            s hs _ _ _ st hnext
          rw [(rawEmissionTable start).runConfig_succ_config
            hs hnext steps] at hfinal
          have hsLocal : s ∈ FuelSimulatorCore.states start := by
            simpa [rawEmissionTable, TypedStateTable.ofList] using hs
          have hsfused : Sum.inr s ∈ (fusedTable start).states := by
            change Sum.inr s ∈ fusedStates start
            simpa [fusedStates] using hsLocal
          have hnextLocal := hnext
          change FuelSimulatorCore.next start s
            (Tape.read T0) (Tape.read T1) (Tape.read T2) = some st at hnextLocal
          have hfnext :
              (fusedTable start).next (Sum.inr s)
                  (Tape.read T0) (Tape.read T1) (Tape.read T2) =
                some (mapRightStep st) := by
            change fusedNext start (Sum.inr s)
              (Tape.read T0) (Tape.read T1) (Tape.read T2) =
                some (mapRightStep st)
            simp [fusedNext, hnextLocal]
          rw [(fusedTable start).runConfig_succ_config
            hsfused hfnext steps]
          exact ih st.target htarget target ht
            (st.action0.apply T0) (st.action1.apply T1)
            (st.action2.apply T2) U0 U1 U2 hfinal

/-- Padding-aware logical entry theorem for the existing generic emitter.
The actual endpoint representatives are carried explicitly; only their
componentwise relation to the canonical semantic endpoint is quotiented. -/
theorem rawEmission_runs_from_prepared
    (attempt : MachineDescription)
    (T0 : Tape Bool) (head : Bool) (tail : Word Bool) (fuel : Nat) :
    exists steps : Nat, exists A0 A1 A2 : Tape Bool,
      (rawEmissionD attempt.start).runConfig steps
          ((rawEmissionTable attempt.start).config (.outFalse0 none)
            T0 (preparedEntryScratch (head :: tail) fuel)
            (erasedRawTape (head :: tail))) =
        (rawEmissionTable attempt.start).config .halt A0 A1 A2 ∧
      Tape.Equiv A0 T0 ∧
      Tape.Equiv A1 (rawEmissionFinalScratch (head :: tail) fuel) ∧
      Tape.Equiv A2
        (rawEmissionOutputTape attempt (head :: tail) fuel) := by
  rcases (leads_halt_from_raw attempt T0 head tail fuel).to_runConfig with
    ⟨steps, hcanonical⟩
  have hcanonical' :
      (rawEmissionD attempt.start).runConfig steps
          ((rawEmissionTable attempt.start).config (.outFalse0 none)
            T0 (rawEmissionEntryScratch (head :: tail) fuel) Tape.blank) =
        (rawEmissionTable attempt.start).config .halt T0
          (rawEmissionFinalScratch (head :: tail) fuel)
          (rawEmissionOutputTape attempt (head :: tail) fuel) := by
    rw [rawEmissionD_runConfig_eq_coreD,
      rawEmissionTable_config_eq_coreCfg,
      rawEmissionTable_config_eq_coreCfg]
    exact hcanonical
  let actual :=
    (rawEmissionD attempt.start).runConfig steps
      ((rawEmissionTable attempt.start).config (.outFalse0 none)
        T0 (preparedEntryScratch (head :: tail) fuel)
        (erasedRawTape (head :: tail)))
  have htransport :=
    typed_runConfig_equiv3 (rawEmissionTable attempt.start) steps
      (.outFalse0 none) (rawEmissionTable attempt.start).start_mem
      T0 (preparedEntryScratch (head :: tail) fuel)
        (erasedRawTape (head :: tail))
      T0 (rawEmissionEntryScratch (head :: tail) fuel) Tape.blank
      (Tape.Equiv.refl T0)
      (preparedEntryScratch_equiv_rawEmissionEntry (head :: tail) fuel)
      (erasedRawTape_equiv_blank (head :: tail))
  have hstate :
      actual.state = (rawEmissionTable attempt.start).stateId .halt := by
    have hs := htransport.1
    change
      actual.state =
        ((rawEmissionD attempt.start).runConfig steps
          ((rawEmissionTable attempt.start).config (.outFalse0 none)
            T0 (rawEmissionEntryScratch (head :: tail) fuel)
            Tape.blank)).state at hs
    rw [hcanonical'] at hs
    exact hs
  have htapes :
      LogicalTapeListEquiv actual.tapes
        [ T0
        , rawEmissionFinalScratch (head :: tail) fuel
        , rawEmissionOutputTape attempt (head :: tail) fuel ] := by
    have ht := htransport.2
    change
      LogicalTapeListEquiv actual.tapes
        ((rawEmissionD attempt.start).runConfig steps
          ((rawEmissionTable attempt.start).config (.outFalse0 none)
            T0 (rawEmissionEntryScratch (head :: tail) fuel)
            Tape.blank)).tapes at ht
    rw [hcanonical'] at ht
    exact ht
  have hlen : actual.tapes.length = 3 := by
    have := logicalTapeListEquiv_length htapes
    simpa using this
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
                | cons extra rest => simp [hlist, hrest, hrest2, hrest3] at hlen
  rw [hactualTapes] at htapes
  change
    Tape.Equiv A0 T0 ∧
      Tape.Equiv A1 (rawEmissionFinalScratch (head :: tail) fuel) ∧
      Tape.Equiv A2 (rawEmissionOutputTape attempt (head :: tail) fuel) ∧
      True at htapes
  have hactualConfig :
      actual =
        (rawEmissionTable attempt.start).config .halt A0 A1 A2 := by
    cases ha : actual with
    | mk actualState actualTapes =>
        have hs :
            actualState = (rawEmissionTable attempt.start).stateId .halt := by
          simpa [ha] using hstate
        have ht : actualTapes = [A0, A1, A2] := by
          simpa [ha] using hactualTapes
        rw [hs, ht]
        rfl
  refine ⟨steps, A0, A1, A2, ?_, htapes.1, htapes.2.1, htapes.2.2.1⟩
  exact hactualConfig

theorem fused_runs_prepare_then_rawEmission
    (attempt : MachineDescription)
    (T0 : Tape Bool) (head : Bool) (tail : Word Bool) (fuel : Nat) :
    exists steps : Nat, exists A0 A1 A2 : Tape Bool,
      (fusedD attempt.start).runConfig steps
          ((fusedTable attempt.start).config
            (Sum.inl RawLayoutPreparation.State.seekRawEnd)
            T0 (cursorFuelSourceTape fuel) (Tape.input (head :: tail))) =
        (fusedTable attempt.start).config
          (Sum.inr FuelSimulatorCore.State.halt) A0 A1 A2 ∧
      Tape.Equiv A0 T0 ∧
      Tape.Equiv A1 (rawEmissionFinalScratch (head :: tail) fuel) ∧
      Tape.Equiv A2
        (rawEmissionOutputTape attempt (head :: tail) fuel) := by
  rcases prep_first_halt_run (head :: tail) (by simp) fuel T0 with
    ⟨prepSteps, hprep, hbefore⟩
  have hprepFused := fused_run_left_to_bridge attempt.start prepSteps
    RawLayoutPreparation.State.seekRawEnd
    RawLayoutPreparation.table.start_mem
    T0 (cursorFuelSourceTape fuel) (Tape.input (head :: tail))
    T0 (preparedEntryScratch (head :: tail) fuel)
      (erasedRawTape (head :: tail))
    hprep hbefore
  have hbridge := fused_bridge_step attempt.start T0
    (preparedEntryScratch (head :: tail) fuel)
    (erasedRawTape (head :: tail))
  rcases rawEmission_runs_from_prepared attempt T0 head tail fuel with
    ⟨emitSteps, A0, A1, A2, hemit, hA0, hA1, hA2⟩
  have hemitFused := fused_run_right attempt.start emitSteps
    (FuelSimulatorCore.State.outFalse0 none)
    (rawEmissionTable attempt.start).start_mem
    FuelSimulatorCore.State.halt
    (rawEmissionTable attempt.start).halt_mem
    T0 (preparedEntryScratch (head :: tail) fuel)
      (erasedRawTape (head :: tail)) A0 A1 A2 hemit
  refine ⟨prepSteps + (1 + emitSteps), A0, A1, A2, ?_,
    hA0, hA1, hA2⟩
  calc
    (fusedD attempt.start).runConfig (prepSteps + (1 + emitSteps))
        ((fusedTable attempt.start).config
          (Sum.inl RawLayoutPreparation.State.seekRawEnd)
          T0 (cursorFuelSourceTape fuel) (Tape.input (head :: tail))) =
      (fusedD attempt.start).runConfig (1 + emitSteps)
        ((fusedD attempt.start).runConfig prepSteps
          ((fusedTable attempt.start).config
            (Sum.inl RawLayoutPreparation.State.seekRawEnd)
            T0 (cursorFuelSourceTape fuel) (Tape.input (head :: tail)))) :=
      (fusedD attempt.start).runConfig_add prepSteps (1 + emitSteps) _
    _ = (fusedD attempt.start).runConfig (1 + emitSteps)
        ((fusedTable attempt.start).config
          (Sum.inl RawLayoutPreparation.State.halt)
          T0 (preparedEntryScratch (head :: tail) fuel)
            (erasedRawTape (head :: tail))) := by rw [hprepFused]
    _ = (fusedD attempt.start).runConfig emitSteps
        ((fusedD attempt.start).runConfig 1
          ((fusedTable attempt.start).config
            (Sum.inl RawLayoutPreparation.State.halt)
            T0 (preparedEntryScratch (head :: tail) fuel)
              (erasedRawTape (head :: tail)))) :=
      (fusedD attempt.start).runConfig_add 1 emitSteps _
    _ = (fusedD attempt.start).runConfig emitSteps
        ((fusedTable attempt.start).config
          (Sum.inr (FuelSimulatorCore.State.outFalse0 none))
          T0 (preparedEntryScratch (head :: tail) fuel)
            (erasedRawTape (head :: tail))) := by rw [hbridge]
    _ = (fusedTable attempt.start).config
        (Sum.inr FuelSimulatorCore.State.halt) A0 A1 A2 := hemitFused

theorem fusedD_haltsWithTapes_prepare_then_rawEmission
    (attempt : MachineDescription)
    (T0 : Tape Bool) (head : Bool) (tail : Word Bool) (fuel : Nat) :
    exists A0 A1 A2 : Tape Bool,
      (fusedD attempt.start).HaltsWithTapes
        ((fusedTable attempt.start).config
          (Sum.inl RawLayoutPreparation.State.seekRawEnd)
          T0 (cursorFuelSourceTape fuel) (Tape.input (head :: tail)))
        [A0, A1, A2] ∧
      Tape.Equiv A0 T0 ∧
      Tape.Equiv A1 (rawEmissionFinalScratch (head :: tail) fuel) ∧
      Tape.Equiv A2
        (rawEmissionOutputTape attempt (head :: tail) fuel) := by
  rcases fused_runs_prepare_then_rawEmission attempt T0 head tail fuel with
    ⟨steps, A0, A1, A2, hrun, hA0, hA1, hA2⟩
  refine ⟨A0, A1, A2, ⟨steps, ?_⟩, hA0, hA1, hA2⟩
  change
    (fusedD attempt.start).runConfig steps
        ((fusedTable attempt.start).config
          (Sum.inl RawLayoutPreparation.State.seekRawEnd)
          T0 (cursorFuelSourceTape fuel) (Tape.input (head :: tail))) =
      (fusedTable attempt.start).config
        (Sum.inr FuelSimulatorCore.State.halt) A0 A1 A2
  exact hrun

/-- The requested single lowerer boundary: prep, the padding-aware handoff,
and generic raw emission execute as one structured machine. -/
theorem fusedLowered_haltsFromTapeEquiv_prepare_then_rawEmission
    (attempt : MachineDescription)
    (T0 : Tape Bool) (head : Bool) (tail : Word Bool) (fuel : Nat) :
    exists A0 A1 A2 : Tape Bool,
      (lowerStructured3Description (fusedD attempt.start)).HaltsFromTapeEquiv
        (encodedGuardedStructured3Tapes T0
          (cursorFuelSourceTape fuel) (Tape.input (head :: tail)))
        (encodedGuardedStructured3Tapes A0 A1 A2) ∧
      Tape.Equiv A0 T0 ∧
      Tape.Equiv A1 (rawEmissionFinalScratch (head :: tail) fuel) ∧
      Tape.Equiv A2
        (rawEmissionOutputTape attempt (head :: tail) fuel) := by
  rcases fusedD_haltsWithTapes_prepare_then_rawEmission
      attempt T0 head tail fuel with
    ⟨A0, A1, A2, hhalts, hA0, hA1, hA2⟩
  have hlowered :=
    lowerStructured3Description_haltsFromConfigWithTapes
      (fusedTable attempt.start).description_wellFormed
      (fusedTable attempt.start).description_haltTransitionFree
      (fusedTable attempt.start).description_supportsReadWriteRows3
      (c := (fusedTable attempt.start).config
        (Sum.inl RawLayoutPreparation.State.seekRawEnd)
        T0 (cursorFuelSourceTape fuel) (Tape.input (head :: tail)))
      (tapes := [A0, A1, A2])
      rfl (by rfl) hhalts
  refine ⟨A0, A1, A2, ?_, hA0, hA1, hA2⟩
  simpa [fusedD, encodedGuardedStructured3Tapes,
    TypedStateTable.config, ThreeTape.config] using hlowered

end FusedLayoutEmission
end StructuredConstructionTargets

end Computability
end FoC

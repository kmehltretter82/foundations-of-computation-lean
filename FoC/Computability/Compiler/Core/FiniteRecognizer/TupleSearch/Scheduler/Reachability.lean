import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.Layout
import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.FairCycle

set_option doc.verso true

/-!
**Physical scheduler reachability.** This module proves reachability for the
concrete tuple-scheduler phase order.
-/

namespace FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.Reachability

open Languages
open Scheduler.Layout
open TuringMachine.FairCycle

inductive Reaches (advance : cursor -> cursor) : cursor -> cursor -> Prop where
  | refl (cursor : cursor) : Reaches advance cursor cursor
  | step {source target : cursor} :
      Reaches advance source target ->
        Reaches advance source (advance target)

theorem Reaches.trans
    {advance : cursor -> cursor} {first second third : cursor}
    (hfirst : Reaches advance first second)
    (hsecond : Reaches advance second third) :
    Reaches advance first third := by
  induction hsecond with
  | refl => exact hfirst
  | step _ ih => exact Reaches.step ih

theorem Reaches.exists_advanceN
    {advance : cursor -> cursor} {source target : cursor}
    (h : Reaches advance source target) :
    exists n : Nat, advanceN advance n source = target := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | step _ ih =>
      rcases ih with ⟨n, hn⟩
      refine ⟨n + 1, ?_⟩
      rw [advanceN_succ_right, hn]

def cursor (round inner outer selectedFuel : Nat) : Cursor :=
  { round := round
    inner := inner
    outer := outer
    selectedFuel := selectedFuel }

theorem reach_fuel
    (geometry : Geometry) (round inner outer selectedFuel : Nat)
    (hfuel : selectedFuel ≤ round) :
    Reaches (Cursor.advance geometry)
      (cursor round inner outer 0)
      (cursor round inner outer selectedFuel) := by
  induction selectedFuel with
  | zero => exact Reaches.refl _
  | succ selectedFuel ih =>
      have hprev : selectedFuel ≤ round := Nat.le_trans
        (Nat.le_succ selectedFuel) hfuel
      have hlt : selectedFuel < round := by lia
      have hreach := ih hprev
      have hstep := Reaches.step hreach
      rw [Cursor.advance_selectedFuel_of_lt geometry
        (cursor round inner outer selectedFuel) hlt] at hstep
      exact hstep

theorem reach_outer
    (geometry : Geometry) (round inner outer : Nat)
    (houter : outer ≤ geometry.pairBound round) :
    Reaches (Cursor.advance geometry)
      (cursor round inner 0 0)
      (cursor round inner outer 0) := by
  induction outer with
  | zero => exact Reaches.refl _
  | succ outer ih =>
      have hprev : outer ≤ geometry.pairBound round := Nat.le_trans
        (Nat.le_succ outer) houter
      have hlt : outer < geometry.pairBound round := by lia
      have hstart := ih hprev
      have hfuels := reach_fuel geometry round inner outer round
        (Nat.le_refl round)
      have hend := Reaches.trans hstart hfuels
      have hstep := Reaches.step hend
      rw [Cursor.advance_outer_of_fuel_end geometry
        (cursor round inner outer round) rfl hlt] at hstep
      exact hstep

theorem reach_inner
    (geometry : Geometry) (round inner : Nat)
    (hinner : inner ≤ geometry.pairBound round) :
    Reaches (Cursor.advance geometry)
      (cursor round 0 0 0)
      (cursor round inner 0 0) := by
  induction inner with
  | zero => exact Reaches.refl _
  | succ inner ih =>
      let bound := geometry.pairBound round
      have hprev : inner ≤ bound := Nat.le_trans
        (Nat.le_succ inner) hinner
      have hlt : inner < bound := by
        dsimp [bound]
        lia
      have hstart := ih (by simpa [bound] using hprev)
      have houters := reach_outer geometry round inner bound
        (by exact Nat.le_refl bound)
      have hfuels := reach_fuel geometry round inner bound round
        (Nat.le_refl round)
      have hend := Reaches.trans (Reaches.trans hstart houters) hfuels
      have hstep := Reaches.step hend
      rw [Cursor.advance_inner_of_fuel_outer_end geometry
        (cursor round inner bound round) rfl rfl
        (by simpa [bound, cursor] using hlt)] at hstep
      exact hstep

theorem reach_round_start
    (geometry : Geometry) (round : Nat) :
    Reaches (Cursor.advance geometry)
      Cursor.initial (cursor round 0 0 0) := by
  induction round with
  | zero => exact Reaches.refl _
  | succ round ih =>
      let bound := geometry.pairBound round
      have hinners := reach_inner geometry round bound
        (by exact Nat.le_refl bound)
      have houters := reach_outer geometry round bound bound
        (by exact Nat.le_refl bound)
      have hfuels := reach_fuel geometry round bound bound round
        (Nat.le_refl round)
      have hend := Reaches.trans
        (Reaches.trans (Reaches.trans ih hinners) houters) hfuels
      have hstep := Reaches.step hend
      rw [Cursor.advance_round_of_cube_end geometry
        (cursor round bound bound round) rfl rfl rfl] at hstep
      exact hstep

theorem reachable_valid_cursor
    (geometry : Geometry) (target : Cursor)
    (hvalid : target.Valid geometry) :
    Reaches (Cursor.advance geometry) Cursor.initial target := by
  rcases target with ⟨round, inner, outer, selectedFuel⟩
  rcases hvalid with ⟨hinner, houter, hfuel⟩
  have hround := reach_round_start geometry round
  have hinnerReach := reach_inner geometry round inner hinner
  have houterReach := reach_outer geometry round inner outer houter
  have hfuelReach := reach_fuel geometry round inner outer selectedFuel hfuel
  exact Reaches.trans
    (Reaches.trans (Reaches.trans hround hinnerReach) houterReach)
    hfuelReach

theorem exists_advanceN_valid_cursor
    (geometry : Geometry) (target : Cursor)
    (hvalid : target.Valid geometry) :
    exists n : Nat,
      advanceN (Cursor.advance geometry) n Cursor.initial = target := by
  exact Reaches.exists_advanceN (reachable_valid_cursor geometry target hvalid)

theorem unbounded_candidate_eventually_reached
    (inner outer selectedFuel : Nat) :
    exists n round : Nat,
      advanceN (Cursor.advance .unbounded) n Cursor.initial =
        cursor round inner outer selectedFuel := by
  let round := Nat.max inner (Nat.max outer selectedFuel)
  have hvalid : (cursor round inner outer selectedFuel).Valid .unbounded := by
    simp only [Cursor.Valid, Geometry.pairBound, cursor]
    exact
      ⟨Nat.le_max_left inner (Nat.max outer selectedFuel),
        Nat.le_trans (Nat.le_max_left outer selectedFuel)
          (Nat.le_max_right inner (Nat.max outer selectedFuel)),
        Nat.le_trans (Nat.le_max_right outer selectedFuel)
          (Nat.le_max_right inner (Nat.max outer selectedFuel))⟩
  rcases exists_advanceN_valid_cursor .unbounded
      (cursor round inner outer selectedFuel) hvalid with ⟨n, hn⟩
  exact ⟨n, round, hn⟩

theorem bounded_candidate_eventually_reached
    (budget inner outer selectedFuel : Nat)
    (hinner : inner ≤ budget) (houter : outer ≤ budget) :
    exists n : Nat,
      advanceN (Cursor.advance (.bounded budget)) n Cursor.initial =
        cursor selectedFuel inner outer selectedFuel := by
  have hvalid :
      (cursor selectedFuel inner outer selectedFuel).Valid
        (.bounded budget) := by
    exact ⟨hinner, houter, Nat.le_refl selectedFuel⟩
  exact exists_advanceN_valid_cursor (.bounded budget)
    (cursor selectedFuel inner outer selectedFuel) hvalid

def initialFrame (geometry : Geometry)
    (input : Word MachineCodeSymbol) : Frame :=
  { geometry := geometry
    cursor := Cursor.initial
    input := input }

theorem advanceN_frame
    (geometry : Geometry) (start : Cursor)
    (input : Word MachineCodeSymbol) (n : Nat) :
    advanceN Frame.advance n
        ({ geometry := geometry, cursor := start, input := input } : Frame) =
      { geometry := geometry
        cursor := advanceN (Cursor.advance geometry) n start
        input := input } := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
      simp only [advanceN_succ]
      simpa [Frame.advance] using ih (start.advance geometry)

theorem advanceN_valid
    (geometry : Geometry) (start : Cursor)
    (hvalid : start.Valid geometry) (n : Nat) :
    (advanceN (Cursor.advance geometry) n start).Valid geometry := by
  induction n generalizing start with
  | zero => exact hvalid
  | succ n ih =>
      simp only [advanceN_succ]
      exact ih (start.advance geometry) (Cursor.advance_valid hvalid)

def CandidateSucceeds {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (frame : Frame) : Prop :=
  TuringMachine.HaltsOnInputIn selected frame.cursor.selectedFuel
    (GeneratedCode.nestedStageCode frame.input
      frame.cursor.inner frame.cursor.outer)

theorem unbounded_eventual_success_iff {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (input : Word MachineCodeSymbol) :
    (exists n : Nat,
      CandidateSucceeds selected
        (advanceN Frame.advance n (initialFrame .unbounded input))) <->
      exists inner outer selectedFuel : Nat,
        TuringMachine.HaltsOnInputIn selected selectedFuel
          (GeneratedCode.nestedStageCode input inner outer) := by
  constructor
  · rintro ⟨n, hsuccess⟩
    rw [advanceN_frame] at hsuccess
    exact
      ⟨(advanceN (Cursor.advance .unbounded) n Cursor.initial).inner,
        (advanceN (Cursor.advance .unbounded) n Cursor.initial).outer,
        (advanceN (Cursor.advance .unbounded) n
          Cursor.initial).selectedFuel,
        hsuccess⟩
  · rintro ⟨inner, outer, selectedFuel, hsuccess⟩
    rcases unbounded_candidate_eventually_reached inner outer selectedFuel with
      ⟨n, round, hreached⟩
    refine ⟨n, ?_⟩
    simp only [initialFrame]
    rw [advanceN_frame, hreached]
    exact hsuccess

theorem bounded_eventual_success_iff {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (input : Word MachineCodeSymbol) (budget : Nat) :
    (exists n : Nat,
      CandidateSucceeds selected
        (advanceN Frame.advance n
          (initialFrame (.bounded budget) input))) <->
      exists inner outer selectedFuel : Nat,
        inner ≤ budget ∧ outer ≤ budget ∧
          TuringMachine.HaltsOnInputIn selected selectedFuel
            (GeneratedCode.nestedStageCode input inner outer) := by
  constructor
  · rintro ⟨n, hsuccess⟩
    have hvalid := advanceN_valid (.bounded budget) Cursor.initial
      (Cursor.initial_valid (.bounded budget)) n
    rw [advanceN_frame] at hsuccess
    exact
      ⟨(advanceN (Cursor.advance (.bounded budget)) n Cursor.initial).inner,
        (advanceN (Cursor.advance (.bounded budget)) n Cursor.initial).outer,
        (advanceN (Cursor.advance (.bounded budget)) n
          Cursor.initial).selectedFuel,
        hvalid.1, hvalid.2.1, hsuccess⟩
  · rintro ⟨inner, outer, selectedFuel, hinner, houter, hsuccess⟩
    rcases bounded_candidate_eventually_reached budget inner outer selectedFuel
        hinner houter with ⟨n, hreached⟩
    refine ⟨n, ?_⟩
    simp only [initialFrame]
    rw [advanceN_frame, hreached]
    exact hsuccess

theorem unbounded_haltsFrom_iff_of_cycle {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (driver : TuringMachine MachineCodeSymbol driverState)
    (source : Frame -> TuringMachine.Configuration MachineCodeSymbol
      driverState)
    (hstop : TuringMachine.HaltingTransitionsDisabled driver)
    (hsuccess : forall frame,
      CandidateSucceeds selected frame ->
        TuringMachine.HaltsFrom driver (source frame))
    (hfailure : forall frame,
      ¬ CandidateSucceeds selected frame ->
        exists steps : Nat,
          0 < steps ∧
            TuringMachine.ComputesIn driver steps (source frame)
              (source frame.advance))
    (input : Word MachineCodeSymbol) :
    TuringMachine.HaltsFrom driver
        (source (initialFrame .unbounded input)) <->
      exists inner outer selectedFuel : Nat,
        TuringMachine.HaltsOnInputIn selected selectedFuel
          (GeneratedCode.nestedStageCode input inner outer) := by
  exact Iff.trans
    (TuringMachine.FairCycle.haltsFrom_iff_eventual_success
      hstop source Frame.advance (CandidateSucceeds selected)
      hsuccess hfailure (initialFrame .unbounded input))
    (unbounded_eventual_success_iff selected input)

theorem bounded_haltsFrom_iff_of_cycle {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (driver : TuringMachine MachineCodeSymbol driverState)
    (source : Frame -> TuringMachine.Configuration MachineCodeSymbol
      driverState)
    (hstop : TuringMachine.HaltingTransitionsDisabled driver)
    (hsuccess : forall frame,
      CandidateSucceeds selected frame ->
        TuringMachine.HaltsFrom driver (source frame))
    (hfailure : forall frame,
      ¬ CandidateSucceeds selected frame ->
        exists steps : Nat,
          0 < steps ∧
            TuringMachine.ComputesIn driver steps (source frame)
              (source frame.advance))
    (input : Word MachineCodeSymbol) (budget : Nat) :
    TuringMachine.HaltsFrom driver
        (source (initialFrame (.bounded budget) input)) <->
      exists inner outer selectedFuel : Nat,
        inner ≤ budget ∧ outer ≤ budget ∧
          TuringMachine.HaltsOnInputIn selected selectedFuel
            (GeneratedCode.nestedStageCode input inner outer) := by
  exact Iff.trans
    (TuringMachine.FairCycle.haltsFrom_iff_eventual_success
      hstop source Frame.advance (CandidateSucceeds selected)
      hsuccess hfailure (initialFrame (.bounded budget) input))
    (bounded_eventual_success_iff selected input budget)

theorem unbounded_haltsFrom_iff_of_rel_cycle {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (driver : TuringMachine MachineCodeSymbol driverState)
    (represents : Frame ->
      TuringMachine.Configuration MachineCodeSymbol driverState -> Prop)
    (hstop : TuringMachine.HaltingTransitionsDisabled driver)
    (hsuccess : forall frame config,
      represents frame config -> CandidateSucceeds selected frame ->
        TuringMachine.HaltsFrom driver config)
    (hfailure : forall frame config,
      represents frame config -> ¬ CandidateSucceeds selected frame ->
        exists steps : Nat,
        exists nextConfig :
            TuringMachine.Configuration MachineCodeSymbol driverState,
          0 < steps ∧
            TuringMachine.ComputesIn driver steps config nextConfig ∧
            represents frame.advance nextConfig)
    (input : Word MachineCodeSymbol)
    (config : TuringMachine.Configuration MachineCodeSymbol driverState)
    (hrep : represents (initialFrame .unbounded input) config) :
    TuringMachine.HaltsFrom driver config <->
      exists inner outer selectedFuel : Nat,
        TuringMachine.HaltsOnInputIn selected selectedFuel
          (GeneratedCode.nestedStageCode input inner outer) := by
  exact Iff.trans
    (TuringMachine.FairCycle.haltsFrom_iff_eventual_success_rel
      hstop represents Frame.advance (CandidateSucceeds selected)
      hsuccess hfailure (initialFrame .unbounded input) config hrep)
    (unbounded_eventual_success_iff selected input)

theorem bounded_haltsFrom_iff_of_rel_cycle {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (driver : TuringMachine MachineCodeSymbol driverState)
    (represents : Frame ->
      TuringMachine.Configuration MachineCodeSymbol driverState -> Prop)
    (hstop : TuringMachine.HaltingTransitionsDisabled driver)
    (hsuccess : forall frame config,
      represents frame config -> CandidateSucceeds selected frame ->
        TuringMachine.HaltsFrom driver config)
    (hfailure : forall frame config,
      represents frame config -> ¬ CandidateSucceeds selected frame ->
        exists steps : Nat,
        exists nextConfig :
            TuringMachine.Configuration MachineCodeSymbol driverState,
          0 < steps ∧
            TuringMachine.ComputesIn driver steps config nextConfig ∧
            represents frame.advance nextConfig)
    (input : Word MachineCodeSymbol) (budget : Nat)
    (config : TuringMachine.Configuration MachineCodeSymbol driverState)
    (hrep : represents (initialFrame (.bounded budget) input) config) :
    TuringMachine.HaltsFrom driver config <->
      exists inner outer selectedFuel : Nat,
        inner ≤ budget ∧ outer ≤ budget ∧
          TuringMachine.HaltsOnInputIn selected selectedFuel
            (GeneratedCode.nestedStageCode input inner outer) := by
  exact Iff.trans
    (TuringMachine.FairCycle.haltsFrom_iff_eventual_success_rel
      hstop represents Frame.advance (CandidateSucceeds selected)
      hsuccess hfailure (initialFrame (.bounded budget) input) config hrep)
    (bounded_eventual_success_iff selected input budget)

end FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.Reachability

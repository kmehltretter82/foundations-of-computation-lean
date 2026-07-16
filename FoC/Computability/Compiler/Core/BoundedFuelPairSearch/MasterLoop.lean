import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.PhaseFusion
import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.HitBranch
import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.BootstrapDispatch
import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.Tape2SubroutineLift
import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.SwappedLayoutEmission

set_option doc.verso true

/-!
# Bounded fuel-pair master loop

A single finite three-tape control union composes bootstrap, simulation, hit extraction, restaging, and dispatch.
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
namespace U12MasterLoop

open StructuredConstructionTargets
open StructuredConstructionTargets.FusedLayoutEmission
open StructuredConstructionTargets.SwappedLayoutEmission
open StructuredConstructionTargets.RawLayoutPreparation
open StructuredConstructionTargets.FuelSimulatorCore
open StructuredConstructionTargets.FuelSimulatorCore.RawLayoutEmission
open U12PhaseFusion

inductive State where
  | bootstrap (state : U12ZeroBootstrap.State)
  | sourceEmit (state : FusedLayoutEmission.FusedState)
  | sourceSim (state : Nat)
  | checkerEmit (state : FusedLayoutEmission.FusedState)
  | checkerSim (state : Nat)
  | hitExtract (state : Nat)
  | hitBranch (state : U12HitBranch.State)
  | restage (state : PersistentRestaging.State)
  | dispatch (state : U12DispatchBootstrap.State)
  | halt
deriving DecidableEq, Repr

def next
    (source sourceSimulator recognizer checkerSimulator : MachineDescription)
    (b : Bool)
    (hsourceSimulator : sourceSimulator.SubroutineReady)
    (hcheckerSimulator : checkerSimulator.SubroutineReady) :
    State -> Option Bool -> Option Bool -> Option Bool ->
      Option (TypedStep State)
  | .bootstrap state => fun r0 r1 r2 =>
      if state = U12ZeroBootstrap.State.halt then
        some ⟨.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd),
          keepS, keepS, keepS⟩
      else
        (U12ZeroBootstrap.table.next state r0 r1 r2).map
          (U12PhaseFusion.mapStep State.bootstrap)
  | .sourceEmit state => fun r0 r1 r2 =>
      if state = (fusedTable source.start).halt then
        some ⟨.sourceSim sourceSimulator.start, keepS, keepS, keepL⟩
      else
        ((fusedTable source.start).next state r0 r1 r2).map
          (U12PhaseFusion.mapStep State.sourceEmit)
  | .sourceSim state => fun r0 r1 r2 =>
      if state = (Tape2SubroutineLift.table
          sourceSimulator hsourceSimulator).halt then
        some ⟨.checkerEmit
          (Sum.inl RawLayoutPreparation.State.seekRawEnd),
          keepS, keepS, keepS⟩
      else
        ((Tape2SubroutineLift.table sourceSimulator hsourceSimulator).next
          state r0 r1 r2).map (U12PhaseFusion.mapStep State.sourceSim)
  | .checkerEmit state => fun r0 r1 r2 =>
      if state = (swappedFusedTable recognizer.start).halt then
        some ⟨.checkerSim checkerSimulator.start, keepS, keepS, keepL⟩
      else
        ((swappedFusedTable recognizer.start).next state r0 r1 r2).map
          (U12PhaseFusion.mapStep State.checkerEmit)
  | .checkerSim state => fun r0 r1 r2 =>
      if state = (Tape2SubroutineLift.table
          checkerSimulator hcheckerSimulator).halt then
        some ⟨.hitExtract SimulatorHitExtractorDescription.start,
          keepS, keepS, keepS⟩
      else
        ((Tape2SubroutineLift.table checkerSimulator hcheckerSimulator).next
          state r0 r1 r2).map (U12PhaseFusion.mapStep State.checkerSim)
  | .hitExtract state => fun r0 r1 r2 =>
      if state = (Tape2SubroutineLift.table SimulatorHitExtractorDescription
          simulatorHitExtractorDescription_subroutineReady).halt then
        some ⟨.hitBranch U12HitBranch.State.inspect,
          keepS, keepS, keepS⟩
      else
        ((Tape2SubroutineLift.table SimulatorHitExtractorDescription
          simulatorHitExtractorDescription_subroutineReady).next
            state r0 r1 r2).map (U12PhaseFusion.mapStep State.hitExtract)
  | .hitBranch state => fun r0 r1 r2 =>
      if state = U12HitBranch.State.successHalt then
        some ⟨.halt, keepS, keepS, keepS⟩
      else if state = U12HitBranch.State.failureExit then
        some ⟨.restage PersistentRestaging.State.checkerSeek,
          keepS, keepS, keepS⟩
      else
        ((U12HitBranch.table b).next state r0 r1 r2).map
          (U12PhaseFusion.mapStep State.hitBranch)
  | .restage state => fun r0 r1 r2 =>
      if state = PersistentRestaging.table.halt then
        some ⟨.dispatch U12DispatchBootstrap.State.length0,
          keepS, keepS, keepS⟩
      else
        (PersistentRestaging.table.next state r0 r1 r2).map
          (U12PhaseFusion.mapStep State.restage)
  | .dispatch state => fun r0 r1 r2 =>
      if state = U12DispatchBootstrap.table.halt then
        some ⟨.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd),
          keepS, keepS, keepS⟩
      else
        (U12DispatchBootstrap.table.next state r0 r1 r2).map
          (U12PhaseFusion.mapStep State.dispatch)
  | .halt => fun _ _ _ => none

def states
    (source sourceSimulator recognizer checkerSimulator : MachineDescription)
    (b : Bool)
    (hsourceSimulator : sourceSimulator.SubroutineReady)
    (hcheckerSimulator : checkerSimulator.SubroutineReady) : List State :=
  List.append (U12ZeroBootstrap.table.states.map State.bootstrap)
    (List.append ((fusedTable source.start).states.map State.sourceEmit)
      (List.append
        ((Tape2SubroutineLift.table sourceSimulator hsourceSimulator).states.map
          State.sourceSim)
        (List.append
          ((swappedFusedTable recognizer.start).states.map State.checkerEmit)
          (List.append
            ((Tape2SubroutineLift.table checkerSimulator
              hcheckerSimulator).states.map State.checkerSim)
            (List.append
              ((Tape2SubroutineLift.table SimulatorHitExtractorDescription
                simulatorHitExtractorDescription_subroutineReady).states.map
                  State.hitExtract)
              (List.append ((U12HitBranch.table b).states.map State.hitBranch)
                (List.append
                  (PersistentRestaging.table.states.map State.restage)
                  (List.append
                    (U12DispatchBootstrap.table.states.map State.dispatch)
                    [.halt]))))))))

theorem next_target_mem
    (source sourceSimulator recognizer checkerSimulator : MachineDescription)
    (b : Bool)
    (hsourceSimulator : sourceSimulator.SubroutineReady)
    (hcheckerSimulator : checkerSimulator.SubroutineReady) :
    forall state : State,
      state ∈ states source sourceSimulator recognizer checkerSimulator b
        hsourceSimulator hcheckerSimulator ->
      forall r0 r1 r2 st,
        next source sourceSimulator recognizer checkerSimulator b
          hsourceSimulator hcheckerSimulator state r0 r1 r2 = some st ->
        st.target ∈ states source sourceSimulator recognizer checkerSimulator b
          hsourceSimulator hcheckerSimulator := by
  intro state hstate r0 r1 r2 st hnext
  cases state with
  | bootstrap state =>
      by_cases hhalt : state = U12ZeroBootstrap.State.halt
      · change (if state = U12ZeroBootstrap.State.halt then _ else _) =
            some st at hnext
        rw [if_pos hhalt] at hnext
        injection hnext with hst
        subst st
        have hstart := (fusedTable source.start).start_mem
        change Sum.inl RawLayoutPreparation.State.seekRawEnd ∈
          (fusedTable source.start).states at hstart
        simpa [states] using hstart
      · change (if state = U12ZeroBootstrap.State.halt then _ else _) =
            some st at hnext
        rw [if_neg hhalt] at hnext
        cases hlocal : U12ZeroBootstrap.table.next state r0 r1 r2 with
        | none => rw [hlocal] at hnext; simp at hnext
        | some localStep =>
            rw [hlocal] at hnext
            simp only [Option.map_some] at hnext
            cases hnext
            have hlocalMem := U12ZeroBootstrap.table.next_target_mem
              state (by simpa [states] using hstate)
              r0 r1 r2 localStep hlocal
            simpa [states, U12PhaseFusion.mapStep] using hlocalMem
  | sourceEmit state =>
      by_cases hhalt : state = (fusedTable source.start).halt
      · change (if state = (fusedTable source.start).halt then _ else _) =
            some st at hnext
        rw [if_pos hhalt] at hnext
        cases hnext
        have hstart := (Tape2SubroutineLift.table
          sourceSimulator hsourceSimulator).start_mem
        change sourceSimulator.start ∈
          (Tape2SubroutineLift.table sourceSimulator
            hsourceSimulator).states at hstart
        simpa [states] using hstart
      · change (if state = (fusedTable source.start).halt then _ else _) =
            some st at hnext
        rw [if_neg hhalt] at hnext
        cases hlocal : (fusedTable source.start).next state r0 r1 r2 with
        | none => rw [hlocal] at hnext; simp at hnext
        | some localStep =>
            rw [hlocal] at hnext
            simp only [Option.map_some] at hnext
            cases hnext
            have hlocalMem := (fusedTable source.start).next_target_mem
              state (by simpa [states] using hstate)
              r0 r1 r2 localStep hlocal
            simpa [states, U12PhaseFusion.mapStep] using hlocalMem
  | sourceSim state =>
      let M := Tape2SubroutineLift.table sourceSimulator hsourceSimulator
      by_cases hhalt : state = M.halt
      · change (if state = M.halt then _ else _) = some st at hnext
        rw [if_pos hhalt] at hnext
        cases hnext
        have hstart := (swappedFusedTable recognizer.start).start_mem
        change Sum.inl RawLayoutPreparation.State.seekRawEnd ∈
          (swappedFusedTable recognizer.start).states at hstart
        simpa [states] using hstart
      · change (if state = M.halt then _ else _) = some st at hnext
        rw [if_neg hhalt] at hnext
        cases hlocal : M.next state r0 r1 r2 with
        | none => rw [hlocal] at hnext; simp at hnext
        | some localStep =>
            rw [hlocal] at hnext
            simp only [Option.map_some] at hnext
            cases hnext
            have hlocalMem := M.next_target_mem state
              (by simpa [states, M] using hstate)
              r0 r1 r2 localStep hlocal
            simpa [states, M, U12PhaseFusion.mapStep] using hlocalMem
  | checkerEmit state =>
      by_cases hhalt : state = (swappedFusedTable recognizer.start).halt
      · change (if state = (swappedFusedTable recognizer.start).halt then
            _ else _) = some st at hnext
        rw [if_pos hhalt] at hnext
        cases hnext
        have hstart := (Tape2SubroutineLift.table
          checkerSimulator hcheckerSimulator).start_mem
        change checkerSimulator.start ∈
          (Tape2SubroutineLift.table checkerSimulator
            hcheckerSimulator).states at hstart
        simpa [states] using hstart
      · change (if state = (swappedFusedTable recognizer.start).halt then
            _ else _) = some st at hnext
        rw [if_neg hhalt] at hnext
        cases hlocal : (swappedFusedTable recognizer.start).next
            state r0 r1 r2 with
        | none => rw [hlocal] at hnext; simp at hnext
        | some localStep =>
            rw [hlocal] at hnext
            simp only [Option.map_some] at hnext
            cases hnext
            have hlocalMem :=
              (swappedFusedTable recognizer.start).next_target_mem state
                (by simpa [states] using hstate)
                r0 r1 r2 localStep hlocal
            simpa [states, U12PhaseFusion.mapStep] using hlocalMem
  | checkerSim state =>
      let M := Tape2SubroutineLift.table checkerSimulator hcheckerSimulator
      by_cases hhalt : state = M.halt
      · change (if state = M.halt then _ else _) = some st at hnext
        rw [if_pos hhalt] at hnext
        cases hnext
        have hstart := (Tape2SubroutineLift.table
          SimulatorHitExtractorDescription
          simulatorHitExtractorDescription_subroutineReady).start_mem
        change SimulatorHitExtractorDescription.start ∈
          (Tape2SubroutineLift.table SimulatorHitExtractorDescription
            simulatorHitExtractorDescription_subroutineReady).states at hstart
        simpa [states] using hstart
      · change (if state = M.halt then _ else _) = some st at hnext
        rw [if_neg hhalt] at hnext
        cases hlocal : M.next state r0 r1 r2 with
        | none => rw [hlocal] at hnext; simp at hnext
        | some localStep =>
            rw [hlocal] at hnext
            simp only [Option.map_some] at hnext
            cases hnext
            have hlocalMem := M.next_target_mem state
              (by simpa [states, M] using hstate)
              r0 r1 r2 localStep hlocal
            simpa [states, M, U12PhaseFusion.mapStep] using hlocalMem
  | hitExtract state =>
      let M := Tape2SubroutineLift.table SimulatorHitExtractorDescription
        simulatorHitExtractorDescription_subroutineReady
      by_cases hhalt : state = M.halt
      · change (if state = M.halt then _ else _) = some st at hnext
        rw [if_pos hhalt] at hnext
        cases hnext
        have hstart := (U12HitBranch.table b).start_mem
        change U12HitBranch.State.inspect ∈
          (U12HitBranch.table b).states at hstart
        simpa [states] using hstart
      · change (if state = M.halt then _ else _) = some st at hnext
        rw [if_neg hhalt] at hnext
        cases hlocal : M.next state r0 r1 r2 with
        | none => rw [hlocal] at hnext; simp at hnext
        | some localStep =>
            rw [hlocal] at hnext
            simp only [Option.map_some] at hnext
            cases hnext
            have hlocalMem := M.next_target_mem state
              (by simpa [states, M] using hstate)
              r0 r1 r2 localStep hlocal
            simpa [states, M, U12PhaseFusion.mapStep] using hlocalMem
  | hitBranch state =>
      by_cases hsuccess : state = U12HitBranch.State.successHalt
      · change (if state = U12HitBranch.State.successHalt then _ else _) =
            some st at hnext
        rw [if_pos hsuccess] at hnext
        cases hnext
        simp [states]
      · by_cases hfailure : state = U12HitBranch.State.failureExit
        · change (if state = U12HitBranch.State.successHalt then _ else _) =
              some st at hnext
          rw [if_neg hsuccess, if_pos hfailure] at hnext
          cases hnext
          have hstart := PersistentRestaging.table.start_mem
          change PersistentRestaging.State.checkerSeek ∈
            PersistentRestaging.table.states at hstart
          simpa [states] using hstart
        · change (if state = U12HitBranch.State.successHalt then _ else _) =
              some st at hnext
          rw [if_neg hsuccess, if_neg hfailure] at hnext
          cases hlocal : (U12HitBranch.table b).next state r0 r1 r2 with
          | none => rw [hlocal] at hnext; simp at hnext
          | some localStep =>
              rw [hlocal] at hnext
              simp only [Option.map_some] at hnext
              cases hnext
              have hlocalMem := (U12HitBranch.table b).next_target_mem
                state (by simpa [states] using hstate)
                r0 r1 r2 localStep hlocal
              simpa [states, U12PhaseFusion.mapStep] using hlocalMem
  | restage state =>
      by_cases hhalt : state = PersistentRestaging.table.halt
      · change (if state = PersistentRestaging.table.halt then _ else _) =
            some st at hnext
        rw [if_pos hhalt] at hnext
        cases hnext
        have hstart := U12DispatchBootstrap.table.start_mem
        change U12DispatchBootstrap.State.length0 ∈
          U12DispatchBootstrap.table.states at hstart
        simpa [states] using hstart
      · change (if state = PersistentRestaging.table.halt then _ else _) =
            some st at hnext
        rw [if_neg hhalt] at hnext
        cases hlocal : PersistentRestaging.table.next state r0 r1 r2 with
        | none => rw [hlocal] at hnext; simp at hnext
        | some localStep =>
            rw [hlocal] at hnext
            simp only [Option.map_some] at hnext
            cases hnext
            have hlocalMem := PersistentRestaging.table.next_target_mem
              state (by simpa [states] using hstate)
              r0 r1 r2 localStep hlocal
            simpa [states, U12PhaseFusion.mapStep] using hlocalMem
  | dispatch state =>
      by_cases hhalt : state = U12DispatchBootstrap.table.halt
      · change (if state = U12DispatchBootstrap.table.halt then _ else _) =
            some st at hnext
        rw [if_pos hhalt] at hnext
        cases hnext
        have hstart := (fusedTable source.start).start_mem
        change Sum.inl RawLayoutPreparation.State.seekRawEnd ∈
          (fusedTable source.start).states at hstart
        simpa [states] using hstart
      · change (if state = U12DispatchBootstrap.table.halt then _ else _) =
            some st at hnext
        rw [if_neg hhalt] at hnext
        cases hlocal : U12DispatchBootstrap.table.next state r0 r1 r2 with
        | none => rw [hlocal] at hnext; simp at hnext
        | some localStep =>
            rw [hlocal] at hnext
            simp only [Option.map_some] at hnext
            cases hnext
            have hlocalMem := U12DispatchBootstrap.table.next_target_mem
              state (by simpa [states] using hstate)
              r0 r1 r2 localStep hlocal
            simpa [states, U12PhaseFusion.mapStep] using hlocalMem
  | halt => simp [next] at hnext

def table
    (source sourceSimulator recognizer checkerSimulator : MachineDescription)
    (b : Bool)
    (hsourceSimulator : sourceSimulator.SubroutineReady)
    (hcheckerSimulator : checkerSimulator.SubroutineReady) :
    TypedStateTable State :=
  TypedStateTable.ofList
    (states source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator)
    (.bootstrap U12ZeroBootstrap.State.lengthScan) .halt
    (next source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator)
    (by
      simpa [states] using
        U12ZeroBootstrap.state_mem U12ZeroBootstrap.State.lengthScan)
    (by simp [states]) (by intros; rfl)
    (next_target_mem source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator)

section PhaseRuns

variable
    (source sourceSimulator recognizer checkerSimulator : MachineDescription)
    (b : Bool)
    (hsourceSimulator : sourceSimulator.SubroutineReady)
    (hcheckerSimulator : checkerSimulator.SubroutineReady)

local notation "M" =>
  table source sourceSimulator recognizer checkerSimulator b
    hsourceSimulator hcheckerSimulator

theorem bootstrap_mem
    (state : U12ZeroBootstrap.State)
    (hstate : state ∈ U12ZeroBootstrap.table.states) :
    State.bootstrap state ∈ (M).states := by
  simpa [table, TypedStateTable.ofList, states] using hstate

theorem sourceEmit_mem
    (state : FusedLayoutEmission.FusedState)
    (hstate : state ∈ (fusedTable source.start).states) :
    State.sourceEmit state ∈ (M).states := by
  simpa [table, TypedStateTable.ofList, states] using hstate

theorem sourceSim_mem
    (state : Nat)
    (hstate : state ∈
      (Tape2SubroutineLift.table sourceSimulator hsourceSimulator).states) :
    State.sourceSim state ∈ (M).states := by
  simpa [table, TypedStateTable.ofList, states] using hstate

theorem checkerEmit_mem
    (state : FusedLayoutEmission.FusedState)
    (hstate : state ∈ (swappedFusedTable recognizer.start).states) :
    State.checkerEmit state ∈ (M).states := by
  simpa [table, TypedStateTable.ofList, states] using hstate

theorem checkerSim_mem
    (state : Nat)
    (hstate : state ∈
      (Tape2SubroutineLift.table checkerSimulator hcheckerSimulator).states) :
    State.checkerSim state ∈ (M).states := by
  simpa [table, TypedStateTable.ofList, states] using hstate

theorem hitExtract_mem
    (state : Nat)
    (hstate : state ∈
      (Tape2SubroutineLift.table SimulatorHitExtractorDescription
        simulatorHitExtractorDescription_subroutineReady).states) :
    State.hitExtract state ∈ (M).states := by
  simpa [table, TypedStateTable.ofList, states] using hstate

theorem hitBranch_mem
    (state : U12HitBranch.State)
    (hstate : state ∈ (U12HitBranch.table b).states) :
    State.hitBranch state ∈ (M).states := by
  simpa [table, TypedStateTable.ofList, states] using hstate

theorem restage_mem
    (state : PersistentRestaging.State)
    (hstate : state ∈ PersistentRestaging.table.states) :
    State.restage state ∈ (M).states := by
  simpa [table, TypedStateTable.ofList, states] using hstate

theorem dispatch_mem
    (state : U12DispatchBootstrap.State)
    (hstate : state ∈ U12DispatchBootstrap.table.states) :
    State.dispatch state ∈ (M).states := by
  simpa [table, TypedStateTable.ofList, states] using hstate

theorem embeds_bootstrap :
    EmbedsBeforeHalt U12ZeroBootstrap.table M State.bootstrap := by
  intro state hstate r0 r1 r2
  change state ≠ U12ZeroBootstrap.State.halt at hstate
  change next source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator (.bootstrap state) r0 r1 r2 = _
  simp [next, hstate]

theorem embeds_sourceEmit :
    EmbedsBeforeHalt (fusedTable source.start) M State.sourceEmit := by
  intro state hstate r0 r1 r2
  change next source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator (.sourceEmit state) r0 r1 r2 = _
  simp [next, hstate]

theorem embeds_sourceSim :
    EmbedsBeforeHalt
      (Tape2SubroutineLift.table sourceSimulator hsourceSimulator)
      M State.sourceSim := by
  intro state hstate r0 r1 r2
  change next source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator (.sourceSim state) r0 r1 r2 = _
  simp [next, hstate]

theorem embeds_checkerEmit :
    EmbedsBeforeHalt (swappedFusedTable recognizer.start)
      M State.checkerEmit := by
  intro state hstate r0 r1 r2
  change next source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator (.checkerEmit state) r0 r1 r2 = _
  simp [next, hstate]

theorem embeds_checkerSim :
    EmbedsBeforeHalt
      (Tape2SubroutineLift.table checkerSimulator hcheckerSimulator)
      M State.checkerSim := by
  intro state hstate r0 r1 r2
  change next source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator (.checkerSim state) r0 r1 r2 = _
  simp [next, hstate]

theorem embeds_hitExtract :
    EmbedsBeforeHalt
      (Tape2SubroutineLift.table SimulatorHitExtractorDescription
        simulatorHitExtractorDescription_subroutineReady)
      M State.hitExtract := by
  intro state hstate r0 r1 r2
  change next source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator (.hitExtract state) r0 r1 r2 = _
  simp [next, hstate]

theorem embeds_restage :
    EmbedsBeforeHalt PersistentRestaging.table M State.restage := by
  intro state hstate r0 r1 r2
  change next source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator (.restage state) r0 r1 r2 = _
  simp [next, hstate]

theorem embeds_dispatch :
    EmbedsBeforeHalt U12DispatchBootstrap.table M State.dispatch := by
  intro state hstate r0 r1 r2
  change next source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator (.dispatch state) r0 r1 r2 = _
  simp [next, hstate]

theorem bridge_bootstrap (T0 T1 T2 : Tape Bool) :
    (M).Leads
      ((M).config (.bootstrap U12ZeroBootstrap.State.halt) T0 T1 T2)
      ((M).config
        (.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
        T0 T1 T2) := by
  exact TypedStateTable.leads_step M
    (bootstrap_mem source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator _ U12ZeroBootstrap.table.halt_mem)
    (st := ⟨.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd),
      keepS, keepS, keepS⟩)
    (by rfl) rfl rfl rfl

theorem bridge_sourceEmit (T0 T1 T2 : Tape Bool) :
    (M).Leads
      ((M).config (.sourceEmit (fusedTable source.start).halt) T0 T1 T2)
      ((M).config (.sourceSim sourceSimulator.start)
        T0 T1 (keepL.apply T2)) := by
  exact TypedStateTable.leads_step M
    (sourceEmit_mem source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator _
      (fusedTable source.start).halt_mem)
    (st := ⟨.sourceSim sourceSimulator.start, keepS, keepS, keepL⟩)
    (by rfl) rfl rfl rfl

theorem bridge_sourceSim (T0 T1 T2 : Tape Bool) :
    (M).Leads
      ((M).config (.sourceSim sourceSimulator.halt) T0 T1 T2)
      ((M).config
        (.checkerEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
        T0 T1 T2) := by
  have hhalt :
      (Tape2SubroutineLift.table sourceSimulator hsourceSimulator).halt =
        sourceSimulator.halt := rfl
  exact TypedStateTable.leads_step M
    (sourceSim_mem source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator _
      (by simpa [hhalt] using
        (Tape2SubroutineLift.table sourceSimulator
          hsourceSimulator).halt_mem))
    (st := ⟨.checkerEmit
      (Sum.inl RawLayoutPreparation.State.seekRawEnd), keepS, keepS, keepS⟩)
    (by
      change next source sourceSimulator recognizer checkerSimulator b
        hsourceSimulator hcheckerSimulator
        (.sourceSim sourceSimulator.halt) _ _ _ = _
      change (if sourceSimulator.halt =
          (Tape2SubroutineLift.table sourceSimulator hsourceSimulator).halt
        then _ else _) = _
      rw [if_pos (by rfl)]) rfl rfl rfl

theorem bridge_checkerEmit (T0 T1 T2 : Tape Bool) :
    (M).Leads
      ((M).config (.checkerEmit (swappedFusedTable recognizer.start).halt)
        T0 T1 T2)
      ((M).config (.checkerSim checkerSimulator.start)
        T0 T1 (keepL.apply T2)) := by
  exact TypedStateTable.leads_step M
    (checkerEmit_mem source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator _
      (swappedFusedTable recognizer.start).halt_mem)
    (st := ⟨.checkerSim checkerSimulator.start, keepS, keepS, keepL⟩)
    (by rfl) rfl rfl rfl

theorem bridge_checkerSim (T0 T1 T2 : Tape Bool) :
    (M).Leads
      ((M).config (.checkerSim checkerSimulator.halt) T0 T1 T2)
      ((M).config (.hitExtract SimulatorHitExtractorDescription.start)
        T0 T1 T2) := by
  exact TypedStateTable.leads_step M
    (checkerSim_mem source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator _
      (Tape2SubroutineLift.table checkerSimulator
        hcheckerSimulator).halt_mem)
    (st := ⟨.hitExtract SimulatorHitExtractorDescription.start,
      keepS, keepS, keepS⟩)
    (by
      change next source sourceSimulator recognizer checkerSimulator b
        hsourceSimulator hcheckerSimulator
        (.checkerSim checkerSimulator.halt) _ _ _ = _
      change (if checkerSimulator.halt =
          (Tape2SubroutineLift.table checkerSimulator
            hcheckerSimulator).halt then _ else _) = _
      rw [if_pos (by rfl)]) rfl rfl rfl

theorem bridge_hitExtract (T0 T1 T2 : Tape Bool) :
    (M).Leads
      ((M).config (.hitExtract SimulatorHitExtractorDescription.halt)
        T0 T1 T2)
      ((M).config (.hitBranch U12HitBranch.State.inspect) T0 T1 T2) := by
  exact TypedStateTable.leads_step M
    (hitExtract_mem source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator _
      (Tape2SubroutineLift.table SimulatorHitExtractorDescription
        simulatorHitExtractorDescription_subroutineReady).halt_mem)
    (st := ⟨.hitBranch U12HitBranch.State.inspect, keepS, keepS, keepS⟩)
    (by rfl) rfl rfl rfl

theorem bridge_hitSuccess (T0 T1 T2 : Tape Bool) :
    (M).Leads
      ((M).config (.hitBranch U12HitBranch.State.successHalt) T0 T1 T2)
      ((M).config .halt T0 T1 T2) := by
  exact TypedStateTable.leads_step M
    (hitBranch_mem source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator _ (U12HitBranch.table b).halt_mem)
    (st := ⟨.halt, keepS, keepS, keepS⟩)
    (by rfl) rfl rfl rfl

theorem bridge_hitFailure (T0 T1 T2 : Tape Bool) :
    (M).Leads
      ((M).config (.hitBranch U12HitBranch.State.failureExit) T0 T1 T2)
      ((M).config (.restage PersistentRestaging.State.checkerSeek)
        T0 T1 T2) := by
  exact TypedStateTable.leads_step M
    (hitBranch_mem source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator _
      (by simp [U12HitBranch.table, TypedStateTable.ofList,
        U12HitBranch.states]))
    (st := ⟨.restage PersistentRestaging.State.checkerSeek,
      keepS, keepS, keepS⟩)
    (by rfl) rfl rfl rfl

theorem bridge_restage (T0 T1 T2 : Tape Bool) :
    (M).Leads
      ((M).config (.restage PersistentRestaging.State.halt) T0 T1 T2)
      ((M).config (.dispatch U12DispatchBootstrap.State.length0)
        T0 T1 T2) := by
  exact TypedStateTable.leads_step M
    (restage_mem source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator _ PersistentRestaging.table.halt_mem)
    (st := ⟨.dispatch U12DispatchBootstrap.State.length0,
      keepS, keepS, keepS⟩)
    (by rfl) rfl rfl rfl

theorem bridge_dispatch (T0 T1 T2 : Tape Bool) :
    (M).Leads
      ((M).config (.dispatch U12DispatchBootstrap.State.halt) T0 T1 T2)
      ((M).config
        (.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
        T0 T1 T2) := by
  exact TypedStateTable.leads_step M
    (dispatch_mem source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator _
      U12DispatchBootstrap.table.halt_mem)
    (st := ⟨.sourceEmit
      (Sum.inl RawLayoutPreparation.State.seekRawEnd), keepS, keepS, keepS⟩)
    (by rfl) rfl rfl rfl

theorem leads_bootstrap
    (raw : List Bool) :
    (M).Leads
      ((M).config (.bootstrap U12ZeroBootstrap.State.lengthScan)
        (Tape.input (show Word Bool from raw)) Tape.blank Tape.blank)
      ((M).config
        (.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
        (U12ZeroBootstrap.bootstrapFuelTape (raw.length + 2))
        (U12ZeroBootstrap.bootstrapFuelTape 1)
        (U12ZeroBootstrap.bootstrapCandidateTape raw)) := by
  apply leads_via_first_halt_and_bridge
    U12ZeroBootstrap.table M State.bootstrap
    (embeds_bootstrap source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator)
    (bootstrap_mem source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator)
    U12ZeroBootstrap.State.lengthScan U12ZeroBootstrap.table.start_mem
    (Tape.input (show Word Bool from raw)) Tape.blank Tape.blank
    (U12ZeroBootstrap.bootstrapFuelTape (raw.length + 2))
    (U12ZeroBootstrap.bootstrapFuelTape 1)
    (U12ZeroBootstrap.bootstrapCandidateTape raw)
    (U12ZeroBootstrap.leads_initialized_to_exact_bootstrap raw)
  exact bridge_bootstrap source sourceSimulator recognizer checkerSimulator b
    hsourceSimulator hcheckerSimulator _ _ _

theorem leads_sourceEmission_of_equiv
    (T0 T1 T2 : Tape Bool) (head : Bool) (tail : Word Bool) (fuel : Nat)
    (hT1 : Tape.Equiv T1 (cursorFuelSourceTape fuel))
    (hT2 : Tape.Equiv T2 (Tape.input (head :: tail))) :
    exists A0 A1 A2 : Tape Bool,
      (M).Leads
        ((M).config
          (.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
          T0 T1 T2)
        ((M).config (.sourceSim sourceSimulator.start)
          A0 A1 (keepL.apply A2)) ∧
      Tape.Equiv A0 T0 ∧
      Tape.Equiv A1 (rawEmissionFinalScratch (head :: tail) fuel) ∧
      Tape.Equiv A2 (rawEmissionOutputTape source (head :: tail) fuel) := by
  rcases fused_runs_prepare_then_rawEmission source T0 head tail fuel with
    ⟨steps, V0, V1, V2, hcanonical, hV0, hV1, hV2⟩
  rcases runConfig_endpoint_of_equiv3 (fusedTable source.start) steps
      (Sum.inl RawLayoutPreparation.State.seekRawEnd)
      (fusedTable source.start).start_mem (fusedTable source.start).halt
      T0 T1 T2 T0 (cursorFuelSourceTape fuel)
      (Tape.input (head :: tail)) V0 V1 V2
      (Tape.Equiv.refl T0) hT1 hT2 hcanonical with
    ⟨A0, A1, A2, hrun, hA0, hA1, hA2⟩
  have hlocal : (fusedTable source.start).Leads
      ((fusedTable source.start).config
        (Sum.inl RawLayoutPreparation.State.seekRawEnd) T0 T1 T2)
      ((fusedTable source.start).config
        (fusedTable source.start).halt A0 A1 A2) :=
    U12PhaseFusion.leads_of_runConfig
      (fusedTable source.start) hrun
  refine ⟨A0, A1, A2, ?_, Tape.Equiv.trans hA0 hV0,
    Tape.Equiv.trans hA1 hV1, Tape.Equiv.trans hA2 hV2⟩
  apply leads_via_first_halt_and_bridge
    (fusedTable source.start) M State.sourceEmit
    (embeds_sourceEmit source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator)
    (sourceEmit_mem source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator)
    (Sum.inl RawLayoutPreparation.State.seekRawEnd)
    (fusedTable source.start).start_mem T0 T1 T2 A0 A1 A2 hlocal
  exact bridge_sourceEmit source sourceSimulator recognizer checkerSimulator b
    hsourceSimulator hcheckerSimulator A0 A1 A2

theorem leads_sourceSimulation
    (T0 T1 Tin Tout : Tape Bool)
    (hhalt : sourceSimulator.HaltsFromTape Tin Tout) :
    (M).Leads
      ((M).config (.sourceSim sourceSimulator.start) T0 T1 Tin)
      ((M).config
        (.checkerEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
        T0 T1 Tout) := by
  rcases Tape2SubroutineLift.description_haltsWithTapes
      sourceSimulator hsourceSimulator T0 T1 Tin Tout hhalt with
    ⟨steps, hrun⟩
  have hlocal :
      (Tape2SubroutineLift.table sourceSimulator hsourceSimulator).Leads
        ((Tape2SubroutineLift.table sourceSimulator hsourceSimulator).config
          sourceSimulator.start T0 T1 Tin)
        ((Tape2SubroutineLift.table sourceSimulator hsourceSimulator).config
          sourceSimulator.halt T0 T1 Tout) :=
    U12PhaseFusion.leads_of_runConfig
      (Tape2SubroutineLift.table sourceSimulator hsourceSimulator) hrun
  apply leads_via_first_halt_and_bridge
    (Tape2SubroutineLift.table sourceSimulator hsourceSimulator)
    M State.sourceSim
    (embeds_sourceSim source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator)
    (sourceSim_mem source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator)
    sourceSimulator.start
    (Tape2SubroutineLift.table sourceSimulator hsourceSimulator).start_mem
    T0 T1 Tin T0 T1 Tout hlocal
  exact bridge_sourceSim source sourceSimulator recognizer checkerSimulator b
    hsourceSimulator hcheckerSimulator T0 T1 Tout

theorem leads_checkerEmission_of_equiv
    (T0 T1 T2 : Tape Bool) (head : Bool) (tail : Word Bool) (fuel : Nat)
    (hT0 : Tape.Equiv T0 (cursorFuelSourceTape fuel))
    (hT2 : Tape.Equiv T2 (Tape.input (head :: tail))) :
    exists A0 A1 A2 : Tape Bool,
      (M).Leads
        ((M).config
          (.checkerEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
          T0 T1 T2)
        ((M).config (.checkerSim checkerSimulator.start)
          A0 A1 (keepL.apply A2)) ∧
      Tape.Equiv A0 (rawEmissionFinalScratch (head :: tail) fuel) ∧
      Tape.Equiv A1 T1 ∧
      Tape.Equiv A2
        (rawEmissionOutputTape recognizer (head :: tail) fuel) := by
  rcases swappedFused_runs_prepare_then_rawEmission
      recognizer T1 head tail fuel with
    ⟨steps, V0, V1, V2, hrun, hV0, hV1, hV2⟩
  have hcanonical :
      (swappedFusedTable recognizer.start).description.runConfig steps
          ((swappedFusedTable recognizer.start).config
            (Sum.inl RawLayoutPreparation.State.seekRawEnd)
            (cursorFuelSourceTape fuel) T1 (Tape.input (head :: tail))) =
        (swappedFusedTable recognizer.start).config
          (swappedFusedTable recognizer.start).halt V0 V1 V2 := by
    change (swappedFusedD recognizer.start).runConfig steps
        (ThreeTape.config
          ((fusedTable recognizer.start).stateId
            (Sum.inl RawLayoutPreparation.State.seekRawEnd))
          (cursorFuelSourceTape fuel) T1 (Tape.input (head :: tail))) =
      ThreeTape.config
        ((fusedTable recognizer.start).stateId
          (Sum.inr FuelSimulatorCore.State.halt)) V0 V1 V2
    exact hrun
  rcases runConfig_endpoint_of_equiv3
      (swappedFusedTable recognizer.start) steps
      (Sum.inl RawLayoutPreparation.State.seekRawEnd)
      (swappedFusedTable recognizer.start).start_mem
      (swappedFusedTable recognizer.start).halt
      T0 T1 T2 (cursorFuelSourceTape fuel) T1
      (Tape.input (head :: tail)) V0 V1 V2
      hT0 (Tape.Equiv.refl T1) hT2 hcanonical with
    ⟨A0, A1, A2, hactual, hA0, hA1, hA2⟩
  have hlocal : (swappedFusedTable recognizer.start).Leads
      ((swappedFusedTable recognizer.start).config
        (Sum.inl RawLayoutPreparation.State.seekRawEnd) T0 T1 T2)
      ((swappedFusedTable recognizer.start).config
        (swappedFusedTable recognizer.start).halt A0 A1 A2) :=
    U12PhaseFusion.leads_of_runConfig
      (swappedFusedTable recognizer.start) hactual
  refine ⟨A0, A1, A2, ?_, Tape.Equiv.trans hA0 hV0,
    Tape.Equiv.trans hA1 hV1, Tape.Equiv.trans hA2 hV2⟩
  apply leads_via_first_halt_and_bridge
    (swappedFusedTable recognizer.start) M State.checkerEmit
    (embeds_checkerEmit source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator)
    (checkerEmit_mem source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator)
    (Sum.inl RawLayoutPreparation.State.seekRawEnd)
    (swappedFusedTable recognizer.start).start_mem
    T0 T1 T2 A0 A1 A2 hlocal
  exact bridge_checkerEmit source sourceSimulator recognizer checkerSimulator b
    hsourceSimulator hcheckerSimulator A0 A1 A2

theorem leads_checkerSimulation
    (T0 T1 Tin Tout : Tape Bool)
    (hhalt : checkerSimulator.HaltsFromTape Tin Tout) :
    (M).Leads
      ((M).config (.checkerSim checkerSimulator.start) T0 T1 Tin)
      ((M).config (.hitExtract SimulatorHitExtractorDescription.start)
        T0 T1 Tout) := by
  rcases Tape2SubroutineLift.description_haltsWithTapes
      checkerSimulator hcheckerSimulator T0 T1 Tin Tout hhalt with
    ⟨steps, hrun⟩
  have hlocal :
      (Tape2SubroutineLift.table checkerSimulator hcheckerSimulator).Leads
        ((Tape2SubroutineLift.table checkerSimulator
          hcheckerSimulator).config checkerSimulator.start T0 T1 Tin)
        ((Tape2SubroutineLift.table checkerSimulator
          hcheckerSimulator).config checkerSimulator.halt T0 T1 Tout) :=
    U12PhaseFusion.leads_of_runConfig
      (Tape2SubroutineLift.table checkerSimulator hcheckerSimulator) hrun
  apply leads_via_first_halt_and_bridge
    (Tape2SubroutineLift.table checkerSimulator hcheckerSimulator)
    M State.checkerSim
    (embeds_checkerSim source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator)
    (checkerSim_mem source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator)
    checkerSimulator.start
    (Tape2SubroutineLift.table checkerSimulator hcheckerSimulator).start_mem
    T0 T1 Tin T0 T1 Tout hlocal
  exact bridge_checkerSim source sourceSimulator recognizer checkerSimulator b
    hsourceSimulator hcheckerSimulator T0 T1 Tout

theorem leads_hitExtraction
    (T0 T1 Tin Tout : Tape Bool)
    (hhalt : SimulatorHitExtractorDescription.HaltsFromTape Tin Tout) :
    (M).Leads
      ((M).config (.hitExtract SimulatorHitExtractorDescription.start)
        T0 T1 Tin)
      ((M).config (.hitBranch U12HitBranch.State.inspect) T0 T1 Tout) := by
  rcases Tape2SubroutineLift.description_haltsWithTapes
      SimulatorHitExtractorDescription
      simulatorHitExtractorDescription_subroutineReady
      T0 T1 Tin Tout hhalt with
    ⟨steps, hrun⟩
  let H := Tape2SubroutineLift.table SimulatorHitExtractorDescription
    simulatorHitExtractorDescription_subroutineReady
  have hlocal : H.Leads
      (H.config SimulatorHitExtractorDescription.start T0 T1 Tin)
      (H.config SimulatorHitExtractorDescription.halt T0 T1 Tout) :=
    U12PhaseFusion.leads_of_runConfig H hrun
  apply leads_via_first_halt_and_bridge H M State.hitExtract
    (embeds_hitExtract source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator)
    (hitExtract_mem source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator)
    SimulatorHitExtractorDescription.start H.start_mem
    T0 T1 Tin T0 T1 Tout hlocal
  exact bridge_hitExtract source sourceSimulator recognizer checkerSimulator b
    hsourceSimulator hcheckerSimulator T0 T1 Tout

/-- Lift one hit-branch row while neither live exit has yet been reached. -/
theorem leads_hitStep
    (state : U12HitBranch.State)
    (hstate : state ∈ (U12HitBranch.table b).states)
    (hsuccess : state ≠ U12HitBranch.State.successHalt)
    (hfailure : state ≠ U12HitBranch.State.failureExit)
    (T0 T1 T2 : Tape Bool) (st : TypedStep U12HitBranch.State)
    (hnext : (U12HitBranch.table b).next state
      (Tape.read T0) (Tape.read T1) (Tape.read T2) = some st) :
    (M).Leads
      ((M).config (.hitBranch state) T0 T1 T2)
      ((M).config (.hitBranch st.target)
        (st.action0.apply T0) (st.action1.apply T1)
        (st.action2.apply T2)) := by
  apply TypedStateTable.leads_step M
    (hitBranch_mem source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator state hstate)
    (st := U12PhaseFusion.mapStep State.hitBranch st)
  · change next source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator (.hitBranch state)
        (Tape.read T0) (Tape.read T1) (Tape.read T2) = _
    simp only [next]
    rw [if_neg hsuccess, if_neg hfailure]
    rw [hnext]
    rfl
  · rfl
  · rfl
  · rfl

theorem leads_hitInspect
    (hit : Bool) (padding : Nat) (T0 T1 : Tape Bool) :
    (M).Leads
      ((M).config (.hitBranch U12HitBranch.State.inspect) T0 T1
        (U12HitBranch.hitOutputTape hit padding))
      ((M).config (.hitBranch U12HitBranch.State.branch) T0 T1
        (U12HitBranch.eraseLeftTape
          (singletonBoolWordBits hit).reverse
          (List.replicate padding none) [none])) := by
  apply leads_hitStep source sourceSimulator recognizer checkerSimulator b
    hsourceSimulator hcheckerSimulator U12HitBranch.State.inspect
    (by simp [U12HitBranch.table, TypedStateTable.ofList,
      U12HitBranch.states]) (by decide) (by decide)
    T0 T1 (U12HitBranch.hitOutputTape hit padding)
    ⟨U12HitBranch.State.branch, keepS, keepS, keepL⟩
    (by rfl)

theorem leads_hitBranchTrue
    (padding : Nat) (T0 T1 : Tape Bool) :
    (M).Leads
      ((M).config (.hitBranch U12HitBranch.State.branch) T0 T1
        (U12HitBranch.eraseLeftTape
          (singletonBoolWordBits true).reverse
          (List.replicate padding none) [none]))
      ((M).config (.hitBranch U12HitBranch.State.eraseSuccess) T0 T1
        (U12HitBranch.eraseLeftTape (U12HitBranch.reversedHitTail true)
          (List.replicate padding none) [none, none])) := by
  apply leads_hitStep source sourceSimulator recognizer checkerSimulator b
    hsourceSimulator hcheckerSimulator U12HitBranch.State.branch
    (by simp [U12HitBranch.table, TypedStateTable.ofList,
      U12HitBranch.states]) (by decide) (by decide)
    T0 T1
    (U12HitBranch.eraseLeftTape
      (singletonBoolWordBits true).reverse
      (List.replicate padding none) [none])
    ⟨U12HitBranch.State.eraseSuccess, keepS, keepS, eraseL⟩
    (by
      rw [U12HitBranch.table_next_apply]
      simp [U12HitBranch.reversedHitBits_true,
        U12HitBranch.eraseLeftTape, U12HitBranch.next,
        tapeAtCells, Tape.read]
      rfl)

theorem leads_hitBranchFalse
    (padding : Nat) (T0 T1 : Tape Bool) :
    (M).Leads
      ((M).config (.hitBranch U12HitBranch.State.branch) T0 T1
        (U12HitBranch.eraseLeftTape
          (singletonBoolWordBits false).reverse
          (List.replicate padding none) [none]))
      ((M).config (.hitBranch U12HitBranch.State.eraseFailure) T0 T1
        (U12HitBranch.eraseLeftTape (U12HitBranch.reversedHitTail false)
          (List.replicate padding none) [none, none])) := by
  apply leads_hitStep source sourceSimulator recognizer checkerSimulator b
    hsourceSimulator hcheckerSimulator U12HitBranch.State.branch
    (by simp [U12HitBranch.table, TypedStateTable.ofList,
      U12HitBranch.states]) (by decide) (by decide)
    T0 T1
    (U12HitBranch.eraseLeftTape
      (singletonBoolWordBits false).reverse
      (List.replicate padding none) [none])
    ⟨U12HitBranch.State.eraseFailure, keepS, keepS, eraseL⟩
    (by
      rw [U12HitBranch.table_next_apply]
      simp [U12HitBranch.reversedHitBits_false,
        U12HitBranch.eraseLeftTape, U12HitBranch.next,
        tapeAtCells, Tape.read]
      rfl)

theorem leads_hitEraseSuccess
    (bits : List Bool) (padding right : List (Option Bool))
    (T0 T1 : Tape Bool) :
    (M).Leads
      ((M).config (.hitBranch U12HitBranch.State.eraseSuccess) T0 T1
        (U12HitBranch.eraseLeftTape bits padding right))
      ((M).config (.hitBranch U12HitBranch.State.eraseSuccess) T0 T1
        (U12HitBranch.eraseLeftTape [] padding
          (List.append (List.replicate bits.length none) right))) := by
  induction bits generalizing right with
  | nil => exact TypedStateTable.Leads.refl M _
  | cons bit rest ih =>
      apply TypedStateTable.Leads.trans
        (d := (M).config (.hitBranch U12HitBranch.State.eraseSuccess)
          T0 T1 (U12HitBranch.eraseLeftTape rest padding (none :: right)))
      · have hstep := leads_hitStep source sourceSimulator
          recognizer checkerSimulator b hsourceSimulator hcheckerSimulator
          U12HitBranch.State.eraseSuccess
          (by simp [U12HitBranch.table, TypedStateTable.ofList,
            U12HitBranch.states]) (by decide) (by decide)
          T0 T1 (U12HitBranch.eraseLeftTape (bit :: rest) padding right)
          ⟨U12HitBranch.State.eraseSuccess, keepS, keepS, eraseL⟩
          (by
            rw [U12HitBranch.table_next_apply]
            simp [U12HitBranch.eraseLeftTape, U12HitBranch.next,
              tapeAtCells, Tape.read]
            rfl)
        change (M).Leads
          ((M).config (.hitBranch U12HitBranch.State.eraseSuccess) T0 T1
            (U12HitBranch.eraseLeftTape (bit :: rest) padding right))
          ((M).config (.hitBranch U12HitBranch.State.eraseSuccess)
            (keepS.apply T0) (keepS.apply T1)
            (eraseL.apply
              (U12HitBranch.eraseLeftTape
                (bit :: rest) padding right))) at hstep
        have herase : eraseL.apply
            (U12HitBranch.eraseLeftTape (bit :: rest) padding right) =
          U12HitBranch.eraseLeftTape rest padding (none :: right) := by
          cases rest <;> rfl
        rw [show keepS.apply T0 = T0 by rfl,
          show keepS.apply T1 = T1 by rfl, herase] at hstep
        exact hstep
      · simp only [List.length_cons]
        rw [PersistentRestaging.replicate_succ_eq_append]
        simpa [List.append_assoc] using ih (none :: right)

theorem leads_hitEraseFailure
    (bits : List Bool) (padding right : List (Option Bool))
    (T0 T1 : Tape Bool) :
    (M).Leads
      ((M).config (.hitBranch U12HitBranch.State.eraseFailure) T0 T1
        (U12HitBranch.eraseLeftTape bits padding right))
      ((M).config (.hitBranch U12HitBranch.State.eraseFailure) T0 T1
        (U12HitBranch.eraseLeftTape [] padding
          (List.append (List.replicate bits.length none) right))) := by
  induction bits generalizing right with
  | nil => exact TypedStateTable.Leads.refl M _
  | cons bit rest ih =>
      apply TypedStateTable.Leads.trans
        (d := (M).config (.hitBranch U12HitBranch.State.eraseFailure)
          T0 T1 (U12HitBranch.eraseLeftTape rest padding (none :: right)))
      · have hstep := leads_hitStep source sourceSimulator
          recognizer checkerSimulator b hsourceSimulator hcheckerSimulator
          U12HitBranch.State.eraseFailure
          (by simp [U12HitBranch.table, TypedStateTable.ofList,
            U12HitBranch.states]) (by decide) (by decide)
          T0 T1 (U12HitBranch.eraseLeftTape (bit :: rest) padding right)
          ⟨U12HitBranch.State.eraseFailure, keepS, keepS, eraseL⟩
          (by
            rw [U12HitBranch.table_next_apply]
            simp [U12HitBranch.eraseLeftTape, U12HitBranch.next,
              tapeAtCells, Tape.read]
            rfl)
        change (M).Leads
          ((M).config (.hitBranch U12HitBranch.State.eraseFailure) T0 T1
            (U12HitBranch.eraseLeftTape (bit :: rest) padding right))
          ((M).config (.hitBranch U12HitBranch.State.eraseFailure)
            (keepS.apply T0) (keepS.apply T1)
            (eraseL.apply
              (U12HitBranch.eraseLeftTape
                (bit :: rest) padding right))) at hstep
        have herase : eraseL.apply
            (U12HitBranch.eraseLeftTape (bit :: rest) padding right) =
          U12HitBranch.eraseLeftTape rest padding (none :: right) := by
          cases rest <;> rfl
        rw [show keepS.apply T0 = T0 by rfl,
          show keepS.apply T1 = T1 by rfl, herase] at hstep
        exact hstep
      · simp only [List.length_cons]
        rw [PersistentRestaging.replicate_succ_eq_append]
        simpa [List.append_assoc] using ih (none :: right)

theorem leads_hitFinishSuccess
    (padding right : List (Option Bool)) (T0 T1 : Tape Bool) :
    (M).Leads
      ((M).config (.hitBranch U12HitBranch.State.eraseSuccess) T0 T1
        (U12HitBranch.eraseLeftTape [] padding right))
      ((M).config (.hitBranch U12HitBranch.State.successHalt) T0 T1
        (U12HitBranch.successTape b padding right)) := by
  apply leads_hitStep source sourceSimulator recognizer checkerSimulator b
    hsourceSimulator hcheckerSimulator U12HitBranch.State.eraseSuccess
    (by simp [U12HitBranch.table, TypedStateTable.ofList,
      U12HitBranch.states]) (by decide) (by decide)
    T0 T1 (U12HitBranch.eraseLeftTape [] padding right)
    ⟨U12HitBranch.State.successHalt, keepS, keepS, writeBitR b⟩
    (by
      rw [U12HitBranch.table_next_apply]
      simp [U12HitBranch.eraseLeftTape, U12HitBranch.next,
        tapeAtCells, Tape.read]
      rfl)

theorem leads_hitFinishFailure
    (padding right : List (Option Bool)) (T0 T1 : Tape Bool) :
    (M).Leads
      ((M).config (.hitBranch U12HitBranch.State.eraseFailure) T0 T1
        (U12HitBranch.eraseLeftTape [] padding right))
      ((M).config (.hitBranch U12HitBranch.State.failureExit) T0 T1
        (U12HitBranch.eraseLeftTape [] padding right)) := by
  apply leads_hitStep source sourceSimulator recognizer checkerSimulator b
    hsourceSimulator hcheckerSimulator U12HitBranch.State.eraseFailure
    (by simp [U12HitBranch.table, TypedStateTable.ofList,
      U12HitBranch.states]) (by decide) (by decide)
    T0 T1 (U12HitBranch.eraseLeftTape [] padding right)
    ⟨U12HitBranch.State.failureExit, keepS, keepS, keepS⟩
    (by
      rw [U12HitBranch.table_next_apply]
      simp [U12HitBranch.eraseLeftTape, U12HitBranch.next,
        tapeAtCells, Tape.read]
      rfl)

theorem leads_hitTrue
    (padding : Nat) (T0 T1 : Tape Bool) :
    (M).Leads
      ((M).config (.hitBranch U12HitBranch.State.inspect) T0 T1
        (U12HitBranch.hitOutputTape true padding))
      ((M).config .halt T0 T1
        (U12HitBranch.successBranchTape b padding)) := by
  apply TypedStateTable.Leads.trans
    (leads_hitInspect source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator true padding T0 T1)
  apply TypedStateTable.Leads.trans
    (leads_hitBranchTrue source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator padding T0 T1)
  apply TypedStateTable.Leads.trans
    (leads_hitEraseSuccess source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator
      (U12HitBranch.reversedHitTail true)
      (List.replicate padding none) [none, none] T0 T1)
  apply TypedStateTable.Leads.trans
    (leads_hitFinishSuccess source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator
      (List.replicate padding none)
      (List.append
        (List.replicate (U12HitBranch.reversedHitTail true).length none)
        [none, none]) T0 T1)
  exact bridge_hitSuccess source sourceSimulator recognizer checkerSimulator b
    hsourceSimulator hcheckerSimulator T0 T1 _

theorem leads_hitFalse
    (padding : Nat) (T0 T1 : Tape Bool) :
    (M).Leads
      ((M).config (.hitBranch U12HitBranch.State.inspect) T0 T1
        (U12HitBranch.hitOutputTape false padding))
      ((M).config (.restage PersistentRestaging.State.checkerSeek) T0 T1
        (U12HitBranch.failureBranchTape padding)) := by
  apply TypedStateTable.Leads.trans
    (leads_hitInspect source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator false padding T0 T1)
  apply TypedStateTable.Leads.trans
    (leads_hitBranchFalse source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator padding T0 T1)
  apply TypedStateTable.Leads.trans
    (leads_hitEraseFailure source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator
      (U12HitBranch.reversedHitTail false)
      (List.replicate padding none) [none, none] T0 T1)
  apply TypedStateTable.Leads.trans
    (leads_hitFinishFailure source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator
      (List.replicate padding none)
      (List.append
        (List.replicate (U12HitBranch.reversedHitTail false).length none)
        [none, none]) T0 T1)
  exact bridge_hitFailure source sourceSimulator recognizer checkerSimulator b
    hsourceSimulator hcheckerSimulator T0 T1 _

theorem leads_hitTrue_of_equiv
    (padding : Nat) (T0 T1 T2 : Tape Bool)
    (hT2 : Tape.Equiv T2 (U12HitBranch.hitOutputTape true padding)) :
    exists A0 A1 A2 : Tape Bool,
      (M).Leads
        ((M).config (.hitBranch U12HitBranch.State.inspect) T0 T1 T2)
        ((M).config .halt A0 A1 A2) ∧
      Tape.Equiv A0 T0 ∧ Tape.Equiv A1 T1 ∧
        Tape.Equiv A2 (U12HitBranch.successBranchTape b padding) := by
  exact leads_endpoint_of_equiv3 M
    (.hitBranch U12HitBranch.State.inspect)
    (hitBranch_mem source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator _ (U12HitBranch.table b).start_mem)
    .halt T0 T1 T2 T0 T1
    (U12HitBranch.hitOutputTape true padding)
    T0 T1 (U12HitBranch.successBranchTape b padding)
    (Tape.Equiv.refl T0) (Tape.Equiv.refl T1) hT2
    (leads_hitTrue source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator padding T0 T1)

theorem leads_hitFalse_of_equiv
    (padding : Nat) (T0 T1 T2 : Tape Bool)
    (hT2 : Tape.Equiv T2 (U12HitBranch.hitOutputTape false padding)) :
    exists A0 A1 A2 : Tape Bool,
      (M).Leads
        ((M).config (.hitBranch U12HitBranch.State.inspect) T0 T1 T2)
        ((M).config (.restage PersistentRestaging.State.checkerSeek)
          A0 A1 A2) ∧
      Tape.Equiv A0 T0 ∧ Tape.Equiv A1 T1 ∧
        Tape.Equiv A2 (U12HitBranch.failureBranchTape padding) := by
  exact leads_endpoint_of_equiv3 M
    (.hitBranch U12HitBranch.State.inspect)
    (hitBranch_mem source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator _ (U12HitBranch.table b).start_mem)
    (.restage PersistentRestaging.State.checkerSeek)
    T0 T1 T2 T0 T1 (U12HitBranch.hitOutputTape false padding)
    T0 T1 (U12HitBranch.failureBranchTape padding)
    (Tape.Equiv.refl T0) (Tape.Equiv.refl T1) hT2
    (leads_hitFalse source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator padding T0 T1)

theorem leads_restaging
    (checkerRaw candidateRaw : Word Bool)
    (checkerFuel sourceFuel : Nat) :
    (M).Leads
      ((M).config (.restage PersistentRestaging.State.checkerSeek)
        (rawEmissionFinalScratch checkerRaw checkerFuel)
        (rawEmissionFinalScratch candidateRaw sourceFuel)
        Tape.blank)
      ((M).config (.dispatch U12DispatchBootstrap.State.length0)
        (PersistentRestaging.cleanedFuelTape checkerRaw checkerFuel)
        (PersistentRestaging.cleanedFuelTape candidateRaw sourceFuel)
        (PersistentRestaging.restagedRawTape candidateRaw)) := by
  apply leads_via_first_halt_and_bridge
    PersistentRestaging.table M State.restage
    (embeds_restage source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator)
    (restage_mem source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator)
    PersistentRestaging.State.checkerSeek
    PersistentRestaging.table.start_mem
    (rawEmissionFinalScratch checkerRaw checkerFuel)
    (rawEmissionFinalScratch candidateRaw sourceFuel)
    Tape.blank
    (PersistentRestaging.cleanedFuelTape checkerRaw checkerFuel)
    (PersistentRestaging.cleanedFuelTape candidateRaw sourceFuel)
    (PersistentRestaging.restagedRawTape candidateRaw)
    (PersistentRestaging.leads_restages
      checkerRaw candidateRaw checkerFuel sourceFuel)
  exact bridge_restage source sourceSimulator recognizer checkerSimulator b
    hsourceSimulator hcheckerSimulator _ _ _

theorem leads_restaging_of_equiv
    (checkerRaw candidateRaw : Word Bool)
    (checkerFuel sourceFuel : Nat)
    (T0 T1 T2 : Tape Bool)
    (hT0 : Tape.Equiv T0
      (rawEmissionFinalScratch checkerRaw checkerFuel))
    (hT1 : Tape.Equiv T1
      (rawEmissionFinalScratch candidateRaw sourceFuel))
    (hT2 : Tape.Equiv T2 Tape.blank) :
    exists A0 A1 A2 : Tape Bool,
      (M).Leads
        ((M).config (.restage PersistentRestaging.State.checkerSeek)
          T0 T1 T2)
        ((M).config (.dispatch U12DispatchBootstrap.State.length0)
          A0 A1 A2) ∧
      Tape.Equiv A0
          (PersistentRestaging.cleanedFuelTape checkerRaw checkerFuel) ∧
        Tape.Equiv A1
          (PersistentRestaging.cleanedFuelTape candidateRaw sourceFuel) ∧
        Tape.Equiv A2
          (PersistentRestaging.restagedRawTape candidateRaw) := by
  exact leads_endpoint_of_equiv3 M
    (.restage PersistentRestaging.State.checkerSeek)
    (restage_mem source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator _ PersistentRestaging.table.start_mem)
    (.dispatch U12DispatchBootstrap.State.length0)
    T0 T1 T2
    (rawEmissionFinalScratch checkerRaw checkerFuel)
    (rawEmissionFinalScratch candidateRaw sourceFuel) Tape.blank
    (PersistentRestaging.cleanedFuelTape checkerRaw checkerFuel)
    (PersistentRestaging.cleanedFuelTape candidateRaw sourceFuel)
    (PersistentRestaging.restagedRawTape candidateRaw)
    hT0 hT1 hT2
    (leads_restaging source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator
      checkerRaw candidateRaw checkerFuel sourceFuel)

theorem leads_dispatch
    (T0 T1 T2 U0 U1 U2 : Tape Bool)
    (hleads : U12DispatchBootstrap.table.Leads
      (U12DispatchBootstrap.table.config
        U12DispatchBootstrap.State.length0 T0 T1 T2)
      (U12DispatchBootstrap.table.config
        U12DispatchBootstrap.State.halt U0 U1 U2)) :
    (M).Leads
      ((M).config (.dispatch U12DispatchBootstrap.State.length0)
        T0 T1 T2)
      ((M).config
        (.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
        U0 U1 U2) := by
  apply leads_via_first_halt_and_bridge
    U12DispatchBootstrap.table M State.dispatch
    (embeds_dispatch source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator)
    (dispatch_mem source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator)
    U12DispatchBootstrap.State.length0
    U12DispatchBootstrap.table.start_mem
    T0 T1 T2 U0 U1 U2 hleads
  exact bridge_dispatch source sourceSimulator recognizer checkerSimulator b
    hsourceSimulator hcheckerSimulator _ _ _

theorem leads_dispatch_of_equiv
    (T0 T1 T2 U0 U1 U2 V0 V1 V2 : Tape Bool)
    (hT0 : Tape.Equiv T0 U0) (hT1 : Tape.Equiv T1 U1)
    (hT2 : Tape.Equiv T2 U2)
    (hdispatch : U12DispatchBootstrap.table.Leads
      (U12DispatchBootstrap.table.config
        U12DispatchBootstrap.State.length0 U0 U1 U2)
      (U12DispatchBootstrap.table.config
        U12DispatchBootstrap.State.halt V0 V1 V2)) :
    exists A0 A1 A2 : Tape Bool,
      (M).Leads
        ((M).config (.dispatch U12DispatchBootstrap.State.length0)
          T0 T1 T2)
        ((M).config
          (.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
          A0 A1 A2) ∧
      Tape.Equiv A0 V0 ∧ Tape.Equiv A1 V1 ∧
        Tape.Equiv A2 V2 := by
  exact leads_endpoint_of_equiv3 M
    (.dispatch U12DispatchBootstrap.State.length0)
    (dispatch_mem source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator _
      U12DispatchBootstrap.table.start_mem)
    (.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
    T0 T1 T2 U0 U1 U2 V0 V1 V2 hT0 hT1 hT2
    (leads_dispatch source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator U0 U1 U2 V0 V1 V2 hdispatch)

end PhaseRuns

end U12MasterLoop
end BoundedFuelPairSearch
end Computability
end FoC

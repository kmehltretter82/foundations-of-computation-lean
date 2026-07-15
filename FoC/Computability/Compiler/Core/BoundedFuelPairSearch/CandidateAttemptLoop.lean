import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.CandidateAttemptPrelude
import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.MasterLoop

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
namespace U12CandidateAttemptLoop

open StructuredConstructionTargets
open StructuredConstructionTargets.FusedLayoutEmission
open StructuredConstructionTargets.SwappedLayoutEmission
open StructuredConstructionTargets.RawLayoutPreparation
open StructuredConstructionTargets.FuelSimulatorCore
open StructuredConstructionTargets.FuelSimulatorCore.RawLayoutEmission
open U12MasterLoop

section CandidateAttempt

variable
    (source sourceSimulator recognizer checkerSimulator : MachineDescription)
    (b : Bool)
    (hsourceSimulator :
      FixedDescriptionBoundedSimulatorEquivSpec source sourceSimulator)
    (hcheckerSimulator :
      SuccessOnlyFairBoundedWrapperSpec recognizer checkerSimulator)

local notation "M" =>
  U12MasterLoop.table source sourceSimulator recognizer checkerSimulator b
    hsourceSimulator.left hcheckerSimulator.left

/-- In the absence of semantic evidence every point of the bound-free cursor
schedule is a false hit. -/
theorem hit_eq_false_of_no_evidence
    (hrecognizer : FixedBoolSimulatorLayoutRecognizerSpec source recognizer b)
    (w : Word Bool)
    (hnoEvidence :
      ¬ PairedRecognizerDovetailControllerStageAttemptFuelPairEvidence
          source w b)
    (cursor : SuccessOnlyDiagonalCursor) :
    (successOnlyCheckerRunLayout recognizer source w
      cursor.limit cursor.candidateFuel cursor.sourceFuel
      cursor.checkerFuel).hit = false := by
  let bound := cursor.limit + cursor.candidateFuel +
    cursor.sourceFuel + cursor.checkerFuel
  let index : SuccessOnlyScheduleIndex :=
    { scheduleBound := bound
      limit := cursor.limit
      candidateFuel := cursor.candidateFuel
      sourceFuel := cursor.sourceFuel
      checkerFuel := cursor.checkerFuel
      limit_le := by simp [bound]; lia
      candidateFuel_le := by simp [bound]; lia
      sourceFuel_le := by simp [bound]; lia
      checkerFuel_le := by simp [bound] }
  cases hhit :
      (successOnlyCheckerRunLayout recognizer source w
        cursor.limit cursor.candidateFuel cursor.sourceFuel
        cursor.checkerFuel).hit with
  | false => rfl
  | true =>
      exfalso
      apply hnoEvidence
      apply (evidence_iff_exists_successOnlySchedule_hit hrecognizer w).mpr
      exact ⟨index, by simpa [index] using hhit⟩

theorem sourceEmit_stateId_ne_halt :
    (M).stateId
        (.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd)) ≠
      (M).description.halt := by
  intro heq
  have hmem := U12MasterLoop.sourceEmit_mem
    source sourceSimulator recognizer checkerSimulator b
    hsourceSimulator.left hcheckerSimulator.left
    (Sum.inl RawLayoutPreparation.State.seekRawEnd)
    (fusedTable source.start).start_mem
  have hstate := (M).stateId_inj
    (.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd)) hmem
    (M).halt (M).halt_mem (by simpa using heq)
  cases hstate

/-- Reachability into a suffix configuration transports halting to that
suffix for a halt-transition-free typed table. -/
theorem haltsFromConfig_of_leads
    {c d : CommonGround.FiniteTransducers.Structured.Configuration}
    (hcd : (M).Leads c d)
    (hhalts : (M).description.HaltsFromConfig c) :
    (M).description.HaltsFromConfig d := by
  rcases hcd with ⟨offset, hrel⟩
  rcases hhalts with ⟨haltSteps, hhalt⟩
  refine ⟨haltSteps, ?_⟩
  have hhaltState :
      ((M).description.runConfig haltSteps c).state =
        (M).description.halt := hhalt
  have hstable :
      (M).description.runConfig (haltSteps + offset) c =
        (M).description.runConfig haltSteps c := by
    rw [Description.runConfig_add]
    exact Description.runConfig_halt (M).description_haltTransitionFree
      ((M).description.runConfig haltSteps c) hhaltState offset
  change ((M).description.runConfig haltSteps d).state =
    (M).description.halt
  rw [← hrel haltSteps, hstable]
  exact hhaltState

/-- The common prefix of a candidate attempt, through total hit extraction. -/
theorem leads_candidate_to_hitBranch
    (w : Word Bool) (i : SuccessOnlyScheduleIndex)
    (rawHead checkerHead : Bool) (rawTail checkerTail : Word Bool)
    (hraw : CandidateInputBits w i.limit i.candidateFuel =
      rawHead :: rawTail)
    (hcheckerRaw :
      SimulatorLayout.asBoolInput
          (successOnlySourceRunLayout source w
            i.limit i.candidateFuel i.sourceFuel) =
        checkerHead :: checkerTail)
    (T0 T1 T2 : Tape Bool)
    (hT0 : Tape.Equiv T0 (cursorFuelSourceTape i.checkerFuel))
    (hT1 : Tape.Equiv T1 (cursorFuelSourceTape i.sourceFuel))
    (hT2 : Tape.Equiv T2
      (Tape.input (CandidateInputBits w i.limit i.candidateFuel))) :
    exists A0 A1 A2 : Tape Bool,
      (M).Leads
        ((M).config
          (.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
          T0 T1 T2)
        ((M).config (.hitBranch U12HitBranch.State.inspect) A0 A1 A2) ∧
      Tape.Equiv A0
          (rawEmissionFinalScratch
            (checkerHead :: checkerTail) i.checkerFuel) ∧
        Tape.Equiv A1
          (rawEmissionFinalScratch (rawHead :: rawTail) i.sourceFuel) ∧
        Tape.Equiv A2
          (SimulatorHitEmitterTargetTape
            (successOnlyCheckerRunLayout recognizer source w
              i.limit i.candidateFuel i.sourceFuel i.checkerFuel)) := by
  rcases U12MasterLoop.leads_sourceEmission_of_equiv
      source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator.left hcheckerSimulator.left
      T0 T1 T2 rawHead rawTail i.sourceFuel hT1
      (by simpa [hraw] using hT2) with
    ⟨S0, S1, S2, hsourceEmit, hS0, hS1, hS2⟩
  rcases sourceSimulator_haltsFromTapeEquiv_carried hsourceSimulator
      w i.limit i.candidateFuel i.sourceFuel S2
      (by simpa [hraw] using hS2) with
    ⟨sourceActual, hsourceHalt, hsourceActual⟩
  have hsourceRun := U12MasterLoop.leads_sourceSimulation
    source sourceSimulator recognizer checkerSimulator b
    hsourceSimulator.left hcheckerSimulator.left
    S0 S1 (keepL.apply S2) sourceActual hsourceHalt
  have hsourceActualInput : Tape.Equiv sourceActual
      (Tape.input (checkerHead :: checkerTail)) := by
    simpa [SimulatorLayout.tape, hcheckerRaw] using hsourceActual
  rcases U12MasterLoop.leads_checkerEmission_of_equiv
      source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator.left hcheckerSimulator.left
      S0 S1 sourceActual checkerHead checkerTail i.checkerFuel
      (Tape.Equiv.trans hS0 hT0) hsourceActualInput with
    ⟨C0, C1, C2, hcheckerEmit, hC0, hC1, hC2⟩
  rcases checkerSimulator_haltsFromTapeEquiv_carried hcheckerSimulator
      source w i C2 (by simpa [hcheckerRaw] using hC2) with
    ⟨checkerActual, hcheckerHalt, hcheckerActual⟩
  have hcheckerRun := U12MasterLoop.leads_checkerSimulation
    source sourceSimulator recognizer checkerSimulator b
    hsourceSimulator.left hcheckerSimulator.left
    C0 C1 (keepL.apply C2) checkerActual hcheckerHalt
  let checkerLayout :=
    successOnlyCheckerRunLayout recognizer source w
      i.limit i.candidateFuel i.sourceFuel i.checkerFuel
  rcases hitExtractor_haltsFromTapeEquiv_carried checkerLayout
      checkerActual (by simpa [checkerLayout] using hcheckerActual) with
    ⟨hitActual, hhitHalt, hhitActual⟩
  have hhitRun := U12MasterLoop.leads_hitExtraction
    source sourceSimulator recognizer checkerSimulator b
    hsourceSimulator.left hcheckerSimulator.left
    C0 C1 checkerActual hitActual hhitHalt
  refine ⟨C0, C1, hitActual, ?_, hC0,
    Tape.Equiv.trans hC1 hS1, ?_⟩
  · exact TypedStateTable.Leads.trans hsourceEmit
      (TypedStateTable.Leads.trans hsourceRun
        (TypedStateTable.Leads.trans hcheckerEmit
          (TypedStateTable.Leads.trans hcheckerRun hhitRun)))
  · simpa [checkerLayout] using hhitActual

/-- A true semantic hit reaches the sole master halt.  The actual endpoint
representatives are related to their semantic tapes componentwise. -/
theorem leads_trueCandidate
    (w : Word Bool) (i : SuccessOnlyScheduleIndex)
    (hhit :
      (successOnlyCheckerRunLayout recognizer source w
        i.limit i.candidateFuel i.sourceFuel i.checkerFuel).hit = true)
    (T0 T1 T2 : Tape Bool)
    (hT0 : Tape.Equiv T0 (cursorFuelSourceTape i.checkerFuel))
    (hT1 : Tape.Equiv T1 (cursorFuelSourceTape i.sourceFuel))
    (hT2 : Tape.Equiv T2
      (Tape.input (CandidateInputBits w i.limit i.candidateFuel))) :
    exists A0 A1 A2 : Tape Bool,
      (M).Leads
        ((M).config
          (.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
          T0 T1 T2)
        ((M).config .halt A0 A1 A2) ∧
      Tape.Equiv A0
          (rawEmissionFinalScratch
            (SimulatorLayout.asBoolInput
              (successOnlySourceRunLayout source w
                i.limit i.candidateFuel i.sourceFuel))
            i.checkerFuel) ∧
        Tape.Equiv A1
          (rawEmissionFinalScratch
            (CandidateInputBits w i.limit i.candidateFuel)
            i.sourceFuel) ∧
        Tape.Equiv A2 (Tape.move Direction.right (Tape.input [b])) := by
  rcases candidateInputBits_exists_cons w i.limit i.candidateFuel with
    ⟨rawHead, rawTail, hraw⟩
  let sourceLayout := successOnlySourceRunLayout source w
    i.limit i.candidateFuel i.sourceFuel
  rcases simulatorLayoutAsBoolInput_exists_cons sourceLayout with
    ⟨checkerHead, checkerTail, hcheckerRaw⟩
  rcases leads_candidate_to_hitBranch
      source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator w i
      rawHead checkerHead rawTail checkerTail hraw
      (by simpa [sourceLayout] using hcheckerRaw)
      T0 T1 T2 hT0 hT1 hT2 with
    ⟨H0, H1, H2, hprefix, hH0, hH1, hH2⟩
  let checkerLayout := successOnlyCheckerRunLayout recognizer source w
    i.limit i.candidateFuel i.sourceFuel i.checkerFuel
  have hhitInput : Tape.Equiv H2
      (U12HitBranch.hitOutputTape true
        (U12HitBranch.simulatorHitPadding checkerLayout)) := by
    refine Tape.Equiv.trans hH2 ?_
    rw [U12HitBranch.simulatorHitEmitterTargetTape_eq_hitOutputTape]
    rw [show checkerLayout.hit = true by simpa [checkerLayout] using hhit]
    exact Tape.Equiv.refl _
  rcases U12MasterLoop.leads_hitTrue_of_equiv
      source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator.left hcheckerSimulator.left
      (U12HitBranch.simulatorHitPadding checkerLayout)
      H0 H1 H2 hhitInput with
    ⟨A0, A1, A2, hsuccess, hA0, hA1, hA2⟩
  refine ⟨A0, A1, A2,
    TypedStateTable.Leads.trans hprefix hsuccess, ?_, ?_, ?_⟩
  · exact Tape.Equiv.trans hA0 (by simpa [sourceLayout, hcheckerRaw] using hH0)
  · exact Tape.Equiv.trans hA1 (by simpa [hraw] using hH1)
  · exact Tape.Equiv.trans hA2
      (U12HitBranch.successBranchTape_equiv b
        (U12HitBranch.simulatorHitPadding checkerLayout))

/-- One unsuccessful scheduled candidate traverses both emitters, both bounded
simulators, total hit extraction, the live false branch, and persistent
restaging.  Every physical endpoint representative is carried explicitly. -/
theorem leads_falseCandidate_to_dispatch
    (w : Word Bool) (i : SuccessOnlyScheduleIndex)
    (rawHead checkerHead : Bool) (rawTail checkerTail : Word Bool)
    (hraw : CandidateInputBits w i.limit i.candidateFuel =
      rawHead :: rawTail)
    (hcheckerRaw :
      SimulatorLayout.asBoolInput
          (successOnlySourceRunLayout source w
            i.limit i.candidateFuel i.sourceFuel) =
        checkerHead :: checkerTail)
    (hhit :
      (successOnlyCheckerRunLayout recognizer source w
        i.limit i.candidateFuel i.sourceFuel i.checkerFuel).hit = false)
    (T0 T1 T2 : Tape Bool)
    (hT0 : Tape.Equiv T0 (cursorFuelSourceTape i.checkerFuel))
    (hT1 : Tape.Equiv T1 (cursorFuelSourceTape i.sourceFuel))
    (hT2 : Tape.Equiv T2
      (Tape.input (CandidateInputBits w i.limit i.candidateFuel))) :
    exists A0 A1 A2 : Tape Bool,
      (M).Leads
        ((M).config
          (.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
          T0 T1 T2)
        ((M).config (.dispatch U12DispatchBootstrap.State.length0)
          A0 A1 A2) ∧
      Tape.Equiv A0
          (PersistentRestaging.cleanedFuelTape
            (checkerHead :: checkerTail) i.checkerFuel) ∧
        Tape.Equiv A1
          (PersistentRestaging.cleanedFuelTape
            (rawHead :: rawTail) i.sourceFuel) ∧
        Tape.Equiv A2
          (PersistentRestaging.restagedRawTape (rawHead :: rawTail)) := by
  rcases U12MasterLoop.leads_sourceEmission_of_equiv
      source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator.left hcheckerSimulator.left
      T0 T1 T2 rawHead rawTail i.sourceFuel hT1
      (by simpa [hraw] using hT2) with
    ⟨S0, S1, S2, hsourceEmit, hS0, hS1, hS2⟩
  rcases sourceSimulator_haltsFromTapeEquiv_carried hsourceSimulator
      w i.limit i.candidateFuel i.sourceFuel S2
      (by simpa [hraw] using hS2) with
    ⟨sourceActual, hsourceHalt, hsourceActual⟩
  have hsourceRun := U12MasterLoop.leads_sourceSimulation
    source sourceSimulator recognizer checkerSimulator b
    hsourceSimulator.left hcheckerSimulator.left
    S0 S1 (keepL.apply S2) sourceActual hsourceHalt
  have hsourceActualInput : Tape.Equiv sourceActual
      (Tape.input (checkerHead :: checkerTail)) := by
    simpa [SimulatorLayout.tape, hcheckerRaw] using hsourceActual
  rcases U12MasterLoop.leads_checkerEmission_of_equiv
      source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator.left hcheckerSimulator.left
      S0 S1 sourceActual checkerHead checkerTail i.checkerFuel
      (Tape.Equiv.trans hS0 hT0) hsourceActualInput with
    ⟨C0, C1, C2, hcheckerEmit, hC0, hC1, hC2⟩
  rcases checkerSimulator_haltsFromTapeEquiv_carried hcheckerSimulator
      source w i C2 (by simpa [hcheckerRaw] using hC2) with
    ⟨checkerActual, hcheckerHalt, hcheckerActual⟩
  have hcheckerRun := U12MasterLoop.leads_checkerSimulation
    source sourceSimulator recognizer checkerSimulator b
    hsourceSimulator.left hcheckerSimulator.left
    C0 C1 (keepL.apply C2) checkerActual hcheckerHalt
  let checkerLayout :=
    successOnlyCheckerRunLayout recognizer source w
      i.limit i.candidateFuel i.sourceFuel i.checkerFuel
  rcases hitExtractor_haltsFromTapeEquiv_carried checkerLayout
      checkerActual (by simpa [checkerLayout] using hcheckerActual) with
    ⟨hitActual, hhitHalt, hhitActual⟩
  have hhitRun := U12MasterLoop.leads_hitExtraction
    source sourceSimulator recognizer checkerSimulator b
    hsourceSimulator.left hcheckerSimulator.left
    C0 C1 checkerActual hitActual hhitHalt
  have hhitInput : Tape.Equiv hitActual
      (U12HitBranch.hitOutputTape false
        (U12HitBranch.simulatorHitPadding checkerLayout)) := by
    refine Tape.Equiv.trans hhitActual ?_
    rw [U12HitBranch.simulatorHitEmitterTargetTape_eq_hitOutputTape]
    rw [show checkerLayout.hit = false by simpa [checkerLayout] using hhit]
    exact Tape.Equiv.refl _
  rcases U12MasterLoop.leads_hitFalse_of_equiv
      source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator.left hcheckerSimulator.left
      (U12HitBranch.simulatorHitPadding checkerLayout)
      C0 C1 hitActual hhitInput with
    ⟨F0, F1, F2, hhitBranch, hF0, hF1, hF2⟩
  have hF2blank : Tape.Equiv F2 Tape.blank :=
    Tape.Equiv.trans hF2
      (U12HitBranch.failureBranchTape_equiv_blank
        (U12HitBranch.simulatorHitPadding checkerLayout))
  rcases U12MasterLoop.leads_restaging_of_equiv
      source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator.left hcheckerSimulator.left
      (checkerHead :: checkerTail) (rawHead :: rawTail)
      i.checkerFuel i.sourceFuel F0 F1 F2
      (Tape.Equiv.trans hF0 hC0)
      (Tape.Equiv.trans hF1 (Tape.Equiv.trans hC1 hS1))
      hF2blank with
    ⟨A0, A1, A2, hrestage, hA0, hA1, hA2⟩
  refine ⟨A0, A1, A2, ?_, hA0, hA1, hA2⟩
  exact TypedStateTable.Leads.trans hsourceEmit
    (TypedStateTable.Leads.trans hsourceRun
      (TypedStateTable.Leads.trans hcheckerEmit
        (TypedStateTable.Leads.trans hcheckerRun
          (TypedStateTable.Leads.trans hhitRun
            (TypedStateTable.Leads.trans hhitBranch hrestage)))))

/-- Compose an unsuccessful candidate with any exact dispatcher branch. -/
theorem leads_falseCandidate_via_dispatch
    (w : Word Bool) (i : SuccessOnlyScheduleIndex)
    (rawHead checkerHead : Bool) (rawTail checkerTail : Word Bool)
    (hraw : CandidateInputBits w i.limit i.candidateFuel =
      rawHead :: rawTail)
    (hcheckerRaw :
      SimulatorLayout.asBoolInput
          (successOnlySourceRunLayout source w
            i.limit i.candidateFuel i.sourceFuel) =
        checkerHead :: checkerTail)
    (hhit :
      (successOnlyCheckerRunLayout recognizer source w
        i.limit i.candidateFuel i.sourceFuel i.checkerFuel).hit = false)
    (T0 T1 T2 : Tape Bool)
    (hT0 : Tape.Equiv T0 (cursorFuelSourceTape i.checkerFuel))
    (hT1 : Tape.Equiv T1 (cursorFuelSourceTape i.sourceFuel))
    (hT2 : Tape.Equiv T2
      (Tape.input (CandidateInputBits w i.limit i.candidateFuel)))
    (V0 V1 V2 : Tape Bool)
    (hdispatch : U12DispatchBootstrap.table.Leads
      (U12DispatchBootstrap.table.config
        U12DispatchBootstrap.State.length0
        (PersistentRestaging.cleanedFuelTape
          (checkerHead :: checkerTail) i.checkerFuel)
        (PersistentRestaging.cleanedFuelTape
          (rawHead :: rawTail) i.sourceFuel)
        (PersistentRestaging.restagedRawTape (rawHead :: rawTail)))
      (U12DispatchBootstrap.table.config
        U12DispatchBootstrap.State.halt V0 V1 V2)) :
    exists A0 A1 A2 : Tape Bool,
      (M).Leads
        ((M).config
          (.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
          T0 T1 T2)
        ((M).config
          (.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
          A0 A1 A2) ∧
      Tape.Equiv A0 V0 ∧ Tape.Equiv A1 V1 ∧
        Tape.Equiv A2 V2 := by
  rcases leads_falseCandidate_to_dispatch
      source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator w i
      rawHead checkerHead rawTail checkerTail hraw hcheckerRaw hhit
      T0 T1 T2 hT0 hT1 hT2 with
    ⟨D0, D1, D2, hattempt, hD0, hD1, hD2⟩
  rcases U12MasterLoop.leads_dispatch_of_equiv
      source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator.left hcheckerSimulator.left
      D0 D1 D2
      (PersistentRestaging.cleanedFuelTape
        (checkerHead :: checkerTail) i.checkerFuel)
      (PersistentRestaging.cleanedFuelTape
        (rawHead :: rawTail) i.sourceFuel)
      (PersistentRestaging.restagedRawTape (rawHead :: rawTail))
      V0 V1 V2 hD0 hD1 hD2 hdispatch with
    ⟨A0, A1, A2, hloop, hA0, hA1, hA2⟩
  exact ⟨A0, A1, A2,
    TypedStateTable.Leads.trans hattempt hloop, hA0, hA1, hA2⟩

/-- The positive-limit dispatcher branch closes one complete unsuccessful
candidate attempt and re-enters source emission at the diagonal successor. -/
theorem leads_falseCandidate_positiveStep
    (w : Word Bool)
    (bound limit candidateFuel sourceFuel checkerFuel : Nat)
    (hlimit : limit + 1 ≤ bound)
    (hcandidate : candidateFuel ≤ bound)
    (hsourceFuel : sourceFuel ≤ bound)
    (hcheckerFuel : checkerFuel ≤ bound)
    (rawHead checkerHead : Bool) (rawTail checkerTail : Word Bool)
    (hraw : CandidateInputBits w (limit + 1) candidateFuel =
      rawHead :: rawTail)
    (hcheckerRaw :
      SimulatorLayout.asBoolInput
          (successOnlySourceRunLayout source w
            (limit + 1) candidateFuel sourceFuel) =
        checkerHead :: checkerTail)
    (hhit :
      (successOnlyCheckerRunLayout recognizer source w
        (limit + 1) candidateFuel sourceFuel checkerFuel).hit = false)
    (T0 T1 T2 : Tape Bool)
    (hT0 : Tape.Equiv T0 (cursorFuelSourceTape checkerFuel))
    (hT1 : Tape.Equiv T1 (cursorFuelSourceTape sourceFuel))
    (hT2 : Tape.Equiv T2
      (Tape.input (CandidateInputBits w (limit + 1) candidateFuel))) :
    exists A0 A1 A2 : Tape Bool,
      (M).Leads
        ((M).config
          (.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
          T0 T1 T2)
        ((M).config
          (.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
          A0 A1 A2) ∧
      Tape.Equiv A0 (cursorFuelSourceTape checkerFuel) ∧
        Tape.Equiv A1 (cursorFuelSourceTape sourceFuel) ∧
        Tape.Equiv A2
          (Tape.input
            (CandidateInputBits w limit (candidateFuel + 1))) := by
  let i : SuccessOnlyScheduleIndex :=
    { scheduleBound := bound
      limit := limit + 1
      candidateFuel := candidateFuel
      sourceFuel := sourceFuel
      checkerFuel := checkerFuel
      limit_le := hlimit
      candidateFuel_le := hcandidate
      sourceFuel_le := hsourceFuel
      checkerFuel_le := hcheckerFuel }
  rcases leads_falseCandidate_to_dispatch
      source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator w i
      rawHead checkerHead rawTail checkerTail
      (by simpa [i] using hraw)
      (by simpa [i] using hcheckerRaw)
      (by simpa [i] using hhit)
      T0 T1 T2
      (by simpa [i] using hT0)
      (by simpa [i] using hT1)
      (by simpa [i] using hT2) with
    ⟨D0, D1, D2, hattempt, hD0, hD1, hD2⟩
  have hdispatch := U12DispatchBootstrap.leads_positiveStep
    (checkerHead :: checkerTail) w limit candidateFuel
      sourceFuel checkerFuel
  rcases U12MasterLoop.leads_dispatch_of_equiv
      source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator.left hcheckerSimulator.left
      D0 D1 D2
      (PersistentRestaging.cleanedFuelTape
        (checkerHead :: checkerTail) checkerFuel)
      (PersistentRestaging.cleanedFuelTape
        (CandidateInputBits w (limit + 1) candidateFuel) sourceFuel)
      (PersistentRestaging.restagedRawTape
        (CandidateInputBits w (limit + 1) candidateFuel))
      (PersistentRestaging.cleanedFuelTape
        (checkerHead :: checkerTail) checkerFuel)
      (PersistentRestaging.cleanedFuelTape
        (CandidateInputBits w (limit + 1) candidateFuel) sourceFuel)
      (PersistentRestaging.restagedRawTape
        (CandidateInputBits w limit (candidateFuel + 1)))
      hD0 (by simpa [hraw] using hD1) (by simpa [hraw] using hD2)
      hdispatch with
    ⟨A0, A1, A2, hloop, hA0, hA1, hA2⟩
  refine ⟨A0, A1, A2,
    TypedStateTable.Leads.trans hattempt hloop, ?_, ?_, ?_⟩
  · exact Tape.Equiv.trans hA0
      (PersistentRestaging.cleanedFuelTape_equiv
        (checkerHead :: checkerTail) checkerFuel)
  · exact Tape.Equiv.trans hA1
      (PersistentRestaging.cleanedFuelTape_equiv
        (CandidateInputBits w (limit + 1) candidateFuel) sourceFuel)
  · exact Tape.Equiv.trans hA2
      (PersistentRestaging.restagedRawTape_equiv_input
        (CandidateInputBits w limit (candidateFuel + 1)))

/-- Exhausting candidate fuel rolls the old candidate coordinate into the
limit and increments source fuel. -/
theorem leads_falseCandidate_candidateRollover
    (w : Word Bool)
    (bound candidateFuel sourceFuel checkerFuel : Nat)
    (hcandidate : candidateFuel + 1 ≤ bound)
    (hsourceFuel : sourceFuel ≤ bound)
    (hcheckerFuel : checkerFuel ≤ bound)
    (rawHead checkerHead : Bool) (rawTail checkerTail : Word Bool)
    (hraw : CandidateInputBits w 0 (candidateFuel + 1) =
      rawHead :: rawTail)
    (hcheckerRaw :
      SimulatorLayout.asBoolInput
          (successOnlySourceRunLayout source w
            0 (candidateFuel + 1) sourceFuel) =
        checkerHead :: checkerTail)
    (hhit :
      (successOnlyCheckerRunLayout recognizer source w
        0 (candidateFuel + 1) sourceFuel checkerFuel).hit = false)
    (T0 T1 T2 : Tape Bool)
    (hT0 : Tape.Equiv T0 (cursorFuelSourceTape checkerFuel))
    (hT1 : Tape.Equiv T1 (cursorFuelSourceTape sourceFuel))
    (hT2 : Tape.Equiv T2
      (Tape.input (CandidateInputBits w 0 (candidateFuel + 1)))) :
    exists A0 A1 A2 : Tape Bool,
      (M).Leads
        ((M).config
          (.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
          T0 T1 T2)
        ((M).config
          (.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
          A0 A1 A2) ∧
      Tape.Equiv A0 (cursorFuelSourceTape checkerFuel) ∧
        Tape.Equiv A1 (cursorFuelSourceTape (sourceFuel + 1)) ∧
        Tape.Equiv A2
          (Tape.input (CandidateInputBits w candidateFuel 0)) := by
  let i : SuccessOnlyScheduleIndex :=
    { scheduleBound := bound
      limit := 0
      candidateFuel := candidateFuel + 1
      sourceFuel := sourceFuel
      checkerFuel := checkerFuel
      limit_le := Nat.zero_le _
      candidateFuel_le := hcandidate
      sourceFuel_le := hsourceFuel
      checkerFuel_le := hcheckerFuel }
  have hdispatch : U12DispatchBootstrap.table.Leads
      (U12DispatchBootstrap.table.config
        U12DispatchBootstrap.State.length0
        (PersistentRestaging.cleanedFuelTape
          (checkerHead :: checkerTail) i.checkerFuel)
        (PersistentRestaging.cleanedFuelTape
          (rawHead :: rawTail) i.sourceFuel)
        (PersistentRestaging.restagedRawTape (rawHead :: rawTail)))
      (U12DispatchBootstrap.table.config U12DispatchBootstrap.State.halt
        (PersistentRestaging.cleanedFuelTape
          (checkerHead :: checkerTail) checkerFuel)
        (PersistentRestaging.cleanedFuelTape
          (CandidateInputBits w candidateFuel 0) (sourceFuel + 1))
        (U12CandidateRollover.paddedRawTape
          (CandidateInputBits w candidateFuel 0))) := by
    simpa [i, hraw] using U12DispatchBootstrap.leads_candidateStep
      (checkerHead :: checkerTail) w candidateFuel sourceFuel checkerFuel
  rcases leads_falseCandidate_via_dispatch
      source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator w i
      rawHead checkerHead rawTail checkerTail
      (by simpa [i] using hraw)
      (by simpa [i] using hcheckerRaw)
      (by simpa [i] using hhit)
      T0 T1 T2 (by simpa [i] using hT0)
      (by simpa [i] using hT1) (by simpa [i] using hT2)
      (PersistentRestaging.cleanedFuelTape
        (checkerHead :: checkerTail) checkerFuel)
      (PersistentRestaging.cleanedFuelTape
        (CandidateInputBits w candidateFuel 0) (sourceFuel + 1))
      (U12CandidateRollover.paddedRawTape
        (CandidateInputBits w candidateFuel 0)) hdispatch with
    ⟨A0, A1, A2, hloop, hA0, hA1, hA2⟩
  refine ⟨A0, A1, A2, hloop, ?_, ?_, ?_⟩
  · exact Tape.Equiv.trans hA0
      (PersistentRestaging.cleanedFuelTape_equiv
        (checkerHead :: checkerTail) checkerFuel)
  · exact Tape.Equiv.trans hA1
      (PersistentRestaging.cleanedFuelTape_equiv
        (CandidateInputBits w candidateFuel 0) (sourceFuel + 1))
  · exact Tape.Equiv.trans hA2
      (Tape.Equiv.trans
        (U12CandidateRollover.paddedRawTape_equiv_restaged
          (CandidateInputBits w candidateFuel 0))
        (PersistentRestaging.restagedRawTape_equiv_input
          (CandidateInputBits w candidateFuel 0)))

/-- Exhausting source fuel resets the source cursor, increments checker fuel,
and moves the old source coordinate into the candidate limit. -/
theorem leads_falseCandidate_sourceRollover
    (w : Word Bool) (bound sourceFuel checkerFuel : Nat)
    (hsourceFuel : sourceFuel + 1 ≤ bound)
    (hcheckerFuel : checkerFuel ≤ bound)
    (rawHead checkerHead : Bool) (rawTail checkerTail : Word Bool)
    (hraw : CandidateInputBits w 0 0 = rawHead :: rawTail)
    (hcheckerRaw :
      SimulatorLayout.asBoolInput
          (successOnlySourceRunLayout source w 0 0 (sourceFuel + 1)) =
        checkerHead :: checkerTail)
    (hhit :
      (successOnlyCheckerRunLayout recognizer source w
        0 0 (sourceFuel + 1) checkerFuel).hit = false)
    (T0 T1 T2 : Tape Bool)
    (hT0 : Tape.Equiv T0 (cursorFuelSourceTape checkerFuel))
    (hT1 : Tape.Equiv T1 (cursorFuelSourceTape (sourceFuel + 1)))
    (hT2 : Tape.Equiv T2
      (Tape.input (CandidateInputBits w 0 0))) :
    exists A0 A1 A2 : Tape Bool,
      (M).Leads
        ((M).config
          (.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
          T0 T1 T2)
        ((M).config
          (.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
          A0 A1 A2) ∧
      Tape.Equiv A0 (cursorFuelSourceTape (checkerFuel + 1)) ∧
        Tape.Equiv A1 (cursorFuelSourceTape 0) ∧
        Tape.Equiv A2
          (Tape.input (CandidateInputBits w sourceFuel 0)) := by
  let i : SuccessOnlyScheduleIndex :=
    { scheduleBound := bound
      limit := 0
      candidateFuel := 0
      sourceFuel := sourceFuel + 1
      checkerFuel := checkerFuel
      limit_le := Nat.zero_le _
      candidateFuel_le := Nat.zero_le _
      sourceFuel_le := hsourceFuel
      checkerFuel_le := hcheckerFuel }
  have hdispatch : U12DispatchBootstrap.table.Leads
      (U12DispatchBootstrap.table.config
        U12DispatchBootstrap.State.length0
        (PersistentRestaging.cleanedFuelTape
          (checkerHead :: checkerTail) i.checkerFuel)
        (PersistentRestaging.cleanedFuelTape
          (rawHead :: rawTail) i.sourceFuel)
        (PersistentRestaging.restagedRawTape (rawHead :: rawTail)))
      (U12DispatchBootstrap.table.config U12DispatchBootstrap.State.halt
        (U12SourceRollover.sourceRolloverCheckerTape
          (checkerHead :: checkerTail) checkerFuel)
        (U12SourceRollover.sourceRolloverZeroTape w sourceFuel)
        (PersistentRestaging.restagedRawTape
          (CandidateInputBits w sourceFuel 0))) := by
    simpa [i, hraw] using U12DispatchBootstrap.leads_sourceStep
      (checkerHead :: checkerTail) w sourceFuel checkerFuel
  rcases leads_falseCandidate_via_dispatch
      source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator w i
      rawHead checkerHead rawTail checkerTail
      (by simpa [i] using hraw)
      (by simpa [i] using hcheckerRaw)
      (by simpa [i] using hhit)
      T0 T1 T2 (by simpa [i] using hT0)
      (by simpa [i] using hT1) (by simpa [i] using hT2)
      (U12SourceRollover.sourceRolloverCheckerTape
        (checkerHead :: checkerTail) checkerFuel)
      (U12SourceRollover.sourceRolloverZeroTape w sourceFuel)
      (PersistentRestaging.restagedRawTape
        (CandidateInputBits w sourceFuel 0)) hdispatch with
    ⟨A0, A1, A2, hloop, hA0, hA1, hA2⟩
  have hendpoint := U12SourceRollover.sourceRollover_endpoint
    (checkerHead :: checkerTail) w sourceFuel checkerFuel
  exact ⟨A0, A1, A2, hloop,
    Tape.Equiv.trans hA0 hendpoint.1,
    Tape.Equiv.trans hA1 hendpoint.2.1,
    Tape.Equiv.trans hA2 hendpoint.2.2⟩

/-- The final zero-coordinate case resets both fuel tapes and advances to the
next checker/schedule diagonal. -/
theorem leads_falseCandidate_checkerRollover
    (w : Word Bool) (bound checkerFuel : Nat)
    (hcheckerFuel : checkerFuel ≤ bound)
    (rawHead checkerHead : Bool) (rawTail checkerTail : Word Bool)
    (hraw : CandidateInputBits w 0 0 = rawHead :: rawTail)
    (hcheckerRaw :
      SimulatorLayout.asBoolInput
          (successOnlySourceRunLayout source w 0 0 0) =
        checkerHead :: checkerTail)
    (hhit :
      (successOnlyCheckerRunLayout recognizer source w
        0 0 0 checkerFuel).hit = false)
    (T0 T1 T2 : Tape Bool)
    (hT0 : Tape.Equiv T0 (cursorFuelSourceTape checkerFuel))
    (hT1 : Tape.Equiv T1 (cursorFuelSourceTape 0))
    (hT2 : Tape.Equiv T2
      (Tape.input (CandidateInputBits w 0 0))) :
    exists A0 A1 A2 : Tape Bool,
      (M).Leads
        ((M).config
          (.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
          T0 T1 T2)
        ((M).config
          (.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
          A0 A1 A2) ∧
      Tape.Equiv A0 (cursorFuelSourceTape 0) ∧
        Tape.Equiv A1 (cursorFuelSourceTape 0) ∧
        Tape.Equiv A2
          (Tape.input (CandidateInputBits w (checkerFuel + 1) 0)) := by
  let i : SuccessOnlyScheduleIndex :=
    { scheduleBound := bound
      limit := 0
      candidateFuel := 0
      sourceFuel := 0
      checkerFuel := checkerFuel
      limit_le := Nat.zero_le _
      candidateFuel_le := Nat.zero_le _
      sourceFuel_le := Nat.zero_le _
      checkerFuel_le := hcheckerFuel }
  have hdispatch : U12DispatchBootstrap.table.Leads
      (U12DispatchBootstrap.table.config
        U12DispatchBootstrap.State.length0
        (PersistentRestaging.cleanedFuelTape
          (checkerHead :: checkerTail) i.checkerFuel)
        (PersistentRestaging.cleanedFuelTape
          (rawHead :: rawTail) i.sourceFuel)
        (PersistentRestaging.restagedRawTape (rawHead :: rawTail)))
      (U12DispatchBootstrap.table.config U12DispatchBootstrap.State.halt
        (U12CheckerRollover.checkerRolloverCheckerTape
          (checkerHead :: checkerTail) checkerFuel)
        (PersistentRestaging.cleanedFuelTape
          (CandidateInputBits w 0 0) 0)
        (PersistentRestaging.restagedRawTape
          (CandidateInputBits w (checkerFuel + 1) 0))) := by
    simpa [i, hraw] using U12DispatchBootstrap.leads_checkerStep
      (checkerHead :: checkerTail) w checkerFuel
  rcases leads_falseCandidate_via_dispatch
      source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator w i
      rawHead checkerHead rawTail checkerTail
      (by simpa [i] using hraw)
      (by simpa [i] using hcheckerRaw)
      (by simpa [i] using hhit)
      T0 T1 T2 (by simpa [i] using hT0)
      (by simpa [i] using hT1) (by simpa [i] using hT2)
      (U12CheckerRollover.checkerRolloverCheckerTape
        (checkerHead :: checkerTail) checkerFuel)
      (PersistentRestaging.cleanedFuelTape
        (CandidateInputBits w 0 0) 0)
      (PersistentRestaging.restagedRawTape
        (CandidateInputBits w (checkerFuel + 1) 0)) hdispatch with
    ⟨A0, A1, A2, hloop, hA0, hA1, hA2⟩
  have hendpoint := U12CheckerRollover.checkerRollover_endpoint
    (checkerHead :: checkerTail) w checkerFuel
  exact ⟨A0, A1, A2, hloop,
    Tape.Equiv.trans hA0 hendpoint.1,
    Tape.Equiv.trans hA1 hendpoint.2.1,
    Tape.Equiv.trans hA2 hendpoint.2.2⟩

/-- A false hit realizes exactly one step of the bound-free four-coordinate
diagonal schedule. -/
theorem leads_falseCandidate_advance
    (w : Word Bool) (cursor : SuccessOnlyDiagonalCursor)
    (hhit :
      (successOnlyCheckerRunLayout recognizer source w
        cursor.limit cursor.candidateFuel cursor.sourceFuel
        cursor.checkerFuel).hit = false)
    (T0 T1 T2 : Tape Bool)
    (hT0 : Tape.Equiv T0
      (cursorFuelSourceTape cursor.checkerFuel))
    (hT1 : Tape.Equiv T1
      (cursorFuelSourceTape cursor.sourceFuel))
    (hT2 : Tape.Equiv T2
      (Tape.input
        (CandidateInputBits w cursor.limit cursor.candidateFuel))) :
    exists A0 A1 A2 : Tape Bool,
      (M).Leads
        ((M).config
          (.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
          T0 T1 T2)
        ((M).config
          (.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
          A0 A1 A2) ∧
      Tape.Equiv A0
          (cursorFuelSourceTape cursor.advance.checkerFuel) ∧
        Tape.Equiv A1
          (cursorFuelSourceTape cursor.advance.sourceFuel) ∧
        Tape.Equiv A2
          (Tape.input
            (CandidateInputBits w cursor.advance.limit
              cursor.advance.candidateFuel)) := by
  rcases cursor with ⟨limit, candidateFuel, sourceFuel, checkerFuel⟩
  cases limit with
  | succ limit =>
      rcases candidateInputBits_exists_cons
          w (limit + 1) candidateFuel with ⟨rawHead, rawTail, hraw⟩
      rcases simulatorLayoutAsBoolInput_exists_cons
          (successOnlySourceRunLayout source w
            (limit + 1) candidateFuel sourceFuel) with
        ⟨checkerHead, checkerTail, hcheckerRaw⟩
      have h := leads_falseCandidate_positiveStep
        source sourceSimulator recognizer checkerSimulator b
        hsourceSimulator hcheckerSimulator w
        (limit + 1 + candidateFuel + sourceFuel + checkerFuel)
        limit candidateFuel sourceFuel checkerFuel
        (by lia) (by lia) (by lia) (by lia)
        rawHead checkerHead rawTail checkerTail hraw hcheckerRaw
        (by simpa using hhit) T0 T1 T2
        (by simpa using hT0) (by simpa using hT1)
        (by simpa using hT2)
      simpa [SuccessOnlyDiagonalCursor.advance] using h
  | zero =>
      cases candidateFuel with
      | succ candidateFuel =>
          rcases candidateInputBits_exists_cons
              w 0 (candidateFuel + 1) with ⟨rawHead, rawTail, hraw⟩
          rcases simulatorLayoutAsBoolInput_exists_cons
              (successOnlySourceRunLayout source w
                0 (candidateFuel + 1) sourceFuel) with
            ⟨checkerHead, checkerTail, hcheckerRaw⟩
          have h := leads_falseCandidate_candidateRollover
            source sourceSimulator recognizer checkerSimulator b
            hsourceSimulator hcheckerSimulator w
            (candidateFuel + 1 + sourceFuel + checkerFuel)
            candidateFuel sourceFuel checkerFuel
            (by lia) (by lia) (by lia)
            rawHead checkerHead rawTail checkerTail hraw hcheckerRaw
            (by simpa using hhit) T0 T1 T2
            (by simpa using hT0) (by simpa using hT1)
            (by simpa using hT2)
          simpa [SuccessOnlyDiagonalCursor.advance] using h
      | zero =>
          cases sourceFuel with
          | succ sourceFuel =>
              rcases candidateInputBits_exists_cons w 0 0 with
                ⟨rawHead, rawTail, hraw⟩
              rcases simulatorLayoutAsBoolInput_exists_cons
                  (successOnlySourceRunLayout source w
                    0 0 (sourceFuel + 1)) with
                ⟨checkerHead, checkerTail, hcheckerRaw⟩
              have h := leads_falseCandidate_sourceRollover
                source sourceSimulator recognizer checkerSimulator b
                hsourceSimulator hcheckerSimulator w
                (sourceFuel + 1 + checkerFuel) sourceFuel checkerFuel
                (by lia) (by lia)
                rawHead checkerHead rawTail checkerTail hraw hcheckerRaw
                (by simpa using hhit) T0 T1 T2
                (by simpa using hT0) (by simpa using hT1)
                (by simpa using hT2)
              simpa [SuccessOnlyDiagonalCursor.advance] using h
          | zero =>
              rcases candidateInputBits_exists_cons w 0 0 with
                ⟨rawHead, rawTail, hraw⟩
              rcases simulatorLayoutAsBoolInput_exists_cons
                  (successOnlySourceRunLayout source w 0 0 0) with
                ⟨checkerHead, checkerTail, hcheckerRaw⟩
              have h := leads_falseCandidate_checkerRollover
                source sourceSimulator recognizer checkerSimulator b
                hsourceSimulator hcheckerSimulator w checkerFuel checkerFuel
                (Nat.le_refl _)
                rawHead checkerHead rawTail checkerTail hraw hcheckerRaw
                (by simpa using hhit) T0 T1 T2
                (by simpa using hT0) (by simpa using hT1)
                (by simpa using hT2)
              simpa [SuccessOnlyDiagonalCursor.advance] using h

/-- A complete unsuccessful attempt consumes at least one concrete master
step.  Positivity follows semantically: a zero-step loop would give the same
three physical tapes two distinct persistent cursor interpretations. -/
theorem falseCandidate_advance_positiveRun
    (w : Word Bool) (cursor : SuccessOnlyDiagonalCursor)
    (hhit :
      (successOnlyCheckerRunLayout recognizer source w
        cursor.limit cursor.candidateFuel cursor.sourceFuel
        cursor.checkerFuel).hit = false)
    (T0 T1 T2 : Tape Bool)
    (hT0 : Tape.Equiv T0
      (cursorFuelSourceTape cursor.checkerFuel))
    (hT1 : Tape.Equiv T1
      (cursorFuelSourceTape cursor.sourceFuel))
    (hT2 : Tape.Equiv T2
      (Tape.input
        (CandidateInputBits w cursor.limit cursor.candidateFuel))) :
    exists A0 A1 A2 : Tape Bool, exists j : Nat,
      0 < j ∧
      (M).description.runConfig j
          ((M).config
            (.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
            T0 T1 T2) =
        (M).config
          (.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
          A0 A1 A2 ∧
      Tape.Equiv A0
          (cursorFuelSourceTape cursor.advance.checkerFuel) ∧
        Tape.Equiv A1
          (cursorFuelSourceTape cursor.advance.sourceFuel) ∧
        Tape.Equiv A2
          (Tape.input
            (CandidateInputBits w cursor.advance.limit
              cursor.advance.candidateFuel)) := by
  rcases leads_falseCandidate_advance
      source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator w cursor hhit
      T0 T1 T2 hT0 hT1 hT2 with
    ⟨A0, A1, A2, hloop, hA0, hA1, hA2⟩
  rcases hloop.to_runConfig with ⟨j, hj⟩
  have hjpos : 0 < j := by
    cases j with
    | zero =>
        have htapes := congrArg (fun c => c.tapes) hj
        simp only [Description.runConfig, TypedStateTable.config,
          ThreeTape.config_tapes] at htapes
        injection htapes with heq0 htail
        injection htail with heq1 htail
        injection htail with heq2 _hnil
        have hcursor : cursor = cursor.advance :=
          persistentCursor_eq w cursor cursor.advance T0 T1 T2
            hT0 hT1 hT2 (by simpa [heq0] using hA0)
            (by simpa [heq1] using hA1) (by simpa [heq2] using hA2)
        exact (diagonalAdvance_ne cursor hcursor.symm).elim
    | succ j => exact Nat.zero_lt_succ j
  exact ⟨A0, A1, A2, j, hjpos, hj, hA0, hA1, hA2⟩

/-- Iterate the concrete master loop across any finite prefix containing only
false hits. -/
theorem leads_falseCandidates_advanceN
    (w : Word Bool) :
    forall (steps : Nat) (cursor : SuccessOnlyDiagonalCursor)
      (T0 T1 T2 : Tape Bool),
      (forall k : Nat, k < steps ->
        (successOnlyCheckerRunLayout recognizer source w
          (SuccessOnlyDiagonalCursor.advanceN k cursor).limit
          (SuccessOnlyDiagonalCursor.advanceN k cursor).candidateFuel
          (SuccessOnlyDiagonalCursor.advanceN k cursor).sourceFuel
          (SuccessOnlyDiagonalCursor.advanceN k cursor).checkerFuel).hit =
            false) ->
      Tape.Equiv T0 (cursorFuelSourceTape cursor.checkerFuel) ->
      Tape.Equiv T1 (cursorFuelSourceTape cursor.sourceFuel) ->
      Tape.Equiv T2
        (Tape.input
          (CandidateInputBits w cursor.limit cursor.candidateFuel)) ->
      exists A0 A1 A2 : Tape Bool,
        (M).Leads
          ((M).config
            (.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
            T0 T1 T2)
          ((M).config
            (.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
            A0 A1 A2) ∧
        Tape.Equiv A0
            (cursorFuelSourceTape
              (SuccessOnlyDiagonalCursor.advanceN steps cursor).checkerFuel) ∧
          Tape.Equiv A1
            (cursorFuelSourceTape
              (SuccessOnlyDiagonalCursor.advanceN steps cursor).sourceFuel) ∧
          Tape.Equiv A2
            (Tape.input
              (CandidateInputBits w
                (SuccessOnlyDiagonalCursor.advanceN steps cursor).limit
                (SuccessOnlyDiagonalCursor.advanceN steps cursor).candidateFuel)) := by
  intro steps
  induction steps with
  | zero =>
      intro cursor T0 T1 T2 _hfalse hT0 hT1 hT2
      exact ⟨T0, T1, T2, TypedStateTable.Leads.refl M _,
        hT0, hT1, hT2⟩
  | succ steps ih =>
      intro cursor T0 T1 T2 hfalse hT0 hT1 hT2
      rcases ih cursor T0 T1 T2
          (fun k hk => hfalse k (Nat.lt_trans hk (Nat.lt_succ_self _)))
          hT0 hT1 hT2 with
        ⟨U0, U1, U2, hprefix, hU0, hU1, hU2⟩
      let endpoint := SuccessOnlyDiagonalCursor.advanceN steps cursor
      have hhit :
          (successOnlyCheckerRunLayout recognizer source w
            endpoint.limit endpoint.candidateFuel endpoint.sourceFuel
            endpoint.checkerFuel).hit = false := by
        simpa [endpoint] using hfalse steps (Nat.lt_succ_self steps)
      rcases leads_falseCandidate_advance
          source sourceSimulator recognizer checkerSimulator b
          hsourceSimulator hcheckerSimulator w endpoint hhit
          U0 U1 U2
          (by simpa [endpoint] using hU0)
          (by simpa [endpoint] using hU1)
          (by simpa [endpoint] using hU2) with
        ⟨A0, A1, A2, hstep, hA0, hA1, hA2⟩
      refine ⟨A0, A1, A2,
        TypedStateTable.Leads.trans hprefix hstep, ?_, ?_, ?_⟩
      · simpa [SuccessOnlyDiagonalCursor.advanceN, endpoint] using hA0
      · simpa [SuccessOnlyDiagonalCursor.advanceN, endpoint] using hA1
      · simpa [SuccessOnlyDiagonalCursor.advanceN, endpoint] using hA2

/-- Iterating `steps` unsuccessful candidates produces a concrete run whose
length is at least `steps`.  This quantitative strengthening is used only for
halt inversion; the forward construction remains phrased with `Leads`. -/
theorem falseCandidates_advanceN_boundedRun
    (w : Word Bool) :
    forall (steps : Nat) (cursor : SuccessOnlyDiagonalCursor)
      (T0 T1 T2 : Tape Bool),
      (forall k : Nat, k < steps ->
        (successOnlyCheckerRunLayout recognizer source w
          (SuccessOnlyDiagonalCursor.advanceN k cursor).limit
          (SuccessOnlyDiagonalCursor.advanceN k cursor).candidateFuel
          (SuccessOnlyDiagonalCursor.advanceN k cursor).sourceFuel
          (SuccessOnlyDiagonalCursor.advanceN k cursor).checkerFuel).hit =
            false) ->
      Tape.Equiv T0 (cursorFuelSourceTape cursor.checkerFuel) ->
      Tape.Equiv T1 (cursorFuelSourceTape cursor.sourceFuel) ->
      Tape.Equiv T2
        (Tape.input
          (CandidateInputBits w cursor.limit cursor.candidateFuel)) ->
      exists A0 A1 A2 : Tape Bool, exists j : Nat,
        steps ≤ j ∧
        (M).description.runConfig j
            ((M).config
              (.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
              T0 T1 T2) =
          (M).config
            (.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
            A0 A1 A2 ∧
        Tape.Equiv A0
            (cursorFuelSourceTape
              (SuccessOnlyDiagonalCursor.advanceN steps cursor).checkerFuel) ∧
          Tape.Equiv A1
            (cursorFuelSourceTape
              (SuccessOnlyDiagonalCursor.advanceN steps cursor).sourceFuel) ∧
          Tape.Equiv A2
            (Tape.input
              (CandidateInputBits w
                (SuccessOnlyDiagonalCursor.advanceN steps cursor).limit
                (SuccessOnlyDiagonalCursor.advanceN steps cursor).candidateFuel)) := by
  intro steps
  induction steps with
  | zero =>
      intro cursor T0 T1 T2 _hfalse hT0 hT1 hT2
      exact ⟨T0, T1, T2, 0, Nat.zero_le _, rfl, hT0, hT1, hT2⟩
  | succ steps ih =>
      intro cursor T0 T1 T2 hfalse hT0 hT1 hT2
      rcases ih cursor T0 T1 T2
          (fun k hk => hfalse k (Nat.lt_trans hk (Nat.lt_succ_self _)))
          hT0 hT1 hT2 with
        ⟨U0, U1, U2, prefixSteps, hprefixBound, hprefix,
          hU0, hU1, hU2⟩
      let endpoint := SuccessOnlyDiagonalCursor.advanceN steps cursor
      have hhit :
          (successOnlyCheckerRunLayout recognizer source w
            endpoint.limit endpoint.candidateFuel endpoint.sourceFuel
            endpoint.checkerFuel).hit = false := by
        simpa [endpoint] using hfalse steps (Nat.lt_succ_self steps)
      rcases falseCandidate_advance_positiveRun
          source sourceSimulator recognizer checkerSimulator b
          hsourceSimulator hcheckerSimulator w endpoint hhit
          U0 U1 U2
          (by simpa [endpoint] using hU0)
          (by simpa [endpoint] using hU1)
          (by simpa [endpoint] using hU2) with
        ⟨A0, A1, A2, stepSteps, hstepPositive, hstep,
          hA0, hA1, hA2⟩
      refine ⟨A0, A1, A2, prefixSteps + stepSteps, ?_, ?_, ?_, ?_, ?_⟩
      · lia
      · rw [Description.runConfig_add, hprefix, hstep]
      · simpa [SuccessOnlyDiagonalCursor.advanceN, endpoint] using hA0
      · simpa [SuccessOnlyDiagonalCursor.advanceN, endpoint] using hA1
      · simpa [SuccessOnlyDiagonalCursor.advanceN, endpoint] using hA2

/-- Any halt from a persistent schedule origin exposes a concrete true point
of the finite cursor prefix preceding that halt. -/
theorem exists_true_hit_of_haltsFromConfig_persistentOrigin
    (w : Word Bool)
    (T0 T1 T2 : Tape Bool)
    (hT0 : Tape.Equiv T0 (cursorFuelSourceTape 0))
    (hT1 : Tape.Equiv T1 (cursorFuelSourceTape 0))
    (hT2 : Tape.Equiv T2 (Tape.input (CandidateInputBits w 0 0)))
    (hhalts : (M).description.HaltsFromConfig
      ((M).config
        (.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
        T0 T1 T2)) :
    exists cursor : SuccessOnlyDiagonalCursor,
      (successOnlyCheckerRunLayout recognizer source w
        cursor.limit cursor.candidateFuel cursor.sourceFuel
        cursor.checkerFuel).hit = true := by
  rcases hhalts with ⟨haltSteps, hhalt⟩
  let origin := SuccessOnlyDiagonalCursor.initial
  let hitAt : Nat -> Bool := fun k =>
    (successOnlyCheckerRunLayout recognizer source w
      (SuccessOnlyDiagonalCursor.advanceN k origin).limit
      (SuccessOnlyDiagonalCursor.advanceN k origin).candidateFuel
      (SuccessOnlyDiagonalCursor.advanceN k origin).sourceFuel
      (SuccessOnlyDiagonalCursor.advanceN k origin).checkerFuel).hit
  let startConfig :=
    (M).config
      (.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
      T0 T1 T2
  have hhaltState :
      ((M).description.runConfig haltSteps startConfig).state =
        (M).description.halt := by
    simpa [Description.HaltsIn, startConfig] using hhalt
  have hnotAllFalse :
      ¬ forall k : Nat, k < haltSteps + 1 -> hitAt k = false := by
    intro hfalse
    rcases falseCandidates_advanceN_boundedRun
        source sourceSimulator recognizer checkerSimulator b
        hsourceSimulator hcheckerSimulator w (haltSteps + 1) origin
        T0 T1 T2 (by simpa [hitAt] using hfalse)
        (by simpa [origin, SuccessOnlyDiagonalCursor.initial] using hT0)
        (by simpa [origin, SuccessOnlyDiagonalCursor.initial] using hT1)
        (by simpa [origin, SuccessOnlyDiagonalCursor.initial] using hT2) with
      ⟨A0, A1, A2, totalSteps, htotalBound, hrun,
        _hA0, _hA1, _hA2⟩
    have hhaltLe : haltSteps ≤ totalSteps := by lia
    have hsplit :
        haltSteps + (totalSteps - haltSteps) = totalSteps :=
      Nat.add_sub_of_le hhaltLe
    have hstable :
        (M).description.runConfig totalSteps startConfig =
          (M).description.runConfig haltSteps startConfig := by
      calc
        (M).description.runConfig totalSteps startConfig =
            (M).description.runConfig (totalSteps - haltSteps)
              ((M).description.runConfig haltSteps startConfig) := by
          rw [← Description.runConfig_add]
          rw [hsplit]
        _ = (M).description.runConfig haltSteps startConfig :=
          Description.runConfig_halt (M).description_haltTransitionFree
            ((M).description.runConfig haltSteps startConfig)
            hhaltState (totalSteps - haltSteps)
    have hendpointState :
        ((M).config
          (.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
          A0 A1 A2).state = (M).description.halt := by
      rw [← hrun]
      change ((M).description.runConfig totalSteps startConfig).state = _
      rw [hstable]
      exact hhaltState
    exact sourceEmit_stateId_ne_halt
      source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator
      (by simpa [TypedStateTable.config] using hendpointState)
  rcases exists_true_below_of_not_all_false
      hitAt (haltSteps + 1) hnotAllFalse with ⟨k, _hk, htrue⟩
  exact ⟨SuccessOnlyDiagonalCursor.advanceN k origin,
    by simpa [hitAt] using htrue⟩

/-- Constructive halt inversion: a master halt yields a finite true cursor,
which is re-indexed into the semantic bounded schedule and hence into the
original evidence proposition. -/
theorem evidence_of_haltsFromConfig_persistentOrigin
    (hrecognizer : FixedBoolSimulatorLayoutRecognizerSpec source recognizer b)
    (w : Word Bool)
    (T0 T1 T2 : Tape Bool)
    (hT0 : Tape.Equiv T0 (cursorFuelSourceTape 0))
    (hT1 : Tape.Equiv T1 (cursorFuelSourceTape 0))
    (hT2 : Tape.Equiv T2 (Tape.input (CandidateInputBits w 0 0)))
    (hhalts : (M).description.HaltsFromConfig
      ((M).config
        (.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
        T0 T1 T2)) :
    PairedRecognizerDovetailControllerStageAttemptFuelPairEvidence
      source w b := by
  rcases exists_true_hit_of_haltsFromConfig_persistentOrigin
      source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator w T0 T1 T2 hT0 hT1 hT2
      hhalts with ⟨cursor, hhit⟩
  let bound := cursor.limit + cursor.candidateFuel +
    cursor.sourceFuel + cursor.checkerFuel
  let index : SuccessOnlyScheduleIndex :=
    { scheduleBound := bound
      limit := cursor.limit
      candidateFuel := cursor.candidateFuel
      sourceFuel := cursor.sourceFuel
      checkerFuel := cursor.checkerFuel
      limit_le := by simp [bound]; lia
      candidateFuel_le := by simp [bound]; lia
      sourceFuel_le := by simp [bound]; lia
      checkerFuel_le := by simp [bound] }
  apply (evidence_iff_exists_successOnlySchedule_hit hrecognizer w).mpr
  exact ⟨index, by simpa [index] using hhit⟩

/-- Semantic evidence reaches the least true point of the concrete diagonal
schedule and then the sole master halt. -/
theorem leads_evidence_from_persistentOrigin
    (hrecognizer : FixedBoolSimulatorLayoutRecognizerSpec source recognizer b)
    (w : Word Bool)
    (hevidence :
      PairedRecognizerDovetailControllerStageAttemptFuelPairEvidence
        source w b)
    (T0 T1 T2 : Tape Bool)
    (hT0 : Tape.Equiv T0 (cursorFuelSourceTape 0))
    (hT1 : Tape.Equiv T1 (cursorFuelSourceTape 0))
    (hT2 : Tape.Equiv T2 (Tape.input (CandidateInputBits w 0 0))) :
    exists A0 A1 A2 : Tape Bool,
      (M).Leads
        ((M).config
          (.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
          T0 T1 T2)
        ((M).config .halt A0 A1 A2) ∧
      Tape.Equiv A2 (Tape.move Direction.right (Tape.input [b])) := by
  rcases (evidence_iff_exists_successOnlySchedule_hit hrecognizer w).mp
      hevidence with ⟨witness, hwitness⟩
  rcases successOnlyScheduleIndex_reachable_diagonal witness with
    ⟨someSteps, hsomeSteps⟩
  let origin := SuccessOnlyDiagonalCursor.initial
  let p : Nat -> Prop := fun k =>
    (successOnlyCheckerRunLayout recognizer source w
      (SuccessOnlyDiagonalCursor.advanceN k origin).limit
      (SuccessOnlyDiagonalCursor.advanceN k origin).candidateFuel
      (SuccessOnlyDiagonalCursor.advanceN k origin).sourceFuel
      (SuccessOnlyDiagonalCursor.advanceN k origin).checkerFuel).hit = true
  have hp : p someSteps := by
    simpa [p, origin, hsomeSteps] using hwitness
  rcases FusedLayoutEmission.exists_least_up_to someSteps
      ⟨someSteps, Nat.le_refl _, hp⟩ with
    ⟨first, _hfirstLe, hfirst, hbefore⟩
  have hfalse : forall k : Nat, k < first ->
      (successOnlyCheckerRunLayout recognizer source w
        (SuccessOnlyDiagonalCursor.advanceN k origin).limit
        (SuccessOnlyDiagonalCursor.advanceN k origin).candidateFuel
        (SuccessOnlyDiagonalCursor.advanceN k origin).sourceFuel
        (SuccessOnlyDiagonalCursor.advanceN k origin).checkerFuel).hit =
          false := by
    intro k hk
    have hn := hbefore k hk
    change ¬ p k at hn
    unfold p at hn
    cases hv :
        (successOnlyCheckerRunLayout recognizer source w
          (SuccessOnlyDiagonalCursor.advanceN k origin).limit
          (SuccessOnlyDiagonalCursor.advanceN k origin).candidateFuel
          (SuccessOnlyDiagonalCursor.advanceN k origin).sourceFuel
          (SuccessOnlyDiagonalCursor.advanceN k origin).checkerFuel).hit <;>
      simp_all
  rcases leads_falseCandidates_advanceN
      source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator w first origin T0 T1 T2
      hfalse (by simpa [origin, SuccessOnlyDiagonalCursor.initial] using hT0)
      (by simpa [origin, SuccessOnlyDiagonalCursor.initial] using hT1)
      (by simpa [origin, SuccessOnlyDiagonalCursor.initial] using hT2) with
    ⟨U0, U1, U2, hprefix, hU0, hU1, hU2⟩
  let endpoint := SuccessOnlyDiagonalCursor.advanceN first origin
  let endpointBound := endpoint.limit + endpoint.candidateFuel +
    endpoint.sourceFuel + endpoint.checkerFuel
  let index : SuccessOnlyScheduleIndex :=
    { scheduleBound := endpointBound
      limit := endpoint.limit
      candidateFuel := endpoint.candidateFuel
      sourceFuel := endpoint.sourceFuel
      checkerFuel := endpoint.checkerFuel
      limit_le := by simp [endpointBound]; lia
      candidateFuel_le := by simp [endpointBound]; lia
      sourceFuel_le := by simp [endpointBound]; lia
      checkerFuel_le := by simp [endpointBound] }
  have hendpointHit :
      (successOnlyCheckerRunLayout recognizer source w
        index.limit index.candidateFuel index.sourceFuel
        index.checkerFuel).hit = true := by
    simpa [index, endpoint] using hfirst
  rcases leads_trueCandidate
      source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator w index hendpointHit
      U0 U1 U2
      (by simpa [index, endpoint] using hU0)
      (by simpa [index, endpoint] using hU1)
      (by simpa [index, endpoint] using hU2) with
    ⟨A0, A1, A2, hsuccess, _hA0, _hA1, hA2⟩
  exact ⟨A0, A1, A2,
    TypedStateTable.Leads.trans hprefix hsuccess, hA2⟩

/-- Forward master-table execution from the exact zero bootstrap. -/
theorem leads_initialized_of_evidence
    (hrecognizer : FixedBoolSimulatorLayoutRecognizerSpec source recognizer b)
    (raw : List Bool)
    (hevidence :
      PairedRecognizerDovetailControllerStageAttemptFuelPairEvidence
        source (show Word Bool from raw) b) :
    exists A0 A1 A2 : Tape Bool,
      (M).Leads
        ((M).config (.bootstrap U12ZeroBootstrap.State.lengthScan)
          (Tape.input (show Word Bool from raw)) Tape.blank Tape.blank)
        ((M).config .halt A0 A1 A2) ∧
      Tape.Equiv A2 (Tape.move Direction.right (Tape.input [b])) := by
  have hbootstrap := U12MasterLoop.leads_bootstrap
    source sourceSimulator recognizer checkerSimulator b
    hsourceSimulator.left hcheckerSimulator.left raw
  have horigin := U12ZeroBootstrap.exact_bootstrap_persistentOrigin raw
  rcases leads_evidence_from_persistentOrigin
      source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator hrecognizer
      (show Word Bool from raw) hevidence
      (U12ZeroBootstrap.bootstrapFuelTape (raw.length + 2))
      (U12ZeroBootstrap.bootstrapFuelTape 1)
      (U12ZeroBootstrap.bootstrapCandidateTape raw)
      horigin.1 horigin.2.1 horigin.2.2 with
    ⟨A0, A1, A2, hsearch, hA2⟩
  exact ⟨A0, A1, A2,
    TypedStateTable.Leads.trans hbootstrap hsearch, hA2⟩

/-- Closed semantic inversion from the exact zero-bootstrap configuration. -/
theorem evidence_of_haltsFromConfig_initialized
    (hrecognizer : FixedBoolSimulatorLayoutRecognizerSpec source recognizer b)
    (raw : List Bool)
    (hhalts : (M).description.HaltsFromConfig
      ((M).config (.bootstrap U12ZeroBootstrap.State.lengthScan)
        (Tape.input (show Word Bool from raw)) Tape.blank Tape.blank)) :
    PairedRecognizerDovetailControllerStageAttemptFuelPairEvidence
      source (show Word Bool from raw) b := by
  have hbootstrap := U12MasterLoop.leads_bootstrap
    source sourceSimulator recognizer checkerSimulator b
    hsourceSimulator.left hcheckerSimulator.left raw
  have hsearchHalts := haltsFromConfig_of_leads
    source sourceSimulator recognizer checkerSimulator b
    hsourceSimulator hcheckerSimulator hbootstrap hhalts
  have horigin := U12ZeroBootstrap.exact_bootstrap_persistentOrigin raw
  exact evidence_of_haltsFromConfig_persistentOrigin
    source sourceSimulator recognizer checkerSimulator b
    hsourceSimulator hcheckerSimulator hrecognizer
    (show Word Bool from raw)
    (U12ZeroBootstrap.bootstrapFuelTape (raw.length + 2))
    (U12ZeroBootstrap.bootstrapFuelTape 1)
    (U12ZeroBootstrap.bootstrapCandidateTape raw)
    horigin.1 horigin.2.1 horigin.2.2 hsearchHalts

end CandidateAttempt

end U12CandidateAttemptLoop
end BoundedFuelPairSearch
end Computability
end FoC

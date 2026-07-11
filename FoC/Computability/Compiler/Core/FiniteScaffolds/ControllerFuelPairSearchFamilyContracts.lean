import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.Contract
import FoC.Computability.Compiler.Core.ConstructionTargets

set_option doc.verso true

/-!
# Output-indexed controller fuel-pair search routes

The repaired fuel-pair search interface fixes the observable Boolean before a
machine is selected.  This module states the corresponding attempt-level
evidence and transports the runner-level search family across an exact-fuel
runner realization.  It deliberately contains no physical search-machine
construction.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

/-!
## Attempt-level evidence
-/

/-- Exact-fuel evidence that one stage attempt produces the fixed Boolean. -/
def PairedRecognizerDovetailControllerStageAttemptExactFuelEvidence
    (attempt : MachineDescription) (w : Word Bool) (b : Bool)
    (limit candidateFuel : Nat) : Prop :=
  attempt.HaltsWithOutputIn candidateFuel
    (encodeCodeWordAsInput
      (PairedRecognizerDovetailStageInputCode w limit))
    (encodeCodeWordAsInput (encodeBoolWord [b]))

/-- Unbounded hidden-pair evidence for a fixed observable Boolean. -/
def PairedRecognizerDovetailControllerStageAttemptUnboundedFuelPairEvidence
    (attempt : MachineDescription) (w : Word Bool) (b : Bool) : Prop :=
  exists limit : Nat,
  exists candidateFuel : Nat,
    PairedRecognizerDovetailControllerStageAttemptExactFuelEvidence
      attempt w b limit candidateFuel

/-- Exact-fuel evidence is equivalent to the former result/raw-output shape. -/
theorem pairedRecognizerDovetailControllerStageAttemptExactFuelEvidence_iff_exists_result
    {attempt : MachineDescription} {w : Word Bool} {b : Bool}
    {limit candidateFuel : Nat} :
    PairedRecognizerDovetailControllerStageAttemptExactFuelEvidence
        attempt w b limit candidateFuel <->
      exists result : Word Bool,
        attempt.HaltsWithOutputIn candidateFuel
          (encodeCodeWordAsInput
            (PairedRecognizerDovetailStageInputCode w limit))
          (encodeCodeWordAsInput (encodeBoolWord result)) ∧
        PairedRecognizerDovetailControllerRawOutput result = some [b] := by
  constructor
  · intro h
    refine ⟨[b], h, ?_⟩
    simpa [PairedRecognizerDovetailControllerRawOutput] using
      (DovetailControllerLayout.rawOutput_eq_some_singleton_iff [b] b).mpr rfl
  · intro h
    rcases h with ⟨result, hrun, hraw⟩
    have hresult : result = [b] :=
      (DovetailControllerLayout.rawOutput_eq_some_singleton_iff result b).mp
        (by simpa [PairedRecognizerDovetailControllerRawOutput] using hraw)
    subst result
    exact hrun

/-- Hidden-pair evidence is equivalent to the former result/raw-output existential. -/
theorem pairedRecognizerDovetailControllerStageAttemptUnboundedFuelPairEvidence_iff_exists_result
    {attempt : MachineDescription} {w : Word Bool} {b : Bool} :
    PairedRecognizerDovetailControllerStageAttemptUnboundedFuelPairEvidence attempt w b <->
      exists limit : Nat,
      exists candidateFuel : Nat,
      exists result : Word Bool,
        attempt.HaltsWithOutputIn candidateFuel
          (encodeCodeWordAsInput
            (PairedRecognizerDovetailStageInputCode w limit))
          (encodeCodeWordAsInput (encodeBoolWord result)) ∧
        PairedRecognizerDovetailControllerRawOutput result = some [b] := by
  constructor
  · intro h
    rcases h with ⟨limit, candidateFuel, hexact⟩
    rcases
        pairedRecognizerDovetailControllerStageAttemptExactFuelEvidence_iff_exists_result.mp
          hexact with
      ⟨result, hrun, hraw⟩
    exact ⟨limit, candidateFuel, result, hrun, hraw⟩
  · intro h
    rcases h with ⟨limit, candidateFuel, result, hrun, hraw⟩
    exact
      ⟨limit, candidateFuel,
        pairedRecognizerDovetailControllerStageAttemptExactFuelEvidence_iff_exists_result.mpr
          ⟨result, hrun, hraw⟩⟩

/-!
## Runner-level fixed-Boolean family route
-/

structure ControllerStageAttemptFuelPairSearchRunnerFamilyRoute
    (runner : MachineDescription) where
  family :
    PairedRecognizerDovetailControllerStageAttemptFuelPairSearchFamily runner
  subroutineReady :
    forall b : Bool,
      (family.machine b).SubroutineReady
  searchIff :
    forall w : Word Bool,
    forall b : Bool,
      (family.machine b).HaltsWithOutput w [b] <->
        PairedRecognizerDovetailControllerStageAttemptFuelPairEvidence
          runner w b
  searchIffResult :
    forall w : Word Bool,
    forall b : Bool,
      (family.machine b).HaltsWithOutput w [b] <->
        exists limit : Nat,
        exists fuel : Nat,
        exists result : Word Bool,
          runner.HaltsWithOutput
            (encodeCodeWordAsInput
              (PairedRecognizerDovetailControllerStageAttemptFuelInputCode
                w limit fuel))
            (encodeCodeWordAsInput (encodeBoolWord result)) ∧
          PairedRecognizerDovetailControllerRawOutput result = some [b]
  toEvidence :
    forall w : Word Bool,
    forall b : Bool,
      (family.machine b).HaltsWithOutput w [b] ->
        PairedRecognizerDovetailControllerStageAttemptFuelPairEvidence
          runner w b
  ofEvidence :
    forall w : Word Bool,
    forall b : Bool,
      PairedRecognizerDovetailControllerStageAttemptFuelPairEvidence
          runner w b ->
        (family.machine b).HaltsWithOutput w [b]

def controllerStageAttemptFuelPairSearchRunnerFamilyRoute_of_family
    {runner : MachineDescription}
    (family :
      PairedRecognizerDovetailControllerStageAttemptFuelPairSearchFamily
        runner) :
    ControllerStageAttemptFuelPairSearchRunnerFamilyRoute runner := by
  exact
    { family := family
      subroutineReady := fun b => (family.spec b).subroutineReady
      searchIff := fun w b =>
        PairedRecognizerDovetailControllerStageAttemptFuelPairBoolSearchSpec.realizes
          (family.spec b) w
      searchIffResult := fun w b =>
        Iff.trans
          (PairedRecognizerDovetailControllerStageAttemptFuelPairBoolSearchSpec.realizes
            (family.spec b) w)
          pairedRecognizerDovetailControllerStageAttemptFuelPairEvidence_iff_exists_result
      toEvidence := fun w b hhalt =>
        (PairedRecognizerDovetailControllerStageAttemptFuelPairBoolSearchSpec.realizes
          (family.spec b) w).mp hhalt
      ofEvidence := fun w b hevidence =>
        (PairedRecognizerDovetailControllerStageAttemptFuelPairBoolSearchSpec.realizes
          (family.spec b) w).mpr hevidence }

namespace ControllerStageAttemptFuelPairSearchRunnerFamilyRoute

/-- A runner family is output-functional when the runner has cross-limit coherence. -/
theorem output_functional_of_coherent
    {runner : MachineDescription}
    (route : ControllerStageAttemptFuelPairSearchRunnerFamilyRoute runner)
    (hcoherent :
      PairedRecognizerDovetailControllerStageAttemptFuelPairObservableCoherent
        runner)
    {w : Word Bool} {b₁ b₂ : Bool}
    (h₁ : (route.family.machine b₁).HaltsWithOutput w [b₁])
    (h₂ : (route.family.machine b₂).HaltsWithOutput w [b₂]) :
    b₁ = b₂ := by
  exact hcoherent w b₁ b₂
    ((route.searchIff w b₁).mp h₁)
    ((route.searchIff w b₂).mp h₂)

end ControllerStageAttemptFuelPairSearchRunnerFamilyRoute

/-!
## Exact-fuel runner transport
-/

theorem pairedRecognizerDovetailControllerStageAttemptExactFuelRunner_halts_iff_evidence
    {attempt runner : MachineDescription}
    (hrunner :
      PairedRecognizerDovetailControllerStageAttemptExactFuelRunnerRealizes
        attempt runner)
    (w : Word Bool) (b : Bool) (limit candidateFuel : Nat) :
    runner.HaltsWithOutput
        (encodeCodeWordAsInput
          (PairedRecognizerDovetailControllerStageAttemptFuelInputCode
            w limit candidateFuel))
        (encodeCodeWordAsInput (encodeBoolWord [b])) <->
      PairedRecognizerDovetailControllerStageAttemptExactFuelEvidence
        attempt w b limit candidateFuel := by
  exact hrunner.right w limit candidateFuel [b]

theorem pairedRecognizerDovetailControllerStageAttemptRunnerFuelPairEvidence_iff_attempt
    {attempt runner : MachineDescription}
    (hrunner :
      PairedRecognizerDovetailControllerStageAttemptExactFuelRunnerRealizes
        attempt runner)
    (w : Word Bool) (b : Bool) :
    PairedRecognizerDovetailControllerStageAttemptFuelPairEvidence runner w b <->
      PairedRecognizerDovetailControllerStageAttemptUnboundedFuelPairEvidence
        attempt w b := by
  constructor
  · rintro ⟨limit, candidateFuel, hhalt⟩
    exact
      ⟨limit, candidateFuel,
        (pairedRecognizerDovetailControllerStageAttemptExactFuelRunner_halts_iff_evidence
          hrunner w b limit candidateFuel).mp hhalt⟩
  · rintro ⟨limit, candidateFuel, hevidence⟩
    exact
      ⟨limit, candidateFuel,
        (pairedRecognizerDovetailControllerStageAttemptExactFuelRunner_halts_iff_evidence
          hrunner w b limit candidateFuel).mpr hevidence⟩

/-- Cross-limit Boolean coherence stated directly for the supplied attempt. -/
def PairedRecognizerDovetailControllerStageAttemptUnboundedFuelPairObservableCoherent
    (attempt : MachineDescription) : Prop :=
  forall w : Word Bool,
  forall b₁ b₂ : Bool,
    PairedRecognizerDovetailControllerStageAttemptUnboundedFuelPairEvidence
      attempt w b₁ ->
    PairedRecognizerDovetailControllerStageAttemptUnboundedFuelPairEvidence
      attempt w b₂ ->
      b₁ = b₂

/-- Exact-fuel runner realization preserves and reflects cross-limit coherence. -/
theorem pairedRecognizerDovetailControllerStageAttemptFuelPairObservableCoherent_iff_runner
    {attempt runner : MachineDescription}
    (hrunner :
      PairedRecognizerDovetailControllerStageAttemptExactFuelRunnerRealizes
        attempt runner) :
    PairedRecognizerDovetailControllerStageAttemptFuelPairObservableCoherent
        runner <->
      PairedRecognizerDovetailControllerStageAttemptUnboundedFuelPairObservableCoherent
        attempt := by
  constructor
  · intro h w b₁ b₂ h₁ h₂
    exact h w b₁ b₂
      ((pairedRecognizerDovetailControllerStageAttemptRunnerFuelPairEvidence_iff_attempt
        hrunner w b₁).mpr h₁)
      ((pairedRecognizerDovetailControllerStageAttemptRunnerFuelPairEvidence_iff_attempt
        hrunner w b₂).mpr h₂)
  · intro h w b₁ b₂ h₁ h₂
    exact h w b₁ b₂
      ((pairedRecognizerDovetailControllerStageAttemptRunnerFuelPairEvidence_iff_attempt
        hrunner w b₁).mp h₁)
      ((pairedRecognizerDovetailControllerStageAttemptRunnerFuelPairEvidence_iff_attempt
        hrunner w b₂).mp h₂)

/-!
## Fixed-Boolean and family routes
-/

structure ControllerStageAttemptFuelPairBoolSearchRoute
    (attempt runner searcher : MachineDescription) (b : Bool) : Prop where
  runnerRealizes :
    PairedRecognizerDovetailControllerStageAttemptExactFuelRunnerRealizes
      attempt runner
  searchSpec :
    PairedRecognizerDovetailControllerStageAttemptFuelPairBoolSearchSpec
      runner searcher b
  subroutineReady : searcher.SubroutineReady
  searchIff :
    forall w : Word Bool,
      searcher.HaltsWithOutput w [b] <->
        PairedRecognizerDovetailControllerStageAttemptUnboundedFuelPairEvidence
          attempt w b
  searchIffResult :
    forall w : Word Bool,
      searcher.HaltsWithOutput w [b] <->
        exists limit : Nat,
        exists candidateFuel : Nat,
        exists result : Word Bool,
          attempt.HaltsWithOutputIn candidateFuel
            (encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w limit))
            (encodeCodeWordAsInput (encodeBoolWord result)) ∧
          PairedRecognizerDovetailControllerRawOutput result = some [b]
  toEvidence :
    forall w : Word Bool,
      searcher.HaltsWithOutput w [b] ->
        PairedRecognizerDovetailControllerStageAttemptUnboundedFuelPairEvidence
          attempt w b
  ofEvidence :
    forall w : Word Bool,
      PairedRecognizerDovetailControllerStageAttemptUnboundedFuelPairEvidence
          attempt w b ->
        searcher.HaltsWithOutput w [b]

theorem controllerStageAttemptFuelPairBoolSearchRoute_of_runnerRealizes
    {attempt runner searcher : MachineDescription} {b : Bool}
    (hrunner :
      PairedRecognizerDovetailControllerStageAttemptExactFuelRunnerRealizes
        attempt runner)
    (hsearch :
      PairedRecognizerDovetailControllerStageAttemptFuelPairBoolSearchSpec
        runner searcher b) :
    ControllerStageAttemptFuelPairBoolSearchRoute
      attempt runner searcher b := by
  refine
    { runnerRealizes := hrunner
      searchSpec := hsearch
      subroutineReady := hsearch.subroutineReady
      searchIff := by
        intro w
        exact
          Iff.trans
            (PairedRecognizerDovetailControllerStageAttemptFuelPairBoolSearchSpec.realizes
              hsearch w)
            (pairedRecognizerDovetailControllerStageAttemptRunnerFuelPairEvidence_iff_attempt
              hrunner w b)
      searchIffResult := by
        intro w
        exact
          Iff.trans
            (Iff.trans
              (PairedRecognizerDovetailControllerStageAttemptFuelPairBoolSearchSpec.realizes
                hsearch w)
              (pairedRecognizerDovetailControllerStageAttemptRunnerFuelPairEvidence_iff_attempt
                hrunner w b))
            pairedRecognizerDovetailControllerStageAttemptUnboundedFuelPairEvidence_iff_exists_result
      toEvidence := by
        intro w hhalt
        exact
          (Iff.trans
            (PairedRecognizerDovetailControllerStageAttemptFuelPairBoolSearchSpec.realizes
              hsearch w)
            (pairedRecognizerDovetailControllerStageAttemptRunnerFuelPairEvidence_iff_attempt
              hrunner w b)).mp hhalt
      ofEvidence := by
        intro w hevidence
        exact
          (Iff.trans
            (PairedRecognizerDovetailControllerStageAttemptFuelPairBoolSearchSpec.realizes
              hsearch w)
            (pairedRecognizerDovetailControllerStageAttemptRunnerFuelPairEvidence_iff_attempt
              hrunner w b)).mpr hevidence }

structure ControllerStageAttemptFuelPairSearchFamilyRoute
    (attempt runner : MachineDescription) where
  runnerRealizes :
    PairedRecognizerDovetailControllerStageAttemptExactFuelRunnerRealizes
      attempt runner
  family :
    PairedRecognizerDovetailControllerStageAttemptFuelPairSearchFamily runner
  boolRoute :
    forall b : Bool,
      ControllerStageAttemptFuelPairBoolSearchRoute
        attempt runner (family.machine b) b

def controllerStageAttemptFuelPairSearchFamilyRoute_of_runnerRealizes
    {attempt runner : MachineDescription}
    (hrunner :
      PairedRecognizerDovetailControllerStageAttemptExactFuelRunnerRealizes
        attempt runner)
    (family :
      PairedRecognizerDovetailControllerStageAttemptFuelPairSearchFamily
        runner) :
    ControllerStageAttemptFuelPairSearchFamilyRoute attempt runner := by
  exact
    { runnerRealizes := hrunner
      family := family
      boolRoute := fun b =>
        controllerStageAttemptFuelPairBoolSearchRoute_of_runnerRealizes
          hrunner (family.spec b) }

namespace ControllerStageAttemptFuelPairSearchFamilyRoute

theorem subroutineReady
    {attempt runner : MachineDescription}
    (route : ControllerStageAttemptFuelPairSearchFamilyRoute attempt runner)
    (b : Bool) :
    (route.family.machine b).SubroutineReady := by
  exact (route.boolRoute b).subroutineReady

theorem searchIff
    {attempt runner : MachineDescription}
    (route : ControllerStageAttemptFuelPairSearchFamilyRoute attempt runner)
    (w : Word Bool) (b : Bool) :
    (route.family.machine b).HaltsWithOutput w [b] <->
      PairedRecognizerDovetailControllerStageAttemptUnboundedFuelPairEvidence
        attempt w b := by
  exact (route.boolRoute b).searchIff w

theorem searchIffResult
    {attempt runner : MachineDescription}
    (route : ControllerStageAttemptFuelPairSearchFamilyRoute attempt runner)
    (w : Word Bool) (b : Bool) :
    (route.family.machine b).HaltsWithOutput w [b] <->
      exists limit : Nat,
      exists candidateFuel : Nat,
      exists result : Word Bool,
        attempt.HaltsWithOutputIn candidateFuel
          (encodeCodeWordAsInput
            (PairedRecognizerDovetailStageInputCode w limit))
          (encodeCodeWordAsInput (encodeBoolWord result)) ∧
        PairedRecognizerDovetailControllerRawOutput result = some [b] := by
  exact (route.boolRoute b).searchIffResult w

/-- A family is pointwise output-functional once cross-limit coherence is supplied. -/
theorem output_functional_of_coherent
    {attempt runner : MachineDescription}
    (route : ControllerStageAttemptFuelPairSearchFamilyRoute attempt runner)
    (hcoherent :
      PairedRecognizerDovetailControllerStageAttemptUnboundedFuelPairObservableCoherent
        attempt)
    {w : Word Bool} {b₁ b₂ : Bool}
    (h₁ : (route.family.machine b₁).HaltsWithOutput w [b₁])
    (h₂ : (route.family.machine b₂).HaltsWithOutput w [b₂]) :
    b₁ = b₂ := by
  exact hcoherent w b₁ b₂
    ((route.boolRoute b₁).searchIff w |>.mp h₁)
    ((route.boolRoute b₂).searchIff w |>.mp h₂)

end ControllerStageAttemptFuelPairSearchFamilyRoute

end Computability
end FoC

import FoC.Computability.Compiler.Core.FiniteScaffolds.ControllerFuelPairSearchFamilyContracts
import FoC.Computability.Compiler.Core.FiniteScaffolds.ControllerOutputLevelSimulatorContracts

set_option doc.verso true

/-!
# Controller search-driver family contract

This module keeps the honest output-indexed search surface: one
subroutine-ready description per observable Boolean.  It deliberately does
not rebuild the historical scalar search-driver and finite-route bundle
lattice, because those declarations had no consumers and a single
halt-transition-free description cannot expose incompatible outputs for the
same public input.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

theorem pairedRecognizerDovetailControllerStageAttemptUnboundedFuelPairEvidence_iff_total_result
    {attempt : MachineDescription} {w : Word Bool} {b : Bool} :
    PairedRecognizerDovetailControllerStageAttemptUnboundedFuelPairEvidence
        attempt w b <->
      exists limit : Nat,
      exists result : Word Bool,
        attempt.HaltsWithOutput
          (encodeCodeWordAsInput
            (PairedRecognizerDovetailStageInputCode w limit))
          (encodeCodeWordAsInput (encodeBoolWord result)) ∧
        PairedRecognizerDovetailControllerRawOutput result = some [b] := by
  constructor
  · intro h
    rcases
        pairedRecognizerDovetailControllerStageAttemptUnboundedFuelPairEvidence_iff_exists_result.mp
          h with
      ⟨limit, candidateFuel, result, hrun, hraw⟩
    exact ⟨limit, result, ⟨candidateFuel, hrun⟩, hraw⟩
  · intro h
    rcases h with ⟨limit, result, ⟨candidateFuel, hrun⟩, hraw⟩
    exact
      pairedRecognizerDovetailControllerStageAttemptUnboundedFuelPairEvidence_iff_exists_result.mpr
        ⟨limit, candidateFuel, result, hrun, hraw⟩

structure ControllerStageAttemptFuelSearchDriverFamilyRoute
    (attempt runner : MachineDescription) where
  fuelPairFamily :
    ControllerStageAttemptFuelPairSearchFamilyRoute attempt runner
  subroutineReady :
    forall b : Bool,
      (fuelPairFamily.family.machine b).SubroutineReady
  fuelSearchIff :
    forall w : Word Bool,
    forall b : Bool,
      (fuelPairFamily.family.machine b).HaltsWithOutput w [b] <->
        exists limit : Nat,
        exists candidateFuel : Nat,
        exists result : Word Bool,
          attempt.HaltsWithOutputIn candidateFuel
            (encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w limit))
            (encodeCodeWordAsInput (encodeBoolWord result)) ∧
          PairedRecognizerDovetailControllerRawOutput result = some [b]
  totalSearchIff :
    forall w : Word Bool,
    forall b : Bool,
      (fuelPairFamily.family.machine b).HaltsWithOutput w [b] <->
        exists limit : Nat,
        exists result : Word Bool,
          attempt.HaltsWithOutput
            (encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w limit))
            (encodeCodeWordAsInput (encodeBoolWord result)) ∧
          PairedRecognizerDovetailControllerRawOutput result = some [b]
  toFuelOutput :
    forall w : Word Bool,
    forall b : Bool,
      (fuelPairFamily.family.machine b).HaltsWithOutput w [b] ->
        PairedRecognizerDovetailControllerStageAttemptUnboundedFuelPairEvidence
          attempt w b
  ofFuelOutput :
    forall w : Word Bool,
    forall b : Bool,
      PairedRecognizerDovetailControllerStageAttemptUnboundedFuelPairEvidence
          attempt w b ->
        (fuelPairFamily.family.machine b).HaltsWithOutput w [b]

def controllerStageAttemptFuelSearchDriverFamilyRoute_of_familyRoute
    {attempt runner : MachineDescription}
    (route :
      ControllerStageAttemptFuelPairSearchFamilyRoute attempt runner) :
    ControllerStageAttemptFuelSearchDriverFamilyRoute attempt runner := by
  exact
    { fuelPairFamily := route
      subroutineReady := fun b =>
        ControllerStageAttemptFuelPairSearchFamilyRoute.subroutineReady
          route b
      fuelSearchIff := fun w b =>
        ControllerStageAttemptFuelPairSearchFamilyRoute.searchIffResult
          route w b
      totalSearchIff := fun w b =>
        Iff.trans
          (ControllerStageAttemptFuelPairSearchFamilyRoute.searchIff
            route w b)
          pairedRecognizerDovetailControllerStageAttemptUnboundedFuelPairEvidence_iff_total_result
      toFuelOutput := fun w b hhalt =>
        (ControllerStageAttemptFuelPairSearchFamilyRoute.searchIff
          route w b).mp hhalt
      ofFuelOutput := fun w b hevidence =>
        (ControllerStageAttemptFuelPairSearchFamilyRoute.searchIff
          route w b).mpr hevidence }

structure ProtectedControllerStageAttemptFuelSearchDriverFamilyRoute
    (attempt invoker runner : MachineDescription) where
  protectedInvocation :
    PairedRecognizerDovetailStageAttemptProtectedInvocationRealizes
      attempt invoker
  fuelSearchFamily :
    ControllerStageAttemptFuelSearchDriverFamilyRoute attempt runner

def protectedControllerStageAttemptFuelSearchDriverFamilyRoute_of_familyRoute
    {attempt invoker runner : MachineDescription}
    (hinvoker :
      PairedRecognizerDovetailStageAttemptProtectedInvocationRealizes
        attempt invoker)
    (route :
      ControllerStageAttemptFuelSearchDriverFamilyRoute attempt runner) :
    ProtectedControllerStageAttemptFuelSearchDriverFamilyRoute
      attempt invoker runner :=
  { protectedInvocation := hinvoker
    fuelSearchFamily := route }

def protectedControllerStageAttemptFuelSearchDriverFamilyRoute_of_exactFuelRunner
    {attempt invoker runner : MachineDescription}
    (hrunner :
      ProtectedControllerStageAttemptExactFuelRunnerRoute
        attempt invoker runner)
    (family :
      PairedRecognizerDovetailControllerStageAttemptFuelPairSearchFamily
        runner) :
    ProtectedControllerStageAttemptFuelSearchDriverFamilyRoute
      attempt invoker runner := by
  let fuelPairRoute :
      ControllerStageAttemptFuelPairSearchFamilyRoute attempt runner :=
    controllerStageAttemptFuelPairSearchFamilyRoute_of_runnerRealizes
      hrunner.realizes family
  exact
    protectedControllerStageAttemptFuelSearchDriverFamilyRoute_of_familyRoute
      hrunner.protectedInvocation
      (controllerStageAttemptFuelSearchDriverFamilyRoute_of_familyRoute
        fuelPairRoute)

/-- Construct the protected search-driver route without collapsing its two
observable Boolean fibers to one machine. -/
def ProtectedControllerStageAttemptFuelSearchDriverFamilyRouteConstruction :
    Prop :=
  forall attempt invoker : MachineDescription,
    PairedRecognizerDovetailStageAttemptProtectedInvocationRealizes
      attempt invoker ->
      exists runner : MachineDescription,
        Nonempty
          (ProtectedControllerStageAttemptFuelSearchDriverFamilyRoute
            attempt invoker runner)

theorem protectedControllerStageAttemptFuelSearchDriverFamilyRouteConstruction_of_exactFuelRunner_and_searchFamily
    (hrunner :
      PairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerConstruction)
    (hsearch :
      PairedRecognizerDovetailControllerStageAttemptFuelPairSearchFamilyConstruction) :
    ProtectedControllerStageAttemptFuelSearchDriverFamilyRouteConstruction := by
  intro attempt invoker hinvoker
  rcases hrunner attempt invoker hinvoker with ⟨runner, hrunnerSpec⟩
  rcases hsearch runner hrunnerSpec.left with ⟨family⟩
  exact
    ⟨runner,
      ⟨protectedControllerStageAttemptFuelSearchDriverFamilyRoute_of_exactFuelRunner
          (protectedControllerStageAttemptExactFuelRunnerRoute_of_realizes
            hinvoker hrunnerSpec)
          family⟩⟩

/-- The direct family replacement for the historical scalar controller
search-driver realization.  The Boolean is fixed before selecting a machine. -/
def PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverFamilyRealizes
    (attempt : MachineDescription)
    (family : Bool -> MachineDescription) : Prop :=
  forall b : Bool,
    (family b).WellFormed ∧
      forall w : Word Bool,
        (family b).HaltsWithOutput w [b] <->
          exists limit : Nat,
          exists result : Word Bool,
            attempt.HaltsWithOutput
              (encodeCodeWordAsInput
                (PairedRecognizerDovetailStageInputCode w limit))
              (encodeCodeWordAsInput (encodeBoolWord result)) ∧
            PairedRecognizerDovetailControllerRawOutput result = some [b]

/-- Protected construction of one honest search-driver machine per Boolean. -/
def PairedRecognizerDovetailProtectedStageAttemptControllerSearchDriverFamilyConstruction :
    Prop :=
  forall attempt invoker : MachineDescription,
    PairedRecognizerDovetailStageAttemptProtectedInvocationRealizes
      attempt invoker ->
      exists family : Bool -> MachineDescription,
        PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverFamilyRealizes
          attempt family

/-- Honest finite-loop controller boundary for arbitrary stage attempts.  It
returns one machine per observable Boolean and makes no cross-limit coherence
claim. -/
def PairedRecognizerDovetailFiniteStageLoopControllerFamilyConstruction :
    Prop :=
  forall attempt : MachineDescription,
    attempt.SubroutineReady ->
      exists family : Bool -> MachineDescription,
        PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverFamilyRealizes
          attempt family

theorem pairedRecognizerDovetailProtectedStageAttemptControllerSearchDriverFamilyConstruction_of_route
    (hroute :
      ProtectedControllerStageAttemptFuelSearchDriverFamilyRouteConstruction) :
    PairedRecognizerDovetailProtectedStageAttemptControllerSearchDriverFamilyConstruction := by
  intro attempt invoker hinvoker
  rcases hroute attempt invoker hinvoker with ⟨runner, ⟨route⟩⟩
  refine
    ⟨fun b => route.fuelSearchFamily.fuelPairFamily.family.machine b, ?_⟩
  intro b
  constructor
  · exact (route.fuelSearchFamily.subroutineReady b).left
  · intro w
    exact route.fuelSearchFamily.totalSearchIff w b

end Computability
end FoC

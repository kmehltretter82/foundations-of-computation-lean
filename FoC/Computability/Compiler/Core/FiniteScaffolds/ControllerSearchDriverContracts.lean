import FoC.Computability.Compiler.Core.FiniteScaffolds.ControllerFuelPairSearchContracts
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

end Computability
end FoC

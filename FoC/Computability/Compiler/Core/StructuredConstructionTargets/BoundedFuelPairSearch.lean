import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.SearchSemantics
import FoC.Computability.Compiler.Core.StructuredConstructionTargets.TwoStageEndpoints

set_option doc.verso true

/-!
# Output-indexed structured fuel-pair search

This is the consistent replacement frontier for the former all-result bounded
fuel-pair enumerator.  The observable Boolean is fixed for each constructed
machine, while the hidden pair and decoded result remain semantic witnesses.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace StructuredConstructionTargets

open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

def boundedFuelPairBoolSearchStructuredInputBits
    (w : Word Bool) : Word Bool :=
  w

def boundedFuelPairBoolSearchStructuredInputTape
    {runner : MachineDescription} {b : Bool}
    (i :
      PairedRecognizerDovetailControllerStageAttemptFuelPairEvidenceWitness
        runner b) : Tape Bool :=
  Tape.input (boundedFuelPairBoolSearchStructuredInputBits i.input)

def boundedFuelPairBoolSearchStructuredInitializedTape
    (w : Word Bool) : Tape Bool :=
  CommonGround.FiniteTransducers.structured3InputMaterializerTargetTape
    (Tape.input (boundedFuelPairBoolSearchStructuredInputBits w))
    Tape.blank

def boundedFuelPairBoolSearchStructuredLoweredTape
    {runner : MachineDescription} {b : Bool}
    (i :
      PairedRecognizerDovetailControllerStageAttemptFuelPairEvidenceWitness
        runner b) : Tape Bool :=
  encodedGuardedStructured3Tapes
    (boundedFuelPairBoolSearchStructuredInputTape i)
    Tape.blank
    (PairedRecognizerDovetailControllerStageAttemptFuelPairBoolRightShiftedOutputTape
      b)

def BoundedFuelPairBoolSearchStructuredMaterializerConstruction : Prop :=
  Structured3EndpointWordStartEquivMaterializerConstruction
    boundedFuelPairBoolSearchStructuredInputBits
    boundedFuelPairBoolSearchStructuredInitializedTape

def BoundedFuelPairBoolSearchStructuredExactSemanticCoreConstruction
    (runner : MachineDescription) (b : Bool) : Prop :=
  Structured3EndpointExactSemanticCoreConstruction
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptFuelPairEvidenceWitness
        runner b => i.input)
    boundedFuelPairBoolSearchStructuredInitializedTape
    boundedFuelPairBoolSearchStructuredLoweredTape
    (fun _i =>
      PairedRecognizerDovetailControllerStageAttemptFuelPairBoolRightShiftedOutputTape
        b)
    boundedFuelPairBoolSearchStructuredInputTape
    (fun _i => Tape.blank)

def BoundedFuelPairBoolSearchStructuredEndpointConstruction
    (runner : MachineDescription) (b : Bool) : Prop :=
  exists W : Structured3EndpointWrapper,
    Structured3EndpointWordStartEquivIndexedFamilySpec
      W
      (fun i :
        PairedRecognizerDovetailControllerStageAttemptFuelPairEvidenceWitness
          runner b =>
        boundedFuelPairBoolSearchStructuredInputBits i.input)
      (fun _i =>
        PairedRecognizerDovetailControllerStageAttemptFuelPairBoolRightShiftedOutputTape
          b)

/-- The clean public-word embedding is shared by both Boolean searchers. -/
theorem boundedFuelPairBoolSearchStructuredMaterializerConstruction_core :
    BoundedFuelPairBoolSearchStructuredMaterializerConstruction := by
  refine
    ⟨structured3InputEmbeddingEmitterDescription,
      structured3InputEmbeddingEmitterDescription_spec.left, ?_⟩
  constructor
  · intro w
    simpa [boundedFuelPairBoolSearchStructuredInputBits,
      boundedFuelPairBoolSearchStructuredInitializedTape] using
      structured3InputEmbeddingEmitterDescription_spec.right w
  · intro w T hhalt
    refine ⟨w, rfl, ?_⟩
    exact
      haltsFromTape_equiv_target_of_forward
        structured3InputEmbeddingEmitterDescription_spec.left
        hhalt
        (by
          simpa [boundedFuelPairBoolSearchStructuredInputBits,
            boundedFuelPairBoolSearchStructuredInitializedTape] using
            structured3InputEmbeddingEmitterDescription_spec.right w)

theorem boundedFuelPairBoolSearchStructuredEndpointConstruction_of_components
    (runner : MachineDescription) (b : Bool)
    (hcore :
      BoundedFuelPairBoolSearchStructuredExactSemanticCoreConstruction
        runner b) :
    BoundedFuelPairBoolSearchStructuredEndpointConstruction runner b := by
  simpa [BoundedFuelPairBoolSearchStructuredEndpointConstruction,
    BoundedFuelPairBoolSearchStructuredMaterializerConstruction,
    BoundedFuelPairBoolSearchStructuredExactSemanticCoreConstruction] using
    structured3EndpointWordStartEquivIndexedConstruction_of_components
      boundedFuelPairBoolSearchStructuredMaterializerConstruction_core
      (structured3EndpointEquivSemanticCoreConstruction_of_exact hcore)
      (by
        intro _i
        simpa [
          PairedRecognizerDovetailControllerStageAttemptFuelPairBoolRightShiftedOutputTape] using
          structuredTape2EndpointTape_moveRight_input b [])
      structured3EndpointTape2ProjectorConstruction_core

/-- A fixed-output structured endpoint realizes the public Boolean search contract. -/
theorem boundedFuelPairBoolSearchSpec_of_endpointEquivIndexed
    {runner : MachineDescription} {b : Bool}
    {W : Structured3EndpointWrapper}
    (hspec :
      Structured3EndpointWordStartEquivIndexedFamilySpec
        W
        (fun i :
          PairedRecognizerDovetailControllerStageAttemptFuelPairEvidenceWitness
            runner b =>
          boundedFuelPairBoolSearchStructuredInputBits i.input)
        (fun _i =>
          PairedRecognizerDovetailControllerStageAttemptFuelPairBoolRightShiftedOutputTape
            b)) :
    PairedRecognizerDovetailControllerStageAttemptFuelPairBoolSearchSpec
      runner W.machine b := by
  constructor
  · exact W.machine_subroutineReady
  · intro w hevidence
    rcases hevidence with ⟨limit, fuel, hrunner⟩
    let i :
        PairedRecognizerDovetailControllerStageAttemptFuelPairEvidenceWitness
          runner b :=
      { input := w
        limit := limit
        fuel := fuel
        runner_halts := hrunner }
    have hforward :=
      MachineDescription.haltsFromTapeWithOutput_of_haltsFromTapeEquiv
        (hspec.forward i)
    rw [
      pairedRecognizerDovetailControllerStageAttemptFuelPairBoolRightShiftedOutputTape_normalizedOutput]
      at hforward
    simpa [MachineDescription.HaltsWithOutput,
      MachineDescription.HaltsFromTapeWithOutput,
      MachineDescription.HaltsWithOutputIn,
      MachineDescription.HaltsFromTapeWithOutputIn,
      MachineDescription.initial,
      boundedFuelPairBoolSearchStructuredInputBits, i] using hforward
  · intro w out hhalt
    rcases hhalt with ⟨steps, hhaltSteps⟩
    let T :=
      (W.machine.runConfig steps (W.machine.initial w)).tape
    have hfrom :
        W.machine.HaltsFromTape (Tape.input w) T := by
      exact
        ⟨steps,
          by
            rcases hhaltSteps with ⟨hstate, _houtput⟩
            exact ⟨hstate, rfl⟩⟩
    rcases hspec.closedIndex w T hfrom with
      ⟨i, hinput, hT⟩
    have hpublic : w = i.input := by
      simpa [boundedFuelPairBoolSearchStructuredInputBits] using hinput
    have houtput : Tape.normalizedOutput T = out := by
      rcases hhaltSteps with ⟨_hstate, hnormalized⟩
      simpa [T] using hnormalized
    have htarget : Tape.normalizedOutput T = [b] := by
      rw [Tape.Equiv.normalizedOutput_eq hT,
        pairedRecognizerDovetailControllerStageAttemptFuelPairBoolRightShiftedOutputTape_normalizedOutput]
    constructor
    · exact houtput.symm.trans htarget
    · rw [hpublic]
      exact ⟨i.limit, i.fuel, i.runner_halts⟩

/-- Two fixed-output endpoint constructions assemble into the Boolean search family. -/
theorem boundedFuelPairSearchFamily_of_structuredEndpointConstructions
    (runner : MachineDescription)
    (hendpoint :
      forall b : Bool,
        BoundedFuelPairBoolSearchStructuredEndpointConstruction runner b) :
    Nonempty
      (PairedRecognizerDovetailControllerStageAttemptFuelPairSearchFamily
        runner) := by
  rcases hendpoint false with ⟨Wfalse, hfalse⟩
  rcases hendpoint true with ⟨Wtrue, htrue⟩
  refine ⟨{
    machine := fun b => match b with
      | false => Wfalse.machine
      | true => Wtrue.machine
    spec := ?_
  }⟩
  intro b
  cases b
  · exact boundedFuelPairBoolSearchSpec_of_endpointEquivIndexed hfalse
  · exact boundedFuelPairBoolSearchSpec_of_endpointEquivIndexed htrue

/-- Endpoint construction for each Boolean discharges the repaired public frontier. -/
theorem boundedFuelPairSearchFamilyConstruction_of_structuredEndpoints
    (hendpoint :
      forall runner : MachineDescription,
        runner.SubroutineReady ->
          forall b : Bool,
            BoundedFuelPairBoolSearchStructuredEndpointConstruction
              runner b) :
    PairedRecognizerDovetailControllerStageAttemptFuelPairSearchFamilyConstruction := by
  intro runner hrunner
  exact
    boundedFuelPairSearchFamily_of_structuredEndpointConstructions
      runner (hendpoint runner hrunner)

end StructuredConstructionTargets

end Computability
end FoC

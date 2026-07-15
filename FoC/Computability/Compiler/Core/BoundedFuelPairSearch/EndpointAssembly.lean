import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.EquivAdapter
import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.LoweredInversion
import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.MasterProgress
import FoC.Computability.Compiler.Core.StructuredConstructionTargets.BoundedFuelPairSearch
import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Simulator.PaddedEmitter

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape

namespace BoundedFuelPairSearch
namespace U12EndpointAssembly

open StructuredConstructionTargets
open U12CandidateAttemptLoop
open U12EquivAdapter
open U12MasterLoop
open U12MasterProgress

def wrapper
    (source sourceSimulator recognizer checkerSimulator : MachineDescription)
    (b : Bool)
    (hsourceSimulator :
      FixedDescriptionBoundedSimulatorEquivSpec source sourceSimulator)
    (hcheckerSimulator :
      SuccessOnlyFairBoundedWrapperSpec recognizer checkerSimulator) :
    Structured3EndpointWrapper where
  core :=
    (U12MasterLoop.table source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator.left hcheckerSimulator.left).description
  initializer := structured3InputEmbeddingEmitterDescription
  projector := fixedBoolCloseoutDescription b
  coreWellFormed :=
    (U12MasterLoop.table source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator.left hcheckerSimulator.left).description_wellFormed
  coreHaltTransitionFree :=
    (U12MasterLoop.table source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator.left hcheckerSimulator.left).description_haltTransitionFree
  coreSupportsRows :=
    (U12MasterLoop.table source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator.left hcheckerSimulator.left).description_supportsReadWriteRows3
  initializerSubroutineReady :=
    structured3InputEmbeddingEmitterDescription_spec.left
  projectorSubroutineReady := fixedBoolCloseoutDescription_subroutineReady b

theorem lowered_forward_of_evidence
    (source sourceSimulator recognizer checkerSimulator : MachineDescription)
    (b : Bool)
    (hsourceSimulator :
      FixedDescriptionBoundedSimulatorEquivSpec source sourceSimulator)
    (hcheckerSimulator :
      SuccessOnlyFairBoundedWrapperSpec recognizer checkerSimulator)
    (hrecognizer :
      FixedBoolSimulatorLayoutRecognizerSpec source recognizer b)
    (i :
      PairedRecognizerDovetailControllerStageAttemptFuelPairEvidenceWitness
        source b) :
    exists A0 A1 A2 : Tape Bool,
      (wrapper source sourceSimulator recognizer checkerSimulator b
          hsourceSimulator hcheckerSimulator).lowered.HaltsFromTapeEquiv
        (structured3InputMaterializerTargetTape
          (Tape.input i.input) Tape.blank)
        (encodedGuardedStructured3Tapes A0 A1 A2) ∧
      Tape.Equiv A2
        (PairedRecognizerDovetailControllerStageAttemptFuelPairBoolRightShiftedOutputTape
          b) := by
  let M :=
    U12MasterLoop.table source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator.left hcheckerSimulator.left
  rcases U12CandidateAttemptLoop.leads_initialized_of_evidence
      source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator hrecognizer
      (show List Bool from i.input)
      ⟨i.limit, i.fuel, i.runner_halts⟩ with
    ⟨A0, A1, A2, hleads, hA2⟩
  rcases hleads.to_runConfig with ⟨steps, hrun⟩
  have hhalts : M.description.HaltsWithTapes
      (M.config (.bootstrap U12ZeroBootstrap.State.lengthScan)
        (Tape.input i.input) Tape.blank Tape.blank)
      [A0, A1, A2] := by
    refine ⟨steps, ?_⟩
    change M.description.runConfig steps
        (M.config (.bootstrap U12ZeroBootstrap.State.lengthScan)
          (Tape.input i.input) Tape.blank Tape.blank) =
      M.config .halt A0 A1 A2
    exact hrun
  have hlowered :=
    lowerStructured3Description_haltsFromConfigWithTapes
      M.description_wellFormed
      M.description_haltTransitionFree
      M.description_supportsReadWriteRows3
      (c := M.config (.bootstrap U12ZeroBootstrap.State.lengthScan)
        (Tape.input i.input) Tape.blank Tape.blank)
      (tapes := [A0, A1, A2])
      rfl rfl hhalts
  refine ⟨A0, A1, A2, ?_, ?_⟩
  · simpa [wrapper, Structured3EndpointWrapper.lowered, M,
      structured3InputMaterializerTargetTape,
      encodedGuardedStructured3Tapes, TypedStateTable.config,
      ThreeTape.config] using hlowered
  · simpa [
      PairedRecognizerDovetailControllerStageAttemptFuelPairBoolRightShiftedOutputTape]
      using hA2

theorem wrapper_forward
    (source sourceSimulator recognizer checkerSimulator : MachineDescription)
    (b : Bool)
    (hsourceSimulator :
      FixedDescriptionBoundedSimulatorEquivSpec source sourceSimulator)
    (hcheckerSimulator :
      SuccessOnlyFairBoundedWrapperSpec recognizer checkerSimulator)
    (hrecognizer :
      FixedBoolSimulatorLayoutRecognizerSpec source recognizer b)
    (i :
      PairedRecognizerDovetailControllerStageAttemptFuelPairEvidenceWitness
        source b) :
    (wrapper source sourceSimulator recognizer checkerSimulator b
        hsourceSimulator hcheckerSimulator).machine.HaltsFromTapeEquiv
      (Tape.input i.input)
      (PairedRecognizerDovetailControllerStageAttemptFuelPairBoolRightShiftedOutputTape
        b) := by
  let W := wrapper source sourceSimulator recognizer checkerSimulator b
    hsourceSimulator hcheckerSimulator
  rcases lowered_forward_of_evidence
      source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator hrecognizer i with
    ⟨A0, A1, A2, hlowered, _hA2⟩
  exact W.haltsFromTapeEquiv
    (by
      simpa [W, wrapper, structured3InputMaterializerTargetTape] using
        structured3InputEmbeddingEmitterDescription_spec.right i.input)
    (by
      simpa [W, structured3InputMaterializerTargetTape] using hlowered)
    (by
      simpa [W, wrapper,
        PairedRecognizerDovetailControllerStageAttemptFuelPairBoolRightShiftedOutputTape]
        using fixedBoolCloseoutDescription_haltsFrom_encodedGuardedStructured3Tapes
          b A0 A1 A2)

theorem wrapper_spec
    (source sourceSimulator recognizer checkerSimulator : MachineDescription)
    (b : Bool)
    (hsourceSimulator :
      FixedDescriptionBoundedSimulatorEquivSpec source sourceSimulator)
    (hcheckerSimulator :
      SuccessOnlyFairBoundedWrapperSpec recognizer checkerSimulator)
    (hrecognizer :
      FixedBoolSimulatorLayoutRecognizerSpec source recognizer b) :
    Structured3EndpointWordStartEquivIndexedFamilySpec
      (wrapper source sourceSimulator recognizer checkerSimulator b
        hsourceSimulator hcheckerSimulator)
      (fun i :
        PairedRecognizerDovetailControllerStageAttemptFuelPairEvidenceWitness
          source b => i.input)
      (fun _i =>
        PairedRecognizerDovetailControllerStageAttemptFuelPairBoolRightShiftedOutputTape
          b) := by
  let W := wrapper source sourceSimulator recognizer checkerSimulator b
    hsourceSimulator hcheckerSimulator
  change Structured3EndpointWordStartEquivIndexedFamilySpec W _ _
  constructor
  · intro i
    exact wrapper_forward
      source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator hrecognizer i
  · intro w T hhalt
    rcases
        canonicalPrimitiveSeqDescription_haltsFromTape_inv
          (canonicalPrimitiveSeqDescription_subroutineReady
            W.initializerSubroutineReady W.lowered_subroutineReady)
          W.projectorSubroutineReady
          (by
            simpa [Structured3EndpointWrapper.machine,
              structured3EndpointBridgeDescription] using hhalt) with
      ⟨TloweredActual, hfirst, _hprojectorActual⟩
    rcases
        canonicalPrimitiveSeqDescription_haltsFromTape_inv
          W.initializerSubroutineReady
          W.lowered_subroutineReady
          hfirst with
      ⟨TinitActual, hinitializerActual, hloweredActual⟩
    let Tinitialized :=
      structured3InputMaterializerTargetTape (Tape.input w) Tape.blank
    have hinitializerForward :
        W.initializer.HaltsFromTapeEquiv (Tape.input w) Tinitialized := by
      simpa [W, wrapper, Tinitialized] using
        structured3InputEmbeddingEmitterDescription_spec.right w
    have hTinit : Tape.Equiv TinitActual Tinitialized :=
      (closedFromTapeEquiv_of_haltsFromTapeEquiv_of_subroutineReady
        W.initializerSubroutineReady hinitializerForward)
        TinitActual hinitializerActual
    have hLoweredInput :
        Tape.Equiv
          (canonicalPrimitiveSeqHandoffTape TinitActual)
          Tinitialized :=
      Tape.Equiv.trans
        (canonicalPrimitiveSeqHandoffTape_equiv TinitActual)
        hTinit
    rcases
        HaltsFromTapeEquiv_of_input_equiv
          (D := W.lowered)
          (Tin := canonicalPrimitiveSeqHandoffTape TinitActual)
          (Tin' := Tinitialized)
          (Tout := TloweredActual)
          hLoweredInput hloweredActual with
      ⟨TloweredFromInput, hloweredFromInput,
        _hTloweredFromInput⟩
    have hLoweredCanonical :
        (lowerStructured3Description
          (U12MasterLoop.table source sourceSimulator recognizer
            checkerSimulator b hsourceSimulator.left
              hcheckerSimulator.left).description).HaltsFromTape
          (encodedGuardedStructuredTapes
            ((U12MasterLoop.table source sourceSimulator recognizer
              checkerSimulator b hsourceSimulator.left
                hcheckerSimulator.left).config
              (.bootstrap U12ZeroBootstrap.State.lengthScan)
              (Tape.input w) Tape.blank Tape.blank).tapes)
          TloweredFromInput := by
      simpa [W, wrapper, Structured3EndpointWrapper.lowered, Tinitialized,
        structured3InputMaterializerTargetTape,
        encodedGuardedStructured3Tapes, TypedStateTable.config,
        ThreeTape.config] using hloweredFromInput
    have hevidence :=
      U12EquivAdapter.evidence_of_lowered_haltsFromTape_initialized
        source sourceSimulator recognizer checkerSimulator b
        hsourceSimulator hcheckerSimulator hrecognizer
        (U12MasterProgress.master_stepConfig_progress
          source sourceSimulator recognizer checkerSimulator b
          hsourceSimulator.left hcheckerSimulator.left)
        (show List Bool from w) TloweredFromInput hLoweredCanonical
    rcases hevidence with ⟨limit, fuel, hrunner⟩
    let i :
        PairedRecognizerDovetailControllerStageAttemptFuelPairEvidenceWitness
          source b :=
      { input := w
        limit := limit
        fuel := fuel
        runner_halts := hrunner }
    refine ⟨i, rfl, ?_⟩
    exact haltsFromTape_equiv_target_of_forward
      W.machine_subroutineReady hhalt
      (by
        simpa [i] using
          wrapper_forward
            source sourceSimulator recognizer checkerSimulator b
            hsourceSimulator hcheckerSimulator hrecognizer i)

theorem endpointConstruction_of_components
    (source sourceSimulator recognizer checkerSimulator : MachineDescription)
    (b : Bool)
    (hsourceSimulator :
      FixedDescriptionBoundedSimulatorEquivSpec source sourceSimulator)
    (hcheckerSimulator :
      SuccessOnlyFairBoundedWrapperSpec recognizer checkerSimulator)
    (hrecognizer :
      FixedBoolSimulatorLayoutRecognizerSpec source recognizer b) :
    BoundedFuelPairBoolSearchStructuredEndpointConstruction source b := by
  refine ⟨wrapper source sourceSimulator recognizer checkerSimulator b
    hsourceSimulator hcheckerSimulator, ?_⟩
  simpa [boundedFuelPairBoolSearchStructuredInputBits] using
    wrapper_spec source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator hrecognizer

theorem endpointConstruction
    (source : MachineDescription) (b : Bool) :
    BoundedFuelPairBoolSearchStructuredEndpointConstruction source b := by
  rcases
      EncRewriters.BoundedLayoutRunner.fixedDescriptionBoundedSimulatorEquivConstruction_scaffold_configRunner
        source with
    ⟨sourceSimulator, hsourceSimulator⟩
  rcases fixedBoolSimulatorLayoutRecognizerConstruction source b with
    ⟨recognizer, hrecognizer⟩
  rcases successOnlyFairBoundedWrapperConstruction recognizer with
    ⟨checkerSimulator, hcheckerSimulator⟩
  exact endpointConstruction_of_components
    source sourceSimulator recognizer checkerSimulator b
    hsourceSimulator hcheckerSimulator hrecognizer

theorem searchFamilyConstruction :
    PairedRecognizerDovetailControllerStageAttemptFuelPairSearchFamilyConstruction := by
  apply boundedFuelPairSearchFamilyConstruction_of_structuredEndpoints
  intro runner _hrunner b
  exact endpointConstruction runner b

end U12EndpointAssembly
end BoundedFuelPairSearch
end Computability
end FoC

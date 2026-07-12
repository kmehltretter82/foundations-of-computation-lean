import FoC.Computability.Compiler.Core.StructuredConstructionTargets.FuelOutput
import FoC.Computability.Compiler.Core.StructuredConstructionTargets.TwoStageEndpoints

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace StructuredConstructionTargets

open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

def boundedFuelPairEnumeratorStructuredInputBits
    (w : Word Bool) : Word Bool :=
  w

def boundedFuelPairEnumeratorStructuredInputTape
    {runner : MachineDescription}
    (i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner) : Tape Bool :=
  Tape.input (boundedFuelPairEnumeratorStructuredInputBits i.input)

def boundedFuelPairEnumeratorStructuredInitializedTape
    (w : Word Bool) : Tape Bool :=
  CommonGround.FiniteTransducers.structured3InputMaterializerTargetTape
    (Tape.input (boundedFuelPairEnumeratorStructuredInputBits w))
    Tape.blank

def boundedFuelPairEnumeratorStructuredLoweredTape
    {runner : MachineDescription}
    (i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner) : Tape Bool :=
  encodedGuardedStructured3Tapes
    (boundedFuelPairEnumeratorStructuredInputTape i)
    Tape.blank
    (PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape
      i)

def BoundedFuelPairEnumeratorStructuredMaterializerConstruction : Prop :=
  Structured3EndpointWordStartEquivMaterializerConstruction
    boundedFuelPairEnumeratorStructuredInputBits
    boundedFuelPairEnumeratorStructuredInitializedTape

def BoundedFuelPairEnumeratorStructuredExactSemanticCoreConstruction
    (runner : MachineDescription) : Prop :=
  Structured3EndpointExactSemanticCoreConstruction
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner => i.input)
    boundedFuelPairEnumeratorStructuredInitializedTape
    boundedFuelPairEnumeratorStructuredLoweredTape
    PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape
    boundedFuelPairEnumeratorStructuredInputTape
    (fun _i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner => Tape.blank)

def BoundedFuelPairEnumeratorStructuredEndpointEquivIndexedConstruction
    (runner : MachineDescription) : Prop :=
  exists W : Structured3EndpointWrapper,
    Structured3EndpointWordStartEquivIndexedFamilySpec
      W
      (fun i :
        PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
          runner =>
        boundedFuelPairEnumeratorStructuredInputBits i.input)
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape

/--
Finite-table leaf for the bounded fuel-pair enumerator public-input
materializer.
-/
theorem boundedFuelPairEnumeratorStructuredMaterializerConstruction_core :
    BoundedFuelPairEnumeratorStructuredMaterializerConstruction := by
  refine
    ⟨structured3InputEmbeddingEmitterDescription,
      structured3InputEmbeddingEmitterDescription_spec.left, ?_⟩
  constructor
  · intro w
    simpa [boundedFuelPairEnumeratorStructuredInputBits,
      boundedFuelPairEnumeratorStructuredInitializedTape] using
      structured3InputEmbeddingEmitterDescription_spec.right w
  · intro w T hhalt
    refine ⟨w, rfl, ?_⟩
    exact
      haltsFromTape_equiv_target_of_forward
        structured3InputEmbeddingEmitterDescription_spec.left
        hhalt
        (by
          simpa [boundedFuelPairEnumeratorStructuredInputBits,
            boundedFuelPairEnumeratorStructuredInitializedTape] using
            structured3InputEmbeddingEmitterDescription_spec.right w)

/--
Finite-table leaf for the lowered bounded fuel-pair enumerator structured
core.
-/
theorem boundedFuelPairEnumeratorStructuredExactSemanticCoreConstruction_core
    (runner : MachineDescription)
    (_hrunner : runner.SubroutineReady) :
    BoundedFuelPairEnumeratorStructuredExactSemanticCoreConstruction
      runner := by
  -- Remaining structured-core obligation: enumerate bounded fuel pairs,
  -- invoke the exact-fuel runner endpoint, and leave the right-shifted
  -- classifier handoff tape on logical tape 2.
  sorry

/--
Target-local parser/core obligation for the bounded fuel-pair enumerator
target.  The public endpoint theorem below only composes this with the shared
equivalence tape-2 projector.
-/
theorem boundedFuelPairEnumeratorStructuredEndpointEquivIndexedConstruction_of_components
    (runner : MachineDescription)
    (hmaterializer :
      BoundedFuelPairEnumeratorStructuredMaterializerConstruction)
    (hcore :
      BoundedFuelPairEnumeratorStructuredExactSemanticCoreConstruction
        runner) :
    BoundedFuelPairEnumeratorStructuredEndpointEquivIndexedConstruction
      runner := by
  simpa [BoundedFuelPairEnumeratorStructuredEndpointEquivIndexedConstruction,
    BoundedFuelPairEnumeratorStructuredMaterializerConstruction,
    BoundedFuelPairEnumeratorStructuredExactSemanticCoreConstruction] using
    structured3EndpointWordStartEquivIndexedConstruction_of_components
      hmaterializer
      (structured3EndpointEquivSemanticCoreConstruction_of_exact hcore)
      (by
        intro i
        rcases EncRewriters.encodeBoolWord_cons i.result with
          ⟨symbol, tail, hcode⟩
        simpa [
          PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape,
          PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorOutputCode,
          hcode] using
          structuredTape2EndpointTape_moveRight_encodeCodeWordAsInput_cons
            symbol tail)
      structured3EndpointTape2ProjectorConstruction_core
theorem boundedFuelPairEnumeratorStructuredEndpointEquivIndexedConstruction_core
    (runner : MachineDescription)
    (hrunner : runner.SubroutineReady) :
    BoundedFuelPairEnumeratorStructuredEndpointEquivIndexedConstruction runner :=
  boundedFuelPairEnumeratorStructuredEndpointEquivIndexedConstruction_of_components
    runner
    boundedFuelPairEnumeratorStructuredMaterializerConstruction_core
    (boundedFuelPairEnumeratorStructuredExactSemanticCoreConstruction_core
      runner hrunner)

end StructuredConstructionTargets

end Computability
end FoC

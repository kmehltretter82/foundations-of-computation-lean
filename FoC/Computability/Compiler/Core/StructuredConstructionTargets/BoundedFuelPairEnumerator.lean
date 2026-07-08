import FoC.Computability.Compiler.Core.StructuredConstructionTargets.FuelOutput
import FoC.Computability.Compiler.Core.StructuredConstructionTargets.EndpointMacro

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace StructuredConstructionTargets

open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

def boundedFuelPairEnumeratorStructuredInputTape
    {runner : MachineDescription}
    (i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner) : Tape Bool :=
  Tape.input i.input

declare_structured_endpoint
  Prefix: BoundedFuelPairEnumeratorStructured
  lowerPrefix: boundedFuelPairEnumeratorStructured
  Param: (runner : MachineDescription)
  Index: PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness runner
  InputTape: boundedFuelPairEnumeratorStructuredInputTape
  OutputTape: PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape

/--
Finite-table leaf for the bounded fuel-pair enumerator public-input
materializer.
-/
theorem boundedFuelPairEnumeratorStructuredIndexedMaterializerConstruction_core
    (runner : MachineDescription) :
    BoundedFuelPairEnumeratorStructuredIndexedMaterializerConstruction
      runner := by
  -- Remaining parser/materializer obligation: recognize bounded enumerator
  -- inputs and materialize the guarded three-logical-tape input.
  sorry

/--
Finite-table leaf for the lowered bounded fuel-pair enumerator structured
core.
-/
theorem boundedFuelPairEnumeratorStructuredLoweredCoreConstruction_core
    (runner : MachineDescription)
    (_hrunner : runner.SubroutineReady) :
    BoundedFuelPairEnumeratorStructuredLoweredCoreConstruction
      runner := by
  -- Remaining structured-core obligation: enumerate bounded fuel pairs,
  -- invoke the exact-fuel runner endpoint, and leave the right-shifted
  -- classifier handoff tape on logical tape 2.
  sorry

/--
Target-local parser/core obligation for the bounded fuel-pair enumerator
target.  The public endpoint theorem below only composes this with the shared
exact tape-2 projector.
-/
theorem boundedFuelPairEnumeratorStructuredCanonicalEndpointCoreComponentConstruction_core
    (runner : MachineDescription)
    (hrunner : runner.SubroutineReady) :
    BoundedFuelPairEnumeratorStructuredCanonicalEndpointCoreComponentConstruction
      runner :=
  boundedFuelPairEnumeratorStructuredCanonicalEndpointCoreComponentConstruction_of_materializer_loweredCore
    (boundedFuelPairEnumeratorStructuredIndexedMaterializerConstruction_core
      runner)
    (boundedFuelPairEnumeratorStructuredLoweredCoreConstruction_core
      runner hrunner)



/--
Remaining structured-core endpoint obligation for bounded {lit}`(limit, fuel)`
enumeration against a ready exact-fuel runner.
-/
def BoundedFuelPairEnumeratorStructuredCoreEndpointConstruction
    (runner : MachineDescription) : Prop :=
    runner.SubroutineReady ->
    BoundedFuelPairEnumeratorStructuredEndpointExactIndexedConstruction
      runner

/--
Canonical bounded fuel-pair enumerator endpoint obligations imply the existing
flexible exact-indexed core endpoint obligation.
-/
theorem boundedFuelPairEnumeratorStructuredCoreEndpointConstruction_of_canonical
    (hcanonical :
      forall runner : MachineDescription,
        runner.SubroutineReady ->
          BoundedFuelPairEnumeratorStructuredCanonicalEndpointConstruction
            runner) :
    forall runner : MachineDescription,
      BoundedFuelPairEnumeratorStructuredCoreEndpointConstruction runner := by
  intro runner hrunner
  exact
    boundedFuelPairEnumeratorStructuredEndpointExactIndexedConstruction_of_canonical
      (hcanonical runner hrunner)

theorem boundedFuelPairEnumeratorInput_eq_of_inputTape_eq
    {runner : MachineDescription}
    {w : Word Bool}
    {i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner}
    (h :
      Tape.input w =
        boundedFuelPairEnumeratorStructuredInputTape i) :
    w = i.input := by
  exact
    Tape.input_injective
      (by
        simpa [boundedFuelPairEnumeratorStructuredInputTape] using h)

theorem boundedFuelPairEnumeratorRightShiftedSpec_of_endpointExactIndexed
    {runner : MachineDescription}
    {W : Structured3EndpointWrapper}
    {initialized lowered :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner -> Tape Bool}
    (hspec :
      Structured3EndpointExactIndexedFamilySpec
        W
        boundedFuelPairEnumeratorStructuredInputTape
        initialized
        lowered
        PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape) :
    PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedSpec
      runner W.machine := by
  constructor
  · exact W.machine_subroutineReady
  constructor
  · intro i
    simpa [boundedFuelPairEnumeratorStructuredInputTape] using
      haltsWithTape_of_haltsFromTape_input
        (Structured3EndpointExactIndexedFamilySpec.forward hspec i)
  · intro w T hhalt
    have hfrom :
        W.machine.HaltsFromTape (Tape.input w) T :=
      haltsFromTape_input_of_haltsWithTape hhalt
    rcases
        Structured3EndpointExactIndexedFamilySpec.closedIndex
          hspec (Tape.input w) T hfrom with
      ⟨i, hinput, hT⟩
    have hw : w = i.input :=
      boundedFuelPairEnumeratorInput_eq_of_inputTape_eq hinput
    exact ⟨i, hw, hT⟩

theorem boundedFuelPairEnumeratorStructuredEndpointEquivIndexedConstruction_core
    (runner : MachineDescription)
    (hrunner : runner.SubroutineReady) :
    BoundedFuelPairEnumeratorStructuredEndpointEquivIndexedConstruction runner :=
  boundedFuelPairEnumeratorStructuredEndpointEquivIndexedConstruction_of_equivSharedProjector
    (boundedFuelPairEnumeratorStructuredCanonicalEndpointEquivSharedProjectorConstruction_of_coreComponents
      (boundedFuelPairEnumeratorStructuredCanonicalEndpointCoreComponentConstruction_core
        runner hrunner)
      structured3EndpointTape2ProjectorConstruction_core)

end StructuredConstructionTargets

end Computability
end FoC

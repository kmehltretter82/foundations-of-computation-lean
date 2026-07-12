import FoC.Computability.Compiler.Core.StructuredConstructionTargets.FuelSimulatorCore.Shape

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace StructuredConstructionTargets

open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

def fuelSimulatorStructuredOutputTape
    (attempt : MachineDescription)
    (i : FuelSimulatorStructuredIndex) : Tape Bool :=
  PairedRecognizerDovetailControllerStageAttemptFuelSimulatorOutputTape
    attempt i.w i.limit i.fuel

def FuelSimulatorStructuredEndpointEquivIndexedConstruction
    (attempt : MachineDescription) : Prop :=
  exists W : Structured3EndpointWrapper,
  exists initialized lowered : FuelSimulatorStructuredIndex -> Tape Bool,
    Structured3EndpointEquivIndexedFamilySpec
      W
      fuelSimulatorStructuredInputTape
      initialized
      lowered
      (fuelSimulatorStructuredOutputTape attempt)

/--
Equivalence-facing fuel-simulator lowered structured core data.

Logical tape 2 contains the exact simulator-layout output. Logical tapes 0 and
1 carry the concrete representatives left by the structured construction; the
endpoint projector does not observe them, so requiring the pristine input and
an exactly blank scratch tape would impose an unnecessary cleanup phase.
-/
structure FuelSimulatorStructuredEquivLoweredCoreComponents
    (attempt : MachineDescription) where
  tape0 : FuelSimulatorStructuredIndex -> Tape Bool
  tape1 : FuelSimulatorStructuredIndex -> Tape Bool
  lowered : FuelSimulatorStructuredIndex -> Tape Bool
  components :
    Structured3CanonicalEquivEndpointLoweredCoreComponents
      (fun i : FuelSimulatorStructuredIndex =>
        fuelSimulatorStructuredInitializedTape i)
      lowered
      (fun i => fuelSimulatorStructuredOutputTape attempt i)
      tape0
      tape1

/--
Existence form for the equivalence-facing fuel-simulator lowered structured
core.
-/
def FuelSimulatorStructuredEquivLoweredCoreConstruction
    (attempt : MachineDescription) : Prop :=
  Nonempty (FuelSimulatorStructuredEquivLoweredCoreComponents attempt)

/--
Finite-table leaf for the lowered fuel-simulator structured core.

The concrete three-tape lowerer preserves the represented logical tapes only
up to tape equivalence, and the sole endpoint consumer uses that same currency.
Requiring an exact guarded physical representative here would add a separate
normalization problem that is not observable at the endpoint.
-/
theorem fuelSimulatorStructuredEquivLoweredCoreConstruction_core
    (attempt : MachineDescription) :
    FuelSimulatorStructuredEquivLoweredCoreConstruction attempt := by
  -- Remaining structured-core obligation: construct the initial simulator
  -- layout on logical tape 2 and lower the run up to tape equivalence.
  sorry

end StructuredConstructionTargets

end Computability
end FoC

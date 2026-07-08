import FoC.Computability.Compiler.Core.CommonGround.CodeWordEmitters
import FoC.Computability.Compiler.Core.StructuredConstructionTargets.StageAttemptFramed
import FoC.Computability.Compiler.Core.StructuredConstructionTargets.EndpointMacro

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace StructuredConstructionTargets

open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

def fuelOutputStructuredInputTape
    {attempt : MachineDescription}
    (i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt) : Tape Bool :=
  Tape.input
    (encodeCodeWordAsInput
      (PairedRecognizerDovetailControllerStageAttemptFuelOutputInputCode
        i))

declare_structured_endpoint
  Prefix: FuelOutputStructured
  lowerPrefix: fuelOutputStructured
  Param: (attempt : MachineDescription)
  Index: PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex attempt
  InputTape: fuelOutputStructuredInputTape
  OutputTape: PairedRecognizerDovetailControllerStageAttemptFuelOutputTape

/--
Finite-table leaf for the fuel-output public-input materializer.
-/
theorem fuelOutputStructuredIndexedMaterializerConstruction_core
    (attempt : MachineDescription) :
    FuelOutputStructuredIndexedMaterializerConstruction
      attempt := by
  -- Remaining parser/materializer obligation: recognize halted simulator
  -- layouts and materialize the guarded three-logical-tape input.
  sorry

/--
Finite-table leaf for the lowered fuel-output structured core.
-/
theorem fuelOutputStructuredLoweredCoreConstruction_core
    (attempt : MachineDescription) :
    FuelOutputStructuredLoweredCoreConstruction attempt := by
  -- Remaining structured-core obligation: extract the normalized
  -- boolean-word result code onto logical tape 2.
  sorry

/--
Target-local parser/core obligation for the fuel-output target.  The public
endpoint theorem below only composes this with a shared tape-2
projector.
-/
theorem fuelOutputStructuredCanonicalEndpointCoreComponentConstruction_core
    (attempt : MachineDescription) :
    FuelOutputStructuredCanonicalEndpointCoreComponentConstruction
      attempt :=
  fuelOutputStructuredCanonicalEndpointCoreComponentConstruction_of_materializer_loweredCore
    (fuelOutputStructuredIndexedMaterializerConstruction_core attempt)
    (fuelOutputStructuredLoweredCoreConstruction_core attempt)

/--
Equivalence-facing fuel-output endpoint assembled from the parser/core
components and the shared equivalence tape-2 projector.
-/
theorem fuelOutputStructuredEndpointEquivIndexedConstruction_core
    (attempt : MachineDescription) :
    FuelOutputStructuredEndpointEquivIndexedConstruction attempt :=
  fuelOutputStructuredEndpointEquivIndexedConstruction_of_equivSharedProjector
    (fuelOutputStructuredCanonicalEndpointEquivSharedProjectorConstruction_of_coreComponents
      (fuelOutputStructuredCanonicalEndpointCoreComponentConstruction_core
        attempt)
      structured3EndpointTape2ProjectorConstruction_core)

/--
Remaining structured-core endpoint obligation for the simulator-output
extractor, indexed by halted simulator layouts and their exact output code.
-/
def FuelOutputStructuredCoreEndpointConstruction : Prop :=
  forall attempt : MachineDescription,
    FuelOutputStructuredEndpointExactIndexedConstruction attempt

/--
Canonical fuel-output endpoint obligations imply the existing flexible
exact-indexed core endpoint obligation.
-/
theorem fuelOutputStructuredCoreEndpointConstruction_of_canonical
    (hcanonical :
      forall attempt : MachineDescription,
        FuelOutputStructuredCanonicalEndpointConstruction attempt) :
    FuelOutputStructuredCoreEndpointConstruction := by
  intro attempt
  exact
    fuelOutputStructuredEndpointExactIndexedConstruction_of_canonical
      (hcanonical attempt)

theorem fuelOutputInputCode_eq_of_inputTape_eq
    {attempt : MachineDescription}
    {code : Word MachineCodeSymbol}
    {i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt}
    (h :
      Tape.input (encodeCodeWordAsInput code) =
        fuelOutputStructuredInputTape i) :
    code =
      PairedRecognizerDovetailControllerStageAttemptFuelOutputInputCode
        i := by
  apply encodeCodeWordAsInput_injective
  exact
    Tape.input_injective
      (by
        simpa [fuelOutputStructuredInputTape] using h)

theorem fuelOutputCodeSubroutineSpec_of_endpointExactIndexed
    {attempt : MachineDescription}
    {W : Structured3EndpointWrapper}
    {initialized lowered :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt -> Tape Bool}
    (hspec :
      Structured3EndpointExactIndexedFamilySpec
        W
        fuelOutputStructuredInputTape
        initialized
        lowered
        PairedRecognizerDovetailControllerStageAttemptFuelOutputTape) :
    PairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineSpec
      attempt W.machine := by
  constructor
  · exact W.machine_subroutineReady
  constructor
  · intro i
    simpa [fuelOutputStructuredInputTape] using
      haltsWithTape_of_haltsFromTape_input
        (Structured3EndpointExactIndexedFamilySpec.forward hspec i)
  · intro code T hhalt
    have hfrom :
        W.machine.HaltsFromTape
          (Tape.input (encodeCodeWordAsInput code)) T :=
      haltsFromTape_input_of_haltsWithTape hhalt
    rcases
        Structured3EndpointExactIndexedFamilySpec.closedIndex
          hspec
          (Tape.input (encodeCodeWordAsInput code)) T
          hfrom with
      ⟨i, hinput, hT⟩
    have hcode :
        code =
          PairedRecognizerDovetailControllerStageAttemptFuelOutputInputCode
            i :=
      fuelOutputInputCode_eq_of_inputTape_eq hinput
    exact ⟨i, hcode, hT⟩

def PairedRecognizerDovetailControllerStageAttemptFuelOutputStructuredCodeSubroutineConstruction :
    Prop :=
  forall attempt : MachineDescription,
    Structured3EndpointWrappedConstruction
      (PairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineSpec
        attempt)

theorem fuelOutputStructuredConstruction_of_endpointExactIndexed
    (h :
      forall attempt : MachineDescription,
        FuelOutputStructuredEndpointExactIndexedConstruction attempt) :
    PairedRecognizerDovetailControllerStageAttemptFuelOutputStructuredCodeSubroutineConstruction := by
  intro attempt
  rcases h attempt with ⟨W, initialized, lowered, hspec⟩
  exact
    ⟨W,
      fuelOutputCodeSubroutineSpec_of_endpointExactIndexed
        (attempt := attempt)
        (W := W)
        (initialized := initialized)
        (lowered := lowered)
        hspec⟩

theorem fuelOutputStructuredConstruction_of_coreEndpoint
    (h : FuelOutputStructuredCoreEndpointConstruction) :
    PairedRecognizerDovetailControllerStageAttemptFuelOutputStructuredCodeSubroutineConstruction :=
  fuelOutputStructuredConstruction_of_endpointExactIndexed h

theorem fuelOutputCodeSubroutineConstruction_of_endpointEquivIndexed
    {attempt : MachineDescription}
    {W : Structured3EndpointWrapper}
    {initialized lowered :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt -> Tape Bool}
    (hspec :
      Structured3EndpointEquivIndexedFamilySpec
        W
        fuelOutputStructuredInputTape
        initialized
        lowered
        PairedRecognizerDovetailControllerStageAttemptFuelOutputTape) :
    exists extractor : MachineDescription,
      TapeCodePrimitiveOutputCompiledSubroutineByDescription
        (PairedRecognizerDovetailControllerStageAttemptFuelOutputCodePrimitive
          attempt)
        extractor := by
  refine ⟨W.machine, ?_⟩
  exact
    CommonGround.CodeWordEmitters.outputCompiled_of_indexed_tape_equiv_spec
      W.machine_subroutineReady.left
      W.machine_subroutineReady.right
      PairedRecognizerDovetailControllerStageAttemptFuelOutputInputCode
      PairedRecognizerDovetailControllerStageAttemptFuelOutputOutputCode
      PairedRecognizerDovetailControllerStageAttemptFuelOutputTape
      (fun i =>
        CommonGround.CodeWordEmitters.exactOutputTape_normalizedOutput
          PairedRecognizerDovetailControllerStageAttemptFuelOutputOutputCode i)
      (fun i => by
        simpa [fuelOutputStructuredInputTape] using
          Structured3EndpointEquivIndexedFamilySpec.forward hspec i)
      (fun code T hhalt => by
        have hfrom :
            W.machine.HaltsFromTape
              (Tape.input (encodeCodeWordAsInput code)) T :=
          haltsFromTape_input_of_haltsWithTape hhalt
        rcases
            Structured3EndpointEquivIndexedFamilySpec.closedIndex
              hspec
              (Tape.input (encodeCodeWordAsInput code)) T
              hfrom with
          ⟨i, hinput, hT⟩
        exact
          ⟨i, fuelOutputInputCode_eq_of_inputTape_eq hinput, hT⟩)
      (by
        intro code out
        constructor
        · intro htransform
          rcases
              (pairedRecognizerDovetailControllerStageAttemptFuelOutputCodePrimitive_transform_eq_some_iff
                attempt code out).mp htransform with
            ⟨L, hcode, hstate, houtput⟩
          let i :
              PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
                attempt :=
            ⟨(L, out), ⟨hstate, houtput⟩⟩
          exact ⟨i, hcode, rfl⟩
        · intro hindexed
          rcases hindexed with ⟨i, hcode, hout⟩
          exact
            (pairedRecognizerDovetailControllerStageAttemptFuelOutputCodePrimitive_transform_eq_some_iff
              attempt code out).mpr
              ⟨i.1.1, hcode, i.2.left, by
                rw [hout]
                exact i.2.right⟩)

theorem pairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineConstruction_of_endpointEquivIndexed
    (h :
      forall attempt : MachineDescription,
        FuelOutputStructuredEndpointEquivIndexedConstruction attempt) :
    PairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineConstruction := by
  intro attempt
  rcases h attempt with ⟨W, initialized, lowered, hspec⟩
  exact
    fuelOutputCodeSubroutineConstruction_of_endpointEquivIndexed
      (attempt := attempt)
      (W := W)
      (initialized := initialized)
      (lowered := lowered)
      hspec

theorem pairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineConstruction_of_structured
    (h :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputStructuredCodeSubroutineConstruction) :
    PairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineConstruction := by
  exact
    pairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineConstruction_of_spec
      (by
        intro attempt
        rcases h attempt with ⟨W, hspec⟩
        exact ⟨W.machine, hspec⟩)


end StructuredConstructionTargets

end Computability
end FoC

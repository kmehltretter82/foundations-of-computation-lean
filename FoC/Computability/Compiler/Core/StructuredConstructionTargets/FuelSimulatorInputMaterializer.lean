import FoC.Computability.Compiler.Core.StructuredConstructionTargets.Base
import FoC.Computability.Compiler.Core.EncRewriters.CanonicalLayouts.DovetailStagePrefix
import FoC.Computability.Compiler.Core.DovetailInitLayout.StageInputValidator

set_option doc.verso true

/-!
# Fuel-simulator structured input materializer pilot

This module is the Phase 3 pilot route for the public FuelSimulator input
materializer.  The route is intentionally decomposed into a FuelSimulator input
recognizer and a structured three-logical-tape embedding emitter, so remaining
holes identify concrete finite-machine phases instead of assuming the endpoint
materializer wholesale.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace StructuredConstructionTargets

open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open FoC.Computability.EncRewriters.CanonicalLayouts.DovetailStagePrefix
open FoC.Computability.DovetailInitialLayoutInitializer

/-- Index for the fuel-simulator structured input family: word, stage limit,
and fuel budget. -/
structure FuelSimulatorStructuredIndex where
  w     : Word Bool
  limit : Nat
  fuel  : Nat

def fuelSimulatorStructuredInputCode
    (i : FuelSimulatorStructuredIndex) : Word MachineCodeSymbol :=
  PairedRecognizerDovetailControllerStageAttemptFuelInputCode
    i.w i.limit i.fuel

def fuelSimulatorStructuredInputTape
    (i : FuelSimulatorStructuredIndex) : Tape Bool :=
  Tape.input
    (encodeCodeWordAsInput
      (fuelSimulatorStructuredInputCode i))

/--
Canonical blank output buffer used when materializing public fuel-simulator
parser inputs into the three-logical-tape core.
-/
def fuelSimulatorStructuredOutputBuffer
    (_i : FuelSimulatorStructuredIndex) : Tape Bool :=
  Tape.blank

/--
Canonical endpoint input to the lowered fuel-simulator structured core.

Tape 0 contains the public generated fuel-input code, tape 1 is blank scratch,
and tape 2 starts as a blank output buffer.
-/
def fuelSimulatorStructuredInitializedTape
    (i : FuelSimulatorStructuredIndex) : Tape Bool :=
  structured3InputMaterializerTargetTape
    (fuelSimulatorStructuredInputTape i)
    (fuelSimulatorStructuredOutputBuffer i)

/--
Decoder for exactly the public FuelSimulator input-code family.

The accepted codes are stage-input prefixes with a complete unary fuel suffix:
{lit}`stageInputCodeAppend w limit (encodeNatAppend fuel [])`.
-/
def decodeFuelSimulatorStructuredInputCode
    (code : Word MachineCodeSymbol) :
    Option FuelSimulatorStructuredIndex :=
  match DovetailLayout.decodeStageInput code with
  | none => none
  | some ((w, limit), suffix) =>
      match decodeNat suffix with
      | some (fuel, []) => some { w, limit, fuel }
      | _ => none

theorem decodeFuelSimulatorStructuredInputCode_encode
    (i : FuelSimulatorStructuredIndex) :
    decodeFuelSimulatorStructuredInputCode
      (fuelSimulatorStructuredInputCode i) = some i := by
  cases i with | mk w limit fuel =>
  simp [decodeFuelSimulatorStructuredInputCode,
    fuelSimulatorStructuredInputCode,
    PairedRecognizerDovetailControllerStageAttemptFuelInputCode,
    DovetailLayout.decodeStageInput_stageInputCodeAppend,
    decodeNat_encodeNatAppend]

theorem decodeFuelSimulatorStructuredInputCode_eq_some_encode
    {code : Word MachineCodeSymbol}
    {i : FuelSimulatorStructuredIndex}
    (h :
      decodeFuelSimulatorStructuredInputCode code = some i) :
    code = fuelSimulatorStructuredInputCode i := by
  simp only [decodeFuelSimulatorStructuredInputCode] at h
  cases hstage : DovetailLayout.decodeStageInput code with
  | none => simp [hstage] at h
  | some parsed =>
    rcases parsed with ⟨⟨w, limit⟩, suffix⟩
    cases hfuel : decodeNat suffix with
    | none => simp [hstage, hfuel] at h
    | some parsedFuel =>
      rcases parsedFuel with ⟨fuel, rest⟩
      cases rest with
      | cons _ _ => simp [hstage, hfuel] at h
      | nil =>
        simp [hstage, hfuel] at h; cases h
        rw [DovetailLayout.decodeStageInput_eq_some_stageInputCodeAppend hstage,
            decodeNat_eq_some_encodeNatAppend hfuel]
        rfl

theorem fuelSimulatorStructuredInputCode_injective :
    Function.Injective fuelSimulatorStructuredInputCode := by
  intro i j h
  cases i with | mk w1 limit1 fuel1 =>
  cases j with | mk w2 limit2 fuel2 =>
  simp [fuelSimulatorStructuredInputCode] at h ⊢
  rcases
      pairedRecognizerDovetailControllerStageAttemptFuelInputCode_injective
        h with
    ⟨hw, hlimit, hfuel⟩
  simp [hw, hlimit, hfuel]

theorem fuelSimulatorStructuredInputTape_injective :
    Function.Injective fuelSimulatorStructuredInputTape := by
  intro i j h
  apply fuelSimulatorStructuredInputCode_injective
  apply encodeCodeWordAsInput_injective
  exact Tape.input_injective
    (by simpa [fuelSimulatorStructuredInputTape] using h)

theorem fuelSimulatorStructuredInputCode_cons
    (i : FuelSimulatorStructuredIndex) :
    ∃ symbol : MachineCodeSymbol,
    ∃ tail : Word MachineCodeSymbol,
      fuelSimulatorStructuredInputCode i = symbol :: tail := by
  cases i with | mk w limit fuel =>
  unfold fuelSimulatorStructuredInputCode
  unfold PairedRecognizerDovetailControllerStageAttemptFuelInputCode
  unfold DovetailLayout.stageInputCodeAppend
  unfold encodeBoolWordAppend
  unfold encodeCellListAppend
  exact
    EncRewriters.encodeNatAppend_cons
      (List.length (List.map some w))
      (encodeCellsAppend (List.map some w)
        (encodeNatAppend limit (encodeNatAppend fuel [])))

theorem fuelSimulatorStructuredInputCode_eq_of_inputTape_eq
    {code : Word MachineCodeSymbol}
    {i : FuelSimulatorStructuredIndex}
    (h :
      Tape.input (encodeCodeWordAsInput code) =
        fuelSimulatorStructuredInputTape i) :
    code = fuelSimulatorStructuredInputCode i := by
  apply encodeCodeWordAsInput_injective
  exact
    Tape.input_injective
      (by
        simpa [fuelSimulatorStructuredInputTape] using h)


/--
Exact materializer behavior needed by the canonical fuel-simulator endpoint.
-/
def FuelSimulatorStructuredExactMaterializerSpec
    (materializer : MachineDescription) : Prop :=
  Structured3EndpointExactMaterializerSpec
    fuelSimulatorStructuredInputTape
    fuelSimulatorStructuredInitializedTape
    materializer

/--
Target-specific fuel-simulator materializer obligation before deterministic
per-input exact closedness is installed by the shared endpoint infrastructure.
-/
def FuelSimulatorStructuredIndexedMaterializerSpec
    (materializer : MachineDescription) : Prop :=
  Structured3EndpointIndexedMaterializerSpec
    fuelSimulatorStructuredInputTape
    fuelSimulatorStructuredInitializedTape
    materializer

/--
Fuel-simulator input parser/materializer construction, separated from the
lowered structured simulator core.
-/
def FuelSimulatorStructuredIndexedMaterializerConstruction : Prop :=
  Structured3EndpointIndexedMaterializerConstruction
    fuelSimulatorStructuredInputTape
    fuelSimulatorStructuredInitializedTape

/--
Equivalence-facing fuel-simulator input parser/materializer construction.

This is the Phase 3 prototype contract for the public-input materializer: it
keeps indexed closedness, but allows the initialized guarded tape to be reached
up to tape equivalence.
-/
def FuelSimulatorStructuredEquivIndexedMaterializerConstruction :
    Prop :=
  Structured3EndpointEquivIndexedMaterializerConstruction
    fuelSimulatorStructuredInputTape
    fuelSimulatorStructuredInitializedTape

/--
Fuel-simulator materializer through the reusable CommonGround structured-input
contract, plus the indexed closedness required by endpoint wrappers.
-/
def FuelSimulatorStructuredEquivInputMaterializerConstruction :
    Prop :=
  Structured3EndpointEquivInputMaterializerConstruction
    fuelSimulatorStructuredInputTape
    fuelSimulatorStructuredOutputBuffer

/--
The existing exact indexed materializer obligation feeds the equivalence-facing
materializer contract.
-/
theorem fuelSimulatorStructuredEquivIndexedMaterializerConstruction_of_indexed
    (hmaterializer :
      FuelSimulatorStructuredIndexedMaterializerConstruction) :
    FuelSimulatorStructuredEquivIndexedMaterializerConstruction := by
  simpa [FuelSimulatorStructuredIndexedMaterializerConstruction,
    FuelSimulatorStructuredEquivIndexedMaterializerConstruction] using
    structured3EndpointEquivIndexedMaterializerConstruction_of_exact
      hmaterializer

theorem fuelSimulatorStructuredEquivIndexedMaterializerConstruction_of_inputMaterializer
    (hmaterializer :
      FuelSimulatorStructuredEquivInputMaterializerConstruction) :
    FuelSimulatorStructuredEquivIndexedMaterializerConstruction := by
  simpa [
    FuelSimulatorStructuredEquivInputMaterializerConstruction,
    FuelSimulatorStructuredEquivIndexedMaterializerConstruction,
    Structured3EndpointEquivInputMaterializerInitialized,
    fuelSimulatorStructuredInitializedTape] using
    structured3EndpointEquivIndexedMaterializerConstruction_of_inputMaterializer
      hmaterializer

theorem fuelSimulatorStructuredEquivInputMaterializerConstruction_of_indexed
    (hmaterializer :
      FuelSimulatorStructuredIndexedMaterializerConstruction) :
    FuelSimulatorStructuredEquivInputMaterializerConstruction := by
  simpa [FuelSimulatorStructuredIndexedMaterializerConstruction,
    FuelSimulatorStructuredEquivInputMaterializerConstruction,
    Structured3EndpointEquivInputMaterializerInitialized,
    fuelSimulatorStructuredInitializedTape] using
    structured3EndpointEquivInputMaterializerConstruction_of_indexed
      hmaterializer (fun _i => rfl)

/-- Semantic contract for the FuelSimulator-family recognizer phase. -/
def FuelSimulatorInputRecognizerSpec
    (recognizer : MachineDescription) : Prop :=
  ClosedInputFamilyRecognizerSpec
    decodeFuelSimulatorStructuredInputCode
    fuelSimulatorStructuredInputCode
    recognizer

/-- Existence wrapper for the FuelSimulator-family recognizer phase. -/
def FuelSimulatorInputRecognizerConstruction : Prop :=
  ClosedInputFamilyRecognizerConstruction
    decodeFuelSimulatorStructuredInputCode
    fuelSimulatorStructuredInputCode

/--
Exact finite-machine behavior for the FuelSimulator-family recognizer.

The recognizer must accept exactly the canonical public input tapes indexed by
{name}`FuelSimulatorStructuredIndex`, hand off by moving one cell right, and
reject all other starting tapes by never halting.
-/
structure FuelSimulatorInputRecognizerExactRunSpec
    (recognizer : MachineDescription) : Prop where
  ready : recognizer.SubroutineReady
  forward :
    forall i : FuelSimulatorStructuredIndex,
      recognizer.HaltsFromTape
        (fuelSimulatorStructuredInputTape i)
        (EncRewriters.CanonicalLayouts.HandoffTape
          fuelSimulatorStructuredInputCode i)
  closedIndex :
    forall Tin T : Tape Bool,
      recognizer.HaltsFromTape Tin T ->
        ∃ i : FuelSimulatorStructuredIndex,
          Tin = fuelSimulatorStructuredInputTape i ∧
            T = EncRewriters.CanonicalLayouts.HandoffTape
              fuelSimulatorStructuredInputCode i

theorem fuelSimulatorInputRecognizerSpec_of_exactRunSpec
    {recognizer : MachineDescription}
    (hspec : FuelSimulatorInputRecognizerExactRunSpec recognizer) :
    FuelSimulatorInputRecognizerSpec recognizer := by
  constructor
  · refine ⟨hspec.ready, ?_, ?_⟩
    · intro i
      apply haltsWithTape_of_haltsFromTape_input
      simpa [fuelSimulatorStructuredInputTape,
        EncRewriters.CanonicalLayouts.Bits] using hspec.forward i
    · intro code T hhalt
      have hfrom :
          recognizer.HaltsFromTape
            (Tape.input (encodeCodeWordAsInput code)) T :=
        haltsFromTape_input_of_haltsWithTape hhalt
      rcases hspec.closedIndex _ _ hfrom with ⟨i, hTin, hT⟩
      refine ⟨i, ?_, hT⟩
      have hcode : code = fuelSimulatorStructuredInputCode i :=
        fuelSimulatorStructuredInputCode_eq_of_inputTape_eq hTin
      rw [hcode]
      exact decodeFuelSimulatorStructuredInputCode_encode i
  · intro Tin T hhalt
    rcases hspec.closedIndex Tin T hhalt with ⟨i, hTin, hT⟩
    refine ⟨i, ?_, hT⟩
    simpa [fuelSimulatorStructuredInputTape,
      EncRewriters.CanonicalLayouts.InputTape,
      EncRewriters.CanonicalLayouts.Bits] using hTin

/--
Concrete finite parser for generated FuelSimulator public-input codes.

This is the first real machine leaf left by the pilot: parse
{lit}`stageInputCodeAppend w limit suffix`, require
{lit}`suffix = encodeNatAppend fuel []`,
and preserve the source tape as the handoff tape for the embedding emitter.
-/
def fuelSimulatorInputRecognizerCoreDescription : MachineDescription :=
  seqSubroutine MarkedPrefixScannerDescription NatSuffixScannerDescription Direction.right

def fuelSimulatorInputRecognizerDescription : MachineDescription :=
  StageInputRecognizerDescription
    (StageInputMarkedCoreDescription fuelSimulatorInputRecognizerCoreDescription)

theorem fuelSimulatorInputRecognizerDescription_exactRunSpec :
    FuelSimulatorInputRecognizerExactRunSpec
      fuelSimulatorInputRecognizerDescription := by
  -- Remaining finite-machine obligation: replace the placeholder description
  -- with the concrete FuelSimulator-family parser and prove the closed
  -- indexed run spec above, including arbitrary-input closedness for the
  -- recognizer phase.
  sorry

theorem fuelSimulatorInputRecognizerDescription_spec :
    FuelSimulatorInputRecognizerSpec
      fuelSimulatorInputRecognizerDescription :=
  fuelSimulatorInputRecognizerSpec_of_exactRunSpec
    fuelSimulatorInputRecognizerDescription_exactRunSpec

theorem fuelSimulatorInputRecognizerConstruction_core :
    FuelSimulatorInputRecognizerConstruction :=
  ⟨fuelSimulatorInputRecognizerDescription,
    fuelSimulatorInputRecognizerDescription_spec⟩

theorem fuelSimulatorStructuredEquivInputMaterializerConstruction_of_parts
    (hrecognizer : FuelSimulatorInputRecognizerConstruction)
    (hemitter : Structured3InputEmbeddingEmitterConstruction) :
    FuelSimulatorStructuredEquivInputMaterializerConstruction := by
  simpa [
    FuelSimulatorStructuredEquivInputMaterializerConstruction,
    fuelSimulatorStructuredInputTape,
    fuelSimulatorStructuredOutputBuffer,
    EncRewriters.CanonicalLayouts.InputTape,
    EncRewriters.CanonicalLayouts.Bits] using
    closedRecognizerStructuredEquivInputMaterializerConstruction_of_parts
      (α := FuelSimulatorStructuredIndex)
      (decode := decodeFuelSimulatorStructuredInputCode)
      (encode := fuelSimulatorStructuredInputCode)
      fuelSimulatorStructuredInputCode_cons
      hrecognizer
      hemitter

/--
Finite-table leaf for the fuel-simulator public-input materializer on the
equivalence-facing endpoint route.
-/
theorem fuelSimulatorStructuredEquivInputMaterializerConstruction_core :
    FuelSimulatorStructuredEquivInputMaterializerConstruction :=
  fuelSimulatorStructuredEquivInputMaterializerConstruction_of_parts
    fuelSimulatorInputRecognizerConstruction_core
    structured3InputEmbeddingEmitterConstruction_core

end StructuredConstructionTargets

end Computability
end FoC

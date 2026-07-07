import FoC.Computability.Compiler.FST.BoolRawInput.Output

set_option doc.verso true

/-!
# Bool-word raw-bits input materializer route contracts

This module packages the feasible canonical Boolean-word raw-bits input
materializer boundary.  The older arbitrary-padding initializer contracts are
known impossible; this route keeps the source, output buffer, and indexed view
all functional in the same input index.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers

namespace BoolWordRawBitsDecoderInputMaterializerRouteContracts

open BoolWordRawBitsDecoderInputMaterializerEndpointContracts

/-!
## Canonical indexed family

The canonical route is also an indexed route whose index is the pair
{lit}`(bits, suffixTail)`, whose source right padding is empty, and whose output
padding is the deterministic suffix-preserving padding from the same index.
-/

def canonicalIndexedBits
    (input : Word Bool × Word Bool) : Word Bool :=
  input.1

def canonicalIndexedSuffixTail
    (input : Word Bool × Word Bool) : Word Bool :=
  input.2

def canonicalIndexedRightPadding
    (_input : Word Bool × Word Bool) : List (Option Bool) :=
  []

def canonicalIndexedOutputPadding
    (input : Word Bool × Word Bool) : List (Option Bool) :=
  boolWordRawBitsDecoderPreservedPadding input.2 []

def CanonicalIndexedInputMaterializerSpec
    (materializer : MachineDescription) : Prop :=
  StructuredBoolWordRawBitsDecoderIndexedInputMaterializerSpec
    canonicalIndexedBits
    canonicalIndexedSuffixTail
    canonicalIndexedRightPadding
    canonicalIndexedOutputPadding
    materializer

def CanonicalIndexedInputMaterializerConstruction : Prop :=
  exists materializer : MachineDescription,
    CanonicalIndexedInputMaterializerSpec materializer

def CanonicalIndexedInputInitializerSpec
    (materializer : MachineDescription) : Prop :=
  StructuredBoolWordRawBitsDecoderIndexedInputInitializerSpec
    canonicalIndexedBits
    canonicalIndexedSuffixTail
    canonicalIndexedRightPadding
    canonicalIndexedOutputPadding
    materializer

def CanonicalIndexedInputInitializerConstruction : Prop :=
  exists materializer : MachineDescription,
    CanonicalIndexedInputInitializerSpec materializer

def CanonicalIndexedEndpointTargetFamilySpec
    (materializer : MachineDescription) : Prop :=
  IndexedEndpointTargetFamilySpec
    canonicalIndexedBits
    canonicalIndexedSuffixTail
    canonicalIndexedRightPadding
    canonicalIndexedOutputPadding
    materializer

def CanonicalIndexedEndpointTargetFamilyConstruction : Prop :=
  exists materializer : MachineDescription,
    CanonicalIndexedEndpointTargetFamilySpec materializer

def CanonicalIndexedNamedTargetFamilySpec
    (materializer : MachineDescription) : Prop :=
  IndexedNamedTargetFamilySpec
    canonicalIndexedBits
    canonicalIndexedSuffixTail
    canonicalIndexedRightPadding
    canonicalIndexedOutputPadding
    materializer

def CanonicalIndexedNamedTargetFamilyConstruction : Prop :=
  exists materializer : MachineDescription,
    CanonicalIndexedNamedTargetFamilySpec materializer

def CanonicalIndexedInputMaterializerOutputSpec
    (materializer : MachineDescription) : Prop :=
  StructuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputSpec
    canonicalIndexedBits
    canonicalIndexedSuffixTail
    canonicalIndexedRightPadding
    canonicalIndexedOutputPadding
    materializer

def CanonicalIndexedInputMaterializerOutputConstruction : Prop :=
  exists materializer : MachineDescription,
    CanonicalIndexedInputMaterializerOutputSpec materializer

def CanonicalIndexedInputInitializerOutputSpec
    (materializer : MachineDescription) : Prop :=
  StructuredBoolWordRawBitsDecoderIndexedInputInitializerOutputSpec
    canonicalIndexedBits
    canonicalIndexedSuffixTail
    canonicalIndexedRightPadding
    canonicalIndexedOutputPadding
    materializer

def CanonicalIndexedInputInitializerOutputConstruction : Prop :=
  exists materializer : MachineDescription,
    CanonicalIndexedInputInitializerOutputSpec materializer

theorem canonicalIndexedSource_eq_canonicalSource
    (input : Word Bool × Word Bool) :
    structuredBoolWordRawBitsDecoderIndexedInputMaterializerSource
        canonicalIndexedBits
        canonicalIndexedSuffixTail
        canonicalIndexedRightPadding input =
      structuredBoolWordRawBitsDecoderCanonicalInputMaterializerSource
        input := by
  cases input with
  | mk bits suffixTail =>
      rfl

theorem canonicalIndexedOutput_eq_canonicalOutput
    (input : Word Bool × Word Bool) :
    structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputTape
        canonicalIndexedBits
        canonicalIndexedOutputPadding input =
      structuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputTape
        input := by
  cases input with
  | mk bits suffixTail =>
      rfl

theorem canonicalIndexedTarget_eq_canonicalTarget
    (input : Word Bool × Word Bool) :
    structuredBoolWordRawBitsDecoderIndexedInputMaterializerTargetTape
        canonicalIndexedBits
        canonicalIndexedSuffixTail
        canonicalIndexedRightPadding
        canonicalIndexedOutputPadding input =
      structured3InputMaterializerTargetTape
        (structuredBoolWordRawBitsDecoderCanonicalInputMaterializerSource
          input)
        (structuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputTape
          input) := by
  cases input with
  | mk bits suffixTail =>
      rfl

theorem canonicalIndexedNamedTarget_eq_canonicalInitializerTarget
    (input : Word Bool × Word Bool) :
    indexedNamedTarget
        canonicalIndexedBits
        canonicalIndexedSuffixTail
        canonicalIndexedRightPadding
        canonicalIndexedOutputPadding input =
      canonicalInitializerTarget input := by
  cases input with
  | mk bits suffixTail =>
      rfl

/-!
## Exact canonical/indexed adapters
-/

theorem canonicalIndexedMaterializerSpec_of_canonicalMaterializerSpec
    {materializer : MachineDescription}
    (hmaterializer :
      StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerSpec
        materializer) :
    CanonicalIndexedInputMaterializerSpec materializer := by
  rcases hmaterializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro input
  simpa [
      CanonicalIndexedInputMaterializerSpec,
      StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerSpec,
      canonicalIndexedBits,
      canonicalIndexedSuffixTail,
      canonicalIndexedRightPadding,
      canonicalIndexedOutputPadding,
      structuredBoolWordRawBitsDecoderIndexedInputMaterializerSource,
      structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputTape] using
    hrun input

theorem canonicalMaterializerSpec_of_canonicalIndexedMaterializerSpec
    {materializer : MachineDescription}
    (hmaterializer :
      CanonicalIndexedInputMaterializerSpec materializer) :
    StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerSpec
      materializer := by
  rcases hmaterializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro input
  simpa [
      CanonicalIndexedInputMaterializerSpec,
      StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerSpec,
      canonicalIndexedBits,
      canonicalIndexedSuffixTail,
      canonicalIndexedRightPadding,
      canonicalIndexedOutputPadding,
      structuredBoolWordRawBitsDecoderIndexedInputMaterializerSource,
      structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputTape] using
    hrun input

theorem canonicalMaterializerSpec_iff_indexedMaterializerSpec
    (materializer : MachineDescription) :
    StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerSpec
        materializer ↔
      CanonicalIndexedInputMaterializerSpec materializer := by
  constructor
  · exact canonicalIndexedMaterializerSpec_of_canonicalMaterializerSpec
  · exact canonicalMaterializerSpec_of_canonicalIndexedMaterializerSpec

theorem canonicalIndexedMaterializerConstruction_of_canonical
    (hmaterializer :
      StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerConstruction) :
    CanonicalIndexedInputMaterializerConstruction := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      canonicalIndexedMaterializerSpec_of_canonicalMaterializerSpec
        hspec⟩

theorem canonicalMaterializerConstruction_of_indexed
    (hmaterializer :
      CanonicalIndexedInputMaterializerConstruction) :
    StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerConstruction := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      canonicalMaterializerSpec_of_canonicalIndexedMaterializerSpec
        hspec⟩

theorem canonicalMaterializerConstruction_iff_indexed :
    StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerConstruction ↔
      CanonicalIndexedInputMaterializerConstruction := by
  constructor
  · exact canonicalIndexedMaterializerConstruction_of_canonical
  · exact canonicalMaterializerConstruction_of_indexed

theorem canonicalIndexedInitializerSpec_of_materializerSpec
    {materializer : MachineDescription}
    (hmaterializer :
      CanonicalIndexedInputMaterializerSpec materializer) :
    CanonicalIndexedInputInitializerSpec materializer :=
  structuredBoolWordRawBitsDecoderIndexedInputInitializerSpec_of_materializerSpec
    hmaterializer

theorem canonicalIndexedMaterializerSpec_of_initializerSpec
    {materializer : MachineDescription}
    (hinitializer :
      CanonicalIndexedInputInitializerSpec materializer) :
    CanonicalIndexedInputMaterializerSpec materializer :=
  structuredBoolWordRawBitsDecoderIndexedInputMaterializerSpec_of_initializerSpec
    hinitializer

theorem canonicalIndexedInitializerSpec_iff_materializerSpec
    (materializer : MachineDescription) :
    CanonicalIndexedInputInitializerSpec materializer ↔
      CanonicalIndexedInputMaterializerSpec materializer := by
  constructor
  · exact canonicalIndexedMaterializerSpec_of_initializerSpec
  · exact canonicalIndexedInitializerSpec_of_materializerSpec

theorem canonicalIndexedEndpointTargetFamilySpec_of_materializerSpec
    {materializer : MachineDescription}
    (hmaterializer :
      CanonicalIndexedInputMaterializerSpec materializer) :
    CanonicalIndexedEndpointTargetFamilySpec materializer :=
  indexedEndpointTargetFamilySpec_of_materializerSpec hmaterializer

theorem canonicalIndexedMaterializerSpec_of_endpointTargetFamilySpec
    {materializer : MachineDescription}
    (hmaterializer :
      CanonicalIndexedEndpointTargetFamilySpec materializer) :
    CanonicalIndexedInputMaterializerSpec materializer :=
  indexedMaterializerSpec_of_endpointTargetFamilySpec hmaterializer

theorem canonicalIndexedNamedTargetFamilySpec_of_endpointTargetFamilySpec
    {materializer : MachineDescription}
    (hmaterializer :
      CanonicalIndexedEndpointTargetFamilySpec materializer) :
    CanonicalIndexedNamedTargetFamilySpec materializer :=
  indexedNamedTargetFamilySpec_of_endpointTargetFamilySpec hmaterializer

theorem canonicalIndexedEndpointTargetFamilySpec_of_namedTargetFamilySpec
    {materializer : MachineDescription}
    (hmaterializer :
      CanonicalIndexedNamedTargetFamilySpec materializer) :
    CanonicalIndexedEndpointTargetFamilySpec materializer :=
  indexedEndpointTargetFamilySpec_of_namedTargetFamilySpec hmaterializer

theorem canonicalIndexedInitializerSpec_of_namedTargetFamilySpec
    {materializer : MachineDescription}
    (hmaterializer :
      CanonicalIndexedNamedTargetFamilySpec materializer) :
    CanonicalIndexedInputInitializerSpec materializer :=
  indexedInitializerSpec_of_namedTargetFamilySpec hmaterializer

theorem canonicalIndexedNamedTargetFamilySpec_of_initializerSpec
    {materializer : MachineDescription}
    (hinitializer :
      CanonicalIndexedInputInitializerSpec materializer) :
    CanonicalIndexedNamedTargetFamilySpec materializer :=
  indexedNamedTargetFamilySpec_of_initializerSpec hinitializer

/-!
## Exact route contract
-/

structure ExactCanonicalRouteSpec
    (materializer : MachineDescription) : Prop where
  canonicalMaterializer :
    StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerSpec
      materializer
  canonicalInitializer :
    StructuredBoolWordRawBitsDecoderCanonicalInputInitializerSpec
      materializer
  canonicalMaterializerTarget :
    CanonicalMaterializerTargetFamilySpec materializer
  canonicalEndpointTarget :
    CanonicalEndpointTargetFamilySpec materializer
  canonicalInitializerTarget :
    CanonicalInitializerTargetFamilySpec materializer
  indexedMaterializer :
    CanonicalIndexedInputMaterializerSpec materializer
  indexedInitializer :
    CanonicalIndexedInputInitializerSpec materializer
  indexedEndpointTarget :
    CanonicalIndexedEndpointTargetFamilySpec materializer
  indexedNamedTarget :
    CanonicalIndexedNamedTargetFamilySpec materializer

def ExactCanonicalRouteConstruction : Prop :=
  exists materializer : MachineDescription,
    ExactCanonicalRouteSpec materializer

theorem exactCanonicalRouteSpec_of_materializerSpec
    {materializer : MachineDescription}
    (hmaterializer :
      StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerSpec
        materializer) :
    ExactCanonicalRouteSpec materializer := by
  have hcanonicalInitializer :
      StructuredBoolWordRawBitsDecoderCanonicalInputInitializerSpec
        materializer :=
    structuredBoolWordRawBitsDecoderCanonicalInputInitializerSpec_of_structured3InputMaterializerSpec
      hmaterializer
  have hcanonicalTarget :
      CanonicalMaterializerTargetFamilySpec materializer :=
    canonicalMaterializerTargetFamilySpec_of_exact hmaterializer
  have hcanonicalEndpoint :
      CanonicalEndpointTargetFamilySpec materializer :=
    canonicalEndpointTargetFamilySpec_of_materializerTargetFamilySpec
      hcanonicalTarget
  have hcanonicalInitializerTarget :
      CanonicalInitializerTargetFamilySpec materializer :=
    canonicalInitializerTargetFamilySpec_of_endpointTargetFamilySpec
      hcanonicalEndpoint
  have hindexed :
      CanonicalIndexedInputMaterializerSpec materializer :=
    canonicalIndexedMaterializerSpec_of_canonicalMaterializerSpec
      hmaterializer
  have hindexedInitializer :
      CanonicalIndexedInputInitializerSpec materializer :=
    canonicalIndexedInitializerSpec_of_materializerSpec hindexed
  have hindexedEndpoint :
      CanonicalIndexedEndpointTargetFamilySpec materializer :=
    canonicalIndexedEndpointTargetFamilySpec_of_materializerSpec
      hindexed
  have hindexedNamed :
      CanonicalIndexedNamedTargetFamilySpec materializer :=
    canonicalIndexedNamedTargetFamilySpec_of_endpointTargetFamilySpec
      hindexedEndpoint
  exact
    { canonicalMaterializer := hmaterializer
      canonicalInitializer := hcanonicalInitializer
      canonicalMaterializerTarget := hcanonicalTarget
      canonicalEndpointTarget := hcanonicalEndpoint
      canonicalInitializerTarget := hcanonicalInitializerTarget
      indexedMaterializer := hindexed
      indexedInitializer := hindexedInitializer
      indexedEndpointTarget := hindexedEndpoint
      indexedNamedTarget := hindexedNamed }

theorem exactCanonicalRouteSpec_of_initializerSpec
    {materializer : MachineDescription}
    (hinitializer :
      StructuredBoolWordRawBitsDecoderCanonicalInputInitializerSpec
        materializer) :
    ExactCanonicalRouteSpec materializer :=
  exactCanonicalRouteSpec_of_materializerSpec
    (structuredBoolWordRawBitsDecoderCanonicalInputMaterializerSpec_of_initializerSpec
      hinitializer)

theorem exactCanonicalRouteSpec_of_materializerTargetFamilySpec
    {materializer : MachineDescription}
    (hmaterializer :
      CanonicalMaterializerTargetFamilySpec materializer) :
    ExactCanonicalRouteSpec materializer :=
  exactCanonicalRouteSpec_of_materializerSpec
    (canonicalMaterializerSpec_of_targetFamilySpec hmaterializer)

theorem exactCanonicalRouteSpec_of_endpointTargetFamilySpec
    {materializer : MachineDescription}
    (hmaterializer :
      CanonicalEndpointTargetFamilySpec materializer) :
    ExactCanonicalRouteSpec materializer :=
  exactCanonicalRouteSpec_of_materializerTargetFamilySpec
    (canonicalMaterializerTargetFamilySpec_of_endpointTargetFamilySpec
      hmaterializer)

theorem exactCanonicalRouteSpec_of_initializerTargetFamilySpec
    {materializer : MachineDescription}
    (hmaterializer :
      CanonicalInitializerTargetFamilySpec materializer) :
    ExactCanonicalRouteSpec materializer :=
  exactCanonicalRouteSpec_of_initializerSpec
    (canonicalInitializerSpec_of_initializerTargetFamilySpec
      hmaterializer)

theorem exactCanonicalRouteSpec_of_indexedMaterializerSpec
    {materializer : MachineDescription}
    (hmaterializer :
      CanonicalIndexedInputMaterializerSpec materializer) :
    ExactCanonicalRouteSpec materializer :=
  exactCanonicalRouteSpec_of_materializerSpec
    (canonicalMaterializerSpec_of_canonicalIndexedMaterializerSpec
      hmaterializer)

theorem exactCanonicalRouteSpec_of_indexedInitializerSpec
    {materializer : MachineDescription}
    (hinitializer :
      CanonicalIndexedInputInitializerSpec materializer) :
    ExactCanonicalRouteSpec materializer :=
  exactCanonicalRouteSpec_of_indexedMaterializerSpec
    (canonicalIndexedMaterializerSpec_of_initializerSpec
      hinitializer)

theorem exactCanonicalRouteSpec_of_indexedEndpointTargetFamilySpec
    {materializer : MachineDescription}
    (hmaterializer :
      CanonicalIndexedEndpointTargetFamilySpec materializer) :
    ExactCanonicalRouteSpec materializer :=
  exactCanonicalRouteSpec_of_indexedMaterializerSpec
    (canonicalIndexedMaterializerSpec_of_endpointTargetFamilySpec
      hmaterializer)

theorem exactCanonicalRouteSpec_of_indexedNamedTargetFamilySpec
    {materializer : MachineDescription}
    (hmaterializer :
      CanonicalIndexedNamedTargetFamilySpec materializer) :
    ExactCanonicalRouteSpec materializer :=
  exactCanonicalRouteSpec_of_indexedInitializerSpec
    (canonicalIndexedInitializerSpec_of_namedTargetFamilySpec
      hmaterializer)

theorem exactCanonicalRouteConstruction_of_materializer
    (hmaterializer :
      StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerConstruction) :
    ExactCanonicalRouteConstruction := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      exactCanonicalRouteSpec_of_materializerSpec hspec⟩

theorem materializerConstruction_of_exactCanonicalRouteConstruction
    (hroute : ExactCanonicalRouteConstruction) :
    StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerConstruction := by
  rcases hroute with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.canonicalMaterializer⟩

theorem exactCanonicalRouteConstruction_iff_materializerConstruction :
    ExactCanonicalRouteConstruction ↔
      StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerConstruction := by
  constructor
  · exact materializerConstruction_of_exactCanonicalRouteConstruction
  · exact exactCanonicalRouteConstruction_of_materializer

theorem exactCanonicalRouteConstruction_of_initializer
    (hinitializer :
      StructuredBoolWordRawBitsDecoderCanonicalInputInitializerConstruction) :
    ExactCanonicalRouteConstruction :=
  exactCanonicalRouteConstruction_of_materializer
    (structuredBoolWordRawBitsDecoderCanonicalInputMaterializerConstruction_of_initializer
      hinitializer)

theorem initializerConstruction_of_exactCanonicalRouteConstruction
    (hroute : ExactCanonicalRouteConstruction) :
    StructuredBoolWordRawBitsDecoderCanonicalInputInitializerConstruction := by
  rcases hroute with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.canonicalInitializer⟩

theorem exactCanonicalRouteConstruction_iff_initializerConstruction :
    ExactCanonicalRouteConstruction ↔
      StructuredBoolWordRawBitsDecoderCanonicalInputInitializerConstruction := by
  constructor
  · exact initializerConstruction_of_exactCanonicalRouteConstruction
  · exact exactCanonicalRouteConstruction_of_initializer

theorem exactCanonicalRouteConstruction_of_endpointTargetFamilyConstruction
    (hmaterializer :
      CanonicalEndpointTargetFamilyConstruction) :
    ExactCanonicalRouteConstruction := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      exactCanonicalRouteSpec_of_endpointTargetFamilySpec hspec⟩

theorem endpointTargetFamilyConstruction_of_exactCanonicalRouteConstruction
    (hroute : ExactCanonicalRouteConstruction) :
    CanonicalEndpointTargetFamilyConstruction := by
  rcases hroute with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.canonicalEndpointTarget⟩

theorem exactCanonicalRouteConstruction_iff_endpointTargetFamilyConstruction :
    ExactCanonicalRouteConstruction ↔
      CanonicalEndpointTargetFamilyConstruction := by
  constructor
  · exact endpointTargetFamilyConstruction_of_exactCanonicalRouteConstruction
  · exact exactCanonicalRouteConstruction_of_endpointTargetFamilyConstruction

theorem exactCanonicalRouteConstruction_of_indexed
    (hmaterializer :
      CanonicalIndexedInputMaterializerConstruction) :
    ExactCanonicalRouteConstruction := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      exactCanonicalRouteSpec_of_indexedMaterializerSpec hspec⟩

theorem indexedConstruction_of_exactCanonicalRouteConstruction
    (hroute : ExactCanonicalRouteConstruction) :
    CanonicalIndexedInputMaterializerConstruction := by
  rcases hroute with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.indexedMaterializer⟩

theorem exactCanonicalRouteConstruction_iff_indexed :
    ExactCanonicalRouteConstruction ↔
      CanonicalIndexedInputMaterializerConstruction := by
  constructor
  · exact indexedConstruction_of_exactCanonicalRouteConstruction
  · exact exactCanonicalRouteConstruction_of_indexed

/-!
## Output route contract
-/

theorem canonicalIndexedMaterializerOutputSpec_of_canonicalOutputSpec
    {materializer : MachineDescription}
    (hmaterializer :
      StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputSpec
        materializer) :
    CanonicalIndexedInputMaterializerOutputSpec materializer := by
  rcases hmaterializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro input
  simpa [
      CanonicalIndexedInputMaterializerOutputSpec,
      StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputSpec,
      canonicalIndexedBits,
      canonicalIndexedSuffixTail,
      canonicalIndexedRightPadding,
      canonicalIndexedOutputPadding,
      structuredBoolWordRawBitsDecoderIndexedInputMaterializerSource,
      structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputTape] using
    hrun input

theorem canonicalOutputSpec_of_canonicalIndexedMaterializerOutputSpec
    {materializer : MachineDescription}
    (hmaterializer :
      CanonicalIndexedInputMaterializerOutputSpec materializer) :
    StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputSpec
      materializer := by
  rcases hmaterializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro input
  simpa [
      CanonicalIndexedInputMaterializerOutputSpec,
      StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputSpec,
      canonicalIndexedBits,
      canonicalIndexedSuffixTail,
      canonicalIndexedRightPadding,
      canonicalIndexedOutputPadding,
      structuredBoolWordRawBitsDecoderIndexedInputMaterializerSource,
      structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputTape] using
    hrun input

theorem canonicalIndexedInitializerOutputSpec_of_indexedMaterializerOutputSpec
    {materializer : MachineDescription}
    (hmaterializer :
      CanonicalIndexedInputMaterializerOutputSpec materializer) :
    CanonicalIndexedInputInitializerOutputSpec materializer :=
  structuredBoolWordRawBitsDecoderIndexedInputInitializerOutputSpec_of_materializerOutputSpec
    hmaterializer

theorem canonicalIndexedMaterializerOutputSpec_of_initializerOutputSpec
    {materializer : MachineDescription}
    (hinitializer :
      CanonicalIndexedInputInitializerOutputSpec materializer) :
    CanonicalIndexedInputMaterializerOutputSpec materializer :=
  structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputSpec_of_initializerOutputSpec
    hinitializer

structure OutputCanonicalRouteSpec
    (materializer : MachineDescription) : Prop where
  canonicalMaterializerOutput :
    StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputSpec
      materializer
  canonicalInitializerOutput :
    StructuredBoolWordRawBitsDecoderCanonicalInputInitializerOutputSpec
      materializer
  indexedMaterializerOutput :
    CanonicalIndexedInputMaterializerOutputSpec materializer
  indexedInitializerOutput :
    CanonicalIndexedInputInitializerOutputSpec materializer

def OutputCanonicalRouteConstruction : Prop :=
  exists materializer : MachineDescription,
    OutputCanonicalRouteSpec materializer

theorem outputCanonicalRouteSpec_of_materializerOutputSpec
    {materializer : MachineDescription}
    (hmaterializer :
      StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputSpec
        materializer) :
    OutputCanonicalRouteSpec materializer := by
  have hinitializer :
      StructuredBoolWordRawBitsDecoderCanonicalInputInitializerOutputSpec
        materializer :=
    structuredBoolWordRawBitsDecoderCanonicalInputInitializerOutputSpec_of_materializerOutputSpec
      hmaterializer
  have hindexed :
      CanonicalIndexedInputMaterializerOutputSpec materializer :=
    canonicalIndexedMaterializerOutputSpec_of_canonicalOutputSpec
      hmaterializer
  have hindexedInitializer :
      CanonicalIndexedInputInitializerOutputSpec materializer :=
    canonicalIndexedInitializerOutputSpec_of_indexedMaterializerOutputSpec
      hindexed
  exact
    { canonicalMaterializerOutput := hmaterializer
      canonicalInitializerOutput := hinitializer
      indexedMaterializerOutput := hindexed
      indexedInitializerOutput := hindexedInitializer }

theorem outputCanonicalRouteSpec_of_initializerOutputSpec
    {materializer : MachineDescription}
    (hinitializer :
      StructuredBoolWordRawBitsDecoderCanonicalInputInitializerOutputSpec
        materializer) :
    OutputCanonicalRouteSpec materializer :=
  outputCanonicalRouteSpec_of_materializerOutputSpec
    (structuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputSpec_of_initializerOutputSpec
      hinitializer)

theorem outputCanonicalRouteSpec_of_indexedMaterializerOutputSpec
    {materializer : MachineDescription}
    (hmaterializer :
      CanonicalIndexedInputMaterializerOutputSpec materializer) :
    OutputCanonicalRouteSpec materializer :=
  outputCanonicalRouteSpec_of_materializerOutputSpec
    (canonicalOutputSpec_of_canonicalIndexedMaterializerOutputSpec
      hmaterializer)

theorem outputCanonicalRouteSpec_of_indexedInitializerOutputSpec
    {materializer : MachineDescription}
    (hinitializer :
      CanonicalIndexedInputInitializerOutputSpec materializer) :
    OutputCanonicalRouteSpec materializer :=
  outputCanonicalRouteSpec_of_indexedMaterializerOutputSpec
    (canonicalIndexedMaterializerOutputSpec_of_initializerOutputSpec
      hinitializer)

theorem outputCanonicalRouteSpec_of_exactRouteSpec
    {materializer : MachineDescription}
    (hroute : ExactCanonicalRouteSpec materializer) :
    OutputCanonicalRouteSpec materializer :=
  outputCanonicalRouteSpec_of_materializerOutputSpec
    (structuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputSpec_of_exact
      hroute.canonicalMaterializer)

theorem outputCanonicalRouteConstruction_of_materializerOutput
    (hmaterializer :
      StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputConstruction) :
    OutputCanonicalRouteConstruction := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      outputCanonicalRouteSpec_of_materializerOutputSpec hspec⟩

theorem materializerOutputConstruction_of_outputCanonicalRouteConstruction
    (hroute : OutputCanonicalRouteConstruction) :
    StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputConstruction := by
  rcases hroute with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.canonicalMaterializerOutput⟩

theorem outputCanonicalRouteConstruction_iff_materializerOutputConstruction :
    OutputCanonicalRouteConstruction ↔
      StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputConstruction := by
  constructor
  · exact materializerOutputConstruction_of_outputCanonicalRouteConstruction
  · exact outputCanonicalRouteConstruction_of_materializerOutput

theorem outputCanonicalRouteConstruction_of_initializerOutput
    (hinitializer :
      StructuredBoolWordRawBitsDecoderCanonicalInputInitializerOutputConstruction) :
    OutputCanonicalRouteConstruction :=
  outputCanonicalRouteConstruction_of_materializerOutput
    (structuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputConstruction_of_initializerOutput
      hinitializer)

theorem initializerOutputConstruction_of_outputCanonicalRouteConstruction
    (hroute : OutputCanonicalRouteConstruction) :
    StructuredBoolWordRawBitsDecoderCanonicalInputInitializerOutputConstruction := by
  rcases hroute with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.canonicalInitializerOutput⟩

theorem outputCanonicalRouteConstruction_iff_initializerOutputConstruction :
    OutputCanonicalRouteConstruction ↔
      StructuredBoolWordRawBitsDecoderCanonicalInputInitializerOutputConstruction := by
  constructor
  · exact initializerOutputConstruction_of_outputCanonicalRouteConstruction
  · exact outputCanonicalRouteConstruction_of_initializerOutput

theorem outputCanonicalRouteConstruction_of_indexedOutput
    (hmaterializer :
      CanonicalIndexedInputMaterializerOutputConstruction) :
    OutputCanonicalRouteConstruction := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      outputCanonicalRouteSpec_of_indexedMaterializerOutputSpec hspec⟩

theorem indexedOutputConstruction_of_outputCanonicalRouteConstruction
    (hroute : OutputCanonicalRouteConstruction) :
    CanonicalIndexedInputMaterializerOutputConstruction := by
  rcases hroute with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.indexedMaterializerOutput⟩

theorem outputCanonicalRouteConstruction_iff_indexedOutput :
    OutputCanonicalRouteConstruction ↔
      CanonicalIndexedInputMaterializerOutputConstruction := by
  constructor
  · exact indexedOutputConstruction_of_outputCanonicalRouteConstruction
  · exact outputCanonicalRouteConstruction_of_indexedOutput

theorem outputCanonicalRouteConstruction_of_exactCanonicalRouteConstruction
    (hroute : ExactCanonicalRouteConstruction) :
    OutputCanonicalRouteConstruction := by
  rcases hroute with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      outputCanonicalRouteSpec_of_exactRouteSpec hspec⟩

theorem outputCanonicalRouteConstruction_of_materializerConstruction
    (hmaterializer :
      StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerConstruction) :
    OutputCanonicalRouteConstruction :=
  outputCanonicalRouteConstruction_of_exactCanonicalRouteConstruction
    (exactCanonicalRouteConstruction_of_materializer hmaterializer)

theorem outputCanonicalRouteConstruction_of_initializerConstruction
    (hinitializer :
      StructuredBoolWordRawBitsDecoderCanonicalInputInitializerConstruction) :
    OutputCanonicalRouteConstruction :=
  outputCanonicalRouteConstruction_of_exactCanonicalRouteConstruction
    (exactCanonicalRouteConstruction_of_initializer hinitializer)

end BoolWordRawBitsDecoderInputMaterializerRouteContracts

end FiniteTransducers
end CommonGround
end Computability
end FoC

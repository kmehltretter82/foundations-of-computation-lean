import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.BoolWordRawBitsDecoderInputMaterializerEndpoint

set_option doc.verso true

/-!
# Bool-word raw-bits input materializer endpoint contracts

This module names exact target-family contracts over the Boolean-word raw-bits
input materializer endpoint facts.  The contracts are construction-free
adapters: they let downstream proofs choose between the canonical
{lit}`Structured3InputMaterializerSpec`, the endpoint-named target, and the
initializer-style named target without restating the same shape equalities.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers

namespace BoolWordRawBitsDecoderInputMaterializerEndpointContracts

open BoolWordRawBitsDecoderInputMaterializerEndpoint

/-!
## Canonical target-family contracts
-/

def canonicalInitializerTarget
    (input : Word Bool × Word Bool) : Tape Bool :=
  structuredBoolWordRawBitsDecoderCanonicalInputInitializerTargetTape
    input.1 input.2

def CanonicalMaterializerTargetFamilySpec
    (materializer : MachineDescription) : Prop :=
  Structured3InputTargetFamilySpec
    structuredBoolWordRawBitsDecoderCanonicalInputMaterializerSource
    canonicalIndexTarget
    materializer

def CanonicalMaterializerTargetFamilyConstruction : Prop :=
  exists materializer : MachineDescription,
    CanonicalMaterializerTargetFamilySpec materializer

def CanonicalEndpointTargetFamilySpec
    (materializer : MachineDescription) : Prop :=
  Structured3InputTargetFamilySpec
    canonicalIndexSource
    canonicalIndexTarget
    materializer

def CanonicalEndpointTargetFamilyConstruction : Prop :=
  exists materializer : MachineDescription,
    CanonicalEndpointTargetFamilySpec materializer

def CanonicalInitializerTargetFamilySpec
    (materializer : MachineDescription) : Prop :=
  Structured3InputTargetFamilySpec
    canonicalIndexSource
    canonicalInitializerTarget
    materializer

def CanonicalInitializerTargetFamilyConstruction : Prop :=
  exists materializer : MachineDescription,
    CanonicalInitializerTargetFamilySpec materializer

theorem canonicalIndexTarget_eq_initializerTarget
    (input : Word Bool × Word Bool) :
    canonicalIndexTarget input = canonicalInitializerTarget input := by
  cases input with
  | mk bits suffixTail =>
      exact canonicalTarget_eq_initializerTargetTape bits suffixTail

theorem canonicalMaterializerTargetFamilySpec_of_exact
    {materializer : MachineDescription}
    (hmaterializer :
      StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerSpec
        materializer) :
    CanonicalMaterializerTargetFamilySpec materializer := by
  exact
    structured3InputTargetFamilySpec_of_materializerSpec
      hmaterializer
      (fun input =>
        canonicalIndexTarget_eq_materializerTarget input)

theorem canonicalMaterializerSpec_of_targetFamilySpec
    {materializer : MachineDescription}
    (hmaterializer :
      CanonicalMaterializerTargetFamilySpec materializer) :
    StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerSpec
      materializer := by
  exact
    structured3InputMaterializerSpec_of_targetFamilySpec
      hmaterializer
      (fun input =>
        canonicalIndexTarget_eq_materializerTarget input)

theorem canonicalMaterializerSpec_iff_targetFamilySpec
    (materializer : MachineDescription) :
    StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerSpec
        materializer ↔
      CanonicalMaterializerTargetFamilySpec materializer := by
  constructor
  · exact canonicalMaterializerTargetFamilySpec_of_exact
  · exact canonicalMaterializerSpec_of_targetFamilySpec

theorem canonicalMaterializerTargetFamilyConstruction_of_exact
    (hmaterializer :
      StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerConstruction) :
    CanonicalMaterializerTargetFamilyConstruction := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      canonicalMaterializerTargetFamilySpec_of_exact hspec⟩

theorem canonicalMaterializerConstruction_of_targetFamilyConstruction
    (hmaterializer :
      CanonicalMaterializerTargetFamilyConstruction) :
    StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerConstruction := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      canonicalMaterializerSpec_of_targetFamilySpec hspec⟩

theorem canonicalMaterializerConstruction_iff_targetFamilyConstruction :
    StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerConstruction ↔
      CanonicalMaterializerTargetFamilyConstruction := by
  constructor
  · exact canonicalMaterializerTargetFamilyConstruction_of_exact
  · exact canonicalMaterializerConstruction_of_targetFamilyConstruction

/-!
## Canonical endpoint source adapters
-/

theorem canonicalEndpointTargetFamilySpec_of_materializerTargetFamilySpec
    {materializer : MachineDescription}
    (hmaterializer :
      CanonicalMaterializerTargetFamilySpec materializer) :
    CanonicalEndpointTargetFamilySpec materializer := by
  exact
    structured3InputTargetFamilySpec_of_eq hmaterializer
      canonicalIndexSource_eq_materializerSource
      (fun _ => rfl)

theorem canonicalMaterializerTargetFamilySpec_of_endpointTargetFamilySpec
    {materializer : MachineDescription}
    (hmaterializer :
      CanonicalEndpointTargetFamilySpec materializer) :
    CanonicalMaterializerTargetFamilySpec materializer := by
  exact
    structured3InputTargetFamilySpec_of_eq hmaterializer
      (fun input =>
        (canonicalIndexSource_eq_materializerSource input).symm)
      (fun _ => rfl)

theorem canonicalEndpointTargetFamilySpec_iff_materializerTargetFamilySpec
    (materializer : MachineDescription) :
    CanonicalEndpointTargetFamilySpec materializer ↔
      CanonicalMaterializerTargetFamilySpec materializer := by
  constructor
  · exact canonicalMaterializerTargetFamilySpec_of_endpointTargetFamilySpec
  · exact canonicalEndpointTargetFamilySpec_of_materializerTargetFamilySpec

theorem canonicalEndpointTargetFamilyConstruction_of_materializerTargetFamilyConstruction
    (hmaterializer :
      CanonicalMaterializerTargetFamilyConstruction) :
    CanonicalEndpointTargetFamilyConstruction := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      canonicalEndpointTargetFamilySpec_of_materializerTargetFamilySpec
        hspec⟩

theorem canonicalMaterializerTargetFamilyConstruction_of_endpointTargetFamilyConstruction
    (hmaterializer :
      CanonicalEndpointTargetFamilyConstruction) :
    CanonicalMaterializerTargetFamilyConstruction := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      canonicalMaterializerTargetFamilySpec_of_endpointTargetFamilySpec
        hspec⟩

theorem canonicalEndpointTargetFamilyConstruction_iff_materializerTargetFamilyConstruction :
    CanonicalEndpointTargetFamilyConstruction ↔
      CanonicalMaterializerTargetFamilyConstruction := by
  constructor
  · exact
      canonicalMaterializerTargetFamilyConstruction_of_endpointTargetFamilyConstruction
  · exact
      canonicalEndpointTargetFamilyConstruction_of_materializerTargetFamilyConstruction

/-!
## Canonical initializer target adapters
-/

theorem canonicalInitializerTargetFamilySpec_of_endpointTargetFamilySpec
    {materializer : MachineDescription}
    (hmaterializer :
      CanonicalEndpointTargetFamilySpec materializer) :
    CanonicalInitializerTargetFamilySpec materializer := by
  exact
    structured3InputTargetFamilySpec_of_eq hmaterializer
      (fun _ => rfl)
      (fun input =>
        (canonicalIndexTarget_eq_initializerTarget input).symm)

theorem canonicalEndpointTargetFamilySpec_of_initializerTargetFamilySpec
    {materializer : MachineDescription}
    (hmaterializer :
      CanonicalInitializerTargetFamilySpec materializer) :
    CanonicalEndpointTargetFamilySpec materializer := by
  exact
    structured3InputTargetFamilySpec_of_eq hmaterializer
      (fun _ => rfl)
      (fun input => canonicalIndexTarget_eq_initializerTarget input)

theorem canonicalInitializerTargetFamilySpec_iff_endpointTargetFamilySpec
    (materializer : MachineDescription) :
    CanonicalInitializerTargetFamilySpec materializer ↔
      CanonicalEndpointTargetFamilySpec materializer := by
  constructor
  · exact canonicalEndpointTargetFamilySpec_of_initializerTargetFamilySpec
  · exact canonicalInitializerTargetFamilySpec_of_endpointTargetFamilySpec

theorem canonicalInitializerTargetFamilyConstruction_of_endpointTargetFamilyConstruction
    (hmaterializer :
      CanonicalEndpointTargetFamilyConstruction) :
    CanonicalInitializerTargetFamilyConstruction := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      canonicalInitializerTargetFamilySpec_of_endpointTargetFamilySpec
        hspec⟩

theorem canonicalEndpointTargetFamilyConstruction_of_initializerTargetFamilyConstruction
    (hmaterializer :
      CanonicalInitializerTargetFamilyConstruction) :
    CanonicalEndpointTargetFamilyConstruction := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      canonicalEndpointTargetFamilySpec_of_initializerTargetFamilySpec
        hspec⟩

theorem canonicalInitializerTargetFamilyConstruction_iff_endpointTargetFamilyConstruction :
    CanonicalInitializerTargetFamilyConstruction ↔
      CanonicalEndpointTargetFamilyConstruction := by
  constructor
  · exact
      canonicalEndpointTargetFamilyConstruction_of_initializerTargetFamilyConstruction
  · exact
      canonicalInitializerTargetFamilyConstruction_of_endpointTargetFamilyConstruction

theorem canonicalInitializerTargetFamilySpec_of_initializerSpec
    {materializer : MachineDescription}
    (hinitializer :
      StructuredBoolWordRawBitsDecoderCanonicalInputInitializerSpec
        materializer) :
    CanonicalInitializerTargetFamilySpec materializer := by
  rcases hinitializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro input
  rcases input with ⟨bits, suffixTail⟩
  simpa [canonicalIndexSource, canonicalSource,
    canonicalInitializerTarget] using
    hrun bits suffixTail

theorem canonicalInitializerSpec_of_initializerTargetFamilySpec
    {materializer : MachineDescription}
    (hmaterializer :
      CanonicalInitializerTargetFamilySpec materializer) :
    StructuredBoolWordRawBitsDecoderCanonicalInputInitializerSpec
      materializer := by
  rcases hmaterializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro bits suffixTail
  simpa [canonicalIndexSource, canonicalSource,
    canonicalInitializerTarget] using
    hrun (bits, suffixTail)

theorem canonicalInitializerSpec_iff_initializerTargetFamilySpec
    (materializer : MachineDescription) :
    StructuredBoolWordRawBitsDecoderCanonicalInputInitializerSpec
        materializer ↔
      CanonicalInitializerTargetFamilySpec materializer := by
  constructor
  · exact canonicalInitializerTargetFamilySpec_of_initializerSpec
  · exact canonicalInitializerSpec_of_initializerTargetFamilySpec

theorem canonicalInitializerTargetFamilyConstruction_of_initializer
    (hinitializer :
      StructuredBoolWordRawBitsDecoderCanonicalInputInitializerConstruction) :
    CanonicalInitializerTargetFamilyConstruction := by
  rcases hinitializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      canonicalInitializerTargetFamilySpec_of_initializerSpec hspec⟩

theorem canonicalInitializerConstruction_of_initializerTargetFamilyConstruction
    (hmaterializer :
      CanonicalInitializerTargetFamilyConstruction) :
    StructuredBoolWordRawBitsDecoderCanonicalInputInitializerConstruction := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      canonicalInitializerSpec_of_initializerTargetFamilySpec hspec⟩

theorem canonicalInitializerConstruction_iff_initializerTargetFamilyConstruction :
    StructuredBoolWordRawBitsDecoderCanonicalInputInitializerConstruction ↔
      CanonicalInitializerTargetFamilyConstruction := by
  constructor
  · exact canonicalInitializerTargetFamilyConstruction_of_initializer
  · exact canonicalInitializerConstruction_of_initializerTargetFamilyConstruction

/-!
## Indexed target-family contracts
-/

def indexedNamedTarget
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) : Tape Bool :=
  structuredBoolWordRawBitsDecoderIndexedInputMaterializerTargetTape
    bits suffixTail rightPadding outputPadding input

def IndexedEndpointTargetFamilySpec
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (materializer : MachineDescription) : Prop :=
  Structured3InputTargetFamilySpec
    (structuredBoolWordRawBitsDecoderIndexedInputMaterializerSource
      bits suffixTail rightPadding)
    (indexedTarget bits suffixTail rightPadding outputPadding)
    materializer

def IndexedEndpointTargetFamilyConstruction
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool)) :
    Prop :=
  exists materializer : MachineDescription,
    IndexedEndpointTargetFamilySpec
      bits suffixTail rightPadding outputPadding materializer

def IndexedNamedTargetFamilySpec
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (materializer : MachineDescription) : Prop :=
  Structured3InputTargetFamilySpec
    (structuredBoolWordRawBitsDecoderIndexedInputMaterializerSource
      bits suffixTail rightPadding)
    (indexedNamedTarget bits suffixTail rightPadding outputPadding)
    materializer

def IndexedNamedTargetFamilyConstruction
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool)) :
    Prop :=
  exists materializer : MachineDescription,
    IndexedNamedTargetFamilySpec
      bits suffixTail rightPadding outputPadding materializer

theorem indexedEndpointTargetFamilySpec_of_materializerSpec
    {ι : Type}
    {bits suffixTail : ι -> Word Bool}
    {rightPadding outputPadding : ι -> List (Option Bool)}
    {materializer : MachineDescription}
    (hmaterializer :
      StructuredBoolWordRawBitsDecoderIndexedInputMaterializerSpec
        bits suffixTail rightPadding outputPadding materializer) :
    IndexedEndpointTargetFamilySpec
      bits suffixTail rightPadding outputPadding materializer := by
  exact
    structured3InputTargetFamilySpec_of_materializerSpec
      hmaterializer
      (fun input => by
        simpa [indexedSource, indexedOutput] using
          indexedTarget_eq_materializerTargetTape
            bits suffixTail rightPadding outputPadding input)

theorem indexedMaterializerSpec_of_endpointTargetFamilySpec
    {ι : Type}
    {bits suffixTail : ι -> Word Bool}
    {rightPadding outputPadding : ι -> List (Option Bool)}
    {materializer : MachineDescription}
    (hmaterializer :
      IndexedEndpointTargetFamilySpec
        bits suffixTail rightPadding outputPadding materializer) :
    StructuredBoolWordRawBitsDecoderIndexedInputMaterializerSpec
      bits suffixTail rightPadding outputPadding materializer := by
  exact
    structured3InputMaterializerSpec_of_targetFamilySpec
      hmaterializer
      (fun input => by
        simpa [indexedSource, indexedOutput] using
          indexedTarget_eq_materializerTargetTape
            bits suffixTail rightPadding outputPadding input)

theorem indexedMaterializerSpec_iff_endpointTargetFamilySpec
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (materializer : MachineDescription) :
    StructuredBoolWordRawBitsDecoderIndexedInputMaterializerSpec
        bits suffixTail rightPadding outputPadding materializer ↔
      IndexedEndpointTargetFamilySpec
        bits suffixTail rightPadding outputPadding materializer := by
  constructor
  · exact indexedEndpointTargetFamilySpec_of_materializerSpec
  · exact indexedMaterializerSpec_of_endpointTargetFamilySpec

theorem indexedEndpointTargetFamilyConstruction_of_materializer
    {ι : Type}
    {bits suffixTail : ι -> Word Bool}
    {rightPadding outputPadding : ι -> List (Option Bool)}
    (hmaterializer :
      StructuredBoolWordRawBitsDecoderIndexedInputMaterializerConstruction
        bits suffixTail rightPadding outputPadding) :
    IndexedEndpointTargetFamilyConstruction
      bits suffixTail rightPadding outputPadding := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      indexedEndpointTargetFamilySpec_of_materializerSpec hspec⟩

theorem indexedMaterializerConstruction_of_endpointTargetFamilyConstruction
    {ι : Type}
    {bits suffixTail : ι -> Word Bool}
    {rightPadding outputPadding : ι -> List (Option Bool)}
    (hmaterializer :
      IndexedEndpointTargetFamilyConstruction
        bits suffixTail rightPadding outputPadding) :
    StructuredBoolWordRawBitsDecoderIndexedInputMaterializerConstruction
      bits suffixTail rightPadding outputPadding := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      indexedMaterializerSpec_of_endpointTargetFamilySpec hspec⟩

theorem indexedMaterializerConstruction_iff_endpointTargetFamilyConstruction
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool)) :
    StructuredBoolWordRawBitsDecoderIndexedInputMaterializerConstruction
        bits suffixTail rightPadding outputPadding ↔
      IndexedEndpointTargetFamilyConstruction
        bits suffixTail rightPadding outputPadding := by
  constructor
  · exact indexedEndpointTargetFamilyConstruction_of_materializer
  · exact indexedMaterializerConstruction_of_endpointTargetFamilyConstruction

/-!
## Indexed named-target and initializer adapters
-/

theorem indexedNamedTargetFamilySpec_of_endpointTargetFamilySpec
    {ι : Type}
    {bits suffixTail : ι -> Word Bool}
    {rightPadding outputPadding : ι -> List (Option Bool)}
    {materializer : MachineDescription}
    (hmaterializer :
      IndexedEndpointTargetFamilySpec
        bits suffixTail rightPadding outputPadding materializer) :
    IndexedNamedTargetFamilySpec
      bits suffixTail rightPadding outputPadding materializer := by
  exact
    structured3InputTargetFamilySpec_of_eq hmaterializer
      (fun _ => rfl)
      (fun input =>
        indexedTarget_eq_namedTargetTape
          bits suffixTail rightPadding outputPadding input)

theorem indexedEndpointTargetFamilySpec_of_namedTargetFamilySpec
    {ι : Type}
    {bits suffixTail : ι -> Word Bool}
    {rightPadding outputPadding : ι -> List (Option Bool)}
    {materializer : MachineDescription}
    (hmaterializer :
      IndexedNamedTargetFamilySpec
        bits suffixTail rightPadding outputPadding materializer) :
    IndexedEndpointTargetFamilySpec
      bits suffixTail rightPadding outputPadding materializer := by
  exact
    structured3InputTargetFamilySpec_of_eq hmaterializer
      (fun _ => rfl)
      (fun input =>
        (indexedTarget_eq_namedTargetTape
          bits suffixTail rightPadding outputPadding input).symm)

theorem indexedNamedTargetFamilySpec_iff_endpointTargetFamilySpec
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (materializer : MachineDescription) :
    IndexedNamedTargetFamilySpec
        bits suffixTail rightPadding outputPadding materializer ↔
      IndexedEndpointTargetFamilySpec
        bits suffixTail rightPadding outputPadding materializer := by
  constructor
  · exact indexedEndpointTargetFamilySpec_of_namedTargetFamilySpec
  · exact indexedNamedTargetFamilySpec_of_endpointTargetFamilySpec

theorem indexedNamedTargetFamilyConstruction_of_endpointTargetFamilyConstruction
    {ι : Type}
    {bits suffixTail : ι -> Word Bool}
    {rightPadding outputPadding : ι -> List (Option Bool)}
    (hmaterializer :
      IndexedEndpointTargetFamilyConstruction
        bits suffixTail rightPadding outputPadding) :
    IndexedNamedTargetFamilyConstruction
      bits suffixTail rightPadding outputPadding := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      indexedNamedTargetFamilySpec_of_endpointTargetFamilySpec hspec⟩

theorem indexedEndpointTargetFamilyConstruction_of_namedTargetFamilyConstruction
    {ι : Type}
    {bits suffixTail : ι -> Word Bool}
    {rightPadding outputPadding : ι -> List (Option Bool)}
    (hmaterializer :
      IndexedNamedTargetFamilyConstruction
        bits suffixTail rightPadding outputPadding) :
    IndexedEndpointTargetFamilyConstruction
      bits suffixTail rightPadding outputPadding := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      indexedEndpointTargetFamilySpec_of_namedTargetFamilySpec hspec⟩

theorem indexedNamedTargetFamilyConstruction_iff_endpointTargetFamilyConstruction
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool)) :
    IndexedNamedTargetFamilyConstruction
        bits suffixTail rightPadding outputPadding ↔
      IndexedEndpointTargetFamilyConstruction
        bits suffixTail rightPadding outputPadding := by
  constructor
  · exact indexedEndpointTargetFamilyConstruction_of_namedTargetFamilyConstruction
  · exact indexedNamedTargetFamilyConstruction_of_endpointTargetFamilyConstruction

theorem indexedNamedTargetFamilySpec_of_initializerSpec
    {ι : Type}
    {bits suffixTail : ι -> Word Bool}
    {rightPadding outputPadding : ι -> List (Option Bool)}
    {materializer : MachineDescription}
    (hinitializer :
      StructuredBoolWordRawBitsDecoderIndexedInputInitializerSpec
        bits suffixTail rightPadding outputPadding materializer) :
    IndexedNamedTargetFamilySpec
      bits suffixTail rightPadding outputPadding materializer := by
  exact hinitializer

theorem indexedInitializerSpec_of_namedTargetFamilySpec
    {ι : Type}
    {bits suffixTail : ι -> Word Bool}
    {rightPadding outputPadding : ι -> List (Option Bool)}
    {materializer : MachineDescription}
    (hmaterializer :
      IndexedNamedTargetFamilySpec
        bits suffixTail rightPadding outputPadding materializer) :
    StructuredBoolWordRawBitsDecoderIndexedInputInitializerSpec
      bits suffixTail rightPadding outputPadding materializer := by
  exact hmaterializer

theorem indexedInitializerSpec_iff_namedTargetFamilySpec
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (materializer : MachineDescription) :
    StructuredBoolWordRawBitsDecoderIndexedInputInitializerSpec
        bits suffixTail rightPadding outputPadding materializer ↔
      IndexedNamedTargetFamilySpec
        bits suffixTail rightPadding outputPadding materializer := by
  constructor
  · exact indexedNamedTargetFamilySpec_of_initializerSpec
  · exact indexedInitializerSpec_of_namedTargetFamilySpec

theorem indexedNamedTargetFamilyConstruction_of_initializer
    {ι : Type}
    {bits suffixTail : ι -> Word Bool}
    {rightPadding outputPadding : ι -> List (Option Bool)}
    (hinitializer :
      StructuredBoolWordRawBitsDecoderIndexedInputInitializerConstruction
        bits suffixTail rightPadding outputPadding) :
    IndexedNamedTargetFamilyConstruction
      bits suffixTail rightPadding outputPadding := by
  rcases hinitializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      indexedNamedTargetFamilySpec_of_initializerSpec hspec⟩

theorem indexedInitializerConstruction_of_namedTargetFamilyConstruction
    {ι : Type}
    {bits suffixTail : ι -> Word Bool}
    {rightPadding outputPadding : ι -> List (Option Bool)}
    (hmaterializer :
      IndexedNamedTargetFamilyConstruction
        bits suffixTail rightPadding outputPadding) :
    StructuredBoolWordRawBitsDecoderIndexedInputInitializerConstruction
      bits suffixTail rightPadding outputPadding := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      indexedInitializerSpec_of_namedTargetFamilySpec hspec⟩

theorem indexedInitializerConstruction_iff_namedTargetFamilyConstruction
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool)) :
    StructuredBoolWordRawBitsDecoderIndexedInputInitializerConstruction
        bits suffixTail rightPadding outputPadding ↔
      IndexedNamedTargetFamilyConstruction
        bits suffixTail rightPadding outputPadding := by
  constructor
  · exact indexedNamedTargetFamilyConstruction_of_initializer
  · exact indexedInitializerConstruction_of_namedTargetFamilyConstruction

/-!
## Canonical as indexed target-family specialization
-/

theorem canonicalEndpointTargetFamilySpec_of_indexedEndpointTargetFamilySpec
    {materializer : MachineDescription}
    (hmaterializer :
      IndexedEndpointTargetFamilySpec
        (fun input : Word Bool × Word Bool => input.1)
        (fun input : Word Bool × Word Bool => input.2)
        (fun _ : Word Bool × Word Bool => [])
        (fun input : Word Bool × Word Bool =>
          boolWordRawBitsDecoderPreservedPadding input.2 [])
        materializer) :
    CanonicalEndpointTargetFamilySpec materializer := by
  exact
    structured3InputTargetFamilySpec_of_eq hmaterializer
      (fun input => by
        exact (canonicalSource_eq_indexedSource input.1 input.2).symm)
      (fun input => by
        exact (canonicalTarget_eq_indexedTarget input.1 input.2).symm)

theorem indexedEndpointTargetFamilySpec_of_canonicalEndpointTargetFamilySpec
    {materializer : MachineDescription}
    (hmaterializer :
      CanonicalEndpointTargetFamilySpec materializer) :
    IndexedEndpointTargetFamilySpec
      (fun input : Word Bool × Word Bool => input.1)
      (fun input : Word Bool × Word Bool => input.2)
      (fun _ : Word Bool × Word Bool => [])
      (fun input : Word Bool × Word Bool =>
        boolWordRawBitsDecoderPreservedPadding input.2 [])
      materializer := by
  exact
    structured3InputTargetFamilySpec_of_eq hmaterializer
      (fun input => canonicalSource_eq_indexedSource input.1 input.2)
      (fun input => canonicalTarget_eq_indexedTarget input.1 input.2)

theorem canonicalEndpointTargetFamilyConstruction_of_indexedEndpointTargetFamilyConstruction
    (hmaterializer :
      IndexedEndpointTargetFamilyConstruction
        (fun input : Word Bool × Word Bool => input.1)
        (fun input : Word Bool × Word Bool => input.2)
        (fun _ : Word Bool × Word Bool => [])
        (fun input : Word Bool × Word Bool =>
          boolWordRawBitsDecoderPreservedPadding input.2 [])) :
    CanonicalEndpointTargetFamilyConstruction := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      canonicalEndpointTargetFamilySpec_of_indexedEndpointTargetFamilySpec
        hspec⟩

theorem indexedEndpointTargetFamilyConstruction_of_canonicalEndpointTargetFamilyConstruction
    (hmaterializer :
      CanonicalEndpointTargetFamilyConstruction) :
    IndexedEndpointTargetFamilyConstruction
      (fun input : Word Bool × Word Bool => input.1)
      (fun input : Word Bool × Word Bool => input.2)
      (fun _ : Word Bool × Word Bool => [])
      (fun input : Word Bool × Word Bool =>
        boolWordRawBitsDecoderPreservedPadding input.2 []) := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      indexedEndpointTargetFamilySpec_of_canonicalEndpointTargetFamilySpec
        hspec⟩

end BoolWordRawBitsDecoderInputMaterializerEndpointContracts

end FiniteTransducers
end CommonGround
end Computability
end FoC

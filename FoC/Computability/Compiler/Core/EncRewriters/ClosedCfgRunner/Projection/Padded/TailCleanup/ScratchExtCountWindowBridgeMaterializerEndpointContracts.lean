import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.TailCleanup.ScratchExtCountWindowBridgeMaterializerEndpoint

set_option doc.verso true

/-!
# Count-window structured input materializer endpoint contracts

This module names exact target-family contracts over the count-window
materializer endpoint facts.  The executable construction leaf is still the
indexed bool-word materializer in `ScratchExtCountWindowBridge.lean`; these
contracts are adapter surfaces for later proofs that want to target the named
count-window endpoint, the indexed bool-word endpoint, or the public encoded
input tape directly.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

namespace CountWindowPostFieldDecodedPrefixStructuredMaterializerEndpointContracts

open CountWindowPostFieldDecodedPrefixStructuredMaterializerEndpoint

/-!
## Target-family specs
-/

def InputTargetFamilySpec
    (useAccept : Bool) (materializer : MachineDescription) : Prop :=
  Structured3InputTargetFamilySpec
    (inputSource useAccept)
    (inputTarget useAccept)
    materializer

def InputTargetFamilyConstruction : Prop :=
  forall useAccept : Bool,
    exists materializer : MachineDescription,
      InputTargetFamilySpec useAccept materializer

def EncodedInputTargetFamilySpec
    (useAccept : Bool) (materializer : MachineDescription) : Prop :=
  Structured3InputTargetFamilySpec
    (inputSource useAccept)
    (encodedInputTape useAccept)
    materializer

def EncodedInputTargetFamilyConstruction : Prop :=
  forall useAccept : Bool,
    exists materializer : MachineDescription,
      EncodedInputTargetFamilySpec useAccept materializer

def BoolWordTargetFamilySpec
    (useAccept : Bool) (materializer : MachineDescription) : Prop :=
  Structured3InputTargetFamilySpec
    (boolWordSource useAccept)
    (boolWordTarget useAccept)
    materializer

def BoolWordTargetFamilyConstruction : Prop :=
  forall useAccept : Bool,
    exists materializer : MachineDescription,
      BoolWordTargetFamilySpec useAccept materializer

def BoolWordInputTargetFamilySpec
    (useAccept : Bool) (materializer : MachineDescription) : Prop :=
  Structured3InputTargetFamilySpec
    (boolWordSource useAccept)
    (inputTarget useAccept)
    materializer

def BoolWordInputTargetFamilyConstruction : Prop :=
  forall useAccept : Bool,
    exists materializer : MachineDescription,
      BoolWordInputTargetFamilySpec useAccept materializer

def BoolWordEncodedInputTargetFamilySpec
    (useAccept : Bool) (materializer : MachineDescription) : Prop :=
  Structured3InputTargetFamilySpec
    (boolWordSource useAccept)
    (encodedInputTape useAccept)
    materializer

def BoolWordEncodedInputTargetFamilyConstruction : Prop :=
  forall useAccept : Bool,
    exists materializer : MachineDescription,
      BoolWordEncodedInputTargetFamilySpec useAccept materializer

def IndexedBoolWordTargetFamilySpec
    (useAccept : Bool) (materializer : MachineDescription) : Prop :=
  Structured3InputTargetFamilySpec
    (BoolWordRawBitsDecoderInputMaterializerEndpoint.indexedSource
      (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordBits
        useAccept)
      (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSuffixTail
        useAccept)
      (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSourcePadding
        useAccept))
    (BoolWordRawBitsDecoderInputMaterializerEndpoint.indexedTarget
      (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordBits
        useAccept)
      (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSuffixTail
        useAccept)
      (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSourcePadding
        useAccept)
      (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordOutputPadding
        useAccept))
    materializer

def IndexedBoolWordTargetFamilyConstruction : Prop :=
  forall useAccept : Bool,
    exists materializer : MachineDescription,
      IndexedBoolWordTargetFamilySpec useAccept materializer

/-!
## Input target adapters
-/

theorem inputTargetFamilySpec_of_inputMaterializerSpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec
        useAccept materializer) :
    InputTargetFamilySpec useAccept materializer := by
  exact
    structured3InputTargetFamilySpec_of_materializerSpec
      hmaterializer
      (fun input => inputTarget_eq_materializerTargetTape
        useAccept input)

theorem inputMaterializerSpec_of_inputTargetFamilySpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      InputTargetFamilySpec useAccept materializer) :
    CountWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec
      useAccept materializer := by
  exact
    structured3InputMaterializerSpec_of_targetFamilySpec
      hmaterializer
      (fun input => inputTarget_eq_materializerTargetTape
        useAccept input)

theorem inputMaterializerSpec_iff_inputTargetFamilySpec
    (useAccept : Bool) (materializer : MachineDescription) :
    CountWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec
        useAccept materializer ↔
      InputTargetFamilySpec useAccept materializer := by
  constructor
  · exact inputTargetFamilySpec_of_inputMaterializerSpec
  · exact inputMaterializerSpec_of_inputTargetFamilySpec

theorem inputTargetFamilyConstruction_of_inputMaterializerConstruction
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerConstruction) :
    InputTargetFamilyConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      inputTargetFamilySpec_of_inputMaterializerSpec hspec⟩

theorem inputMaterializerConstruction_of_inputTargetFamilyConstruction
    (hmaterializer : InputTargetFamilyConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredInputMaterializerConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      inputMaterializerSpec_of_inputTargetFamilySpec hspec⟩

theorem inputMaterializerConstruction_iff_inputTargetFamilyConstruction :
    CountWindowPostFieldDecodedPrefixStructuredInputMaterializerConstruction ↔
      InputTargetFamilyConstruction := by
  constructor
  · exact inputTargetFamilyConstruction_of_inputMaterializerConstruction
  · exact inputMaterializerConstruction_of_inputTargetFamilyConstruction

/-!
## Encoded-input target adapters
-/

theorem encodedInputTargetFamilySpec_of_inputTargetFamilySpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer : InputTargetFamilySpec useAccept materializer) :
    EncodedInputTargetFamilySpec useAccept materializer := by
  exact
    structured3InputTargetFamilySpec_of_eq hmaterializer
      (fun _ => rfl)
      (fun input =>
        (inputTarget_eq_encodedInputTape useAccept input).symm)

theorem inputTargetFamilySpec_of_encodedInputTargetFamilySpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      EncodedInputTargetFamilySpec useAccept materializer) :
    InputTargetFamilySpec useAccept materializer := by
  exact
    structured3InputTargetFamilySpec_of_eq hmaterializer
      (fun _ => rfl)
      (fun input => inputTarget_eq_encodedInputTape useAccept input)

theorem encodedInputTargetFamilySpec_of_inputMaterializerSpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec
        useAccept materializer) :
    EncodedInputTargetFamilySpec useAccept materializer :=
  encodedInputTargetFamilySpec_of_inputTargetFamilySpec
    (inputTargetFamilySpec_of_inputMaterializerSpec hmaterializer)

theorem inputMaterializerSpec_of_encodedInputTargetFamilySpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      EncodedInputTargetFamilySpec useAccept materializer) :
    CountWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec
      useAccept materializer :=
  inputMaterializerSpec_of_inputTargetFamilySpec
    (inputTargetFamilySpec_of_encodedInputTargetFamilySpec hmaterializer)

theorem encodedInputTargetFamilySpec_iff_inputTargetFamilySpec
    (useAccept : Bool) (materializer : MachineDescription) :
    EncodedInputTargetFamilySpec useAccept materializer ↔
      InputTargetFamilySpec useAccept materializer := by
  constructor
  · exact inputTargetFamilySpec_of_encodedInputTargetFamilySpec
  · exact encodedInputTargetFamilySpec_of_inputTargetFamilySpec

theorem encodedInputTargetFamilyConstruction_of_inputTargetFamilyConstruction
    (hmaterializer : InputTargetFamilyConstruction) :
    EncodedInputTargetFamilyConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      encodedInputTargetFamilySpec_of_inputTargetFamilySpec hspec⟩

theorem inputTargetFamilyConstruction_of_encodedInputTargetFamilyConstruction
    (hmaterializer : EncodedInputTargetFamilyConstruction) :
    InputTargetFamilyConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      inputTargetFamilySpec_of_encodedInputTargetFamilySpec hspec⟩

theorem encodedInputTargetFamilyConstruction_iff_inputTargetFamilyConstruction :
    EncodedInputTargetFamilyConstruction ↔
      InputTargetFamilyConstruction := by
  constructor
  · exact inputTargetFamilyConstruction_of_encodedInputTargetFamilyConstruction
  · exact encodedInputTargetFamilyConstruction_of_inputTargetFamilyConstruction

/-!
## Bool-word target adapters
-/

theorem boolWordTarget_eq_boolWordMaterializerTargetTape
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    boolWordTarget useAccept input =
      structured3InputMaterializerTargetTape
        (boolWordSource useAccept input)
        (outputTape useAccept input) := by
  rw [boolWordTarget_eq_inputTarget]
  simp [inputTarget, inputSource, boolWordSource, outputTape,
    StructuredInputMaterializerEndpoint.targetTape,
    countWindowPostFieldDecodedPrefixStructuredInputMaterializerSource_eq_boolWordSource]

theorem boolWordTargetFamilySpec_of_boolWordMaterializerSpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec
        useAccept materializer) :
    BoolWordTargetFamilySpec useAccept materializer := by
  exact
    structured3InputTargetFamilySpec_of_materializerSpec
      hmaterializer
      (fun input =>
        boolWordTarget_eq_boolWordMaterializerTargetTape useAccept input)

theorem boolWordMaterializerSpec_of_boolWordTargetFamilySpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      BoolWordTargetFamilySpec useAccept materializer) :
    CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec
      useAccept materializer := by
  exact
    structured3InputMaterializerSpec_of_targetFamilySpec
      hmaterializer
      (fun input =>
        boolWordTarget_eq_boolWordMaterializerTargetTape useAccept input)

theorem boolWordMaterializerSpec_iff_boolWordTargetFamilySpec
    (useAccept : Bool) (materializer : MachineDescription) :
    CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec
        useAccept materializer ↔
      BoolWordTargetFamilySpec useAccept materializer := by
  constructor
  · exact boolWordTargetFamilySpec_of_boolWordMaterializerSpec
  · exact boolWordMaterializerSpec_of_boolWordTargetFamilySpec

theorem boolWordTargetFamilyConstruction_of_boolWordMaterializerConstruction
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerConstruction) :
    BoolWordTargetFamilyConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      boolWordTargetFamilySpec_of_boolWordMaterializerSpec hspec⟩

theorem boolWordMaterializerConstruction_of_boolWordTargetFamilyConstruction
    (hmaterializer : BoolWordTargetFamilyConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      boolWordMaterializerSpec_of_boolWordTargetFamilySpec hspec⟩

theorem boolWordMaterializerConstruction_iff_boolWordTargetFamilyConstruction :
    CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerConstruction ↔
      BoolWordTargetFamilyConstruction := by
  constructor
  · exact boolWordTargetFamilyConstruction_of_boolWordMaterializerConstruction
  · exact boolWordMaterializerConstruction_of_boolWordTargetFamilyConstruction

/-!
## Bool-word source with input/encoded targets
-/

theorem boolWordInputTargetFamilySpec_of_boolWordTargetFamilySpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer : BoolWordTargetFamilySpec useAccept materializer) :
    BoolWordInputTargetFamilySpec useAccept materializer := by
  exact
    structured3InputTargetFamilySpec_of_eq hmaterializer
      (fun _ => rfl)
      (fun input => (boolWordTarget_eq_inputTarget useAccept input).symm)

theorem boolWordTargetFamilySpec_of_boolWordInputTargetFamilySpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      BoolWordInputTargetFamilySpec useAccept materializer) :
    BoolWordTargetFamilySpec useAccept materializer := by
  exact
    structured3InputTargetFamilySpec_of_eq hmaterializer
      (fun _ => rfl)
      (fun input => boolWordTarget_eq_inputTarget useAccept input)

theorem boolWordEncodedInputTargetFamilySpec_of_boolWordInputTargetFamilySpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      BoolWordInputTargetFamilySpec useAccept materializer) :
    BoolWordEncodedInputTargetFamilySpec useAccept materializer := by
  exact
    structured3InputTargetFamilySpec_of_eq hmaterializer
      (fun _ => rfl)
      (fun input =>
        (inputTarget_eq_encodedInputTape useAccept input).symm)

theorem boolWordInputTargetFamilySpec_of_boolWordEncodedInputTargetFamilySpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      BoolWordEncodedInputTargetFamilySpec useAccept materializer) :
    BoolWordInputTargetFamilySpec useAccept materializer := by
  exact
    structured3InputTargetFamilySpec_of_eq hmaterializer
      (fun _ => rfl)
      (fun input => inputTarget_eq_encodedInputTape useAccept input)

theorem boolWordEncodedInputTargetFamilySpec_of_boolWordTargetFamilySpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer : BoolWordTargetFamilySpec useAccept materializer) :
    BoolWordEncodedInputTargetFamilySpec useAccept materializer :=
  boolWordEncodedInputTargetFamilySpec_of_boolWordInputTargetFamilySpec
    (boolWordInputTargetFamilySpec_of_boolWordTargetFamilySpec hmaterializer)

theorem boolWordTargetFamilySpec_of_boolWordEncodedInputTargetFamilySpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      BoolWordEncodedInputTargetFamilySpec useAccept materializer) :
    BoolWordTargetFamilySpec useAccept materializer :=
  boolWordTargetFamilySpec_of_boolWordInputTargetFamilySpec
    (boolWordInputTargetFamilySpec_of_boolWordEncodedInputTargetFamilySpec
      hmaterializer)

theorem boolWordEncodedInputTargetFamilyConstruction_of_boolWordTargetFamilyConstruction
    (hmaterializer : BoolWordTargetFamilyConstruction) :
    BoolWordEncodedInputTargetFamilyConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      boolWordEncodedInputTargetFamilySpec_of_boolWordTargetFamilySpec
        hspec⟩

theorem boolWordTargetFamilyConstruction_of_boolWordEncodedInputTargetFamilyConstruction
    (hmaterializer : BoolWordEncodedInputTargetFamilyConstruction) :
    BoolWordTargetFamilyConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      boolWordTargetFamilySpec_of_boolWordEncodedInputTargetFamilySpec
        hspec⟩

theorem boolWordEncodedInputTargetFamilyConstruction_iff_boolWordTargetFamilyConstruction :
    BoolWordEncodedInputTargetFamilyConstruction ↔
      BoolWordTargetFamilyConstruction := by
  constructor
  · exact
      boolWordTargetFamilyConstruction_of_boolWordEncodedInputTargetFamilyConstruction
  · exact
      boolWordEncodedInputTargetFamilyConstruction_of_boolWordTargetFamilyConstruction

/-!
## Indexed bool-word target adapters
-/

theorem indexedBoolWordTargetFamilySpec_of_indexedBoolWordMaterializerSpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerSpec
        useAccept materializer) :
    IndexedBoolWordTargetFamilySpec useAccept materializer := by
  exact
    structured3InputTargetFamilySpec_of_materializerSpec
      hmaterializer
      (fun input =>
        BoolWordRawBitsDecoderInputMaterializerEndpoint.indexedTarget_eq_materializerTargetTape
            (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordBits
              useAccept)
            (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSuffixTail
              useAccept)
            (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSourcePadding
              useAccept)
            (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordOutputPadding
              useAccept)
            input)

theorem indexedBoolWordMaterializerSpec_of_indexedBoolWordTargetFamilySpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      IndexedBoolWordTargetFamilySpec useAccept materializer) :
    CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerSpec
      useAccept materializer := by
  exact
    structured3InputMaterializerSpec_of_targetFamilySpec
      hmaterializer
      (fun input =>
        BoolWordRawBitsDecoderInputMaterializerEndpoint.indexedTarget_eq_materializerTargetTape
            (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordBits
              useAccept)
            (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSuffixTail
              useAccept)
            (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSourcePadding
              useAccept)
            (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordOutputPadding
              useAccept)
            input)

theorem indexedBoolWordMaterializerSpec_iff_indexedBoolWordTargetFamilySpec
    (useAccept : Bool) (materializer : MachineDescription) :
    CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerSpec
        useAccept materializer ↔
      IndexedBoolWordTargetFamilySpec useAccept materializer := by
  constructor
  · exact indexedBoolWordTargetFamilySpec_of_indexedBoolWordMaterializerSpec
  · exact indexedBoolWordMaterializerSpec_of_indexedBoolWordTargetFamilySpec

theorem indexedBoolWordTargetFamilyConstruction_of_indexedBoolWordMaterializerConstruction
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerConstruction) :
    IndexedBoolWordTargetFamilyConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      indexedBoolWordTargetFamilySpec_of_indexedBoolWordMaterializerSpec
        hspec⟩

theorem indexedBoolWordMaterializerConstruction_of_indexedBoolWordTargetFamilyConstruction
    (hmaterializer : IndexedBoolWordTargetFamilyConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      indexedBoolWordMaterializerSpec_of_indexedBoolWordTargetFamilySpec
        hspec⟩

theorem indexedBoolWordMaterializerConstruction_iff_indexedBoolWordTargetFamilyConstruction :
    CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerConstruction ↔
      IndexedBoolWordTargetFamilyConstruction := by
  constructor
  · exact
      indexedBoolWordTargetFamilyConstruction_of_indexedBoolWordMaterializerConstruction
  · exact
      indexedBoolWordMaterializerConstruction_of_indexedBoolWordTargetFamilyConstruction

theorem boolWordTargetFamilySpec_of_indexedBoolWordTargetFamilySpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      IndexedBoolWordTargetFamilySpec useAccept materializer) :
    BoolWordTargetFamilySpec useAccept materializer := by
  exact
    structured3InputTargetFamilySpec_of_eq hmaterializer
      (fun input => by
        exact
          (boolWordSource_eq_indexedSource useAccept input).symm)
      (fun input => by
        rfl)

theorem indexedBoolWordTargetFamilySpec_of_boolWordTargetFamilySpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      BoolWordTargetFamilySpec useAccept materializer) :
    IndexedBoolWordTargetFamilySpec useAccept materializer := by
  exact
    structured3InputTargetFamilySpec_of_eq hmaterializer
      (fun input => boolWordSource_eq_indexedSource useAccept input)
      (fun input => rfl)

theorem boolWordTargetFamilyConstruction_of_indexedBoolWordTargetFamilyConstruction
    (hmaterializer : IndexedBoolWordTargetFamilyConstruction) :
    BoolWordTargetFamilyConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      boolWordTargetFamilySpec_of_indexedBoolWordTargetFamilySpec hspec⟩

theorem indexedBoolWordTargetFamilyConstruction_of_boolWordTargetFamilyConstruction
    (hmaterializer : BoolWordTargetFamilyConstruction) :
    IndexedBoolWordTargetFamilyConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      indexedBoolWordTargetFamilySpec_of_boolWordTargetFamilySpec hspec⟩

theorem boolWordTargetFamilyConstruction_iff_indexedBoolWordTargetFamilyConstruction :
    BoolWordTargetFamilyConstruction ↔
      IndexedBoolWordTargetFamilyConstruction := by
  constructor
  · exact
      indexedBoolWordTargetFamilyConstruction_of_boolWordTargetFamilyConstruction
  · exact
      boolWordTargetFamilyConstruction_of_indexedBoolWordTargetFamilyConstruction

end CountWindowPostFieldDecodedPrefixStructuredMaterializerEndpointContracts

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters
end Computability
end FoC

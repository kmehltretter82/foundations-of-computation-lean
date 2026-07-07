import FoC.Computability.Compiler.FST.BoolRawInput.EndpointContracts
import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.Mat.EndpointSpec

set_option doc.verso true

/-!
# Count-window specialization of generic bool-word materializer contracts

This module records that the count-window indexed bool-word materializer leaf is
an instance of the generic Boolean-word raw-bits input materializer contract
API.  It keeps the count-window bridge reusable: higher layers can use the
count-window endpoint names, while lower materializer work can target the
generic indexed bool-word contract.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

namespace CountWindowPostFieldDecodedPrefixStructuredMaterializerGenericContracts

open CountWindowPostFieldDecodedPrefixStructuredMaterializerEndpoint
open CountWindowPostFieldDecodedPrefixStructuredMaterializerEndpointContracts

/-!
## Generic indexed bool-word specializations
-/

def GenericIndexedEndpointTargetFamilySpec
    (useAccept : Bool) (materializer : MachineDescription) : Prop :=
  _root_.FoC.Computability.CommonGround.FiniteTransducers.BoolWordRawBitsDecoderInputMaterializerEndpointContracts.IndexedEndpointTargetFamilySpec
      (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordBits
        useAccept)
      (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSuffixTail
        useAccept)
      (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSourcePadding
        useAccept)
      (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordOutputPadding
        useAccept)
      materializer

def GenericIndexedEndpointTargetFamilyConstruction : Prop :=
  forall useAccept : Bool,
    exists materializer : MachineDescription,
      GenericIndexedEndpointTargetFamilySpec useAccept materializer

def GenericIndexedNamedTargetFamilySpec
    (useAccept : Bool) (materializer : MachineDescription) : Prop :=
  _root_.FoC.Computability.CommonGround.FiniteTransducers.BoolWordRawBitsDecoderInputMaterializerEndpointContracts.IndexedNamedTargetFamilySpec
      (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordBits
        useAccept)
      (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSuffixTail
        useAccept)
      (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSourcePadding
        useAccept)
      (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordOutputPadding
        useAccept)
      materializer

def GenericIndexedNamedTargetFamilyConstruction : Prop :=
  forall useAccept : Bool,
    exists materializer : MachineDescription,
      GenericIndexedNamedTargetFamilySpec useAccept materializer

def GenericIndexedInitializerSpec
    (useAccept : Bool) (materializer : MachineDescription) : Prop :=
  StructuredBoolWordRawBitsDecoderIndexedInputInitializerSpec
    (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordBits
      useAccept)
    (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSuffixTail
      useAccept)
    (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSourcePadding
      useAccept)
    (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordOutputPadding
      useAccept)
    materializer

def GenericIndexedInitializerConstruction : Prop :=
  forall useAccept : Bool,
    exists materializer : MachineDescription,
      GenericIndexedInitializerSpec useAccept materializer

/-!
## Generic endpoint target and count-window endpoint target
-/

theorem indexedBoolWordTargetFamilySpec_of_genericEndpointTargetFamilySpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      GenericIndexedEndpointTargetFamilySpec useAccept materializer) :
    IndexedBoolWordTargetFamilySpec useAccept materializer := by
  exact
    structured3InputTargetFamilySpec_of_eq hmaterializer
      (fun input =>
        BoolWordRawBitsDecoderInputMaterializerEndpoint.indexedSource_eq
          (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordBits
            useAccept)
          (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSuffixTail
            useAccept)
          (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSourcePadding
            useAccept)
          input)
      (fun _ => rfl)

theorem genericEndpointTargetFamilySpec_of_indexedBoolWordTargetFamilySpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      IndexedBoolWordTargetFamilySpec useAccept materializer) :
    GenericIndexedEndpointTargetFamilySpec useAccept materializer := by
  exact
    structured3InputTargetFamilySpec_of_eq hmaterializer
      (fun input =>
        (BoolWordRawBitsDecoderInputMaterializerEndpoint.indexedSource_eq
          (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordBits
            useAccept)
          (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSuffixTail
            useAccept)
          (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSourcePadding
            useAccept)
          input).symm)
      (fun _ => rfl)

theorem genericEndpointTargetFamilySpec_iff_indexedBoolWordTargetFamilySpec
    (useAccept : Bool) (materializer : MachineDescription) :
    GenericIndexedEndpointTargetFamilySpec useAccept materializer ↔
      IndexedBoolWordTargetFamilySpec useAccept materializer := by
  constructor
  · exact indexedBoolWordTargetFamilySpec_of_genericEndpointTargetFamilySpec
  · exact genericEndpointTargetFamilySpec_of_indexedBoolWordTargetFamilySpec

theorem indexedBoolWordTargetFamilyConstruction_of_genericEndpointTargetFamilyConstruction
    (hmaterializer :
      GenericIndexedEndpointTargetFamilyConstruction) :
    IndexedBoolWordTargetFamilyConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      indexedBoolWordTargetFamilySpec_of_genericEndpointTargetFamilySpec
        hspec⟩

theorem genericEndpointTargetFamilyConstruction_of_indexedBoolWordTargetFamilyConstruction
    (hmaterializer :
      IndexedBoolWordTargetFamilyConstruction) :
    GenericIndexedEndpointTargetFamilyConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      genericEndpointTargetFamilySpec_of_indexedBoolWordTargetFamilySpec
        hspec⟩

theorem genericEndpointTargetFamilyConstruction_iff_indexedBoolWordTargetFamilyConstruction :
    GenericIndexedEndpointTargetFamilyConstruction ↔
      IndexedBoolWordTargetFamilyConstruction := by
  constructor
  · exact
      indexedBoolWordTargetFamilyConstruction_of_genericEndpointTargetFamilyConstruction
  · exact
      genericEndpointTargetFamilyConstruction_of_indexedBoolWordTargetFamilyConstruction

/-!
## Generic endpoint target and exact materializer spec
-/

theorem genericEndpointTargetFamilySpec_of_indexedMaterializerSpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerSpec
        useAccept materializer) :
    GenericIndexedEndpointTargetFamilySpec useAccept materializer := by
  exact
    _root_.FoC.Computability.CommonGround.FiniteTransducers.BoolWordRawBitsDecoderInputMaterializerEndpointContracts.indexedEndpointTargetFamilySpec_of_materializerSpec
        hmaterializer

theorem indexedMaterializerSpec_of_genericEndpointTargetFamilySpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      GenericIndexedEndpointTargetFamilySpec useAccept materializer) :
    CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerSpec
      useAccept materializer := by
  exact
    _root_.FoC.Computability.CommonGround.FiniteTransducers.BoolWordRawBitsDecoderInputMaterializerEndpointContracts.indexedMaterializerSpec_of_endpointTargetFamilySpec
        hmaterializer

theorem indexedMaterializerSpec_iff_genericEndpointTargetFamilySpec
    (useAccept : Bool) (materializer : MachineDescription) :
    CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerSpec
        useAccept materializer ↔
      GenericIndexedEndpointTargetFamilySpec useAccept materializer := by
  constructor
  · exact genericEndpointTargetFamilySpec_of_indexedMaterializerSpec
  · exact indexedMaterializerSpec_of_genericEndpointTargetFamilySpec

theorem genericEndpointTargetFamilyConstruction_of_indexedMaterializerConstruction
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerConstruction) :
    GenericIndexedEndpointTargetFamilyConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      genericEndpointTargetFamilySpec_of_indexedMaterializerSpec hspec⟩

theorem indexedMaterializerConstruction_of_genericEndpointTargetFamilyConstruction
    (hmaterializer :
      GenericIndexedEndpointTargetFamilyConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      indexedMaterializerSpec_of_genericEndpointTargetFamilySpec hspec⟩

theorem indexedMaterializerConstruction_iff_genericEndpointTargetFamilyConstruction :
    CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerConstruction ↔
      GenericIndexedEndpointTargetFamilyConstruction := by
  constructor
  · exact genericEndpointTargetFamilyConstruction_of_indexedMaterializerConstruction
  · exact indexedMaterializerConstruction_of_genericEndpointTargetFamilyConstruction

/-!
## Generic named target and initializer spec
-/

theorem genericNamedTargetFamilySpec_of_endpointTargetFamilySpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      GenericIndexedEndpointTargetFamilySpec useAccept materializer) :
    GenericIndexedNamedTargetFamilySpec useAccept materializer := by
  exact
    _root_.FoC.Computability.CommonGround.FiniteTransducers.BoolWordRawBitsDecoderInputMaterializerEndpointContracts.indexedNamedTargetFamilySpec_of_endpointTargetFamilySpec
        hmaterializer

theorem genericEndpointTargetFamilySpec_of_namedTargetFamilySpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      GenericIndexedNamedTargetFamilySpec useAccept materializer) :
    GenericIndexedEndpointTargetFamilySpec useAccept materializer := by
  exact
    _root_.FoC.Computability.CommonGround.FiniteTransducers.BoolWordRawBitsDecoderInputMaterializerEndpointContracts.indexedEndpointTargetFamilySpec_of_namedTargetFamilySpec
        hmaterializer

theorem genericNamedTargetFamilySpec_iff_endpointTargetFamilySpec
    (useAccept : Bool) (materializer : MachineDescription) :
    GenericIndexedNamedTargetFamilySpec useAccept materializer ↔
      GenericIndexedEndpointTargetFamilySpec useAccept materializer := by
  constructor
  · exact genericEndpointTargetFamilySpec_of_namedTargetFamilySpec
  · exact genericNamedTargetFamilySpec_of_endpointTargetFamilySpec

theorem genericInitializerSpec_of_namedTargetFamilySpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      GenericIndexedNamedTargetFamilySpec useAccept materializer) :
    GenericIndexedInitializerSpec useAccept materializer := by
  exact
    _root_.FoC.Computability.CommonGround.FiniteTransducers.BoolWordRawBitsDecoderInputMaterializerEndpointContracts.indexedInitializerSpec_of_namedTargetFamilySpec
        hmaterializer

theorem genericNamedTargetFamilySpec_of_initializerSpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hinitializer :
      GenericIndexedInitializerSpec useAccept materializer) :
    GenericIndexedNamedTargetFamilySpec useAccept materializer := by
  exact
    _root_.FoC.Computability.CommonGround.FiniteTransducers.BoolWordRawBitsDecoderInputMaterializerEndpointContracts.indexedNamedTargetFamilySpec_of_initializerSpec
        hinitializer

theorem genericInitializerSpec_iff_namedTargetFamilySpec
    (useAccept : Bool) (materializer : MachineDescription) :
    GenericIndexedInitializerSpec useAccept materializer ↔
      GenericIndexedNamedTargetFamilySpec useAccept materializer := by
  constructor
  · exact genericNamedTargetFamilySpec_of_initializerSpec
  · exact genericInitializerSpec_of_namedTargetFamilySpec

theorem genericNamedTargetFamilyConstruction_of_endpointTargetFamilyConstruction
    (hmaterializer :
      GenericIndexedEndpointTargetFamilyConstruction) :
    GenericIndexedNamedTargetFamilyConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      genericNamedTargetFamilySpec_of_endpointTargetFamilySpec hspec⟩

theorem genericEndpointTargetFamilyConstruction_of_namedTargetFamilyConstruction
    (hmaterializer :
      GenericIndexedNamedTargetFamilyConstruction) :
    GenericIndexedEndpointTargetFamilyConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      genericEndpointTargetFamilySpec_of_namedTargetFamilySpec hspec⟩

theorem genericNamedTargetFamilyConstruction_iff_endpointTargetFamilyConstruction :
    GenericIndexedNamedTargetFamilyConstruction ↔
      GenericIndexedEndpointTargetFamilyConstruction := by
  constructor
  · exact genericEndpointTargetFamilyConstruction_of_namedTargetFamilyConstruction
  · exact genericNamedTargetFamilyConstruction_of_endpointTargetFamilyConstruction

theorem genericInitializerConstruction_of_namedTargetFamilyConstruction
    (hmaterializer :
      GenericIndexedNamedTargetFamilyConstruction) :
    GenericIndexedInitializerConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      genericInitializerSpec_of_namedTargetFamilySpec hspec⟩

theorem genericNamedTargetFamilyConstruction_of_initializerConstruction
    (hinitializer :
      GenericIndexedInitializerConstruction) :
    GenericIndexedNamedTargetFamilyConstruction := by
  intro useAccept
  rcases hinitializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      genericNamedTargetFamilySpec_of_initializerSpec hspec⟩

theorem genericInitializerConstruction_iff_namedTargetFamilyConstruction :
    GenericIndexedInitializerConstruction ↔
      GenericIndexedNamedTargetFamilyConstruction := by
  constructor
  · exact genericNamedTargetFamilyConstruction_of_initializerConstruction
  · exact genericInitializerConstruction_of_namedTargetFamilyConstruction

/-!
## Bridges to count-window bool-word target contracts
-/

theorem boolWordTargetFamilySpec_of_genericEndpointTargetFamilySpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      GenericIndexedEndpointTargetFamilySpec useAccept materializer) :
    BoolWordTargetFamilySpec useAccept materializer :=
  boolWordTargetFamilySpec_of_indexedBoolWordTargetFamilySpec
    (indexedBoolWordTargetFamilySpec_of_genericEndpointTargetFamilySpec
      hmaterializer)

theorem genericEndpointTargetFamilySpec_of_boolWordTargetFamilySpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      BoolWordTargetFamilySpec useAccept materializer) :
    GenericIndexedEndpointTargetFamilySpec useAccept materializer :=
  genericEndpointTargetFamilySpec_of_indexedBoolWordTargetFamilySpec
    (indexedBoolWordTargetFamilySpec_of_boolWordTargetFamilySpec
      hmaterializer)

theorem boolWordEncodedInputTargetFamilySpec_of_genericEndpointTargetFamilySpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      GenericIndexedEndpointTargetFamilySpec useAccept materializer) :
    BoolWordEncodedInputTargetFamilySpec useAccept materializer :=
  boolWordEncodedInputTargetFamilySpec_of_boolWordTargetFamilySpec
    (boolWordTargetFamilySpec_of_genericEndpointTargetFamilySpec
      hmaterializer)

theorem genericEndpointTargetFamilySpec_of_boolWordEncodedInputTargetFamilySpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      BoolWordEncodedInputTargetFamilySpec useAccept materializer) :
    GenericIndexedEndpointTargetFamilySpec useAccept materializer :=
  genericEndpointTargetFamilySpec_of_boolWordTargetFamilySpec
    (boolWordTargetFamilySpec_of_boolWordEncodedInputTargetFamilySpec
      hmaterializer)

theorem inputTargetFamilySpec_of_genericEndpointTargetFamilySpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      GenericIndexedEndpointTargetFamilySpec useAccept materializer) :
    InputTargetFamilySpec useAccept materializer :=
  inputTargetFamilySpec_of_inputMaterializerSpec
    (countWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec_of_boolWordSpec
      (countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec_of_indexedSpec
        (indexedMaterializerSpec_of_genericEndpointTargetFamilySpec
          hmaterializer)))

theorem encodedInputTargetFamilySpec_of_genericEndpointTargetFamilySpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      GenericIndexedEndpointTargetFamilySpec useAccept materializer) :
    EncodedInputTargetFamilySpec useAccept materializer :=
  encodedInputTargetFamilySpec_of_inputTargetFamilySpec
    (inputTargetFamilySpec_of_genericEndpointTargetFamilySpec hmaterializer)

theorem genericEndpointTargetFamilyConstruction_of_boolWordTargetFamilyConstruction
    (hmaterializer :
      BoolWordTargetFamilyConstruction) :
    GenericIndexedEndpointTargetFamilyConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      genericEndpointTargetFamilySpec_of_boolWordTargetFamilySpec hspec⟩

theorem boolWordTargetFamilyConstruction_of_genericEndpointTargetFamilyConstruction
    (hmaterializer :
      GenericIndexedEndpointTargetFamilyConstruction) :
    BoolWordTargetFamilyConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      boolWordTargetFamilySpec_of_genericEndpointTargetFamilySpec hspec⟩

theorem boolWordTargetFamilyConstruction_iff_genericEndpointTargetFamilyConstruction :
    BoolWordTargetFamilyConstruction ↔
      GenericIndexedEndpointTargetFamilyConstruction := by
  constructor
  · exact genericEndpointTargetFamilyConstruction_of_boolWordTargetFamilyConstruction
  · exact boolWordTargetFamilyConstruction_of_genericEndpointTargetFamilyConstruction

theorem encodedInputTargetFamilyConstruction_of_genericEndpointTargetFamilyConstruction
    (hmaterializer :
      GenericIndexedEndpointTargetFamilyConstruction) :
    EncodedInputTargetFamilyConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      encodedInputTargetFamilySpec_of_genericEndpointTargetFamilySpec
        hspec⟩

theorem genericEndpointTargetFamilyConstruction_of_encodedInputTargetFamilyConstruction
    (hmaterializer :
      EncodedInputTargetFamilyConstruction) :
    GenericIndexedEndpointTargetFamilyConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  have hinput :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec
        useAccept materializer :=
    inputMaterializerSpec_of_encodedInputTargetFamilySpec hspec
  have hbool :
      CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec
        useAccept materializer :=
    countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec_of_inputSpec
      hinput
  have hindexed :
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerSpec
        useAccept materializer :=
    countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerSpec_of_boolWordSpec
      hbool
  exact
    ⟨materializer,
      genericEndpointTargetFamilySpec_of_indexedMaterializerSpec hindexed⟩

theorem encodedInputTargetFamilyConstruction_iff_genericEndpointTargetFamilyConstruction :
    EncodedInputTargetFamilyConstruction ↔
      GenericIndexedEndpointTargetFamilyConstruction := by
  constructor
  · exact genericEndpointTargetFamilyConstruction_of_encodedInputTargetFamilyConstruction
  · exact encodedInputTargetFamilyConstruction_of_genericEndpointTargetFamilyConstruction

theorem inputTargetFamilyConstruction_of_genericEndpointTargetFamilyConstruction
    (hmaterializer :
      GenericIndexedEndpointTargetFamilyConstruction) :
    InputTargetFamilyConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      inputTargetFamilySpec_of_genericEndpointTargetFamilySpec hspec⟩

theorem genericEndpointTargetFamilyConstruction_of_inputTargetFamilyConstruction
    (hmaterializer :
      InputTargetFamilyConstruction) :
    GenericIndexedEndpointTargetFamilyConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  have hinput :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec
        useAccept materializer :=
    inputMaterializerSpec_of_inputTargetFamilySpec hspec
  have hbool :
      CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec
        useAccept materializer :=
    countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec_of_inputSpec
      hinput
  have hindexed :
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerSpec
        useAccept materializer :=
    countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerSpec_of_boolWordSpec
      hbool
  exact
    ⟨materializer,
      genericEndpointTargetFamilySpec_of_indexedMaterializerSpec hindexed⟩

theorem inputTargetFamilyConstruction_iff_genericEndpointTargetFamilyConstruction :
    InputTargetFamilyConstruction ↔
      GenericIndexedEndpointTargetFamilyConstruction := by
  constructor
  · exact genericEndpointTargetFamilyConstruction_of_inputTargetFamilyConstruction
  · exact inputTargetFamilyConstruction_of_genericEndpointTargetFamilyConstruction

theorem boolWordEncodedInputTargetFamilyConstruction_of_genericEndpointTargetFamilyConstruction
    (hmaterializer :
      GenericIndexedEndpointTargetFamilyConstruction) :
    BoolWordEncodedInputTargetFamilyConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      boolWordEncodedInputTargetFamilySpec_of_genericEndpointTargetFamilySpec
        hspec⟩

theorem genericEndpointTargetFamilyConstruction_of_boolWordEncodedInputTargetFamilyConstruction
    (hmaterializer :
      BoolWordEncodedInputTargetFamilyConstruction) :
    GenericIndexedEndpointTargetFamilyConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      genericEndpointTargetFamilySpec_of_boolWordEncodedInputTargetFamilySpec
        hspec⟩

theorem boolWordEncodedInputTargetFamilyConstruction_iff_genericEndpointTargetFamilyConstruction :
    BoolWordEncodedInputTargetFamilyConstruction ↔
      GenericIndexedEndpointTargetFamilyConstruction := by
  constructor
  · exact
      genericEndpointTargetFamilyConstruction_of_boolWordEncodedInputTargetFamilyConstruction
  · exact
      boolWordEncodedInputTargetFamilyConstruction_of_genericEndpointTargetFamilyConstruction

end CountWindowPostFieldDecodedPrefixStructuredMaterializerGenericContracts

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters
end Computability
end FoC

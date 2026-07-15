import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.Shape

set_option doc.verso true

/-!
# Count-window input materializer contracts

Count-window structured input materializer contracts and adapter equivalences.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

open CanonicalLayouts.DovetailLayoutScanner

def CountWindowPostFieldDecodedPrefixStructuredInputInitializerSpec
    (useAccept : Bool) (initializer : MachineDescription) : Prop :=
  initializer.SubroutineReady ∧
    forall (L : DovetailLayout) (pref : Word Bool)
      (leftBit : Bool) (deletedTail : Word Bool),
      configurationFieldBits L.acceptConfig [] = false :: deletedTail ->
      countWindowPostFieldDecodedPrefixMaterializerPayload useAccept L =
          List.append pref [leftBit] ->
      initializer.HaltsFromTapeEquiv
        (countWindowPostFieldDecodedPrefixMaterializerSourceTape
          useAccept L pref leftBit deletedTail)
        (countWindowPostFieldDecodedPrefixStructuredEncodedInputTape
          useAccept L pref leftBit deletedTail)

def CountWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction :
    Prop :=
  forall useAccept : Bool,
    exists initializer : MachineDescription,
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerSpec
        useAccept initializer

structure CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
    (useAccept : Bool) where
  L : DovetailLayout
  pref : Word Bool
  leftBit : Bool
  deletedTail : Word Bool
  hdeleted : configurationFieldBits L.acceptConfig [] = false :: deletedTail
  hpayload :
    countWindowPostFieldDecodedPrefixMaterializerPayload useAccept L =
      List.append pref [leftBit]

def countWindowPostFieldDecodedPrefixStructuredInputMaterializerSource
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) : Tape Bool :=
  countWindowPostFieldDecodedPrefixMaterializerSourceTape
    useAccept input.L input.pref input.leftBit input.deletedTail

def countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) : Tape Bool :=
  boolWordRawBitsDecoderSourceTape
    (ParsedLayoutBits input.L)
    (countWindowPostFieldDecodedPrefixStructuredSuffixTail
      useAccept input.L)
    (countWindowPostFieldDecodedPrefixStructuredSourcePadding
      useAccept input.L input.deletedTail)

theorem countWindowPostFieldDecodedPrefixStructuredInputMaterializerSource_eq_boolWordSource
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    countWindowPostFieldDecodedPrefixStructuredInputMaterializerSource
        useAccept input =
      countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource
        useAccept input := by
  exact
    countWindowPostFieldDecodedPrefixMaterializerSourceTape_eq_boolWordSource
      useAccept input.L input.pref input.leftBit input.deletedTail
      input.hpayload

def countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputTape
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) : Tape Bool :=
  structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
    (ParsedLayoutBits input.L).length
    (postFieldDecodedPrefixScanPadding useAccept input.L)

def CountWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec
    (useAccept : Bool) (initializer : MachineDescription) : Prop :=
  Structured3InputMaterializerSpec
    (countWindowPostFieldDecodedPrefixStructuredInputMaterializerSource
      useAccept)
    (countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputTape
      useAccept)
    initializer

def CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec
    (useAccept : Bool) (initializer : MachineDescription) : Prop :=
  Structured3InputMaterializerSpec
    (countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource
      useAccept)
    (countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputTape
      useAccept)
    initializer

def CountWindowPostFieldDecodedPrefixStructuredInputMaterializerConstruction :
    Prop :=
  forall useAccept : Bool,
    exists initializer : MachineDescription,
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec
        useAccept initializer

def CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerConstruction :
    Prop :=
  forall useAccept : Bool,
    exists initializer : MachineDescription,
      CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec
        useAccept initializer

def countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordBits
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) : Word Bool :=
  ParsedLayoutBits input.L

def countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSuffixTail
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) : Word Bool :=
  countWindowPostFieldDecodedPrefixStructuredSuffixTail
    useAccept input.L

def countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSourcePadding
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) : List (Option Bool) :=
  countWindowPostFieldDecodedPrefixStructuredSourcePadding
    useAccept input.L input.deletedTail

def countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordOutputPadding
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) : List (Option Bool) :=
  postFieldDecodedPrefixScanPadding useAccept input.L

def CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerSpec
    (useAccept : Bool) (initializer : MachineDescription) : Prop :=
  StructuredBoolWordRawBitsDecoderIndexedInputMaterializerSpec
    (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordBits
      useAccept)
    (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSuffixTail
      useAccept)
    (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSourcePadding
      useAccept)
    (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordOutputPadding
      useAccept)
    initializer

def CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerConstruction :
    Prop :=
  forall useAccept : Bool,
    exists initializer : MachineDescription,
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerSpec
        useAccept initializer

theorem countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec_of_indexedSpec
    {useAccept : Bool} {initializer : MachineDescription}
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerSpec
        useAccept initializer) :
    CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec
      useAccept initializer := by
  simpa [
    CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec,
    CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerSpec,
    countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource,
    countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputTape,
    countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordBits,
    countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSuffixTail,
    countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSourcePadding,
    countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordOutputPadding,
    StructuredBoolWordRawBitsDecoderIndexedInputMaterializerSpec,
    structuredBoolWordRawBitsDecoderIndexedInputMaterializerSource,
    structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputTape] using!
    hmaterializer

theorem countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerSpec_of_boolWordSpec
    {useAccept : Bool} {initializer : MachineDescription}
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec
        useAccept initializer) :
    CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerSpec
      useAccept initializer := by
  simpa [
    CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec,
    CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerSpec,
    countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource,
    countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputTape,
    countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordBits,
    countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSuffixTail,
    countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSourcePadding,
    countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordOutputPadding,
    StructuredBoolWordRawBitsDecoderIndexedInputMaterializerSpec,
    structuredBoolWordRawBitsDecoderIndexedInputMaterializerSource,
    structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputTape] using!
    hmaterializer

theorem countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerConstruction_of_indexed
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨initializer, hspec⟩
  exact
    ⟨initializer,
      countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec_of_indexedSpec
        hspec⟩

theorem countWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec_of_boolWordSpec
    {useAccept : Bool} {initializer : MachineDescription}
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec
        useAccept initializer) :
    CountWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec
      useAccept initializer := by
  rcases hmaterializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro input
  rw [
    countWindowPostFieldDecodedPrefixStructuredInputMaterializerSource_eq_boolWordSource
      useAccept input]
  exact hrun input

theorem countWindowPostFieldDecodedPrefixStructuredInputMaterializerConstruction_of_boolWord
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredInputMaterializerConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨initializer, hspec⟩
  exact
    ⟨initializer,
      countWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec_of_boolWordSpec
        hspec⟩

theorem countWindowPostFieldDecodedPrefixStructuredInputInitializerSpec_of_structured3InputMaterializerSpec
    {useAccept : Bool} {initializer : MachineDescription}
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec
        useAccept initializer) :
    CountWindowPostFieldDecodedPrefixStructuredInputInitializerSpec
      useAccept initializer := by
  rcases hmaterializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro L pref leftBit deletedTail hdeleted hpayload
  let input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept :=
    { L := L
      pref := pref
      leftBit := leftBit
      deletedTail := deletedTail
      hdeleted := hdeleted
      hpayload := hpayload }
  simpa [
    input,
    CountWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec,
    countWindowPostFieldDecodedPrefixStructuredInputMaterializerSource,
    countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputTape,
    countWindowPostFieldDecodedPrefixStructuredEncodedInputTape,
    structured3InputMaterializerTargetTape] using
    hrun input

theorem countWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction_of_structured3InputMaterializer
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨initializer, hspec⟩
  exact
    ⟨initializer,
      countWindowPostFieldDecodedPrefixStructuredInputInitializerSpec_of_structured3InputMaterializerSpec
        hspec⟩

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC

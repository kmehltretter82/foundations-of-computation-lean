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

theorem countWindowPostFieldDecodedPrefixStructuredEncodedInputTape_eq_inputMaterializerTargetTape
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    countWindowPostFieldDecodedPrefixStructuredEncodedInputTape
        useAccept input.L input.pref input.leftBit input.deletedTail =
      structured3InputMaterializerTargetTape
        (countWindowPostFieldDecodedPrefixStructuredInputMaterializerSource
          useAccept input)
        (countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputTape
          useAccept input) := by
  rfl

theorem countWindowPostFieldDecodedPrefixStructuredInputMaterializerTargetTape_read
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    Tape.read
        (structured3InputMaterializerTargetTape
          (countWindowPostFieldDecodedPrefixStructuredInputMaterializerSource
            useAccept input)
          (countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputTape
            useAccept input)) =
      none := by
  rfl

theorem countWindowPostFieldDecodedPrefixStructuredInputMaterializerTargetTape_cells_eq_encodedInputTape_cells
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    Tape.cells
        (structured3InputMaterializerTargetTape
          (countWindowPostFieldDecodedPrefixStructuredInputMaterializerSource
            useAccept input)
          (countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputTape
            useAccept input)) =
      Tape.cells
        (countWindowPostFieldDecodedPrefixStructuredEncodedInputTape
          useAccept input.L input.pref input.leftBit input.deletedTail) := by
  rw [
    countWindowPostFieldDecodedPrefixStructuredEncodedInputTape_eq_inputMaterializerTargetTape]

theorem countWindowPostFieldDecodedPrefixStructuredInputMaterializerTargetTape_normalizedOutput_eq_encodedInputTape
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    Tape.normalizedOutput
        (structured3InputMaterializerTargetTape
          (countWindowPostFieldDecodedPrefixStructuredInputMaterializerSource
            useAccept input)
          (countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputTape
            useAccept input)) =
      Tape.normalizedOutput
        (countWindowPostFieldDecodedPrefixStructuredEncodedInputTape
          useAccept input.L input.pref input.leftBit input.deletedTail) := by
  rw [
    countWindowPostFieldDecodedPrefixStructuredEncodedInputTape_eq_inputMaterializerTargetTape]

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

theorem countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource_eq_indexedSource
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource
        useAccept input =
      structuredBoolWordRawBitsDecoderIndexedInputMaterializerSource
        (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordBits
          useAccept)
        (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSuffixTail
          useAccept)
        (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSourcePadding
          useAccept)
        input := by
  rfl

theorem countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputTape_eq_indexedOutputTape
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputTape
        useAccept input =
      structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputTape
        (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordBits
          useAccept)
        (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordOutputPadding
          useAccept)
        input := by
  rfl

theorem countWindowPostFieldDecodedPrefixStructuredBoolWordIndexedTargetTape_eq_materializerTargetTape
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    structuredBoolWordRawBitsDecoderIndexedInputMaterializerTargetTape
        (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordBits
          useAccept)
        (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSuffixTail
          useAccept)
        (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSourcePadding
          useAccept)
        (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordOutputPadding
          useAccept)
        input =
      structured3InputMaterializerTargetTape
        (countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource
          useAccept input)
        (countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputTape
          useAccept input) := by
  rfl

theorem countWindowPostFieldDecodedPrefixStructuredBoolWordIndexedTargetTape_read
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    Tape.read
        (structuredBoolWordRawBitsDecoderIndexedInputMaterializerTargetTape
          (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordBits
            useAccept)
          (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSuffixTail
            useAccept)
          (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSourcePadding
            useAccept)
          (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordOutputPadding
            useAccept)
          input) =
      none := by
  rfl

theorem countWindowPostFieldDecodedPrefixStructuredBoolWordIndexedTargetTape_cells_eq_materializerTargetTape_cells
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    Tape.cells
        (structuredBoolWordRawBitsDecoderIndexedInputMaterializerTargetTape
          (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordBits
            useAccept)
          (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSuffixTail
            useAccept)
          (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSourcePadding
            useAccept)
          (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordOutputPadding
            useAccept)
          input) =
      Tape.cells
        (structured3InputMaterializerTargetTape
          (countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource
            useAccept input)
          (countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputTape
            useAccept input)) := by
  rw [
    countWindowPostFieldDecodedPrefixStructuredBoolWordIndexedTargetTape_eq_materializerTargetTape]

theorem countWindowPostFieldDecodedPrefixStructuredBoolWordIndexedTargetTape_normalizedOutput_eq_materializerTargetTape
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    Tape.normalizedOutput
        (structuredBoolWordRawBitsDecoderIndexedInputMaterializerTargetTape
          (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordBits
            useAccept)
          (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSuffixTail
            useAccept)
          (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSourcePadding
            useAccept)
          (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordOutputPadding
            useAccept)
          input) =
      Tape.normalizedOutput
        (structured3InputMaterializerTargetTape
          (countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource
            useAccept input)
          (countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputTape
            useAccept input)) := by
  rw [
    countWindowPostFieldDecodedPrefixStructuredBoolWordIndexedTargetTape_eq_materializerTargetTape]

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
    structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputTape] using
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
    structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputTape] using
    hmaterializer

theorem countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec_iff_indexedSpec
    (useAccept : Bool) (initializer : MachineDescription) :
    CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec
        useAccept initializer ↔
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerSpec
        useAccept initializer := by
  constructor
  · exact
      countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerSpec_of_boolWordSpec
  · exact
      countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec_of_indexedSpec

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

theorem countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerConstruction_of_boolWord
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨initializer, hspec⟩
  exact
    ⟨initializer,
      countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerSpec_of_boolWordSpec
        hspec⟩

theorem countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerConstruction_iff_indexed :
    CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerConstruction ↔
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerConstruction := by
  constructor
  · exact
      countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerConstruction_of_boolWord
  · exact
      countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerConstruction_of_indexed

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

theorem countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec_of_inputSpec
    {useAccept : Bool} {initializer : MachineDescription}
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec
        useAccept initializer) :
    CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec
      useAccept initializer := by
  rcases hmaterializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro input
  rw [←
    countWindowPostFieldDecodedPrefixStructuredInputMaterializerSource_eq_boolWordSource
      useAccept input]
  exact hrun input

theorem countWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec_iff_boolWordSpec
    (useAccept : Bool) (initializer : MachineDescription) :
    CountWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec
        useAccept initializer ↔
      CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec
        useAccept initializer := by
  constructor
  · exact
      countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec_of_inputSpec
  · exact
      countWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec_of_boolWordSpec

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

theorem countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerConstruction_of_input
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨initializer, hspec⟩
  exact
    ⟨initializer,
      countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec_of_inputSpec
        hspec⟩

theorem countWindowPostFieldDecodedPrefixStructuredInputMaterializerConstruction_iff_boolWordConstruction :
    CountWindowPostFieldDecodedPrefixStructuredInputMaterializerConstruction ↔
      CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerConstruction := by
  constructor
  · exact
      countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerConstruction_of_input
  · exact
      countWindowPostFieldDecodedPrefixStructuredInputMaterializerConstruction_of_boolWord

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

theorem countWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec_of_initializerSpec
    {useAccept : Bool} {initializer : MachineDescription}
    (hinitializer :
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerSpec
        useAccept initializer) :
    CountWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec
      useAccept initializer := by
  rcases hinitializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro input
  simpa [
    CountWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec,
    countWindowPostFieldDecodedPrefixStructuredInputMaterializerSource,
    countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputTape,
    countWindowPostFieldDecodedPrefixStructuredEncodedInputTape,
    structured3InputMaterializerTargetTape] using
    hrun input.L input.pref input.leftBit input.deletedTail
      input.hdeleted input.hpayload

theorem countWindowPostFieldDecodedPrefixStructuredInputMaterializerConstruction_of_initializer
    (hinitializer :
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredInputMaterializerConstruction := by
  intro useAccept
  rcases hinitializer useAccept with ⟨initializer, hspec⟩
  exact
    ⟨initializer,
      countWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec_of_initializerSpec
        hspec⟩

theorem countWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec_iff_initializerSpec
    (useAccept : Bool) (initializer : MachineDescription) :
    CountWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec
        useAccept initializer ↔
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerSpec
        useAccept initializer := by
  constructor
  · exact
      countWindowPostFieldDecodedPrefixStructuredInputInitializerSpec_of_structured3InputMaterializerSpec
  · exact
      countWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec_of_initializerSpec

theorem countWindowPostFieldDecodedPrefixStructuredInputMaterializerConstruction_iff_initializerConstruction :
    CountWindowPostFieldDecodedPrefixStructuredInputMaterializerConstruction ↔
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction := by
  constructor
  · exact
      countWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction_of_structured3InputMaterializer
  · exact
      countWindowPostFieldDecodedPrefixStructuredInputMaterializerConstruction_of_initializer

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC

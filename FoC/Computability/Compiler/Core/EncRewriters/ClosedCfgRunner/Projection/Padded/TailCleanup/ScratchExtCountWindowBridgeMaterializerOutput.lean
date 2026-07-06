import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.BoolWordRawBitsDecoderInputMaterializerOutput
import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.TailCleanup.ScratchExtCountWindowBridgeMaterializerEndpoint
import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.TailCleanup.ScratchExtCountWindowBridgeOutput

set_option doc.verso true

/-!
# Count-window structured input materializer output endpoints

This module adapts the generic and bool-word raw-bits materializer output
contracts to the count-window decoded-prefix bridge.  The exact materializer
leaf remains in `ScratchExtCountWindowBridge.lean`; the output-level surface
here records the weaker endpoint used by later scratch-extension and padded
projection routes.
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

private theorem haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
    {D : MachineDescription} {Tin Tout : Tape Bool}
    (h : D.HaltsFromTapeEquiv Tin Tout) :
    D.HaltsFromTapeWithOutput Tin (Tape.normalizedOutput Tout) :=
  MachineDescription.haltsFromTapeWithOutput_of_haltsFromTapeEquiv h

def CountWindowPostFieldDecodedPrefixStructuredInputInitializerOutputSpec
    (useAccept : Bool) (initializer : MachineDescription) : Prop :=
  initializer.SubroutineReady ∧
    forall (L : DovetailLayout) (pref : Word Bool)
      (leftBit : Bool) (deletedTail : Word Bool),
      configurationFieldBits L.acceptConfig [] = false :: deletedTail ->
      countWindowPostFieldDecodedPrefixMaterializerPayload useAccept L =
          List.append pref [leftBit] ->
      initializer.HaltsFromTapeWithOutput
        (countWindowPostFieldDecodedPrefixMaterializerSourceTape
          useAccept L pref leftBit deletedTail)
        (Tape.normalizedOutput
          (countWindowPostFieldDecodedPrefixStructuredEncodedInputTape
            useAccept L pref leftBit deletedTail))

def CountWindowPostFieldDecodedPrefixStructuredInputInitializerOutputConstruction :
    Prop :=
  forall useAccept : Bool,
    exists initializer : MachineDescription,
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerOutputSpec
        useAccept initializer

def CountWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputSpec
    (useAccept : Bool) (initializer : MachineDescription) : Prop :=
  Structured3InputMaterializerOutputSpec
    (countWindowPostFieldDecodedPrefixStructuredInputMaterializerSource
      useAccept)
    (countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputTape
      useAccept)
    initializer

def CountWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputConstruction :
    Prop :=
  forall useAccept : Bool,
    exists initializer : MachineDescription,
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputSpec
        useAccept initializer

def CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputSpec
    (useAccept : Bool) (initializer : MachineDescription) : Prop :=
  Structured3InputMaterializerOutputSpec
    (countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource
      useAccept)
    (countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputTape
      useAccept)
    initializer

def CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputConstruction :
    Prop :=
  forall useAccept : Bool,
    exists initializer : MachineDescription,
      CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputSpec
        useAccept initializer

def CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerOutputSpec
    (useAccept : Bool) (initializer : MachineDescription) : Prop :=
  StructuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputSpec
    (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordBits
      useAccept)
    (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSuffixTail
      useAccept)
    (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSourcePadding
      useAccept)
    (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordOutputPadding
      useAccept)
    initializer

def CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerOutputConstruction :
    Prop :=
  forall useAccept : Bool,
    exists initializer : MachineDescription,
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerOutputSpec
        useAccept initializer

theorem countWindowPostFieldDecodedPrefixStructuredInputInitializerOutputSpec_of_exact
    {useAccept : Bool} {initializer : MachineDescription}
    (hinitializer :
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerSpec
        useAccept initializer) :
    CountWindowPostFieldDecodedPrefixStructuredInputInitializerOutputSpec
      useAccept initializer := by
  rcases hinitializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro L pref leftBit deletedTail hdeleted hpayload
  exact
    haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
      (hrun L pref leftBit deletedTail hdeleted hpayload)

theorem countWindowPostFieldDecodedPrefixStructuredInputInitializerOutputConstruction_of_exact
    (hinitializer :
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredInputInitializerOutputConstruction := by
  intro useAccept
  rcases hinitializer useAccept with ⟨initializer, hspec⟩
  exact
    ⟨initializer,
      countWindowPostFieldDecodedPrefixStructuredInputInitializerOutputSpec_of_exact
        hspec⟩

theorem countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputSpec_of_exact
    {useAccept : Bool} {initializer : MachineDescription}
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec
        useAccept initializer) :
    CountWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputSpec
      useAccept initializer := by
  exact structured3InputMaterializerOutputSpec_of_exact hmaterializer

theorem countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputConstruction_of_exact
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨initializer, hspec⟩
  exact
    ⟨initializer,
      countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputSpec_of_exact
        hspec⟩

theorem countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputSpec_of_exact
    {useAccept : Bool} {initializer : MachineDescription}
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec
        useAccept initializer) :
    CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputSpec
      useAccept initializer := by
  exact structured3InputMaterializerOutputSpec_of_exact hmaterializer

theorem countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputConstruction_of_exact
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨initializer, hspec⟩
  exact
    ⟨initializer,
      countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputSpec_of_exact
        hspec⟩

theorem countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerOutputSpec_of_exact
    {useAccept : Bool} {initializer : MachineDescription}
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerSpec
        useAccept initializer) :
    CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerOutputSpec
      useAccept initializer := by
  exact
    structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputSpec_of_exact
      hmaterializer

theorem countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerOutputConstruction_of_exact
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerOutputConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨initializer, hspec⟩
  exact
    ⟨initializer,
      countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerOutputSpec_of_exact
        hspec⟩

theorem countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputSpec_of_indexedSpec
    {useAccept : Bool} {initializer : MachineDescription}
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerOutputSpec
        useAccept initializer) :
    CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputSpec
      useAccept initializer := by
  simpa [
    CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputSpec,
    CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerOutputSpec,
    countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource,
    countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputTape,
    countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordBits,
    countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSuffixTail,
    countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSourcePadding,
    countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordOutputPadding,
    StructuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputSpec,
    structuredBoolWordRawBitsDecoderIndexedInputMaterializerSource,
    structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputTape] using
    hmaterializer

theorem countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerOutputSpec_of_boolWordSpec
    {useAccept : Bool} {initializer : MachineDescription}
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputSpec
        useAccept initializer) :
    CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerOutputSpec
      useAccept initializer := by
  simpa [
    CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputSpec,
    CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerOutputSpec,
    countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource,
    countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputTape,
    countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordBits,
    countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSuffixTail,
    countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSourcePadding,
    countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordOutputPadding,
    StructuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputSpec,
    structuredBoolWordRawBitsDecoderIndexedInputMaterializerSource,
    structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputTape] using
    hmaterializer

theorem countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputSpec_iff_indexedSpec
    (useAccept : Bool) (initializer : MachineDescription) :
    CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputSpec
        useAccept initializer ↔
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerOutputSpec
        useAccept initializer := by
  constructor
  · exact
      countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerOutputSpec_of_boolWordSpec
  · exact
      countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputSpec_of_indexedSpec

theorem countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputConstruction_of_indexed
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerOutputConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨initializer, hspec⟩
  exact
    ⟨initializer,
      countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputSpec_of_indexedSpec
        hspec⟩

theorem countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerOutputConstruction_of_boolWord
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerOutputConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨initializer, hspec⟩
  exact
    ⟨initializer,
      countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerOutputSpec_of_boolWordSpec
        hspec⟩

theorem countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputConstruction_iff_indexed :
    CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputConstruction ↔
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerOutputConstruction := by
  constructor
  · exact
      countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerOutputConstruction_of_boolWord
  · exact
      countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputConstruction_of_indexed

theorem countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputSpec_of_boolWordSpec
    {useAccept : Bool} {initializer : MachineDescription}
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputSpec
        useAccept initializer) :
    CountWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputSpec
      useAccept initializer := by
  rcases hmaterializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro input
  rw [
    countWindowPostFieldDecodedPrefixStructuredInputMaterializerSource_eq_boolWordSource
      useAccept input]
  exact hrun input

theorem countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputSpec_of_inputSpec
    {useAccept : Bool} {initializer : MachineDescription}
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputSpec
        useAccept initializer) :
    CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputSpec
      useAccept initializer := by
  rcases hmaterializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro input
  rw [←
    countWindowPostFieldDecodedPrefixStructuredInputMaterializerSource_eq_boolWordSource
      useAccept input]
  exact hrun input

theorem countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputSpec_iff_boolWordSpec
    (useAccept : Bool) (initializer : MachineDescription) :
    CountWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputSpec
        useAccept initializer ↔
      CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputSpec
        useAccept initializer := by
  constructor
  · exact
      countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputSpec_of_inputSpec
  · exact
      countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputSpec_of_boolWordSpec

theorem countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputConstruction_of_boolWord
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨initializer, hspec⟩
  exact
    ⟨initializer,
      countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputSpec_of_boolWordSpec
        hspec⟩

theorem countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputConstruction_of_input
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨initializer, hspec⟩
  exact
    ⟨initializer,
      countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputSpec_of_inputSpec
        hspec⟩

theorem countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputConstruction_iff_boolWordConstruction :
    CountWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputConstruction ↔
      CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputConstruction := by
  constructor
  · exact
      countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputConstruction_of_input
  · exact
      countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputConstruction_of_boolWord

theorem countWindowPostFieldDecodedPrefixStructuredInputInitializerOutputSpec_of_structured3InputMaterializerOutputSpec
    {useAccept : Bool} {initializer : MachineDescription}
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputSpec
        useAccept initializer) :
    CountWindowPostFieldDecodedPrefixStructuredInputInitializerOutputSpec
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
    CountWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputSpec,
    countWindowPostFieldDecodedPrefixStructuredInputMaterializerSource,
    countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputTape,
    countWindowPostFieldDecodedPrefixStructuredEncodedInputTape,
    structured3InputMaterializerTargetTape] using
    hrun input

theorem countWindowPostFieldDecodedPrefixStructuredInputInitializerOutputConstruction_of_structured3InputMaterializerOutput
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredInputInitializerOutputConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨initializer, hspec⟩
  exact
    ⟨initializer,
      countWindowPostFieldDecodedPrefixStructuredInputInitializerOutputSpec_of_structured3InputMaterializerOutputSpec
        hspec⟩

theorem countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputSpec_of_initializerOutputSpec
    {useAccept : Bool} {initializer : MachineDescription}
    (hinitializer :
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerOutputSpec
        useAccept initializer) :
    CountWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputSpec
      useAccept initializer := by
  rcases hinitializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro input
  simpa [
    CountWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputSpec,
    countWindowPostFieldDecodedPrefixStructuredInputMaterializerSource,
    countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputTape,
    countWindowPostFieldDecodedPrefixStructuredEncodedInputTape,
    structured3InputMaterializerTargetTape] using
    hrun input.L input.pref input.leftBit input.deletedTail
      input.hdeleted input.hpayload

theorem countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputConstruction_of_initializerOutput
    (hinitializer :
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerOutputConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputConstruction := by
  intro useAccept
  rcases hinitializer useAccept with ⟨initializer, hspec⟩
  exact
    ⟨initializer,
      countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputSpec_of_initializerOutputSpec
        hspec⟩

theorem countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputSpec_iff_initializerOutputSpec
    (useAccept : Bool) (initializer : MachineDescription) :
    CountWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputSpec
        useAccept initializer ↔
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerOutputSpec
        useAccept initializer := by
  constructor
  · exact
      countWindowPostFieldDecodedPrefixStructuredInputInitializerOutputSpec_of_structured3InputMaterializerOutputSpec
  · exact
      countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputSpec_of_initializerOutputSpec

theorem countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputConstruction_iff_initializerOutputConstruction :
    CountWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputConstruction ↔
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerOutputConstruction := by
  constructor
  · exact
      countWindowPostFieldDecodedPrefixStructuredInputInitializerOutputConstruction_of_structured3InputMaterializerOutput
  · exact
      countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputConstruction_of_initializerOutput

theorem countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputConstruction_core :
    CountWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputConstruction :=
  countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputConstruction_of_exact
    countWindowPostFieldDecodedPrefixStructuredInputMaterializerConstruction_core

theorem countWindowPostFieldDecodedPrefixStructuredInputInitializerOutputConstruction_core :
    CountWindowPostFieldDecodedPrefixStructuredInputInitializerOutputConstruction :=
  countWindowPostFieldDecodedPrefixStructuredInputInitializerOutputConstruction_of_structured3InputMaterializerOutput
    countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputConstruction_core

theorem countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputConstruction_core :
    CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputConstruction :=
  countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputConstruction_of_exact
    countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerConstruction_core

theorem countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerOutputConstruction_core :
    CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerOutputConstruction :=
  countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerOutputConstruction_of_exact
    countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerConstruction_core

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters
end Computability
end FoC

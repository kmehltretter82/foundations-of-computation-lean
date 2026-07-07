import FoC.Computability.Compiler.FST.BoolRawInput.EndpointContracts
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredInputMaterializerOutput

set_option doc.verso true

/-!
# Bool-word raw-bits input materializer output contracts

This module specializes the generic structured-input materializer output
contracts to the Boolean-word raw-bits decoder source families.  These contracts
are weaker views of the exact initializer/materializer interfaces in
`BoolWordRawBitsDecoder.lean`; they are useful for bridge layers that only
consume the emitted encoded structured input word.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open EncRewriters.CanonicalLayouts.DovetailLayoutScanner

namespace CommonGround
namespace FiniteTransducers

private theorem haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
    {D : MachineDescription} {Tin Tout : Tape Bool}
    (h : D.HaltsFromTapeEquiv Tin Tout) :
    D.HaltsFromTapeWithOutput Tin (Tape.normalizedOutput Tout) :=
  MachineDescription.haltsFromTapeWithOutput_of_haltsFromTapeEquiv h

def StructuredBoolWordRawBitsDecoderCanonicalInputInitializerOutputSpec
    (initializer : MachineDescription) : Prop :=
  initializer.SubroutineReady ∧
    forall bits suffixTail : Word Bool,
      initializer.HaltsFromTapeWithOutput
        (structuredBoolWordRawBitsDecoderCanonicalSourceTape
          bits suffixTail)
        (Tape.normalizedOutput
          (structuredBoolWordRawBitsDecoderCanonicalInputInitializerTargetTape
            bits suffixTail))

def StructuredBoolWordRawBitsDecoderCanonicalInputInitializerOutputConstruction :
    Prop :=
  exists initializer : MachineDescription,
    StructuredBoolWordRawBitsDecoderCanonicalInputInitializerOutputSpec
      initializer

def StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputSpec
    (initializer : MachineDescription) : Prop :=
  Structured3InputMaterializerOutputSpec
    structuredBoolWordRawBitsDecoderCanonicalInputMaterializerSource
    structuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputTape
    initializer

def StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputConstruction :
    Prop :=
  Structured3InputMaterializerOutputConstruction
    structuredBoolWordRawBitsDecoderCanonicalInputMaterializerSource
    structuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputTape

theorem structuredBoolWordRawBitsDecoderCanonicalInputInitializerOutputSpec_of_exact
    {initializer : MachineDescription}
    (hinitializer :
      StructuredBoolWordRawBitsDecoderCanonicalInputInitializerSpec
        initializer) :
    StructuredBoolWordRawBitsDecoderCanonicalInputInitializerOutputSpec
      initializer := by
  rcases hinitializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro bits suffixTail
  exact haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
    (hrun bits suffixTail)

theorem structuredBoolWordRawBitsDecoderCanonicalInputInitializerOutputConstruction_of_exact
    (hinitializer :
      StructuredBoolWordRawBitsDecoderCanonicalInputInitializerConstruction) :
    StructuredBoolWordRawBitsDecoderCanonicalInputInitializerOutputConstruction := by
  rcases hinitializer with ⟨initializer, hspec⟩
  exact
    ⟨initializer,
      structuredBoolWordRawBitsDecoderCanonicalInputInitializerOutputSpec_of_exact
        hspec⟩

theorem structuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputSpec_of_exact
    {initializer : MachineDescription}
    (hmaterializer :
      StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerSpec
        initializer) :
    StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputSpec
      initializer := by
  exact structured3InputMaterializerOutputSpec_of_exact hmaterializer

theorem structuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputConstruction_of_exact
    (hmaterializer :
      StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerConstruction) :
    StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputConstruction := by
  exact structured3InputMaterializerOutputConstruction_of_exact hmaterializer

theorem structuredBoolWordRawBitsDecoderCanonicalInputInitializerOutputSpec_of_materializerOutputSpec
    {initializer : MachineDescription}
    (hmaterializer :
      StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputSpec
        initializer) :
    StructuredBoolWordRawBitsDecoderCanonicalInputInitializerOutputSpec
      initializer := by
  rcases hmaterializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro bits suffixTail
  simpa [
    StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputSpec,
    structuredBoolWordRawBitsDecoderCanonicalInputMaterializerSource,
    structuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputTape,
    structuredBoolWordRawBitsDecoderCanonicalInputInitializerTargetTape,
    structuredBoolWordRawBitsDecoderInputInitializerTargetTape,
    structured3InputMaterializerTargetTape] using
    hrun (bits, suffixTail)

theorem structuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputSpec_of_initializerOutputSpec
    {initializer : MachineDescription}
    (hinitializer :
      StructuredBoolWordRawBitsDecoderCanonicalInputInitializerOutputSpec
        initializer) :
    StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputSpec
      initializer := by
  rcases hinitializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro input
  rcases input with ⟨bits, suffixTail⟩
  simpa [
    StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputSpec,
    structuredBoolWordRawBitsDecoderCanonicalInputMaterializerSource,
    structuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputTape,
    structuredBoolWordRawBitsDecoderCanonicalInputInitializerTargetTape,
    structuredBoolWordRawBitsDecoderInputInitializerTargetTape,
    structured3InputMaterializerTargetTape] using
    hrun bits suffixTail

theorem structuredBoolWordRawBitsDecoderCanonicalInputInitializerOutputConstruction_of_materializerOutput
    (hmaterializer :
      StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputConstruction) :
    StructuredBoolWordRawBitsDecoderCanonicalInputInitializerOutputConstruction := by
  rcases hmaterializer with ⟨initializer, hspec⟩
  exact
    ⟨initializer,
      structuredBoolWordRawBitsDecoderCanonicalInputInitializerOutputSpec_of_materializerOutputSpec
        hspec⟩

theorem structuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputConstruction_of_initializerOutput
    (hinitializer :
      StructuredBoolWordRawBitsDecoderCanonicalInputInitializerOutputConstruction) :
    StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputConstruction := by
  rcases hinitializer with ⟨initializer, hspec⟩
  exact
    ⟨initializer,
      structuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputSpec_of_initializerOutputSpec
        hspec⟩

theorem structuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputConstruction_iff_initializerOutputConstruction :
    StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputConstruction ↔
      StructuredBoolWordRawBitsDecoderCanonicalInputInitializerOutputConstruction := by
  constructor
  · exact
      structuredBoolWordRawBitsDecoderCanonicalInputInitializerOutputConstruction_of_materializerOutput
  · exact
      structuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputConstruction_of_initializerOutput

def StructuredBoolWordRawBitsDecoderIndexedInputInitializerOutputSpec
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (initializer : MachineDescription) : Prop :=
  initializer.SubroutineReady ∧
    forall input : ι,
      initializer.HaltsFromTapeWithOutput
        (structuredBoolWordRawBitsDecoderIndexedInputMaterializerSource
          bits suffixTail rightPadding input)
        (Tape.normalizedOutput
          (structuredBoolWordRawBitsDecoderIndexedInputMaterializerTargetTape
            bits suffixTail rightPadding outputPadding input))

def StructuredBoolWordRawBitsDecoderIndexedInputInitializerOutputConstruction
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool)) :
    Prop :=
  exists initializer : MachineDescription,
    StructuredBoolWordRawBitsDecoderIndexedInputInitializerOutputSpec
      bits suffixTail rightPadding outputPadding initializer

def StructuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputSpec
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (initializer : MachineDescription) : Prop :=
  Structured3InputMaterializerOutputSpec
    (structuredBoolWordRawBitsDecoderIndexedInputMaterializerSource
      bits suffixTail rightPadding)
    (structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputTape
      bits outputPadding)
    initializer

def StructuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputConstruction
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool)) :
    Prop :=
  Structured3InputMaterializerOutputConstruction
    (structuredBoolWordRawBitsDecoderIndexedInputMaterializerSource
      bits suffixTail rightPadding)
    (structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputTape
      bits outputPadding)

theorem structuredBoolWordRawBitsDecoderIndexedInputInitializerOutputSpec_of_exact
    {ι : Type}
    {bits suffixTail : ι -> Word Bool}
    {rightPadding outputPadding : ι -> List (Option Bool)}
    {initializer : MachineDescription}
    (hinitializer :
      StructuredBoolWordRawBitsDecoderIndexedInputInitializerSpec
        bits suffixTail rightPadding outputPadding initializer) :
    StructuredBoolWordRawBitsDecoderIndexedInputInitializerOutputSpec
      bits suffixTail rightPadding outputPadding initializer := by
  rcases hinitializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro input
  exact haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
    (hrun input)

theorem structuredBoolWordRawBitsDecoderIndexedInputInitializerOutputConstruction_of_exact
    {ι : Type}
    {bits suffixTail : ι -> Word Bool}
    {rightPadding outputPadding : ι -> List (Option Bool)}
    (hinitializer :
      StructuredBoolWordRawBitsDecoderIndexedInputInitializerConstruction
        bits suffixTail rightPadding outputPadding) :
    StructuredBoolWordRawBitsDecoderIndexedInputInitializerOutputConstruction
      bits suffixTail rightPadding outputPadding := by
  rcases hinitializer with ⟨initializer, hspec⟩
  exact
    ⟨initializer,
      structuredBoolWordRawBitsDecoderIndexedInputInitializerOutputSpec_of_exact
        hspec⟩

theorem structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputSpec_of_exact
    {ι : Type}
    {bits suffixTail : ι -> Word Bool}
    {rightPadding outputPadding : ι -> List (Option Bool)}
    {initializer : MachineDescription}
    (hmaterializer :
      StructuredBoolWordRawBitsDecoderIndexedInputMaterializerSpec
        bits suffixTail rightPadding outputPadding initializer) :
    StructuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputSpec
      bits suffixTail rightPadding outputPadding initializer := by
  exact structured3InputMaterializerOutputSpec_of_exact hmaterializer

theorem structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputConstruction_of_exact
    {ι : Type}
    {bits suffixTail : ι -> Word Bool}
    {rightPadding outputPadding : ι -> List (Option Bool)}
    (hmaterializer :
      StructuredBoolWordRawBitsDecoderIndexedInputMaterializerConstruction
        bits suffixTail rightPadding outputPadding) :
    StructuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputConstruction
      bits suffixTail rightPadding outputPadding := by
  exact structured3InputMaterializerOutputConstruction_of_exact hmaterializer

theorem structuredBoolWordRawBitsDecoderIndexedInputInitializerOutputSpec_of_materializerOutputSpec
    {ι : Type}
    {bits suffixTail : ι -> Word Bool}
    {rightPadding outputPadding : ι -> List (Option Bool)}
    {initializer : MachineDescription}
    (hmaterializer :
      StructuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputSpec
        bits suffixTail rightPadding outputPadding initializer) :
    StructuredBoolWordRawBitsDecoderIndexedInputInitializerOutputSpec
      bits suffixTail rightPadding outputPadding initializer := by
  rcases hmaterializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro input
  simpa [
    StructuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputSpec,
    StructuredBoolWordRawBitsDecoderIndexedInputInitializerOutputSpec,
    structuredBoolWordRawBitsDecoderIndexedInputMaterializerSource,
    structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputTape,
    structuredBoolWordRawBitsDecoderIndexedInputMaterializerTargetTape,
    structuredBoolWordRawBitsDecoderInputInitializerTargetTape,
    structured3InputMaterializerTargetTape] using
    hrun input

theorem structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputSpec_of_initializerOutputSpec
    {ι : Type}
    {bits suffixTail : ι -> Word Bool}
    {rightPadding outputPadding : ι -> List (Option Bool)}
    {initializer : MachineDescription}
    (hinitializer :
      StructuredBoolWordRawBitsDecoderIndexedInputInitializerOutputSpec
        bits suffixTail rightPadding outputPadding initializer) :
    StructuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputSpec
      bits suffixTail rightPadding outputPadding initializer := by
  rcases hinitializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro input
  simpa [
    StructuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputSpec,
    StructuredBoolWordRawBitsDecoderIndexedInputInitializerOutputSpec,
    structuredBoolWordRawBitsDecoderIndexedInputMaterializerSource,
    structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputTape,
    structuredBoolWordRawBitsDecoderIndexedInputMaterializerTargetTape,
    structuredBoolWordRawBitsDecoderInputInitializerTargetTape,
    structured3InputMaterializerTargetTape] using
    hrun input

theorem structuredBoolWordRawBitsDecoderIndexedInputInitializerOutputConstruction_of_materializerOutput
    {ι : Type}
    {bits suffixTail : ι -> Word Bool}
    {rightPadding outputPadding : ι -> List (Option Bool)}
    (hmaterializer :
      StructuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputConstruction
        bits suffixTail rightPadding outputPadding) :
    StructuredBoolWordRawBitsDecoderIndexedInputInitializerOutputConstruction
      bits suffixTail rightPadding outputPadding := by
  rcases hmaterializer with ⟨initializer, hspec⟩
  exact
    ⟨initializer,
      structuredBoolWordRawBitsDecoderIndexedInputInitializerOutputSpec_of_materializerOutputSpec
        hspec⟩

theorem structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputConstruction_of_initializerOutput
    {ι : Type}
    {bits suffixTail : ι -> Word Bool}
    {rightPadding outputPadding : ι -> List (Option Bool)}
    (hinitializer :
      StructuredBoolWordRawBitsDecoderIndexedInputInitializerOutputConstruction
        bits suffixTail rightPadding outputPadding) :
    StructuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputConstruction
      bits suffixTail rightPadding outputPadding := by
  rcases hinitializer with ⟨initializer, hspec⟩
  exact
    ⟨initializer,
      structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputSpec_of_initializerOutputSpec
        hspec⟩

theorem structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputConstruction_iff_initializerOutputConstruction
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool)) :
    StructuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputConstruction
        bits suffixTail rightPadding outputPadding ↔
      StructuredBoolWordRawBitsDecoderIndexedInputInitializerOutputConstruction
        bits suffixTail rightPadding outputPadding := by
  constructor
  · exact
      structuredBoolWordRawBitsDecoderIndexedInputInitializerOutputConstruction_of_materializerOutput
  · exact
      structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputConstruction_of_initializerOutput

theorem structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputSpec_of_eq
    {ι : Type}
    {bits suffixTail bits' suffixTail' : ι -> Word Bool}
    {rightPadding outputPadding rightPadding' outputPadding' :
      ι -> List (Option Bool)}
    {initializer : MachineDescription}
    (hmaterializer :
      StructuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputSpec
        bits suffixTail rightPadding outputPadding initializer)
    (hbits : forall input : ι, bits' input = bits input)
    (hsuffixTail :
      forall input : ι, suffixTail' input = suffixTail input)
    (hrightPadding :
      forall input : ι, rightPadding' input = rightPadding input)
    (houtputPadding :
      forall input : ι, outputPadding' input = outputPadding input) :
    StructuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputSpec
      bits' suffixTail' rightPadding' outputPadding' initializer := by
  exact
    structured3InputMaterializerOutputSpec_of_eq hmaterializer
      (fun input => by
        simp [
          structuredBoolWordRawBitsDecoderIndexedInputMaterializerSource,
          hbits input, hsuffixTail input, hrightPadding input])
      (fun input => by
        simp [
          structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputTape,
          hbits input, houtputPadding input])

theorem structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputConstruction_of_eq
    {ι : Type}
    {bits suffixTail bits' suffixTail' : ι -> Word Bool}
    {rightPadding outputPadding rightPadding' outputPadding' :
      ι -> List (Option Bool)}
    (hmaterializer :
      StructuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputConstruction
        bits suffixTail rightPadding outputPadding)
    (hbits : forall input : ι, bits' input = bits input)
    (hsuffixTail :
      forall input : ι, suffixTail' input = suffixTail input)
    (hrightPadding :
      forall input : ι, rightPadding' input = rightPadding input)
    (houtputPadding :
      forall input : ι, outputPadding' input = outputPadding input) :
    StructuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputConstruction
      bits' suffixTail' rightPadding' outputPadding' := by
  rcases hmaterializer with ⟨initializer, hspec⟩
  exact
    ⟨initializer,
      structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputSpec_of_eq
        hspec hbits hsuffixTail hrightPadding houtputPadding⟩

theorem structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputSpec_reindex
    {ι κ : Type}
    {bits suffixTail : ι -> Word Bool}
    {rightPadding outputPadding : ι -> List (Option Bool)}
    {initializer : MachineDescription}
    (hmaterializer :
      StructuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputSpec
        bits suffixTail rightPadding outputPadding initializer)
    (index : κ -> ι) :
    StructuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputSpec
      (fun input : κ => bits (index input))
      (fun input : κ => suffixTail (index input))
      (fun input : κ => rightPadding (index input))
      (fun input : κ => outputPadding (index input))
      initializer := by
  exact structured3InputMaterializerOutputSpec_reindex hmaterializer index

theorem structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputConstruction_reindex
    {ι κ : Type}
    {bits suffixTail : ι -> Word Bool}
    {rightPadding outputPadding : ι -> List (Option Bool)}
    (hmaterializer :
      StructuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputConstruction
        bits suffixTail rightPadding outputPadding)
    (index : κ -> ι) :
    StructuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputConstruction
      (fun input : κ => bits (index input))
      (fun input : κ => suffixTail (index input))
      (fun input : κ => rightPadding (index input))
      (fun input : κ => outputPadding (index input)) := by
  rcases hmaterializer with ⟨initializer, hspec⟩
  exact
    ⟨initializer,
      structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputSpec_reindex
        hspec index⟩

end FiniteTransducers
end CommonGround
end Computability
end FoC

import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.BoolWordRawBitsDecoder.StructuredBody

set_option doc.verso true

/-!
# Boolean-word raw-bits endpoint adapters

Input materializer, endpoint, and prefix-scanner adapters for the structured raw-bits decoder body.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open EncRewriters.CanonicalLayouts.DovetailLayoutScanner
open DovetailInitialLayoutInitializer.StageInputMarkedScanner

namespace CommonGround
namespace FiniteTransducers

open Structured.MultiTapeLowering.ThreeTape

/-!
The input initializer is the structured endpoint boundary for this decoder.
The structured body starts from three logical tapes; any public one-tape source
must first be materialized as a guarded structured encoding before the lowered
structured decoder is composed with it.
-/

/--
Legacy over-general input-initializer contract.

This contract is intentionally kept only as a guardrail target: it quantifies
over arbitrary physical source right padding and arbitrary output padding, and
{lit}`structuredBoolWordRawBitsDecoderInputInitializerConstruction_impossible`
proves that no deterministic initializer can satisfy it.  New construction
work should use
{lit}`StructuredBoolWordRawBitsDecoderCanonicalInputInitializerSpec`.
-/
def StructuredBoolWordRawBitsDecoderInputInitializerSpec
    (initializer : MachineDescription) : Prop :=
  initializer.SubroutineReady ∧
    forall (bits suffixTail : Word Bool)
      (rightPadding outputPadding : List (Option Bool)),
      initializer.HaltsFromTapeEquiv
        (boolWordRawBitsDecoderSourceTape bits suffixTail rightPadding)
        (structuredBoolWordRawBitsDecoderInputInitializerTargetTape
          bits suffixTail rightPadding outputPadding)

def StructuredBoolWordRawBitsDecoderInputInitializerConstruction : Prop :=
  exists initializer : MachineDescription,
    StructuredBoolWordRawBitsDecoderInputInitializerSpec initializer

/--
The uniform input-initializer contract is over-quantified.

For the same empty source tape, it requires one halt-transition-free machine
to halt equivalently to two guarded structured encodings that differ by a
meaningful nonblank tape-2 padding cell. Determinism forces the actual halted
tape to be the same, while {name}`Tape.Equiv` preserves normalized output.
-/
theorem structuredBoolWordRawBitsDecoderInputInitializerConstruction_impossible :
    ¬ StructuredBoolWordRawBitsDecoderInputInitializerConstruction := by
  rintro ⟨initializer, hinitializerReady, hinitializerRun⟩
  let Tnil : Tape Bool :=
    Structured.MultiTapeLowering.encodedGuardedStructuredTapes
      [ boolWordRawBitsDecoderSourceTape ([] : Word Bool) [] []
      , Tape.blank
      , structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding 0 [] ]
  let Tone : Tape Bool :=
    Structured.MultiTapeLowering.encodedGuardedStructuredTapes
      [ boolWordRawBitsDecoderSourceTape ([] : Word Bool) [] []
      , Tape.blank
      , structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
          0 [some true] ]
  rcases hinitializerRun ([] : Word Bool) [] [] [] with
    ⟨actualNil, hhaltNil, hequivNil⟩
  rcases hinitializerRun ([] : Word Bool) [] [] [some true] with
    ⟨actualOne, hhaltOne, hequivOne⟩
  have hactual : actualNil = actualOne :=
    MachineDescription.haltsFromTape_functional_of_haltTransitionFree
      hinitializerReady.right hhaltNil hhaltOne
  have htargets : Tape.Equiv Tnil Tone := by
    exact
      Tape.Equiv.trans (Tape.Equiv.symm hequivNil)
        (by simpa [hactual] using hequivOne)
  have hnorm := Tape.Equiv.normalizedOutput_eq htargets
  have hne : Tape.normalizedOutput Tnil ≠ Tape.normalizedOutput Tone := by
    decide
  exact hne hnorm

/--
Input initializer contract for a fixed tape-2 output padding.

This is weaker than
{name}`StructuredBoolWordRawBitsDecoderInputInitializerSpec`: the machine may
depend on the padding it must preload.  The contract still preserves arbitrary
explicit source right padding, which is too exact for a public one-tape
initializer; see
{lit}`structuredBoolWordRawBitsDecoderFixedOutputPaddingNilInputInitializerConstruction_impossible`.
-/
def StructuredBoolWordRawBitsDecoderFixedOutputPaddingInputInitializerSpec
    (outputPadding : List (Option Bool))
    (initializer : MachineDescription) : Prop :=
  initializer.SubroutineReady ∧
    forall (bits suffixTail : Word Bool)
      (rightPadding : List (Option Bool)),
      initializer.HaltsFromTapeEquiv
        (boolWordRawBitsDecoderSourceTape bits suffixTail rightPadding)
        (structuredBoolWordRawBitsDecoderInputInitializerTargetTape
          bits suffixTail rightPadding outputPadding)

def StructuredBoolWordRawBitsDecoderFixedOutputPaddingInputInitializerConstruction
    (outputPadding : List (Option Bool)) : Prop :=
  exists initializer : MachineDescription,
    StructuredBoolWordRawBitsDecoderFixedOutputPaddingInputInitializerSpec
      outputPadding initializer

private theorem boolWordRawBitsDecoderSourceTape_empty_rightPadding_none_equiv :
    Tape.Equiv
      (boolWordRawBitsDecoderSourceTape ([] : Word Bool) [] [])
      (boolWordRawBitsDecoderSourceTape ([] : Word Bool) [] [none]) := by
  simp [boolWordRawBitsDecoderSourceTape, rightEdgeRewindTargetTape,
    boolWordRawBitsDecoderHeaderBits,
    boolWordRawBitsDecoderEncodedFieldBits, stageNatBits_zero,
    cellsCodeBits, encodeCodeSymbolAsInput,
    tapeAtCells, Tape.Equiv, Tape.dropTrailingNone]

/--
Even the empty fixed-padding initializer contract still preserves too much
physical padding information: the public source tapes with no explicit right
padding and with one explicit blank right-padding cell are operationally
equivalent, but the guarded structured target encodes that extra blank as
meaningful physical Boolean cells.
-/
theorem structuredBoolWordRawBitsDecoderFixedOutputPaddingNilInputInitializerConstruction_impossible :
    ¬ StructuredBoolWordRawBitsDecoderFixedOutputPaddingInputInitializerConstruction
      [] := by
  rintro ⟨initializer, hinitializerReady, hinitializerRun⟩
  let Tnil : Tape Bool :=
    structuredBoolWordRawBitsDecoderInputInitializerTargetTape
      ([] : Word Bool) [] [] []
  let Tpad : Tape Bool :=
    structuredBoolWordRawBitsDecoderInputInitializerTargetTape
      ([] : Word Bool) [] [none] []
  rcases hinitializerRun ([] : Word Bool) [] [] with
    ⟨actualNil, hhaltNil, hequivNil⟩
  rcases
      MachineDescription.HaltsFromTapeEquiv_of_input_equiv
        boolWordRawBitsDecoderSourceTape_empty_rightPadding_none_equiv
        hhaltNil with
    ⟨actualFromPad, hhaltFromPad, hequivFromPad⟩
  rcases hinitializerRun ([] : Word Bool) [] [none] with
    ⟨actualPad, hhaltPad, hequivPad⟩
  have hactual : actualFromPad = actualPad :=
    MachineDescription.haltsFromTape_functional_of_haltTransitionFree
      hinitializerReady.right hhaltFromPad hhaltPad
  have hactualToPadTarget : Tape.Equiv actualFromPad Tpad := by
    simpa [hactual] using hequivPad
  have htargets : Tape.Equiv Tnil Tpad := by
    exact
      Tape.Equiv.trans
        (Tape.Equiv.symm
          (Tape.Equiv.trans hequivFromPad hequivNil))
        hactualToPadTarget
  have hnorm := Tape.Equiv.normalizedOutput_eq htargets
  have hne : Tape.normalizedOutput Tnil ≠ Tape.normalizedOutput Tpad := by
    decide
  exact hne hnorm

/--
Input initializer contract for the deterministic public-decoder padding.

Here tape-2 padding is not arbitrary: it is the deterministic suffix preserved
from the source tape.  This is still too exact for a public one-tape
initializer while arbitrary explicit right padding remains part of the target;
see
{lit}`structuredBoolWordRawBitsDecoderPreservedPaddingInputInitializerConstruction_impossible`.
-/
def StructuredBoolWordRawBitsDecoderPreservedPaddingInputInitializerSpec
    (initializer : MachineDescription) : Prop :=
  initializer.SubroutineReady ∧
    forall (bits suffixTail : Word Bool)
      (rightPadding : List (Option Bool)),
      initializer.HaltsFromTapeEquiv
        (boolWordRawBitsDecoderSourceTape bits suffixTail rightPadding)
        (structuredBoolWordRawBitsDecoderInputInitializerTargetTape
          bits suffixTail rightPadding
          (boolWordRawBitsDecoderPreservedPadding suffixTail
            rightPadding))

def StructuredBoolWordRawBitsDecoderPreservedPaddingInputInitializerConstruction :
    Prop :=
  exists initializer : MachineDescription,
    StructuredBoolWordRawBitsDecoderPreservedPaddingInputInitializerSpec
      initializer

/--
The preserved-padding initializer contract is also too exact as stated.  It
asks a public one-tape initializer to materialize explicit trailing blank
padding inside the guarded structured representation, but explicit trailing
blank padding is not observable by the machine beyond {name}`Tape.Equiv`.
-/
theorem structuredBoolWordRawBitsDecoderPreservedPaddingInputInitializerConstruction_impossible :
    ¬ StructuredBoolWordRawBitsDecoderPreservedPaddingInputInitializerConstruction := by
  rintro ⟨initializer, hinitializerReady, hinitializerRun⟩
  let Tnil : Tape Bool :=
    structuredBoolWordRawBitsDecoderInputInitializerTargetTape
      ([] : Word Bool) [] []
      (boolWordRawBitsDecoderPreservedPadding [] [])
  let Tpad : Tape Bool :=
    structuredBoolWordRawBitsDecoderInputInitializerTargetTape
      ([] : Word Bool) [] [none]
      (boolWordRawBitsDecoderPreservedPadding [] [none])
  rcases hinitializerRun ([] : Word Bool) [] [] with
    ⟨actualNil, hhaltNil, hequivNil⟩
  rcases
      MachineDescription.HaltsFromTapeEquiv_of_input_equiv
        boolWordRawBitsDecoderSourceTape_empty_rightPadding_none_equiv
        hhaltNil with
    ⟨actualFromPad, hhaltFromPad, hequivFromPad⟩
  rcases hinitializerRun ([] : Word Bool) [] [none] with
    ⟨actualPad, hhaltPad, hequivPad⟩
  have hactual : actualFromPad = actualPad :=
    MachineDescription.haltsFromTape_functional_of_haltTransitionFree
      hinitializerReady.right hhaltFromPad hhaltPad
  have hactualToPadTarget : Tape.Equiv actualFromPad Tpad := by
    simpa [hactual] using hequivPad
  have htargets : Tape.Equiv Tnil Tpad := by
    exact
      Tape.Equiv.trans
        (Tape.Equiv.symm
          (Tape.Equiv.trans hequivFromPad hequivNil))
        hactualToPadTarget
  have hnorm := Tape.Equiv.normalizedOutput_eq htargets
  have hne : Tape.normalizedOutput Tnil ≠ Tape.normalizedOutput Tpad := by
    decide
  exact hne hnorm

def structuredBoolWordRawBitsDecoderCanonicalSourceTape
    (bits suffixTail : Word Bool) : Tape Bool :=
  boolWordRawBitsDecoderSourceTape bits suffixTail []

theorem structuredBoolWordRawBitsDecoderCanonicalSourceTape_cells
    (bits suffixTail : Word Bool) :
    Tape.cells
        (structuredBoolWordRawBitsDecoderCanonicalSourceTape
          bits suffixTail) =
      none ::
        List.append
          ((List.append boolWordRawBitsDecoderHeaderBits
            (List.append
              (boolWordRawBitsDecoderEncodedFieldBits bits)
              (false :: suffixTail))).map some)
          [none] := by
  simpa [structuredBoolWordRawBitsDecoderCanonicalSourceTape] using
    boolWordRawBitsDecoderSourceTape_cells bits suffixTail []

def structuredBoolWordRawBitsDecoderCanonicalInputInitializerTargetTape
    (bits suffixTail : Word Bool) : Tape Bool :=
  structuredBoolWordRawBitsDecoderInputInitializerTargetTape
    bits suffixTail []
    (boolWordRawBitsDecoderPreservedPadding suffixTail [])

theorem structuredBoolWordRawBitsDecoderCanonicalInitialOutputTape_cells
    (bits suffixTail : Word Bool) :
    Tape.cells
        (structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
          bits.length
          (boolWordRawBitsDecoderPreservedPadding suffixTail [])) =
      none ::
        List.append
          (List.replicate (bits.length + 1) (none : Option Bool))
          (List.append ((false :: suffixTail).map some) [none]) := by
  simp [structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding_cells,
    boolWordRawBitsDecoderPreservedPadding]

theorem structuredBoolWordRawBitsDecoderCanonicalInputInitializerTargetTape_cells
    (bits suffixTail : Word Bool) :
    Tape.cells
        (structuredBoolWordRawBitsDecoderCanonicalInputInitializerTargetTape
          bits suffixTail) =
      List.append Structured.MultiTapeLowering.tapeSeparatorCells
        (List.append
          (Structured.MultiTapeLowering.logicalTapeCode
            (Structured.MultiTapeLowering.guardLogicalTape
              (structuredBoolWordRawBitsDecoderCanonicalSourceTape
                bits suffixTail)))
          (List.append Structured.MultiTapeLowering.tapeSeparatorCells
            (List.append
              (Structured.MultiTapeLowering.logicalTapeCode
                (Structured.MultiTapeLowering.guardLogicalTape Tape.blank))
              (List.append
                Structured.MultiTapeLowering.tapeSeparatorCells
                (List.append
                  (Structured.MultiTapeLowering.logicalTapeCode
                    (Structured.MultiTapeLowering.guardLogicalTape
                      (structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
                        bits.length
                        (boolWordRawBitsDecoderPreservedPadding suffixTail []))))
                  Structured.MultiTapeLowering.tapeSeparatorCells))))) := by
  simpa [structuredBoolWordRawBitsDecoderCanonicalInputInitializerTargetTape,
    structuredBoolWordRawBitsDecoderCanonicalSourceTape] using
    structuredBoolWordRawBitsDecoderInputInitializerTargetTape_cells
      bits suffixTail [] (boolWordRawBitsDecoderPreservedPadding suffixTail [])

/--
Primary bool-word input-initializer contract for future construction work.

Unlike the legacy contracts above, this one has a functional target: public
source right padding is canonicalized to {lit}`[]`, and the tape-2 padding is the
deterministic suffix that is visible in the source payload.
-/
def StructuredBoolWordRawBitsDecoderCanonicalInputInitializerSpec
    (initializer : MachineDescription) : Prop :=
  initializer.SubroutineReady ∧
    forall bits suffixTail : Word Bool,
      initializer.HaltsFromTapeEquiv
        (structuredBoolWordRawBitsDecoderCanonicalSourceTape
          bits suffixTail)
        (structuredBoolWordRawBitsDecoderCanonicalInputInitializerTargetTape
          bits suffixTail)

def StructuredBoolWordRawBitsDecoderCanonicalInputInitializerConstruction :
    Prop :=
  exists initializer : MachineDescription,
    StructuredBoolWordRawBitsDecoderCanonicalInputInitializerSpec
      initializer

def structuredBoolWordRawBitsDecoderCanonicalInputMaterializerSource
    (input : Word Bool × Word Bool) : Tape Bool :=
  structuredBoolWordRawBitsDecoderCanonicalSourceTape input.1 input.2

def structuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputTape
    (input : Word Bool × Word Bool) : Tape Bool :=
  structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
    input.1.length
    (boolWordRawBitsDecoderPreservedPadding input.2 [])

theorem structuredBoolWordRawBitsDecoderCanonicalInputInitializerTargetTape_eq_materializerTargetTape
    (bits suffixTail : Word Bool) :
    structuredBoolWordRawBitsDecoderCanonicalInputInitializerTargetTape
        bits suffixTail =
      structured3InputMaterializerTargetTape
        (structuredBoolWordRawBitsDecoderCanonicalSourceTape
          bits suffixTail)
        (structuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputTape
          (bits, suffixTail)) := by
  rfl

theorem structuredBoolWordRawBitsDecoderCanonicalInputMaterializerTargetTape_cells
    (bits suffixTail : Word Bool) :
    Tape.cells
        (structured3InputMaterializerTargetTape
          (structuredBoolWordRawBitsDecoderCanonicalSourceTape
            bits suffixTail)
          (structuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputTape
            (bits, suffixTail))) =
      Tape.cells
        (structuredBoolWordRawBitsDecoderCanonicalInputInitializerTargetTape
          bits suffixTail) := by
  rw [
    structuredBoolWordRawBitsDecoderCanonicalInputInitializerTargetTape_eq_materializerTargetTape]

theorem structuredBoolWordRawBitsDecoderCanonicalInputInitializerTargetTape_read
    (bits suffixTail : Word Bool) :
    Tape.read
        (structuredBoolWordRawBitsDecoderCanonicalInputInitializerTargetTape
          bits suffixTail) =
      none := by
  rfl

theorem structuredBoolWordRawBitsDecoderCanonicalInputMaterializerTargetTape_read
    (bits suffixTail : Word Bool) :
    Tape.read
        (structured3InputMaterializerTargetTape
          (structuredBoolWordRawBitsDecoderCanonicalSourceTape
            bits suffixTail)
          (structuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputTape
            (bits, suffixTail))) =
      Tape.read
        (structuredBoolWordRawBitsDecoderCanonicalInputInitializerTargetTape
          bits suffixTail) := by
  rw [
    structuredBoolWordRawBitsDecoderCanonicalInputInitializerTargetTape_eq_materializerTargetTape]

theorem structuredBoolWordRawBitsDecoderCanonicalInputMaterializerTargetTape_normalizedOutput
    (bits suffixTail : Word Bool) :
    Tape.normalizedOutput
        (structured3InputMaterializerTargetTape
          (structuredBoolWordRawBitsDecoderCanonicalSourceTape
            bits suffixTail)
          (structuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputTape
            (bits, suffixTail))) =
      Tape.normalizedOutput
        (structuredBoolWordRawBitsDecoderCanonicalInputInitializerTargetTape
          bits suffixTail) := by
  rw [
    structuredBoolWordRawBitsDecoderCanonicalInputInitializerTargetTape_eq_materializerTargetTape]

def StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerSpec
    (initializer : MachineDescription) : Prop :=
  Structured3InputMaterializerSpec
    structuredBoolWordRawBitsDecoderCanonicalInputMaterializerSource
    structuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputTape
    initializer

def StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerConstruction :
    Prop :=
  Structured3InputMaterializerConstruction
    structuredBoolWordRawBitsDecoderCanonicalInputMaterializerSource
    structuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputTape

theorem structuredBoolWordRawBitsDecoderCanonicalInputInitializerSpec_of_structured3InputMaterializerSpec
    {initializer : MachineDescription}
    (hmaterializer :
      StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerSpec
        initializer) :
    StructuredBoolWordRawBitsDecoderCanonicalInputInitializerSpec
      initializer := by
  rcases hmaterializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro bits suffixTail
  simpa [
    StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerSpec,
    structuredBoolWordRawBitsDecoderCanonicalInputMaterializerSource,
    structuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputTape,
    structuredBoolWordRawBitsDecoderCanonicalInputInitializerTargetTape,
    structuredBoolWordRawBitsDecoderInputInitializerTargetTape,
    structured3InputMaterializerTargetTape] using
    hrun (bits, suffixTail)

theorem structuredBoolWordRawBitsDecoderCanonicalInputInitializerConstruction_of_structured3InputMaterializer
    (hmaterializer :
      StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerConstruction) :
    StructuredBoolWordRawBitsDecoderCanonicalInputInitializerConstruction := by
  rcases hmaterializer with ⟨initializer, hspec⟩
  exact
    ⟨initializer,
      structuredBoolWordRawBitsDecoderCanonicalInputInitializerSpec_of_structured3InputMaterializerSpec
        hspec⟩

theorem structuredBoolWordRawBitsDecoderCanonicalInputMaterializerSpec_of_initializerSpec
    {initializer : MachineDescription}
    (hinitializer :
      StructuredBoolWordRawBitsDecoderCanonicalInputInitializerSpec
        initializer) :
    StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerSpec
      initializer := by
  rcases hinitializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro input
  rcases input with ⟨bits, suffixTail⟩
  simpa [
    StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerSpec,
    structuredBoolWordRawBitsDecoderCanonicalInputMaterializerSource,
    structuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputTape,
    structuredBoolWordRawBitsDecoderCanonicalInputInitializerTargetTape,
    structuredBoolWordRawBitsDecoderInputInitializerTargetTape,
    structured3InputMaterializerTargetTape] using
    hrun bits suffixTail

theorem structuredBoolWordRawBitsDecoderCanonicalInputMaterializerConstruction_of_initializer
    (hinitializer :
      StructuredBoolWordRawBitsDecoderCanonicalInputInitializerConstruction) :
    StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerConstruction := by
  rcases hinitializer with ⟨initializer, hspec⟩
  exact
    ⟨initializer,
      structuredBoolWordRawBitsDecoderCanonicalInputMaterializerSpec_of_initializerSpec
        hspec⟩

theorem structuredBoolWordRawBitsDecoderCanonicalInputMaterializerSpec_iff_initializerSpec
    (initializer : MachineDescription) :
    StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerSpec
        initializer ↔
      StructuredBoolWordRawBitsDecoderCanonicalInputInitializerSpec
        initializer := by
  constructor
  · exact
      structuredBoolWordRawBitsDecoderCanonicalInputInitializerSpec_of_structured3InputMaterializerSpec
  · exact
      structuredBoolWordRawBitsDecoderCanonicalInputMaterializerSpec_of_initializerSpec

theorem structuredBoolWordRawBitsDecoderCanonicalInputMaterializerConstruction_iff_initializerConstruction :
    StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerConstruction ↔
      StructuredBoolWordRawBitsDecoderCanonicalInputInitializerConstruction := by
  constructor
  · exact
      structuredBoolWordRawBitsDecoderCanonicalInputInitializerConstruction_of_structured3InputMaterializer
  · exact
      structuredBoolWordRawBitsDecoderCanonicalInputMaterializerConstruction_of_initializer

/--
Public source family for an indexed raw-bits decoder materializer.

The index couples the raw bits, the caller suffix, and the physical source
right padding.  It deliberately does not quantify over arbitrary output padding
for a fixed source tape.
-/
def structuredBoolWordRawBitsDecoderIndexedInputMaterializerSource
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding : ι -> List (Option Bool))
    (input : ι) : Tape Bool :=
  boolWordRawBitsDecoderSourceTape
    (bits input) (suffixTail input) (rightPadding input)

/--
Tape-2 output-buffer family for an indexed raw-bits decoder materializer.
-/
def structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputTape
    {ι : Type}
    (bits : ι -> Word Bool)
    (outputPadding : ι -> List (Option Bool))
    (input : ι) : Tape Bool :=
  structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
    (bits input).length (outputPadding input)

/--
Named physical structured target for an indexed raw-bits decoder materializer.
-/
def structuredBoolWordRawBitsDecoderIndexedInputMaterializerTargetTape
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) : Tape Bool :=
  structuredBoolWordRawBitsDecoderInputInitializerTargetTape
    (bits input) (suffixTail input)
    (rightPadding input) (outputPadding input)

theorem structuredBoolWordRawBitsDecoderIndexedInputMaterializerTargetTape_eq_materializerTargetTape
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) :
    structuredBoolWordRawBitsDecoderIndexedInputMaterializerTargetTape
        bits suffixTail rightPadding outputPadding input =
      structured3InputMaterializerTargetTape
        (structuredBoolWordRawBitsDecoderIndexedInputMaterializerSource
          bits suffixTail rightPadding input)
        (structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputTape
          bits outputPadding input) := by
  rfl

theorem structuredBoolWordRawBitsDecoderIndexedInputMaterializerTargetTape_read
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) :
    Tape.read
        (structuredBoolWordRawBitsDecoderIndexedInputMaterializerTargetTape
          bits suffixTail rightPadding outputPadding input) =
      none := by
  rfl

theorem structuredBoolWordRawBitsDecoderIndexedInputMaterializerTargetTape_cells
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) :
    Tape.cells
        (structuredBoolWordRawBitsDecoderIndexedInputMaterializerTargetTape
          bits suffixTail rightPadding outputPadding input) =
      Tape.cells
        (structured3InputMaterializerTargetTape
          (structuredBoolWordRawBitsDecoderIndexedInputMaterializerSource
            bits suffixTail rightPadding input)
          (structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputTape
            bits outputPadding input)) := by
  rw [
    structuredBoolWordRawBitsDecoderIndexedInputMaterializerTargetTape_eq_materializerTargetTape]

theorem structuredBoolWordRawBitsDecoderIndexedInputMaterializerTargetTape_normalizedOutput
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) :
    Tape.normalizedOutput
        (structuredBoolWordRawBitsDecoderIndexedInputMaterializerTargetTape
          bits suffixTail rightPadding outputPadding input) =
      Tape.normalizedOutput
        (structured3InputMaterializerTargetTape
          (structuredBoolWordRawBitsDecoderIndexedInputMaterializerSource
            bits suffixTail rightPadding input)
          (structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputTape
            bits outputPadding input)) := by
  rw [
    structuredBoolWordRawBitsDecoderIndexedInputMaterializerTargetTape_eq_materializerTargetTape]

/--
Initializer-style view for an indexed raw-bits decoder materializer.
-/
def StructuredBoolWordRawBitsDecoderIndexedInputInitializerSpec
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (initializer : MachineDescription) : Prop :=
  initializer.SubroutineReady ∧
    forall input : ι,
      initializer.HaltsFromTapeEquiv
        (structuredBoolWordRawBitsDecoderIndexedInputMaterializerSource
          bits suffixTail rightPadding input)
        (structuredBoolWordRawBitsDecoderIndexedInputMaterializerTargetTape
          bits suffixTail rightPadding outputPadding input)

def StructuredBoolWordRawBitsDecoderIndexedInputInitializerConstruction
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool)) :
    Prop :=
  exists initializer : MachineDescription,
    StructuredBoolWordRawBitsDecoderIndexedInputInitializerSpec
      bits suffixTail rightPadding outputPadding initializer

/--
Structured-input-materializer view for the same indexed raw-bits decoder
target family.
-/
def StructuredBoolWordRawBitsDecoderIndexedInputMaterializerSpec
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (initializer : MachineDescription) : Prop :=
  Structured3InputMaterializerSpec
    (structuredBoolWordRawBitsDecoderIndexedInputMaterializerSource
      bits suffixTail rightPadding)
    (structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputTape
      bits outputPadding)
    initializer

def StructuredBoolWordRawBitsDecoderIndexedInputMaterializerConstruction
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool)) :
    Prop :=
  Structured3InputMaterializerConstruction
    (structuredBoolWordRawBitsDecoderIndexedInputMaterializerSource
      bits suffixTail rightPadding)
    (structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputTape
      bits outputPadding)

theorem structuredBoolWordRawBitsDecoderIndexedInputInitializerSpec_of_materializerSpec
    {ι : Type}
    {bits suffixTail : ι -> Word Bool}
    {rightPadding outputPadding : ι -> List (Option Bool)}
    {initializer : MachineDescription}
    (hmaterializer :
      StructuredBoolWordRawBitsDecoderIndexedInputMaterializerSpec
        bits suffixTail rightPadding outputPadding initializer) :
    StructuredBoolWordRawBitsDecoderIndexedInputInitializerSpec
      bits suffixTail rightPadding outputPadding initializer := by
  rcases hmaterializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro input
  simpa [
    StructuredBoolWordRawBitsDecoderIndexedInputMaterializerSpec,
    StructuredBoolWordRawBitsDecoderIndexedInputInitializerSpec,
    structuredBoolWordRawBitsDecoderIndexedInputMaterializerSource,
    structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputTape,
    structuredBoolWordRawBitsDecoderIndexedInputMaterializerTargetTape,
    structuredBoolWordRawBitsDecoderInputInitializerTargetTape,
    structured3InputMaterializerTargetTape] using
    hrun input

theorem structuredBoolWordRawBitsDecoderIndexedInputMaterializerSpec_of_initializerSpec
    {ι : Type}
    {bits suffixTail : ι -> Word Bool}
    {rightPadding outputPadding : ι -> List (Option Bool)}
    {initializer : MachineDescription}
    (hinitializer :
      StructuredBoolWordRawBitsDecoderIndexedInputInitializerSpec
        bits suffixTail rightPadding outputPadding initializer) :
    StructuredBoolWordRawBitsDecoderIndexedInputMaterializerSpec
      bits suffixTail rightPadding outputPadding initializer := by
  rcases hinitializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro input
  simpa [
    StructuredBoolWordRawBitsDecoderIndexedInputMaterializerSpec,
    StructuredBoolWordRawBitsDecoderIndexedInputInitializerSpec,
    structuredBoolWordRawBitsDecoderIndexedInputMaterializerSource,
    structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputTape,
    structuredBoolWordRawBitsDecoderIndexedInputMaterializerTargetTape,
    structuredBoolWordRawBitsDecoderInputInitializerTargetTape,
    structured3InputMaterializerTargetTape] using
    hrun input

theorem structuredBoolWordRawBitsDecoderIndexedInputMaterializerSpec_iff_initializerSpec
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (initializer : MachineDescription) :
    StructuredBoolWordRawBitsDecoderIndexedInputMaterializerSpec
        bits suffixTail rightPadding outputPadding initializer ↔
      StructuredBoolWordRawBitsDecoderIndexedInputInitializerSpec
        bits suffixTail rightPadding outputPadding initializer := by
  constructor
  · exact
      structuredBoolWordRawBitsDecoderIndexedInputInitializerSpec_of_materializerSpec
  · exact
      structuredBoolWordRawBitsDecoderIndexedInputMaterializerSpec_of_initializerSpec

theorem structuredBoolWordRawBitsDecoderIndexedInputInitializerConstruction_of_materializer
    {ι : Type}
    {bits suffixTail : ι -> Word Bool}
    {rightPadding outputPadding : ι -> List (Option Bool)}
    (hmaterializer :
      StructuredBoolWordRawBitsDecoderIndexedInputMaterializerConstruction
        bits suffixTail rightPadding outputPadding) :
    StructuredBoolWordRawBitsDecoderIndexedInputInitializerConstruction
      bits suffixTail rightPadding outputPadding := by
  rcases hmaterializer with ⟨initializer, hspec⟩
  exact
    ⟨initializer,
      structuredBoolWordRawBitsDecoderIndexedInputInitializerSpec_of_materializerSpec
        hspec⟩

theorem structuredBoolWordRawBitsDecoderIndexedInputMaterializerConstruction_of_initializer
    {ι : Type}
    {bits suffixTail : ι -> Word Bool}
    {rightPadding outputPadding : ι -> List (Option Bool)}
    (hinitializer :
      StructuredBoolWordRawBitsDecoderIndexedInputInitializerConstruction
        bits suffixTail rightPadding outputPadding) :
    StructuredBoolWordRawBitsDecoderIndexedInputMaterializerConstruction
      bits suffixTail rightPadding outputPadding := by
  rcases hinitializer with ⟨initializer, hspec⟩
  exact
    ⟨initializer,
      structuredBoolWordRawBitsDecoderIndexedInputMaterializerSpec_of_initializerSpec
        hspec⟩

theorem structuredBoolWordRawBitsDecoderIndexedInputMaterializerConstruction_iff_initializerConstruction
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool)) :
    StructuredBoolWordRawBitsDecoderIndexedInputMaterializerConstruction
        bits suffixTail rightPadding outputPadding ↔
      StructuredBoolWordRawBitsDecoderIndexedInputInitializerConstruction
        bits suffixTail rightPadding outputPadding := by
  constructor
  · exact
      structuredBoolWordRawBitsDecoderIndexedInputInitializerConstruction_of_materializer
  · exact
      structuredBoolWordRawBitsDecoderIndexedInputMaterializerConstruction_of_initializer

theorem structuredBoolWordRawBitsDecoderIndexedInputMaterializerSpec_of_eq
    {ι : Type}
    {bits suffixTail bits' suffixTail' : ι -> Word Bool}
    {rightPadding outputPadding rightPadding' outputPadding' :
      ι -> List (Option Bool)}
    {initializer : MachineDescription}
    (hmaterializer :
      StructuredBoolWordRawBitsDecoderIndexedInputMaterializerSpec
        bits suffixTail rightPadding outputPadding initializer)
    (hbits : forall input : ι, bits' input = bits input)
    (hsuffixTail :
      forall input : ι, suffixTail' input = suffixTail input)
    (hrightPadding :
      forall input : ι, rightPadding' input = rightPadding input)
    (houtputPadding :
      forall input : ι, outputPadding' input = outputPadding input) :
    StructuredBoolWordRawBitsDecoderIndexedInputMaterializerSpec
      bits' suffixTail' rightPadding' outputPadding' initializer := by
  rcases hmaterializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro input
  simpa [
      StructuredBoolWordRawBitsDecoderIndexedInputMaterializerSpec,
      structuredBoolWordRawBitsDecoderIndexedInputMaterializerSource,
      structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputTape,
      hbits input, hsuffixTail input, hrightPadding input,
      houtputPadding input] using
    hrun input

theorem structuredBoolWordRawBitsDecoderIndexedInputMaterializerConstruction_of_eq
    {ι : Type}
    {bits suffixTail bits' suffixTail' : ι -> Word Bool}
    {rightPadding outputPadding rightPadding' outputPadding' :
      ι -> List (Option Bool)}
    (hmaterializer :
      StructuredBoolWordRawBitsDecoderIndexedInputMaterializerConstruction
        bits suffixTail rightPadding outputPadding)
    (hbits : forall input : ι, bits' input = bits input)
    (hsuffixTail :
      forall input : ι, suffixTail' input = suffixTail input)
    (hrightPadding :
      forall input : ι, rightPadding' input = rightPadding input)
    (houtputPadding :
      forall input : ι, outputPadding' input = outputPadding input) :
    StructuredBoolWordRawBitsDecoderIndexedInputMaterializerConstruction
      bits' suffixTail' rightPadding' outputPadding' := by
  rcases hmaterializer with ⟨initializer, hspec⟩
  exact
    ⟨initializer,
      structuredBoolWordRawBitsDecoderIndexedInputMaterializerSpec_of_eq
        hspec hbits hsuffixTail hrightPadding houtputPadding⟩

theorem structuredBoolWordRawBitsDecoderIndexedInputMaterializerSpec_reindex
    {ι κ : Type}
    {bits suffixTail : ι -> Word Bool}
    {rightPadding outputPadding : ι -> List (Option Bool)}
    {initializer : MachineDescription}
    (hmaterializer :
      StructuredBoolWordRawBitsDecoderIndexedInputMaterializerSpec
        bits suffixTail rightPadding outputPadding initializer)
    (index : κ -> ι) :
    StructuredBoolWordRawBitsDecoderIndexedInputMaterializerSpec
      (fun input : κ => bits (index input))
      (fun input : κ => suffixTail (index input))
      (fun input : κ => rightPadding (index input))
      (fun input : κ => outputPadding (index input))
      initializer := by
  rcases hmaterializer with ⟨hready, hrun⟩
  exact ⟨hready, fun input => hrun (index input)⟩

theorem structuredBoolWordRawBitsDecoderIndexedInputMaterializerConstruction_reindex
    {ι κ : Type}
    {bits suffixTail : ι -> Word Bool}
    {rightPadding outputPadding : ι -> List (Option Bool)}
    (hmaterializer :
      StructuredBoolWordRawBitsDecoderIndexedInputMaterializerConstruction
        bits suffixTail rightPadding outputPadding)
    (index : κ -> ι) :
    StructuredBoolWordRawBitsDecoderIndexedInputMaterializerConstruction
      (fun input : κ => bits (index input))
      (fun input : κ => suffixTail (index input))
      (fun input : κ => rightPadding (index input))
      (fun input : κ => outputPadding (index input)) := by
  rcases hmaterializer with ⟨initializer, hspec⟩
  exact
    ⟨initializer,
      structuredBoolWordRawBitsDecoderIndexedInputMaterializerSpec_reindex
        hspec index⟩

def structuredBoolWordRawBitsDecoderEndpointDescription
    (initializer : MachineDescription) : MachineDescription :=
  Structured.MultiTapeLowering.canonicalPrimitiveSeqDescription
    initializer loweredStructuredBoolWordRawBitsDecoderDescription

theorem structuredBoolWordRawBitsDecoderEndpointDescription_subroutineReady
    {initializer : MachineDescription}
    (hinitializer : initializer.SubroutineReady) :
    (structuredBoolWordRawBitsDecoderEndpointDescription
      initializer).SubroutineReady :=
  Structured.MultiTapeLowering.canonicalPrimitiveSeqDescription_subroutineReady
    hinitializer
    loweredStructuredBoolWordRawBitsDecoderDescription_subroutineReady

/--
Legacy over-general structured-output endpoint.

This is the endpoint analogue of
{name}`StructuredBoolWordRawBitsDecoderInputInitializerSpec`; it is kept for
the proved impossibility guardrail, not as a construction target.
-/
def StructuredBoolWordRawBitsDecoderEndpointSpec
    (endpoint : MachineDescription) : Prop :=
  endpoint.SubroutineReady ∧
    forall (bits suffixTail : Word Bool)
      (rightPadding outputPadding : List (Option Bool)),
      endpoint.HaltsFromTapeEquiv
        (boolWordRawBitsDecoderSourceTape bits suffixTail rightPadding)
        (Structured.MultiTapeLowering.encodedGuardedStructuredTapes
          [ structuredBoolWordRawBitsDecoderSourceTargetTape
              bits suffixTail rightPadding
          , structuredBoolWordRawBitsDecoderCounterDecodeTape 0
              (bits.length + 1)
          , rightEdgeScanSourceTapeFromLeft [none] bits outputPadding ])

def StructuredBoolWordRawBitsDecoderEndpointConstruction : Prop :=
  exists endpoint : MachineDescription,
    StructuredBoolWordRawBitsDecoderEndpointSpec endpoint

/--
The uniform structured-output endpoint is over-quantified for the same reason
as the uniform input initializer: a single deterministic machine cannot map the
same source tape to arbitrary nonblank tape-2 output padding.
-/
theorem structuredBoolWordRawBitsDecoderEndpointConstruction_impossible :
    ¬ StructuredBoolWordRawBitsDecoderEndpointConstruction := by
  rintro ⟨endpoint, hendpointReady, hendpointRun⟩
  let Tnil : Tape Bool :=
    Structured.MultiTapeLowering.encodedGuardedStructuredTapes
      [ structuredBoolWordRawBitsDecoderSourceTargetTape
          ([] : Word Bool) [] []
      , structuredBoolWordRawBitsDecoderCounterDecodeTape 0 (0 + 1)
      , rightEdgeScanSourceTapeFromLeft [none] ([] : Word Bool) [] ]
  let Tone : Tape Bool :=
    Structured.MultiTapeLowering.encodedGuardedStructuredTapes
      [ structuredBoolWordRawBitsDecoderSourceTargetTape
          ([] : Word Bool) [] []
      , structuredBoolWordRawBitsDecoderCounterDecodeTape 0 (0 + 1)
      , rightEdgeScanSourceTapeFromLeft [none]
          ([] : Word Bool) [some true] ]
  rcases hendpointRun ([] : Word Bool) [] [] [] with
    ⟨actualNil, hhaltNil, hequivNil⟩
  rcases hendpointRun ([] : Word Bool) [] [] [some true] with
    ⟨actualOne, hhaltOne, hequivOne⟩
  have hactual : actualNil = actualOne :=
    MachineDescription.haltsFromTape_functional_of_haltTransitionFree
      hendpointReady.right hhaltNil hhaltOne
  have htargets : Tape.Equiv Tnil Tone := by
    exact
      Tape.Equiv.trans (Tape.Equiv.symm hequivNil)
        (by simpa [hactual] using hequivOne)
  have hnorm := Tape.Equiv.normalizedOutput_eq htargets
  have hne : Tape.normalizedOutput Tnil ≠ Tape.normalizedOutput Tone := by
    decide
  exact hne hnorm

def StructuredBoolWordRawBitsDecoderFixedOutputPaddingEndpointSpec
    (outputPadding : List (Option Bool))
    (endpoint : MachineDescription) : Prop :=
  endpoint.SubroutineReady ∧
    forall (bits suffixTail : Word Bool)
      (rightPadding : List (Option Bool)),
      endpoint.HaltsFromTapeEquiv
        (boolWordRawBitsDecoderSourceTape bits suffixTail rightPadding)
        (Structured.MultiTapeLowering.encodedGuardedStructuredTapes
          [ structuredBoolWordRawBitsDecoderSourceTargetTape
              bits suffixTail rightPadding
          , structuredBoolWordRawBitsDecoderCounterDecodeTape 0
              (bits.length + 1)
          , rightEdgeScanSourceTapeFromLeft [none] bits outputPadding ])

def StructuredBoolWordRawBitsDecoderFixedOutputPaddingEndpointConstruction
    (outputPadding : List (Option Bool)) : Prop :=
  exists endpoint : MachineDescription,
    StructuredBoolWordRawBitsDecoderFixedOutputPaddingEndpointSpec
      outputPadding endpoint

def StructuredBoolWordRawBitsDecoderPreservedPaddingEndpointSpec
    (endpoint : MachineDescription) : Prop :=
  endpoint.SubroutineReady ∧
    forall (bits suffixTail : Word Bool)
      (rightPadding : List (Option Bool)),
      endpoint.HaltsFromTapeEquiv
        (boolWordRawBitsDecoderSourceTape bits suffixTail rightPadding)
        (Structured.MultiTapeLowering.encodedGuardedStructuredTapes
          [ structuredBoolWordRawBitsDecoderSourceTargetTape
              bits suffixTail rightPadding
          , structuredBoolWordRawBitsDecoderCounterDecodeTape 0
              (bits.length + 1)
          , rightEdgeScanSourceTapeFromLeft [none] bits
              (boolWordRawBitsDecoderPreservedPadding suffixTail
                rightPadding) ])

def StructuredBoolWordRawBitsDecoderPreservedPaddingEndpointConstruction :
    Prop :=
  exists endpoint : MachineDescription,
    StructuredBoolWordRawBitsDecoderPreservedPaddingEndpointSpec endpoint

def structuredBoolWordRawBitsDecoderCanonicalEndpointTargetTape
    (bits suffixTail : Word Bool) : Tape Bool :=
  Structured.MultiTapeLowering.encodedGuardedStructured3Tapes
    (structuredBoolWordRawBitsDecoderSourceTargetTape
      bits suffixTail [])
    (structuredBoolWordRawBitsDecoderCounterDecodeTape 0
      (bits.length + 1))
    (rightEdgeScanSourceTapeFromLeft [none] bits
      (boolWordRawBitsDecoderPreservedPadding suffixTail []))

theorem structuredBoolWordRawBitsDecoderCanonicalEndpointTargetTape_cells
    (bits suffixTail : Word Bool) :
    Tape.cells
        (structuredBoolWordRawBitsDecoderCanonicalEndpointTargetTape
          bits suffixTail) =
      List.append Structured.MultiTapeLowering.tapeSeparatorCells
        (List.append
          (Structured.MultiTapeLowering.logicalTapeCode
            (Structured.MultiTapeLowering.guardLogicalTape
              (structuredBoolWordRawBitsDecoderSourceTargetTape
                bits suffixTail [])))
          (List.append Structured.MultiTapeLowering.tapeSeparatorCells
            (List.append
              (Structured.MultiTapeLowering.logicalTapeCode
                (Structured.MultiTapeLowering.guardLogicalTape
                  (structuredBoolWordRawBitsDecoderCounterDecodeTape 0
                    (bits.length + 1))))
              (List.append
                Structured.MultiTapeLowering.tapeSeparatorCells
                (List.append
                  (Structured.MultiTapeLowering.logicalTapeCode
                    (Structured.MultiTapeLowering.guardLogicalTape
                      (rightEdgeScanSourceTapeFromLeft [none] bits
                        (boolWordRawBitsDecoderPreservedPadding suffixTail []))))
                  Structured.MultiTapeLowering.tapeSeparatorCells))))) := by
  simpa [structuredBoolWordRawBitsDecoderCanonicalEndpointTargetTape] using
    Structured.MultiTapeLowering.encodedGuardedStructured3Tapes_cells
      (structuredBoolWordRawBitsDecoderSourceTargetTape bits suffixTail [])
      (structuredBoolWordRawBitsDecoderCounterDecodeTape 0
        (bits.length + 1))
      (rightEdgeScanSourceTapeFromLeft [none] bits
        (boolWordRawBitsDecoderPreservedPadding suffixTail []))

def StructuredBoolWordRawBitsDecoderCanonicalEndpointSpec
    (endpoint : MachineDescription) : Prop :=
  endpoint.SubroutineReady ∧
    forall bits suffixTail : Word Bool,
      endpoint.HaltsFromTapeEquiv
        (structuredBoolWordRawBitsDecoderCanonicalSourceTape
          bits suffixTail)
        (structuredBoolWordRawBitsDecoderCanonicalEndpointTargetTape
          bits suffixTail)

def StructuredBoolWordRawBitsDecoderCanonicalEndpointConstruction :
    Prop :=
  exists endpoint : MachineDescription,
    StructuredBoolWordRawBitsDecoderCanonicalEndpointSpec endpoint

theorem structuredBoolWordRawBitsDecoderCanonicalEndpointSpec_of_inputInitializerSpec
    {initializer : MachineDescription}
    (hinitializer :
      StructuredBoolWordRawBitsDecoderCanonicalInputInitializerSpec
        initializer) :
    StructuredBoolWordRawBitsDecoderCanonicalEndpointSpec
      (structuredBoolWordRawBitsDecoderEndpointDescription initializer) := by
  constructor
  · exact
      structuredBoolWordRawBitsDecoderEndpointDescription_subroutineReady
        hinitializer.left
  · intro bits suffixTail
    exact
      Structured.MultiTapeLowering.canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
        hinitializer.left
        loweredStructuredBoolWordRawBitsDecoderDescription_subroutineReady
        (hinitializer.right bits suffixTail)
        (by
          simpa [structuredBoolWordRawBitsDecoderCanonicalInputInitializerTargetTape,
            structuredBoolWordRawBitsDecoderCanonicalEndpointTargetTape,
            structuredBoolWordRawBitsDecoderCanonicalSourceTape,
            Structured.MultiTapeLowering.encodedGuardedStructured3Tapes] using
            loweredStructuredBoolWordRawBitsDecoderDescription_haltsFromTapeWithOutputPadding
              bits suffixTail []
              (boolWordRawBitsDecoderPreservedPadding suffixTail []))

theorem structuredBoolWordRawBitsDecoderCanonicalEndpointConstruction_of_inputInitializer
    (hinitializer :
      StructuredBoolWordRawBitsDecoderCanonicalInputInitializerConstruction) :
    StructuredBoolWordRawBitsDecoderCanonicalEndpointConstruction := by
  rcases hinitializer with ⟨initializer, hinitializerSpec⟩
  exact
    ⟨structuredBoolWordRawBitsDecoderEndpointDescription initializer,
      structuredBoolWordRawBitsDecoderCanonicalEndpointSpec_of_inputInitializerSpec
        hinitializerSpec⟩

theorem structuredBoolWordRawBitsDecoderFixedOutputPaddingEndpointSpec_of_inputInitializerSpec
    {outputPadding : List (Option Bool)}
    {initializer : MachineDescription}
    (hinitializer :
      StructuredBoolWordRawBitsDecoderFixedOutputPaddingInputInitializerSpec
        outputPadding initializer) :
    StructuredBoolWordRawBitsDecoderFixedOutputPaddingEndpointSpec
      outputPadding
      (structuredBoolWordRawBitsDecoderEndpointDescription initializer) := by
  constructor
  · exact
      structuredBoolWordRawBitsDecoderEndpointDescription_subroutineReady
        hinitializer.left
  · intro bits suffixTail rightPadding
    exact
      Structured.MultiTapeLowering.canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
        hinitializer.left
        loweredStructuredBoolWordRawBitsDecoderDescription_subroutineReady
        (hinitializer.right bits suffixTail rightPadding)
        (loweredStructuredBoolWordRawBitsDecoderDescription_haltsFromTapeWithOutputPadding
          bits suffixTail rightPadding outputPadding)

theorem structuredBoolWordRawBitsDecoderPreservedPaddingEndpointSpec_of_inputInitializerSpec
    {initializer : MachineDescription}
    (hinitializer :
      StructuredBoolWordRawBitsDecoderPreservedPaddingInputInitializerSpec
        initializer) :
    StructuredBoolWordRawBitsDecoderPreservedPaddingEndpointSpec
      (structuredBoolWordRawBitsDecoderEndpointDescription initializer) := by
  constructor
  · exact
      structuredBoolWordRawBitsDecoderEndpointDescription_subroutineReady
        hinitializer.left
  · intro bits suffixTail rightPadding
    exact
      Structured.MultiTapeLowering.canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
        hinitializer.left
        loweredStructuredBoolWordRawBitsDecoderDescription_subroutineReady
        (hinitializer.right bits suffixTail rightPadding)
        (loweredStructuredBoolWordRawBitsDecoderDescription_haltsFromTapeWithOutputPadding
          bits suffixTail rightPadding
          (boolWordRawBitsDecoderPreservedPadding suffixTail rightPadding))

theorem structuredBoolWordRawBitsDecoderFixedOutputPaddingEndpointConstruction_of_inputInitializer
    {outputPadding : List (Option Bool)}
    (hinitializer :
      StructuredBoolWordRawBitsDecoderFixedOutputPaddingInputInitializerConstruction
        outputPadding) :
    StructuredBoolWordRawBitsDecoderFixedOutputPaddingEndpointConstruction
      outputPadding := by
  rcases hinitializer with ⟨initializer, hinitializerSpec⟩
  exact
    ⟨structuredBoolWordRawBitsDecoderEndpointDescription initializer,
      structuredBoolWordRawBitsDecoderFixedOutputPaddingEndpointSpec_of_inputInitializerSpec
        hinitializerSpec⟩

theorem structuredBoolWordRawBitsDecoderPreservedPaddingEndpointConstruction_of_inputInitializer
    (hinitializer :
      StructuredBoolWordRawBitsDecoderPreservedPaddingInputInitializerConstruction) :
    StructuredBoolWordRawBitsDecoderPreservedPaddingEndpointConstruction := by
  rcases hinitializer with ⟨initializer, hinitializerSpec⟩
  exact
    ⟨structuredBoolWordRawBitsDecoderEndpointDescription initializer,
      structuredBoolWordRawBitsDecoderPreservedPaddingEndpointSpec_of_inputInitializerSpec
        hinitializerSpec⟩

def boolWordRawBitsDecoderHeaderBase : List (Option Bool) :=
  List.append (boolWordRawBitsDecoderHeaderBits.reverse.map some) [none]

def boolWordRawBitsDecoderAfterHeaderTape
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) : Tape Bool :=
  tapeAtCells boolWordRawBitsDecoderHeaderBase
    (List.append ((boolWordRawBitsDecoderEncodedFieldBits bits).map some)
      (some false ::
        List.append (suffixTail.map some) (none :: rightPadding)))

def boolWordRawBitsDecoderPrefixHandoffTape
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) : Tape Bool :=
  (boolWordCanonicalHandoffConfigWithBaseAndRight
    bits boolWordRawBitsDecoderHeaderBase
    (false :: suffixTail) (none :: rightPadding)).tape

def boolWordRawBitsDecoderPrefixScannerDescription :
    MachineDescription :=
  canonicalSeqDescription
    rightMoveAcrossFourBitsDescription
    BoolWordSuffixScannerDescription

theorem boolWordRawBitsDecoderPrefixScannerDescription_subroutineReady :
    boolWordRawBitsDecoderPrefixScannerDescription.SubroutineReady :=
  canonicalSeqDescription_subroutineReady
    rightMoveAcrossFourBitsDescription_subroutineReady
    boolWordSuffixScannerDescription_subroutineReady

theorem rightMoveAcrossFourBitsDescription_haltsFrom_rawBitsDecoderSource
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    rightMoveAcrossFourBitsDescription.HaltsFromTape
      (boolWordRawBitsDecoderSourceTape bits suffixTail rightPadding)
      (boolWordRawBitsDecoderAfterHeaderTape bits suffixTail
        rightPadding) := by
  simpa [boolWordRawBitsDecoderSourceTape,
    boolWordRawBitsDecoderAfterHeaderTape,
    boolWordRawBitsDecoderHeaderBase,
    boolWordRawBitsDecoderHeaderBits,
    rightEdgeRewindTargetTape, encodeCodeSymbolAsInput,
    List.map_append, List.append_assoc] using
    rightMoveAcrossFourBitsDescription_haltsFromTape_bits
      false false false false [none]
      (List.append ((boolWordRawBitsDecoderEncodedFieldBits bits).map some)
        (some false ::
          List.append (suffixTail.map some) (none :: rightPadding)))

theorem boolWordRawBitsDecoderAfterHeaderTape_move_left_move_right
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (boolWordRawBitsDecoderAfterHeaderTape bits suffixTail
            rightPadding)) =
      boolWordRawBitsDecoderAfterHeaderTape bits suffixTail
        rightPadding := by
  rcases stageNatBits_false_false_tail bits.length with
    ⟨stageTail, hstage⟩
  simp [boolWordRawBitsDecoderAfterHeaderTape,
    boolWordRawBitsDecoderEncodedFieldBits, hstage, tapeAtCells,
    Tape.move, Tape.moveLeft, Tape.moveRight, List.append_assoc]

theorem boolWordSuffixScannerDescription_haltsFrom_rawBitsDecoderAfterHeader
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    BoolWordSuffixScannerDescription.HaltsFromTape
      (boolWordRawBitsDecoderAfterHeaderTape bits suffixTail
        rightPadding)
      (boolWordRawBitsDecoderPrefixHandoffTape bits suffixTail
        rightPadding) := by
  rcases
      run_boolWordSuffix_raw_to_canonical_handoff_withBaseAndRight
        bits boolWordRawBitsDecoderHeaderBase suffixTail
        (none :: rightPadding) with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  constructor
  · simpa [boolWordRawBitsDecoderAfterHeaderTape,
      boolWordRawBitsDecoderPrefixHandoffTape,
      boolWordRawBitsDecoderEncodedFieldBits, List.map_append,
      List.append_assoc] using
      congrArg Configuration.state hsteps
  · simpa [boolWordRawBitsDecoderAfterHeaderTape,
      boolWordRawBitsDecoderPrefixHandoffTape,
      boolWordRawBitsDecoderEncodedFieldBits, List.map_append,
      List.append_assoc] using
      congrArg Configuration.tape hsteps

theorem boolWordRawBitsDecoderPrefixScannerDescription_haltsFromTape
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    boolWordRawBitsDecoderPrefixScannerDescription.HaltsFromTape
      (boolWordRawBitsDecoderSourceTape bits suffixTail rightPadding)
      (boolWordRawBitsDecoderPrefixHandoffTape bits suffixTail
        rightPadding) := by
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      rightMoveAcrossFourBitsDescription_subroutineReady
      boolWordSuffixScannerDescription_subroutineReady
      (rightMoveAcrossFourBitsDescription_haltsFrom_rawBitsDecoderSource
        bits suffixTail rightPadding)
      (boolWordRawBitsDecoderAfterHeaderTape_move_left_move_right
        bits suffixTail rightPadding)
      (boolWordSuffixScannerDescription_haltsFrom_rawBitsDecoderAfterHeader
        bits suffixTail rightPadding)


end FiniteTransducers
end CommonGround

end Computability
end FoC

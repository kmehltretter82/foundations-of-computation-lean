import FoC.Computability.Compiler.FST.BoolRawInput.Contracts

set_option doc.verso true

/-!
# Bool-word materializer endpoint route bundles

This module packages the endpoint facts for the feasible Boolean-word raw-bits
input materializer routes.  The facts are construction-free, but bundling them
under the route API keeps later materializer and count-window proofs from
repeatedly unfolding the canonical source, blank scratch tape, output buffer,
and guarded structured three-tape target.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers

namespace BoolWordRawBitsDecoderInputMaterializerEndpointRoute

open BoolWordRawBitsDecoderInputMaterializerEndpoint
open BoolWordRawBitsDecoderInputMaterializerEndpointContracts
open BoolWordRawBitsDecoderInputMaterializerRouteContracts

/-!
## Canonical endpoint shape
-/

structure CanonicalEndpointShape
    (bits suffixTail : Word Bool) : Prop where
  sourceCells :
    Tape.cells (canonicalSource bits suffixTail) =
      none ::
        List.append
          ((List.append boolWordRawBitsDecoderHeaderBits
            (List.append
              (boolWordRawBitsDecoderEncodedFieldBits bits)
              (false :: suffixTail))).map some)
          [none]
  outputCells :
    Tape.cells (canonicalOutput bits suffixTail) =
      none ::
        List.append
          (List.replicate (bits.length + 1) (none : Option Bool))
          (List.append ((false :: suffixTail).map some) [none])
  targetRead :
    Tape.read (canonicalTarget bits suffixTail) = none
  targetCells :
    Tape.cells (canonicalTarget bits suffixTail) =
      List.append Structured.MultiTapeLowering.tapeSeparatorCells
        (List.append (Structured.MultiTapeLowering.logicalTapeCode
            (Structured.MultiTapeLowering.guardLogicalTape
              (canonicalSource bits suffixTail)))
          (List.append Structured.MultiTapeLowering.tapeSeparatorCells
            (List.append (Structured.MultiTapeLowering.logicalTapeCode
                (Structured.MultiTapeLowering.guardLogicalTape Tape.blank))
              (List.append Structured.MultiTapeLowering.tapeSeparatorCells
                (List.append (Structured.MultiTapeLowering.logicalTapeCode
                    (Structured.MultiTapeLowering.guardLogicalTape
                      (canonicalOutput bits suffixTail)))
                  Structured.MultiTapeLowering.tapeSeparatorCells)))))
  targetCellsInitializer :
    Tape.cells
        (structuredBoolWordRawBitsDecoderCanonicalInputInitializerTargetTape
          bits suffixTail) =
      Tape.cells (canonicalTarget bits suffixTail)
  targetNormalizedOutput :
    Tape.normalizedOutput (canonicalTarget bits suffixTail) =
      List.append
        (Structured.MultiTapeLowering.logicalTapeBits
          (canonicalGuardedSourceTape bits suffixTail))
        (List.append
          (Structured.MultiTapeLowering.logicalTapeBits
            canonicalGuardedScratchTape)
          (Structured.MultiTapeLowering.logicalTapeBits
            (canonicalGuardedOutputTape bits suffixTail)))
  targetNormalizedOutputInitializer :
    Tape.normalizedOutput (canonicalTarget bits suffixTail) =
      Tape.normalizedOutput
        (structuredBoolWordRawBitsDecoderCanonicalInputInitializerTargetTape
          bits suffixTail)
  structuredEncoded :
    Structured.MultiTapeLowering.StructuredEncodedTapes
      (canonicalGuardedLogicalTapes bits suffixTail)
      (canonicalTarget bits suffixTail)
  structuredGuardedEncoded :
    Structured.MultiTapeLowering.StructuredGuardedEncodedTapes
      (canonicalLogicalTapes bits suffixTail)
      (canonicalTarget bits suffixTail)
  structuredLogicalEquivEncoded :
    Structured.MultiTapeLowering.StructuredLogicalEquivEncodedTapes
      (canonicalLogicalTapes bits suffixTail)
      (canonicalTarget bits suffixTail)
  guardedSourceEquiv :
    Tape.Equiv
      (canonicalGuardedSourceTape bits suffixTail)
      (canonicalSource bits suffixTail)
  guardedScratchEquiv :
    Tape.Equiv canonicalGuardedScratchTape Tape.blank
  guardedOutputEquiv :
    Tape.Equiv
      (canonicalGuardedOutputTape bits suffixTail)
      (canonicalOutput bits suffixTail)
  guardedLogicalTapesHaveGuardCells :
    Structured.MultiTapeLowering.LogicalTapesHaveGuardCells
      (canonicalGuardedLogicalTapes bits suffixTail)
  atSeparator0 :
    Structured.MultiTapeLowering.AtTapeSeparator
      (canonicalGuardedLogicalTapes bits suffixTail) 0
      (canonicalTarget bits suffixTail)
  atSeparator1 :
    Structured.MultiTapeLowering.AtTapeSeparator
      (canonicalGuardedLogicalTapes bits suffixTail) 1
      (canonicalSeparator1Tape bits suffixTail)
  atSeparator2 :
    Structured.MultiTapeLowering.AtTapeSeparator
      (canonicalGuardedLogicalTapes bits suffixTail) 2
      (canonicalSeparator2Tape bits suffixTail)
  atExistingSeparator0 :
    Structured.MultiTapeLowering.AtExistingTapeSeparator
      (canonicalGuardedLogicalTapes bits suffixTail) 0
      (canonicalTarget bits suffixTail)
  atExistingSeparator1 :
    Structured.MultiTapeLowering.AtExistingTapeSeparator
      (canonicalGuardedLogicalTapes bits suffixTail) 1
      (canonicalSeparator1Tape bits suffixTail)
  atExistingSeparator2 :
    Structured.MultiTapeLowering.AtExistingTapeSeparator
      (canonicalGuardedLogicalTapes bits suffixTail) 2
      (canonicalSeparator2Tape bits suffixTail)
  atHeadMarker0 :
    Structured.MultiTapeLowering.AtTapeHeadMarker
      (canonicalGuardedLogicalTapes bits suffixTail) 0
      (canonicalHeadMarker0Tape bits suffixTail)
  atHeadMarker1 :
    Structured.MultiTapeLowering.AtTapeHeadMarker
      (canonicalGuardedLogicalTapes bits suffixTail) 1
      (canonicalHeadMarker1Tape bits suffixTail)
  atHeadMarker2 :
    Structured.MultiTapeLowering.AtTapeHeadMarker
      (canonicalGuardedLogicalTapes bits suffixTail) 2
      (canonicalHeadMarker2Tape bits suffixTail)
  atHeadCell0 :
    Structured.MultiTapeLowering.AtTapeHeadCellCode
      (canonicalGuardedLogicalTapes bits suffixTail) 0
      (canonicalHeadCell0Tape bits suffixTail)
  atHeadCell1 :
    Structured.MultiTapeLowering.AtTapeHeadCellCode
      (canonicalGuardedLogicalTapes bits suffixTail) 1
      (canonicalHeadCell1Tape bits suffixTail)
  atHeadCell2 :
    Structured.MultiTapeLowering.AtTapeHeadCellCode
      (canonicalGuardedLogicalTapes bits suffixTail) 2
      (canonicalHeadCell2Tape bits suffixTail)
  atSegmentEnd0 :
    Structured.MultiTapeLowering.AtTapeSegmentEnd
      (canonicalGuardedLogicalTapes bits suffixTail) 0
      (canonicalSegmentEnd0Tape bits suffixTail)
  atSegmentEnd1 :
    Structured.MultiTapeLowering.AtTapeSegmentEnd
      (canonicalGuardedLogicalTapes bits suffixTail) 1
      (canonicalSegmentEnd1Tape bits suffixTail)
  atSegmentEnd2 :
    Structured.MultiTapeLowering.AtTapeSegmentEnd
      (canonicalGuardedLogicalTapes bits suffixTail) 2
      (canonicalSegmentEnd2Tape bits suffixTail)

theorem canonicalEndpointShape
    (bits suffixTail : Word Bool) :
    CanonicalEndpointShape bits suffixTail :=
  { sourceCells := canonicalSource_cells bits suffixTail
    outputCells := canonicalOutput_cells bits suffixTail
    targetRead := canonicalTarget_read bits suffixTail
    targetCells := canonicalTarget_cells bits suffixTail
    targetCellsInitializer :=
      canonicalTarget_cells_via_initializerTargetTape bits suffixTail
    targetNormalizedOutput :=
      canonicalTarget_normalizedOutput_eq_guardedLogicalBits
        bits suffixTail
    targetNormalizedOutputInitializer :=
      canonicalTarget_normalizedOutput_eq_initializerTargetTape
        bits suffixTail
    structuredEncoded :=
      canonicalTarget_structuredEncodedTapes bits suffixTail
    structuredGuardedEncoded :=
      canonicalTarget_structuredGuardedEncodedTapes bits suffixTail
    structuredLogicalEquivEncoded :=
      canonicalTarget_structuredLogicalEquivEncodedTapes bits suffixTail
    guardedSourceEquiv :=
      canonicalGuardedSourceTape_equiv bits suffixTail
    guardedScratchEquiv := canonicalGuardedScratchTape_equiv
    guardedOutputEquiv :=
      canonicalGuardedOutputTape_equiv bits suffixTail
    guardedLogicalTapesHaveGuardCells :=
      canonicalGuardedLogicalTapes_haveGuardCells bits suffixTail
    atSeparator0 := canonicalAtSeparator0 bits suffixTail
    atSeparator1 := canonicalAtSeparator1 bits suffixTail
    atSeparator2 := canonicalAtSeparator2 bits suffixTail
    atExistingSeparator0 :=
      canonicalAtExistingSeparator0 bits suffixTail
    atExistingSeparator1 :=
      canonicalAtExistingSeparator1 bits suffixTail
    atExistingSeparator2 :=
      canonicalAtExistingSeparator2 bits suffixTail
    atHeadMarker0 := canonicalAtHeadMarker0 bits suffixTail
    atHeadMarker1 := canonicalAtHeadMarker1 bits suffixTail
    atHeadMarker2 := canonicalAtHeadMarker2 bits suffixTail
    atHeadCell0 := canonicalAtHeadCell0 bits suffixTail
    atHeadCell1 := canonicalAtHeadCell1 bits suffixTail
    atHeadCell2 := canonicalAtHeadCell2 bits suffixTail
    atSegmentEnd0 := canonicalAtSegmentEnd0 bits suffixTail
    atSegmentEnd1 := canonicalAtSegmentEnd1 bits suffixTail
    atSegmentEnd2 := canonicalAtSegmentEnd2 bits suffixTail }

/-!
## Indexed endpoint shape
-/

structure IndexedEndpointShape {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) : Prop where
  sourceCells :
    Tape.cells (indexedSource bits suffixTail rightPadding input) =
      none ::
        List.append
          ((List.append boolWordRawBitsDecoderHeaderBits
            (List.append
              (boolWordRawBitsDecoderEncodedFieldBits (bits input))
              (false :: suffixTail input))).map some)
          (none :: rightPadding input)
  outputCells :
    Tape.cells (indexedOutput bits outputPadding input) =
      none ::
        List.append
          (List.replicate ((bits input).length + 1)
            (none : Option Bool))
          (outputPadding input)
  targetRead :
    Tape.read
        (indexedTarget bits suffixTail rightPadding outputPadding input) =
      none
  targetCells :
    Tape.cells
        (indexedTarget bits suffixTail rightPadding outputPadding input) =
      List.append Structured.MultiTapeLowering.tapeSeparatorCells
        (List.append (Structured.MultiTapeLowering.logicalTapeCode
            (Structured.MultiTapeLowering.guardLogicalTape
              (indexedSource bits suffixTail rightPadding input)))
          (List.append Structured.MultiTapeLowering.tapeSeparatorCells
            (List.append (Structured.MultiTapeLowering.logicalTapeCode
                (Structured.MultiTapeLowering.guardLogicalTape Tape.blank))
              (List.append Structured.MultiTapeLowering.tapeSeparatorCells
                (List.append (Structured.MultiTapeLowering.logicalTapeCode
                    (Structured.MultiTapeLowering.guardLogicalTape
                      (indexedOutput bits outputPadding input)))
                  Structured.MultiTapeLowering.tapeSeparatorCells)))))
  targetNormalizedOutput :
    Tape.normalizedOutput
        (indexedTarget bits suffixTail rightPadding outputPadding input) =
      List.append
        (Structured.MultiTapeLowering.logicalTapeBits
          (indexedGuardedSourceTape bits suffixTail rightPadding input))
        (List.append
          (Structured.MultiTapeLowering.logicalTapeBits
            canonicalGuardedScratchTape)
          (Structured.MultiTapeLowering.logicalTapeBits
            (indexedGuardedOutputTape bits outputPadding input)))
  targetNormalizedOutputNamed :
    Tape.normalizedOutput
        (indexedTarget bits suffixTail rightPadding outputPadding input) =
      Tape.normalizedOutput
        (structuredBoolWordRawBitsDecoderIndexedInputMaterializerTargetTape
          bits suffixTail rightPadding outputPadding input)
  structuredEncoded :
    Structured.MultiTapeLowering.StructuredEncodedTapes
      (indexedGuardedLogicalTapes
        bits suffixTail rightPadding outputPadding input)
      (indexedTarget bits suffixTail rightPadding outputPadding input)
  structuredGuardedEncoded :
    Structured.MultiTapeLowering.StructuredGuardedEncodedTapes
      (indexedLogicalTapes
        bits suffixTail rightPadding outputPadding input)
      (indexedTarget bits suffixTail rightPadding outputPadding input)
  structuredLogicalEquivEncoded :
    Structured.MultiTapeLowering.StructuredLogicalEquivEncodedTapes
      (indexedLogicalTapes
        bits suffixTail rightPadding outputPadding input)
      (indexedTarget bits suffixTail rightPadding outputPadding input)
  guardedSourceEquiv :
    Tape.Equiv
      (indexedGuardedSourceTape bits suffixTail rightPadding input)
      (indexedSource bits suffixTail rightPadding input)
  guardedOutputEquiv :
    Tape.Equiv
      (indexedGuardedOutputTape bits outputPadding input)
      (indexedOutput bits outputPadding input)
  guardedLogicalTapesHaveGuardCells :
    Structured.MultiTapeLowering.LogicalTapesHaveGuardCells
      (indexedGuardedLogicalTapes
        bits suffixTail rightPadding outputPadding input)
  atSeparator0 :
    Structured.MultiTapeLowering.AtTapeSeparator
      (indexedGuardedLogicalTapes
        bits suffixTail rightPadding outputPadding input) 0
      (indexedTarget bits suffixTail rightPadding outputPadding input)
  atSeparator1 :
    Structured.MultiTapeLowering.AtTapeSeparator
      (indexedGuardedLogicalTapes
        bits suffixTail rightPadding outputPadding input) 1
      (indexedSeparator1Tape
        bits suffixTail rightPadding outputPadding input)
  atSeparator2 :
    Structured.MultiTapeLowering.AtTapeSeparator
      (indexedGuardedLogicalTapes
        bits suffixTail rightPadding outputPadding input) 2
      (indexedSeparator2Tape
        bits suffixTail rightPadding outputPadding input)
  atExistingSeparator0 :
    Structured.MultiTapeLowering.AtExistingTapeSeparator
      (indexedGuardedLogicalTapes
        bits suffixTail rightPadding outputPadding input) 0
      (indexedTarget bits suffixTail rightPadding outputPadding input)
  atExistingSeparator1 :
    Structured.MultiTapeLowering.AtExistingTapeSeparator
      (indexedGuardedLogicalTapes
        bits suffixTail rightPadding outputPadding input) 1
      (indexedSeparator1Tape
        bits suffixTail rightPadding outputPadding input)
  atExistingSeparator2 :
    Structured.MultiTapeLowering.AtExistingTapeSeparator
      (indexedGuardedLogicalTapes
        bits suffixTail rightPadding outputPadding input) 2
      (indexedSeparator2Tape
        bits suffixTail rightPadding outputPadding input)
  atHeadCell0 :
    Structured.MultiTapeLowering.AtTapeHeadCellCode
      (indexedGuardedLogicalTapes
        bits suffixTail rightPadding outputPadding input) 0
      (indexedHeadCell0Tape
        bits suffixTail rightPadding outputPadding input)
  atHeadCell1 :
    Structured.MultiTapeLowering.AtTapeHeadCellCode
      (indexedGuardedLogicalTapes
        bits suffixTail rightPadding outputPadding input) 1
      (indexedHeadCell1Tape
        bits suffixTail rightPadding outputPadding input)
  atHeadCell2 :
    Structured.MultiTapeLowering.AtTapeHeadCellCode
      (indexedGuardedLogicalTapes
        bits suffixTail rightPadding outputPadding input) 2
      (indexedHeadCell2Tape
        bits suffixTail rightPadding outputPadding input)
  atSegmentEnd0 :
    Structured.MultiTapeLowering.AtTapeSegmentEnd
      (indexedGuardedLogicalTapes
        bits suffixTail rightPadding outputPadding input) 0
      (indexedSegmentEnd0Tape
        bits suffixTail rightPadding outputPadding input)
  atSegmentEnd1 :
    Structured.MultiTapeLowering.AtTapeSegmentEnd
      (indexedGuardedLogicalTapes
        bits suffixTail rightPadding outputPadding input) 1
      (indexedSegmentEnd1Tape
        bits suffixTail rightPadding outputPadding input)
  atSegmentEnd2 :
    Structured.MultiTapeLowering.AtTapeSegmentEnd
      (indexedGuardedLogicalTapes
        bits suffixTail rightPadding outputPadding input) 2
      (indexedSegmentEnd2Tape
        bits suffixTail rightPadding outputPadding input)

theorem indexedEndpointShape {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) :
    IndexedEndpointShape bits suffixTail rightPadding outputPadding input :=
  { sourceCells := indexedSource_cells bits suffixTail rightPadding input
    outputCells := indexedOutput_cells bits outputPadding input
    targetRead :=
      indexedTarget_read bits suffixTail rightPadding outputPadding input
    targetCells :=
      indexedTarget_cells bits suffixTail rightPadding outputPadding input
    targetNormalizedOutput :=
      indexedTarget_normalizedOutput_eq_guardedLogicalBits
        bits suffixTail rightPadding outputPadding input
    targetNormalizedOutputNamed :=
      indexedTarget_normalizedOutput_eq_namedTargetTape
        bits suffixTail rightPadding outputPadding input
    structuredEncoded :=
      indexedTarget_structuredEncodedTapes
        bits suffixTail rightPadding outputPadding input
    structuredGuardedEncoded :=
      indexedTarget_structuredGuardedEncodedTapes
        bits suffixTail rightPadding outputPadding input
    structuredLogicalEquivEncoded :=
      indexedTarget_structuredLogicalEquivEncodedTapes
        bits suffixTail rightPadding outputPadding input
    guardedSourceEquiv :=
      indexedGuardedSourceTape_equiv bits suffixTail rightPadding input
    guardedOutputEquiv :=
      indexedGuardedOutputTape_equiv bits outputPadding input
    guardedLogicalTapesHaveGuardCells :=
      indexedGuardedLogicalTapes_haveGuardCells
        bits suffixTail rightPadding outputPadding input
    atSeparator0 :=
      indexedAtSeparator0 bits suffixTail rightPadding outputPadding input
    atSeparator1 :=
      indexedAtSeparator1 bits suffixTail rightPadding outputPadding input
    atSeparator2 :=
      indexedAtSeparator2 bits suffixTail rightPadding outputPadding input
    atExistingSeparator0 :=
      indexedAtExistingSeparator0
        bits suffixTail rightPadding outputPadding input
    atExistingSeparator1 :=
      indexedAtExistingSeparator1
        bits suffixTail rightPadding outputPadding input
    atExistingSeparator2 :=
      indexedAtExistingSeparator2
        bits suffixTail rightPadding outputPadding input
    atHeadCell0 :=
      indexedAtHeadCell0 bits suffixTail rightPadding outputPadding input
    atHeadCell1 :=
      indexedAtHeadCell1 bits suffixTail rightPadding outputPadding input
    atHeadCell2 :=
      indexedAtHeadCell2 bits suffixTail rightPadding outputPadding input
    atSegmentEnd0 :=
      indexedAtSegmentEnd0 bits suffixTail rightPadding outputPadding input
    atSegmentEnd1 :=
      indexedAtSegmentEnd1 bits suffixTail rightPadding outputPadding input
    atSegmentEnd2 :=
      indexedAtSegmentEnd2 bits suffixTail rightPadding outputPadding input }

/-!
## Route-facing endpoint bundles
-/

structure ExactCanonicalEndpointRouteSpec
    (materializer : MachineDescription) : Prop where
  route : ExactCanonicalRouteSpec materializer
  endpoint :
    forall input : Word Bool × Word Bool,
      CanonicalEndpointShape input.1 input.2
  indexedEndpoint :
    forall input : Word Bool × Word Bool,
      IndexedEndpointShape
        canonicalIndexedBits
        canonicalIndexedSuffixTail
        canonicalIndexedRightPadding
        canonicalIndexedOutputPadding
        input

def ExactCanonicalEndpointRouteConstruction : Prop :=
  exists materializer : MachineDescription,
    ExactCanonicalEndpointRouteSpec materializer

theorem exactCanonicalEndpointRouteSpec_of_routeSpec
    {materializer : MachineDescription}
    (hroute : ExactCanonicalRouteSpec materializer) :
    ExactCanonicalEndpointRouteSpec materializer :=
  { route := hroute
    endpoint := fun input => canonicalEndpointShape input.1 input.2
    indexedEndpoint := fun input =>
      indexedEndpointShape
        canonicalIndexedBits
        canonicalIndexedSuffixTail
        canonicalIndexedRightPadding
        canonicalIndexedOutputPadding
        input }

theorem exactCanonicalRouteSpec_of_endpointRouteSpec
    {materializer : MachineDescription}
    (hroute : ExactCanonicalEndpointRouteSpec materializer) :
    ExactCanonicalRouteSpec materializer :=
  hroute.route

theorem exactCanonicalEndpointRouteConstruction_of_routeConstruction
    (hroute : ExactCanonicalRouteConstruction) :
    ExactCanonicalEndpointRouteConstruction := by
  rcases hroute with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      exactCanonicalEndpointRouteSpec_of_routeSpec hspec⟩

theorem exactCanonicalRouteConstruction_of_endpointRouteConstruction
    (hroute : ExactCanonicalEndpointRouteConstruction) :
    ExactCanonicalRouteConstruction := by
  rcases hroute with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      exactCanonicalRouteSpec_of_endpointRouteSpec hspec⟩

theorem exactCanonicalEndpointRouteConstruction_iff_routeConstruction :
    ExactCanonicalEndpointRouteConstruction ↔
      ExactCanonicalRouteConstruction := by
  constructor
  · exact exactCanonicalRouteConstruction_of_endpointRouteConstruction
  · exact exactCanonicalEndpointRouteConstruction_of_routeConstruction

structure OutputCanonicalEndpointRouteSpec
    (materializer : MachineDescription) : Prop where
  route : OutputCanonicalRouteSpec materializer
  endpoint :
    forall input : Word Bool × Word Bool,
      CanonicalEndpointShape input.1 input.2
  indexedEndpoint :
    forall input : Word Bool × Word Bool,
      IndexedEndpointShape
        canonicalIndexedBits
        canonicalIndexedSuffixTail
        canonicalIndexedRightPadding
        canonicalIndexedOutputPadding
        input

def OutputCanonicalEndpointRouteConstruction : Prop :=
  exists materializer : MachineDescription,
    OutputCanonicalEndpointRouteSpec materializer

theorem outputCanonicalEndpointRouteSpec_of_outputRouteSpec
    {materializer : MachineDescription}
    (hroute : OutputCanonicalRouteSpec materializer) :
    OutputCanonicalEndpointRouteSpec materializer :=
  { route := hroute
    endpoint := fun input => canonicalEndpointShape input.1 input.2
    indexedEndpoint := fun input =>
      indexedEndpointShape
        canonicalIndexedBits
        canonicalIndexedSuffixTail
        canonicalIndexedRightPadding
        canonicalIndexedOutputPadding
        input }

theorem outputCanonicalRouteSpec_of_endpointRouteSpec
    {materializer : MachineDescription}
    (hroute : OutputCanonicalEndpointRouteSpec materializer) :
    OutputCanonicalRouteSpec materializer :=
  hroute.route

theorem outputCanonicalEndpointRouteConstruction_of_outputRouteConstruction
    (hroute : OutputCanonicalRouteConstruction) :
    OutputCanonicalEndpointRouteConstruction := by
  rcases hroute with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      outputCanonicalEndpointRouteSpec_of_outputRouteSpec hspec⟩

theorem outputCanonicalRouteConstruction_of_endpointRouteConstruction
    (hroute : OutputCanonicalEndpointRouteConstruction) :
    OutputCanonicalRouteConstruction := by
  rcases hroute with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      outputCanonicalRouteSpec_of_endpointRouteSpec hspec⟩

theorem outputCanonicalEndpointRouteConstruction_iff_outputRouteConstruction :
    OutputCanonicalEndpointRouteConstruction ↔
      OutputCanonicalRouteConstruction := by
  constructor
  · exact outputCanonicalRouteConstruction_of_endpointRouteConstruction
  · exact outputCanonicalEndpointRouteConstruction_of_outputRouteConstruction

theorem outputCanonicalEndpointRouteSpec_of_exactEndpointRouteSpec
    {materializer : MachineDescription}
    (hroute : ExactCanonicalEndpointRouteSpec materializer) :
    OutputCanonicalEndpointRouteSpec materializer :=
  { route := outputCanonicalRouteSpec_of_exactRouteSpec hroute.route
    endpoint := hroute.endpoint
    indexedEndpoint := hroute.indexedEndpoint }

theorem outputCanonicalEndpointRouteConstruction_of_exactEndpointRouteConstruction
    (hroute : ExactCanonicalEndpointRouteConstruction) :
    OutputCanonicalEndpointRouteConstruction := by
  rcases hroute with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      outputCanonicalEndpointRouteSpec_of_exactEndpointRouteSpec hspec⟩

theorem outputCanonicalEndpointRouteConstruction_of_exactRouteConstruction
    (hroute : ExactCanonicalRouteConstruction) :
    OutputCanonicalEndpointRouteConstruction :=
  outputCanonicalEndpointRouteConstruction_of_exactEndpointRouteConstruction
    (exactCanonicalEndpointRouteConstruction_of_routeConstruction hroute)

theorem exactCanonicalEndpointRouteConstruction_of_materializerConstruction
    (hmaterializer :
      StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerConstruction) :
    ExactCanonicalEndpointRouteConstruction :=
  exactCanonicalEndpointRouteConstruction_of_routeConstruction
    (exactCanonicalRouteConstruction_of_materializer hmaterializer)

theorem outputCanonicalEndpointRouteConstruction_of_materializerConstruction
    (hmaterializer :
      StructuredBoolWordRawBitsDecoderCanonicalInputMaterializerConstruction) :
    OutputCanonicalEndpointRouteConstruction :=
  outputCanonicalEndpointRouteConstruction_of_exactEndpointRouteConstruction
    (exactCanonicalEndpointRouteConstruction_of_materializerConstruction
      hmaterializer)

/-!
## Field projections
-/

theorem exactRouteSpec_of_exactEndpointRouteConstruction
    (hroute : ExactCanonicalEndpointRouteConstruction) :
    ExactCanonicalRouteConstruction :=
  exactCanonicalRouteConstruction_of_endpointRouteConstruction hroute

theorem outputRouteSpec_of_outputEndpointRouteConstruction
    (hroute : OutputCanonicalEndpointRouteConstruction) :
    OutputCanonicalRouteConstruction :=
  outputCanonicalRouteConstruction_of_endpointRouteConstruction hroute

theorem canonicalEndpointShape_of_exactEndpointRouteConstruction
    (hroute : ExactCanonicalEndpointRouteConstruction)
    (bits suffixTail : Word Bool) :
    CanonicalEndpointShape bits suffixTail := by
  rcases hroute with ⟨_materializer, hspec⟩
  exact hspec.endpoint (bits, suffixTail)

theorem canonicalEndpointShape_of_outputEndpointRouteConstruction
    (hroute : OutputCanonicalEndpointRouteConstruction)
    (bits suffixTail : Word Bool) :
    CanonicalEndpointShape bits suffixTail := by
  rcases hroute with ⟨_materializer, hspec⟩
  exact hspec.endpoint (bits, suffixTail)

theorem canonicalIndexedEndpointShape_of_exactEndpointRouteConstruction
    (hroute : ExactCanonicalEndpointRouteConstruction)
    (input : Word Bool × Word Bool) :
    IndexedEndpointShape
      canonicalIndexedBits
      canonicalIndexedSuffixTail
      canonicalIndexedRightPadding
      canonicalIndexedOutputPadding
      input := by
  rcases hroute with ⟨_materializer, hspec⟩
  exact hspec.indexedEndpoint input

theorem canonicalIndexedEndpointShape_of_outputEndpointRouteConstruction
    (hroute : OutputCanonicalEndpointRouteConstruction)
    (input : Word Bool × Word Bool) :
    IndexedEndpointShape
      canonicalIndexedBits
      canonicalIndexedSuffixTail
      canonicalIndexedRightPadding
      canonicalIndexedOutputPadding
      input := by
  rcases hroute with ⟨_materializer, hspec⟩
  exact hspec.indexedEndpoint input

theorem canonicalTarget_read_of_exactEndpointRouteConstruction
    (hroute : ExactCanonicalEndpointRouteConstruction)
    (bits suffixTail : Word Bool) :
    Tape.read (canonicalTarget bits suffixTail) = none :=
  (canonicalEndpointShape_of_exactEndpointRouteConstruction
    hroute bits suffixTail).targetRead

theorem canonicalTarget_structuredLogicalEquivEncodedTapes_of_exactEndpointRouteConstruction
    (hroute : ExactCanonicalEndpointRouteConstruction)
    (bits suffixTail : Word Bool) :
    Structured.MultiTapeLowering.StructuredLogicalEquivEncodedTapes
      (canonicalLogicalTapes bits suffixTail)
      (canonicalTarget bits suffixTail) :=
  (canonicalEndpointShape_of_exactEndpointRouteConstruction
    hroute bits suffixTail).structuredLogicalEquivEncoded

theorem canonicalAtSeparator0_of_exactEndpointRouteConstruction
    (hroute : ExactCanonicalEndpointRouteConstruction)
    (bits suffixTail : Word Bool) :
    Structured.MultiTapeLowering.AtTapeSeparator
      (canonicalGuardedLogicalTapes bits suffixTail) 0
      (canonicalTarget bits suffixTail) :=
  (canonicalEndpointShape_of_exactEndpointRouteConstruction
    hroute bits suffixTail).atSeparator0

theorem canonicalAtSeparator2_of_exactEndpointRouteConstruction
    (hroute : ExactCanonicalEndpointRouteConstruction)
    (bits suffixTail : Word Bool) :
    Structured.MultiTapeLowering.AtTapeSeparator
      (canonicalGuardedLogicalTapes bits suffixTail) 2
      (canonicalSeparator2Tape bits suffixTail) :=
  (canonicalEndpointShape_of_exactEndpointRouteConstruction
    hroute bits suffixTail).atSeparator2

theorem canonicalAtSegmentEnd2_of_exactEndpointRouteConstruction
    (hroute : ExactCanonicalEndpointRouteConstruction)
    (bits suffixTail : Word Bool) :
    Structured.MultiTapeLowering.AtTapeSegmentEnd
      (canonicalGuardedLogicalTapes bits suffixTail) 2
      (canonicalSegmentEnd2Tape bits suffixTail) :=
  (canonicalEndpointShape_of_exactEndpointRouteConstruction
    hroute bits suffixTail).atSegmentEnd2

end BoolWordRawBitsDecoderInputMaterializerEndpointRoute

end FiniteTransducers
end CommonGround
end Computability
end FoC

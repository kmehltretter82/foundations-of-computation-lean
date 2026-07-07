import FoC.Computability.Compiler.Structured.HeadRoutes.Projectors

set_option doc.verso true

/-!
# Selected-head route pipeline

This module assembles cleanup, scanner, and projector contracts into the
selected-head route bundles consumed by endpoint construction leaves.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

/-!
## Pipeline route

The physical machine assembled here is the same three-phase pipeline as the
singleton decoder: move right from the separator, run the generated scanner,
then run the cleanup.  The only difference is the scanner target used by the
cleanup specification.
-/

/-- Alias for the selected-head pipeline assembled from the cleanup phase. -/
def selectedSegmentLogicalTapeDecoderHeadPipelineDescription
    (cleanup : MachineDescription) : MachineDescription :=
  selectedSegmentLogicalTapeDecoderPipelineDescription cleanup

/-- Subroutine readiness for the padded selected-head decoder pipeline. -/
theorem selectedSegmentLogicalTapeDecoderHeadPipelineDescription_subroutineReady
    {cleanup : MachineDescription}
    (hcleanup : cleanup.SubroutineReady) :
    (selectedSegmentLogicalTapeDecoderHeadPipelineDescription
      cleanup).SubroutineReady := by
  exact
    selectedSegmentLogicalTapeDecoderPipelineDescription_subroutineReady
      hcleanup

/--
The move-right and generated-scanner phases turn the selected-head source into
the padded scanner target expected by
{name}`SelectedSegmentLogicalTapeDecoderHeadCleanupSpec`.
-/
theorem selectedSegmentLogicalTapeDecoderHeadPipelineSpec_of_cleanupSpec
    {cleanup : MachineDescription}
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadCleanupSpec cleanup) :
    StructuredSelectedHeadSegmentDecoderSpec
      (selectedSegmentLogicalTapeDecoderHeadPipelineDescription
        cleanup) := by
  constructor
  · exact
      selectedSegmentLogicalTapeDecoderHeadPipelineDescription_subroutineReady
        hcleanup.left
  · intro target rest encodedPrefix
    have hmove :
        (cursorMoveOnceDescription Direction.right).HaltsFromTapeEquiv
          (tapeAtEncodedSplit encodedPrefix
            (encodedStructuredTapeCells (guardLogicalTape target :: rest)))
          (Tape.move Direction.right
            (tapeAtEncodedSplit encodedPrefix
              (encodedStructuredTapeCells
                (guardLogicalTape target :: rest)))) :=
      (cursorMoveOnceDescription_haltsFromTape Direction.right
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells
            (guardLogicalTape target :: rest)))).toEquiv
    have hscan :
        selectedSegmentLogicalTapeDecoderDescription.HaltsFromTapeEquiv
          (Tape.move Direction.right
            (tapeAtEncodedSplit encodedPrefix
              (encodedStructuredTapeCells
                (guardLogicalTape target :: rest))))
          (selectedSegmentLogicalTapeDecoderHeadTargetTape
            target rest encodedPrefix) :=
      (selectedSegmentLogicalTapeDecoderDescription_haltsFrom_selectedHeadPayload
        target rest encodedPrefix).toEquiv
    have hpipelineScan :
        (canonicalPrimitiveSeqDescription
          (cursorMoveOnceDescription Direction.right)
          selectedSegmentLogicalTapeDecoderDescription).HaltsFromTapeEquiv
            (tapeAtEncodedSplit encodedPrefix
              (encodedStructuredTapeCells
                (guardLogicalTape target :: rest)))
            (selectedSegmentLogicalTapeDecoderHeadTargetTape
              target rest encodedPrefix) :=
      canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
        (cursorMoveOnceDescription_subroutineReady Direction.right)
        selectedSegmentLogicalTapeDecoderDescription_subroutineReady
        hmove
        hscan
    exact
      canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
        (canonicalPrimitiveSeqDescription_subroutineReady
          (cursorMoveOnceDescription_subroutineReady Direction.right)
          selectedSegmentLogicalTapeDecoderDescription_subroutineReady)
        hcleanup.left
        hpipelineScan
        (hcleanup.right target rest encodedPrefix)

/--
The canonical sequence handoff after moving right from a selected-head
separator is literally the same tape.

After crossing the separator, the physical head is on the first encoded guard
cell of the selected logical tape, and that encoded guard cell has a second
physical bit to its right.
-/
theorem canonicalPrimitiveSeqHandoffTape_selectedHeadAfterMove
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) :
    canonicalPrimitiveSeqHandoffTape
        (Tape.move Direction.right
          (tapeAtEncodedSplit encodedPrefix
            (encodedStructuredTapeCells
              (guardLogicalTape target :: rest)))) =
      Tape.move Direction.right
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells
            (guardLogicalTape target :: rest))) := by
  simp [canonicalPrimitiveSeqHandoffTape, tapeAtEncodedSplit,
    encodedStructuredTapeCells, guardLogicalTape, tapeAtCells,
    tapeSeparatorCells, logicalTapeCode, logicalCellListBits,
    logicalCellBits, logicalCellCode, headMarkerCells, Tape.move,
    Tape.moveLeft, Tape.moveRight]

/--
Exact selected-head decoder pipeline from an exact cleanup phase.

This is the literal-tape version of
{name}`selectedSegmentLogicalTapeDecoderHeadPipelineSpec_of_cleanupSpec`.
The closed side uses deterministic exact halting for the generated move and
scanner phases, then delegates the final target shape to the exact cleanup
contract.
-/
theorem selectedSegmentLogicalTapeDecoderHeadPipelineExactSpec_of_exactCleanupSpec
    {cleanup : MachineDescription}
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadExactCleanupSpec cleanup) :
    StructuredSelectedHeadSegmentDecoderExactSpec
      (selectedSegmentLogicalTapeDecoderHeadPipelineDescription
        cleanup) := by
  constructor
  · exact
      selectedSegmentLogicalTapeDecoderHeadPipelineDescription_subroutineReady
        hcleanup.subroutineReady
  · intro target rest encodedPrefix
    let source :=
      tapeAtEncodedSplit encodedPrefix
        (encodedStructuredTapeCells (guardLogicalTape target :: rest))
    let moved := Tape.move Direction.right source
    let scanned :=
      selectedSegmentLogicalTapeDecoderHeadTargetTape
        target rest encodedPrefix
    have hmove :
        (cursorMoveOnceDescription Direction.right).HaltsFromTape
          source moved := by
      exact cursorMoveOnceDescription_haltsFromTape Direction.right source
    have hscanMoved :
        selectedSegmentLogicalTapeDecoderDescription.HaltsFromTape
          moved scanned := by
      simpa [source, moved, scanned] using
        selectedSegmentLogicalTapeDecoderDescription_haltsFrom_selectedHeadPayload
          target rest encodedPrefix
    have hmoved :
        canonicalPrimitiveSeqHandoffTape moved = moved := by
      simpa [source, moved] using
        canonicalPrimitiveSeqHandoffTape_selectedHeadAfterMove
          target rest encodedPrefix
    have hscan :
        selectedSegmentLogicalTapeDecoderDescription.HaltsFromTape
          (canonicalPrimitiveSeqHandoffTape moved)
          scanned := by
      rw [hmoved]
      exact hscanMoved
    have hpipelineScan :
        (canonicalPrimitiveSeqDescription
          (cursorMoveOnceDescription Direction.right)
          selectedSegmentLogicalTapeDecoderDescription).HaltsFromTape
            source scanned :=
      canonicalPrimitiveSeqDescription_haltsFromTape_exact
        (cursorMoveOnceDescription_subroutineReady Direction.right)
        selectedSegmentLogicalTapeDecoderDescription_subroutineReady
        hmove hscan
    have hpipeline :
        (selectedSegmentLogicalTapeDecoderHeadPipelineDescription
          cleanup).HaltsFromTape source target :=
      by
        simpa [selectedSegmentLogicalTapeDecoderHeadPipelineDescription,
          selectedSegmentLogicalTapeDecoderPipelineDescription, source,
          scanned] using
          canonicalPrimitiveSeqDescription_haltsFromTape_exact
            (canonicalPrimitiveSeqDescription_subroutineReady
              (cursorMoveOnceDescription_subroutineReady Direction.right)
              selectedSegmentLogicalTapeDecoderDescription_subroutineReady)
            hcleanup.subroutineReady
            hpipelineScan
            (hcleanup.forward target rest encodedPrefix)
    simpa [source] using hpipeline
  · intro target rest encodedPrefix
    let source :=
      tapeAtEncodedSplit encodedPrefix
        (encodedStructuredTapeCells (guardLogicalTape target :: rest))
    let moved := Tape.move Direction.right source
    let scanned :=
      selectedSegmentLogicalTapeDecoderHeadTargetTape
        target rest encodedPrefix
    have hmove :
        (cursorMoveOnceDescription Direction.right).HaltsFromTape
          source moved := by
      exact cursorMoveOnceDescription_haltsFromTape Direction.right source
    have hscanMoved :
        selectedSegmentLogicalTapeDecoderDescription.HaltsFromTape
          moved scanned := by
      simpa [source, moved, scanned] using
        selectedSegmentLogicalTapeDecoderDescription_haltsFrom_selectedHeadPayload
          target rest encodedPrefix
    have hmoved :
        canonicalPrimitiveSeqHandoffTape moved = moved := by
      simpa [source, moved] using
        canonicalPrimitiveSeqHandoffTape_selectedHeadAfterMove
          target rest encodedPrefix
    have hscan :
        selectedSegmentLogicalTapeDecoderDescription.HaltsFromTape
          (canonicalPrimitiveSeqHandoffTape moved)
          scanned := by
      rw [hmoved]
      exact hscanMoved
    have hpipelineScanClosed :
        ExactClosedFromTape
          (canonicalPrimitiveSeqDescription
            (cursorMoveOnceDescription Direction.right)
            selectedSegmentLogicalTapeDecoderDescription)
          source scanned :=
      canonicalPrimitiveSeqDescription_exactClosedFromTape
        (cursorMoveOnceDescription_subroutineReady Direction.right)
        selectedSegmentLogicalTapeDecoderDescription_subroutineReady
        (by
          intro T hhalt
          exact
            MachineDescription.haltsFromTape_functional_of_haltTransitionFree
              (cursorMoveOnceDescription_subroutineReady
                Direction.right).right hhalt hmove)
        (by
          intro T hhalt
          exact
            MachineDescription.haltsFromTape_functional_of_haltTransitionFree
              selectedSegmentLogicalTapeDecoderDescription_subroutineReady.right
              hhalt hscan)
    have hpipelineClosed :
        ExactClosedFromTape
          (selectedSegmentLogicalTapeDecoderHeadPipelineDescription
            cleanup)
          source target :=
      by
        simpa [selectedSegmentLogicalTapeDecoderHeadPipelineDescription,
          selectedSegmentLogicalTapeDecoderPipelineDescription, source,
          scanned] using
          canonicalPrimitiveSeqDescription_exactClosedFromTape
            (canonicalPrimitiveSeqDescription_subroutineReady
              (cursorMoveOnceDescription_subroutineReady Direction.right)
              selectedSegmentLogicalTapeDecoderDescription_subroutineReady)
            hcleanup.subroutineReady
            hpipelineScanClosed
            (hcleanup.closed target rest encodedPrefix)
    simpa [source] using hpipelineClosed

/-- Build an exact selected-head decoder from an exact cleanup phase. -/
theorem structuredSelectedHeadSegmentDecoderExactConstruction_of_exactHeadCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction) :
    StructuredSelectedHeadSegmentDecoderExactConstruction := by
  rcases hcleanup with ⟨cleanup, hcleanupSpec⟩
  exact
    ⟨selectedSegmentLogicalTapeDecoderHeadPipelineDescription cleanup,
      selectedSegmentLogicalTapeDecoderHeadPipelineExactSpec_of_exactCleanupSpec
        hcleanupSpec⟩

/-- Exact tape-2 projector from exact selected-head cleanup. -/
theorem structuredTape2ExactProjectorConstruction_of_exactHeadCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction) :
    StructuredTape2ExactProjectorConstruction :=
  structuredTape2ExactProjectorConstruction_of_exactHeadDecoder
    (structuredSelectedHeadSegmentDecoderExactConstruction_of_exactHeadCleanup
      hcleanup)

/-- Equivalence tape-2 projector from exact selected-head cleanup. -/
theorem structuredTape2ProjectorConstruction_of_exactHeadCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction) :
    StructuredTape2ProjectorConstruction :=
  structuredTape2ProjectorConstruction_of_exact
    (structuredTape2ExactProjectorConstruction_of_exactHeadCleanup hcleanup)

/-- Exact selected-head decoder from forward-split exact cleanup. -/
theorem structuredSelectedHeadSegmentDecoderExactConstruction_of_exactHeadCleanupForwardSplit
    (hsplit :
      SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitConstruction) :
    StructuredSelectedHeadSegmentDecoderExactConstruction :=
  structuredSelectedHeadSegmentDecoderExactConstruction_of_exactHeadCleanup
    (selectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction_of_forwardSplit
      hsplit)

/-- Exact tape-2 projector from forward-split exact cleanup. -/
theorem structuredTape2ExactProjectorConstruction_of_exactHeadCleanupForwardSplit
    (hsplit :
      SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitConstruction) :
    StructuredTape2ExactProjectorConstruction :=
  structuredTape2ExactProjectorConstruction_of_exactHeadCleanup
    (selectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction_of_forwardSplit
      hsplit)

/-- Equivalence tape-2 projector from forward-split exact cleanup. -/
theorem structuredTape2ProjectorConstruction_of_exactHeadCleanupForwardSplit
    (hsplit :
      SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitConstruction) :
    StructuredTape2ProjectorConstruction :=
  structuredTape2ProjectorConstruction_of_exact
    (structuredTape2ExactProjectorConstruction_of_exactHeadCleanupForwardSplit
      hsplit)

/--
Legacy bundle of exact selected-head consequences from one forward-split
cleanup construction.

This bundle is over-strong for arbitrary public selected-head targets.  The
public endpoint route should use the equivalence-facing selected-head route
construction, normally obtained from representative cleanup.
-/
structure StructuredSelectedHeadExactDecoderRouteConstruction : Prop where
  exactCleanupForwardSplit :
    SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitConstruction
  exactCleanup :
    SelectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction
  exactHeadDecoder :
    StructuredSelectedHeadSegmentDecoderExactConstruction
  headDecoder :
    StructuredSelectedHeadSegmentDecoderConstruction
  exactTape2Projector :
    StructuredTape2ExactProjectorConstruction
  tape2Projector :
    StructuredTape2ProjectorConstruction

/-- Build the exact selected-head route bundle from forward-split cleanup. -/
theorem structuredSelectedHeadExactDecoderRouteConstruction_of_forwardSplit
    (hsplit :
      SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitConstruction) :
    StructuredSelectedHeadExactDecoderRouteConstruction := by
  let hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction :=
    selectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction_of_forwardSplit
      hsplit
  let hexactHead :
      StructuredSelectedHeadSegmentDecoderExactConstruction :=
    structuredSelectedHeadSegmentDecoderExactConstruction_of_exactHeadCleanup
      hcleanup
  let hhead :
      StructuredSelectedHeadSegmentDecoderConstruction :=
    structuredSelectedHeadSegmentDecoderConstruction_of_exact
      hexactHead
  let hexactProjector :
      StructuredTape2ExactProjectorConstruction :=
    structuredTape2ExactProjectorConstruction_of_exactHeadDecoder
      hexactHead
  let hprojector :
      StructuredTape2ProjectorConstruction :=
    structuredTape2ProjectorConstruction_of_exact
      hexactProjector
  exact
    { exactCleanupForwardSplit := hsplit
      exactCleanup := hcleanup
      exactHeadDecoder := hexactHead
      headDecoder := hhead
      exactTape2Projector := hexactProjector
      tape2Projector := hprojector }

/-- Build a selected-head decoder from a padded selected-head cleanup. -/
theorem structuredSelectedHeadSegmentDecoderConstruction_of_headCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction) :
    StructuredSelectedHeadSegmentDecoderConstruction := by
  rcases hcleanup with ⟨cleanup, hcleanupSpec⟩
  exact
    ⟨selectedSegmentLogicalTapeDecoderHeadPipelineDescription cleanup,
      selectedSegmentLogicalTapeDecoderHeadPipelineSpec_of_cleanupSpec
        hcleanupSpec⟩

/-- The selected-head cleanup route also supplies the selected singleton decoder. -/
theorem structuredSelectedSingletonSegmentDecoderConstruction_of_headCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction) :
    StructuredSelectedSingletonSegmentDecoderConstruction :=
  structuredSelectedSingletonSegmentDecoderConstruction_of_headDecoder
    (structuredSelectedHeadSegmentDecoderConstruction_of_headCleanup hcleanup)

/-!
## Output route

Many downstream routes only need the normalized public word recovered from the
selected logical tape.  The output route is weaker than the exact
{name}`MachineDescription.HaltsFromTapeEquiv` route but follows immediately
from it.
-/

/-- Normalized-output view of a selected-head decoder. -/
def StructuredSelectedHeadSegmentDecoderOutputSpec
    (decoder : MachineDescription) : Prop :=
  decoder.SubroutineReady ∧
    forall (target : Tape Bool) (rest : List (Tape Bool))
      (encodedPrefix : List (Option Bool)),
      decoder.HaltsFromTapeWithOutput
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells (guardLogicalTape target :: rest)))
        (Tape.normalizedOutput target)

/-- Existence wrapper for the selected-head output route. -/
def StructuredSelectedHeadSegmentDecoderOutputConstruction : Prop :=
  exists decoder : MachineDescription,
    StructuredSelectedHeadSegmentDecoderOutputSpec decoder

/-- Exact selected-head decoding implies the normalized-output route. -/
theorem structuredSelectedHeadSegmentDecoderOutputSpec_of_spec
    {decoder : MachineDescription}
    (hdecoder : StructuredSelectedHeadSegmentDecoderSpec decoder) :
    StructuredSelectedHeadSegmentDecoderOutputSpec decoder := by
  constructor
  · exact hdecoder.left
  · intro target rest encodedPrefix
    exact
      MachineDescription.haltsFromTapeWithOutput_of_haltsFromTapeEquiv
        (hdecoder.right target rest encodedPrefix)

/-- Construction-level exact-to-output adapter for selected-head decoders. -/
theorem structuredSelectedHeadSegmentDecoderOutputConstruction_of_exact
    (hdecoder : StructuredSelectedHeadSegmentDecoderConstruction) :
    StructuredSelectedHeadSegmentDecoderOutputConstruction := by
  rcases hdecoder with ⟨decoder, hdecoderSpec⟩
  exact
    ⟨decoder,
      structuredSelectedHeadSegmentDecoderOutputSpec_of_spec
        hdecoderSpec⟩

/-- Build the selected-head output route directly from padded cleanup. -/
theorem structuredSelectedHeadSegmentDecoderOutputConstruction_of_headCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction) :
    StructuredSelectedHeadSegmentDecoderOutputConstruction :=
  structuredSelectedHeadSegmentDecoderOutputConstruction_of_exact
    (structuredSelectedHeadSegmentDecoderConstruction_of_headCleanup
      hcleanup)

/-!
## Projector consequences

Once a selected-head decoder exists, the generic projection module already
knows how to turn it into the tape 0, tape 1, and tape 2 segment normalizers.
This section packages those consequences so downstream code can depend on one
route bundle rather than rebuilding the same adapters.
-/

/-- Tape-0 segment normalizer from padded selected-head cleanup. -/
theorem structuredTape0SegmentNormalizerConstruction_of_headCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction) :
    StructuredTape0SegmentNormalizerConstruction :=
  structuredTape0SegmentNormalizerConstruction_of_selectedHeadDecoder
    (structuredSelectedHeadSegmentDecoderConstruction_of_headCleanup
      hcleanup)

/-- Tape-1 segment normalizer from padded selected-head cleanup. -/
theorem structuredTape1SegmentNormalizerConstruction_of_headCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction) :
    StructuredTape1SegmentNormalizerConstruction :=
  structuredTape1SegmentNormalizerConstruction_of_selectedHeadDecoder
    (structuredSelectedHeadSegmentDecoderConstruction_of_headCleanup
      hcleanup)

/-- Tape-2 segment normalizer from padded selected-head cleanup. -/
theorem structuredTape2SegmentNormalizerConstruction_of_headCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction) :
    StructuredTape2SegmentNormalizerConstruction :=
  structuredTape2SegmentNormalizerConstruction_of_selectedHeadDecoder
    (structuredSelectedHeadSegmentDecoderConstruction_of_headCleanup
      hcleanup)

/-- Tape-0 projector from padded selected-head cleanup. -/
theorem structuredTape0ProjectorConstruction_of_headCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction) :
    StructuredTape0ProjectorConstruction :=
  structuredTape0ProjectorConstruction_of_segmentNormalizerConstruction
    (structuredTape0SegmentNormalizerConstruction_of_headCleanup
      hcleanup)

/-- Tape-1 projector from padded selected-head cleanup. -/
theorem structuredTape1ProjectorConstruction_of_headCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction) :
    StructuredTape1ProjectorConstruction :=
  structuredTape1ProjectorConstruction_of_segmentNormalizerConstruction
    (structuredTape1SegmentNormalizerConstruction_of_headCleanup
      hcleanup)

/-- Tape-2 projector from padded selected-head cleanup. -/
theorem structuredTape2ProjectorConstruction_of_headCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction) :
    StructuredTape2ProjectorConstruction :=
  structuredTape2ProjectorConstruction_of_segmentNormalizerConstruction
    (structuredTape2SegmentNormalizerConstruction_of_headCleanup
      hcleanup)

/-- Tape-2 projector from branch-split padded selected-head cleanup. -/
theorem structuredTape2ProjectorConstruction_of_headCleanupSplit
    (hsplit :
      SelectedSegmentLogicalTapeDecoderHeadCleanupSplitConstruction) :
    StructuredTape2ProjectorConstruction :=
  structuredTape2ProjectorConstruction_of_headCleanup
    (selectedSegmentLogicalTapeDecoderHeadCleanupConstruction_of_split
      hsplit)

/--
Bundle of selected-head decoder consequences from one padded cleanup premise.

The fields are deliberately redundant.  Later bridge modules commonly need a
specific projection of this route; making each consequence a field avoids
re-deriving local lets through large endpoint proofs.
-/
structure StructuredSelectedHeadDecoderRouteConstruction : Prop where
  headCleanup :
    SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction
  singletonCleanup :
    SelectedSegmentLogicalTapeDecoderCleanupConstruction
  headDecoder :
    StructuredSelectedHeadSegmentDecoderConstruction
  singletonDecoder :
    StructuredSelectedSingletonSegmentDecoderConstruction
  headOutput :
    StructuredSelectedHeadSegmentDecoderOutputConstruction
  tape0SegmentNormalizer :
    StructuredTape0SegmentNormalizerConstruction
  tape1SegmentNormalizer :
    StructuredTape1SegmentNormalizerConstruction
  tape2SegmentNormalizer :
    StructuredTape2SegmentNormalizerConstruction
  tape0Projector :
    StructuredTape0ProjectorConstruction
  tape1Projector :
    StructuredTape1ProjectorConstruction
  tape2Projector :
    StructuredTape2ProjectorConstruction

/-- Build the selected-head route bundle from the padded cleanup premise. -/
theorem structuredSelectedHeadDecoderRouteConstruction_of_headCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction) :
    StructuredSelectedHeadDecoderRouteConstruction := by
  let hhead :
      StructuredSelectedHeadSegmentDecoderConstruction :=
    structuredSelectedHeadSegmentDecoderConstruction_of_headCleanup
      hcleanup
  let hsingletonCleanup :
      SelectedSegmentLogicalTapeDecoderCleanupConstruction :=
    selectedSegmentLogicalTapeDecoderCleanupConstruction_of_headCleanup
      hcleanup
  let hsingleton :
      StructuredSelectedSingletonSegmentDecoderConstruction :=
    structuredSelectedSingletonSegmentDecoderConstruction_of_headDecoder
      hhead
  let houtput :
      StructuredSelectedHeadSegmentDecoderOutputConstruction :=
    structuredSelectedHeadSegmentDecoderOutputConstruction_of_exact
      hhead
  let htape0 :
      StructuredTape0SegmentNormalizerConstruction :=
    structuredTape0SegmentNormalizerConstruction_of_selectedHeadDecoder
      hhead
  let htape1 :
      StructuredTape1SegmentNormalizerConstruction :=
    structuredTape1SegmentNormalizerConstruction_of_selectedHeadDecoder
      hhead
  let htape2 :
      StructuredTape2SegmentNormalizerConstruction :=
    structuredTape2SegmentNormalizerConstruction_of_selectedHeadDecoder
      hhead
  let hproject0 :
      StructuredTape0ProjectorConstruction :=
    structuredTape0ProjectorConstruction_of_segmentNormalizerConstruction
      htape0
  let hproject1 :
      StructuredTape1ProjectorConstruction :=
    structuredTape1ProjectorConstruction_of_segmentNormalizerConstruction
      htape1
  let hproject2 :
      StructuredTape2ProjectorConstruction :=
    structuredTape2ProjectorConstruction_of_segmentNormalizerConstruction
      htape2
  exact
    { headCleanup := hcleanup
      singletonCleanup := hsingletonCleanup
      headDecoder := hhead
      singletonDecoder := hsingleton
      headOutput := houtput
      tape0SegmentNormalizer := htape0
      tape1SegmentNormalizer := htape1
      tape2SegmentNormalizer := htape2
      tape0Projector := hproject0
      tape1Projector := hproject1
      tape2Projector := hproject2 }

/--
Build the selected-head route bundle from branch-split cleanup.

This keeps downstream users at the split boundary when the real finite-machine
cleanup naturally separates the empty-rest and nonempty-rest cases.
-/
theorem structuredSelectedHeadDecoderRouteConstruction_of_headCleanupSplit
    (hsplit :
      SelectedSegmentLogicalTapeDecoderHeadCleanupSplitConstruction) :
    StructuredSelectedHeadDecoderRouteConstruction :=
  structuredSelectedHeadDecoderRouteConstruction_of_headCleanup
    (selectedSegmentLogicalTapeDecoderHeadCleanupConstruction_of_split
      hsplit)

/-!
## Bundle projections

These small projection lemmas keep downstream modules independent from the
internal field names if the route bundle is expanded later.
-/

theorem selectedHeadRoute_headCleanup
    (hroute : StructuredSelectedHeadDecoderRouteConstruction) :
    SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction :=
  hroute.headCleanup

theorem selectedHeadRoute_singletonCleanup
    (hroute : StructuredSelectedHeadDecoderRouteConstruction) :
    SelectedSegmentLogicalTapeDecoderCleanupConstruction :=
  hroute.singletonCleanup

theorem selectedHeadRoute_headDecoder
    (hroute : StructuredSelectedHeadDecoderRouteConstruction) :
    StructuredSelectedHeadSegmentDecoderConstruction :=
  hroute.headDecoder

theorem selectedHeadRoute_singletonDecoder
    (hroute : StructuredSelectedHeadDecoderRouteConstruction) :
    StructuredSelectedSingletonSegmentDecoderConstruction :=
  hroute.singletonDecoder

theorem selectedHeadRoute_headOutput
    (hroute : StructuredSelectedHeadDecoderRouteConstruction) :
    StructuredSelectedHeadSegmentDecoderOutputConstruction :=
  hroute.headOutput

theorem selectedHeadRoute_tape0SegmentNormalizer
    (hroute : StructuredSelectedHeadDecoderRouteConstruction) :
    StructuredTape0SegmentNormalizerConstruction :=
  hroute.tape0SegmentNormalizer

theorem selectedHeadRoute_tape1SegmentNormalizer
    (hroute : StructuredSelectedHeadDecoderRouteConstruction) :
    StructuredTape1SegmentNormalizerConstruction :=
  hroute.tape1SegmentNormalizer

theorem selectedHeadRoute_tape2SegmentNormalizer
    (hroute : StructuredSelectedHeadDecoderRouteConstruction) :
    StructuredTape2SegmentNormalizerConstruction :=
  hroute.tape2SegmentNormalizer

theorem selectedHeadRoute_tape0Projector
    (hroute : StructuredSelectedHeadDecoderRouteConstruction) :
    StructuredTape0ProjectorConstruction :=
  hroute.tape0Projector

theorem selectedHeadRoute_tape1Projector
    (hroute : StructuredSelectedHeadDecoderRouteConstruction) :
    StructuredTape1ProjectorConstruction :=
  hroute.tape1Projector

theorem selectedHeadRoute_tape2Projector
    (hroute : StructuredSelectedHeadDecoderRouteConstruction) :
    StructuredTape2ProjectorConstruction :=
  hroute.tape2Projector


end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC

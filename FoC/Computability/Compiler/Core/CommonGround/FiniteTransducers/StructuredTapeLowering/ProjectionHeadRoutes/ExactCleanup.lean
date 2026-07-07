import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.ProjectionHeadRoutes.RawHeadNormalizer

set_option doc.verso true

/-!
# Exact selected-head cleanup contracts

This module contains the exact padded-cleanup and selected-head cleanup
contracts used by the shared tape-2 projector route.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

def SelectedSegmentLogicalTapeDecoderPaddedCleanupSpec
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (target : Tape Bool) (padding : List (Option Bool))
      (encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
          target padding encodedPrefix)
        target

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupSpec_of_guardedCellShapeSpec
    {cleanup : MachineDescription}
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderGuardedCellShapeCleanupSpec cleanup) :
    SelectedSegmentLogicalTapeDecoderPaddedCleanupSpec cleanup := by
  rcases hcleanup with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro target padding encodedPrefix
  rcases hrun target padding encodedPrefix with
    ⟨actual, hhalts, hequiv⟩
  exact
    ⟨actual, hhalts,
      Tape.Equiv.trans hequiv (guardLogicalTape_equiv target)⟩

def SelectedSegmentLogicalTapeDecoderPaddedCleanupConstruction : Prop :=
  exists cleanup : MachineDescription,
    SelectedSegmentLogicalTapeDecoderPaddedCleanupSpec cleanup

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupConstruction_of_guardedCellShape
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderGuardedCellShapeCleanupConstruction) :
    SelectedSegmentLogicalTapeDecoderPaddedCleanupConstruction := by
  rcases hcleanup with ⟨cleanup, hspec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderPaddedCleanupSpec_of_guardedCellShapeSpec
        hspec⟩

def SelectedSegmentLogicalTapeDecoderPaddedCleanupNilPaddingSpec
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (target : Tape Bool) (encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
          target [] encodedPrefix)
        target

def SelectedSegmentLogicalTapeDecoderPaddedCleanupConsPaddingSpec
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (target : Tape Bool) (pad : Option Bool)
      (padding encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
          target (pad :: padding) encodedPrefix)
        target

def SelectedSegmentLogicalTapeDecoderPaddedCleanupSplitSpec
    (cleanup : MachineDescription) : Prop :=
  SelectedSegmentLogicalTapeDecoderPaddedCleanupNilPaddingSpec cleanup ∧
    SelectedSegmentLogicalTapeDecoderPaddedCleanupConsPaddingSpec cleanup

def SelectedSegmentLogicalTapeDecoderPaddedCleanupSplitConstruction : Prop :=
  exists cleanup : MachineDescription,
    SelectedSegmentLogicalTapeDecoderPaddedCleanupSplitSpec cleanup

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupSplitSpec_of_spec
    {cleanup : MachineDescription}
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderPaddedCleanupSpec cleanup) :
    SelectedSegmentLogicalTapeDecoderPaddedCleanupSplitSpec cleanup := by
  rcases hcleanup with ⟨hready, hrun⟩
  constructor
  · exact
      ⟨hready, fun target encodedPrefix =>
        hrun target [] encodedPrefix⟩
  · exact
      ⟨hready, fun target pad padding encodedPrefix =>
        hrun target (pad :: padding) encodedPrefix⟩

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupSpec_of_splitSpec
    {cleanup : MachineDescription}
    (hsplit :
      SelectedSegmentLogicalTapeDecoderPaddedCleanupSplitSpec cleanup) :
    SelectedSegmentLogicalTapeDecoderPaddedCleanupSpec cleanup := by
  rcases hsplit with ⟨hnil, hcons⟩
  rcases hnil with ⟨hready, hnilRun⟩
  rcases hcons with ⟨_hreadyCons, hconsRun⟩
  refine ⟨hready, ?_⟩
  intro target padding encodedPrefix
  cases padding with
  | nil =>
      exact hnilRun target encodedPrefix
  | cons pad padding =>
      exact hconsRun target pad padding encodedPrefix

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupConstruction_of_split
    (hsplit :
      SelectedSegmentLogicalTapeDecoderPaddedCleanupSplitConstruction) :
    SelectedSegmentLogicalTapeDecoderPaddedCleanupConstruction := by
  rcases hsplit with ⟨cleanup, hsplitSpec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderPaddedCleanupSpec_of_splitSpec
        hsplitSpec⟩

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupSplitConstruction_of_construction
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderPaddedCleanupConstruction) :
    SelectedSegmentLogicalTapeDecoderPaddedCleanupSplitConstruction := by
  rcases hcleanup with ⟨cleanup, hspec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderPaddedCleanupSplitSpec_of_spec
        hspec⟩

/-!
## Exact padded cleanup

The equivalence-facing padded cleanup above is enough for normalized-output
projection, but exact endpoint projectors need the cleanup phase to start from
the canonical sequence handoff tape and halt on the literal target tape.  The
selected-head exact route below is just the specialization where the padding is
the encoded rest block after the selected logical tape.
-/

def SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSpec
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (target : Tape Bool) (padding : List (Option Bool))
      (encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape
          (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
            target padding encodedPrefix))
        target

def SelectedSegmentLogicalTapeDecoderPaddedExactCleanupClosedSpec
    (cleanup : MachineDescription) : Prop :=
  forall (target : Tape Bool) (padding : List (Option Bool))
      (encodedPrefix : List (Option Bool)),
    ExactClosedFromTape cleanup
      (canonicalPrimitiveSeqHandoffTape
        (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
          target padding encodedPrefix))
      target

/--
Exact cleanup for a padded scanner target.

This is the reusable exact boundary below the selected-head route.  The
selected-head exact cleanup specializes {lit}`padding` to
{name}`selectedSegmentLogicalTapeDecoderRestPadding`.
-/
structure SelectedSegmentLogicalTapeDecoderPaddedExactCleanupSpec
    (cleanup : MachineDescription) : Prop where
  subroutineReady : cleanup.SubroutineReady
  forward :
    forall (target : Tape Bool) (padding : List (Option Bool))
      (encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape
          (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
            target padding encodedPrefix))
        target
  closed :
    forall (target : Tape Bool) (padding : List (Option Bool))
      (encodedPrefix : List (Option Bool)),
      ExactClosedFromTape cleanup
        (canonicalPrimitiveSeqHandoffTape
          (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
            target padding encodedPrefix))
        target

def SelectedSegmentLogicalTapeDecoderPaddedExactCleanupConstruction :
    Prop :=
  exists cleanup : MachineDescription,
    SelectedSegmentLogicalTapeDecoderPaddedExactCleanupSpec cleanup

namespace SelectedSegmentLogicalTapeDecoderPaddedExactCleanupSpec

theorem toCleanupSpec
    {cleanup : MachineDescription}
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderPaddedExactCleanupSpec cleanup) :
    SelectedSegmentLogicalTapeDecoderPaddedCleanupSpec cleanup := by
  constructor
  · exact hcleanup.subroutineReady
  · intro target padding encodedPrefix
    exact
      HaltsFromTapeEquiv_of_input_equiv
        (D := cleanup)
        (Tin :=
          canonicalPrimitiveSeqHandoffTape
            (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
              target padding encodedPrefix))
        (Tin' :=
          selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
            target padding encodedPrefix)
        (Tout := target)
        (canonicalPrimitiveSeqHandoffTape_equiv
          (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
            target padding encodedPrefix))
        (hcleanup.forward target padding encodedPrefix)

theorem forwardSpec
    {cleanup : MachineDescription}
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderPaddedExactCleanupSpec cleanup) :
    SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSpec
      cleanup :=
  ⟨hcleanup.subroutineReady, hcleanup.forward⟩

theorem closedSpec
    {cleanup : MachineDescription}
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderPaddedExactCleanupSpec cleanup) :
    SelectedSegmentLogicalTapeDecoderPaddedExactCleanupClosedSpec
      cleanup :=
  hcleanup.closed

end SelectedSegmentLogicalTapeDecoderPaddedExactCleanupSpec

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupConstruction_of_exact
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderPaddedExactCleanupConstruction) :
    SelectedSegmentLogicalTapeDecoderPaddedCleanupConstruction := by
  rcases hcleanup with ⟨cleanup, hcleanupSpec⟩
  exact ⟨cleanup, hcleanupSpec.toCleanupSpec⟩

def SelectedSegmentLogicalTapeDecoderPaddedExactCleanupNilPaddingSpec
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (target : Tape Bool) (encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape
          (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
            target [] encodedPrefix))
        target

def SelectedSegmentLogicalTapeDecoderPaddedExactCleanupConsPaddingSpec
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (target : Tape Bool) (pad : Option Bool)
      (padding encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape
          (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
            target (pad :: padding) encodedPrefix))
        target

def SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitSpec
    (cleanup : MachineDescription) : Prop :=
  SelectedSegmentLogicalTapeDecoderPaddedExactCleanupNilPaddingSpec cleanup ∧
    SelectedSegmentLogicalTapeDecoderPaddedExactCleanupConsPaddingSpec cleanup

def SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitConstruction :
    Prop :=
  exists cleanup : MachineDescription,
    SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitSpec cleanup

def SelectedSegmentLogicalTapeDecoderPaddedExactCleanupSingletonPaddingSpec
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (target : Tape Bool) (pad : Option Bool)
      (encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape
          (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
            target [pad] encodedPrefix))
        target

def SelectedSegmentLogicalTapeDecoderPaddedExactCleanupConsConsPaddingSpec
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (target : Tape Bool) (pad next : Option Bool)
      (padding encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape
          (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
            target (pad :: next :: padding) encodedPrefix))
        target

def SelectedSegmentLogicalTapeDecoderPaddedExactCleanupHandoffSplitSpec
    (cleanup : MachineDescription) : Prop :=
  SelectedSegmentLogicalTapeDecoderPaddedExactCleanupNilPaddingSpec cleanup ∧
    SelectedSegmentLogicalTapeDecoderPaddedExactCleanupSingletonPaddingSpec
      cleanup ∧
    SelectedSegmentLogicalTapeDecoderPaddedExactCleanupConsConsPaddingSpec
      cleanup

def SelectedSegmentLogicalTapeDecoderPaddedExactCleanupHandoffSplitConstruction :
    Prop :=
  exists cleanup : MachineDescription,
    SelectedSegmentLogicalTapeDecoderPaddedExactCleanupHandoffSplitSpec cleanup

theorem selectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitSpec_of_handoffSplitSpec
    {cleanup : MachineDescription}
    (hsplit :
      SelectedSegmentLogicalTapeDecoderPaddedExactCleanupHandoffSplitSpec
        cleanup) :
    SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitSpec
      cleanup := by
  rcases hsplit with ⟨hnil, hsingle, hlong⟩
  rcases hnil with ⟨hready, hnilRun⟩
  rcases hsingle with ⟨_hreadySingle, hsingleRun⟩
  rcases hlong with ⟨_hreadyLong, hlongRun⟩
  constructor
  · exact ⟨hready, hnilRun⟩
  · refine ⟨hready, ?_⟩
    intro target pad padding encodedPrefix
    cases padding with
    | nil =>
        exact hsingleRun target pad encodedPrefix
    | cons next padding =>
        exact hlongRun target pad next padding encodedPrefix

theorem selectedSegmentLogicalTapeDecoderPaddedExactCleanupHandoffSplitSpec_of_forwardSplitSpec
    {cleanup : MachineDescription}
    (hsplit :
      SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitSpec
        cleanup) :
    SelectedSegmentLogicalTapeDecoderPaddedExactCleanupHandoffSplitSpec
      cleanup := by
  rcases hsplit with ⟨hnil, hcons⟩
  rcases hnil with ⟨hready, hnilRun⟩
  rcases hcons with ⟨_hreadyCons, hconsRun⟩
  exact
    ⟨⟨hready, hnilRun⟩,
      ⟨hready, fun target pad encodedPrefix =>
        hconsRun target pad [] encodedPrefix⟩,
      ⟨hready, fun target pad next padding encodedPrefix =>
        hconsRun target pad (next :: padding) encodedPrefix⟩⟩

theorem selectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitConstruction_of_handoffSplit
    (hsplit :
      SelectedSegmentLogicalTapeDecoderPaddedExactCleanupHandoffSplitConstruction) :
    SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitConstruction := by
  rcases hsplit with ⟨cleanup, hsplitSpec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitSpec_of_handoffSplitSpec
        hsplitSpec⟩

theorem selectedSegmentLogicalTapeDecoderPaddedExactCleanupHandoffSplitConstruction_of_forwardSplit
    (hsplit :
      SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitConstruction) :
    SelectedSegmentLogicalTapeDecoderPaddedExactCleanupHandoffSplitConstruction := by
  rcases hsplit with ⟨cleanup, hsplitSpec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderPaddedExactCleanupHandoffSplitSpec_of_forwardSplitSpec
        hsplitSpec⟩

theorem selectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitConstruction_iff_handoffSplit :
    SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitConstruction <->
      SelectedSegmentLogicalTapeDecoderPaddedExactCleanupHandoffSplitConstruction := by
  constructor
  · exact
      selectedSegmentLogicalTapeDecoderPaddedExactCleanupHandoffSplitConstruction_of_forwardSplit
  · exact
      selectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitConstruction_of_handoffSplit

theorem selectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitSpec_of_spec
    {cleanup : MachineDescription}
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSpec cleanup) :
    SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitSpec
      cleanup := by
  rcases hcleanup with ⟨hready, hrun⟩
  constructor
  · exact
      ⟨hready, fun target encodedPrefix =>
        hrun target [] encodedPrefix⟩
  · exact
      ⟨hready, fun target pad padding encodedPrefix =>
        hrun target (pad :: padding) encodedPrefix⟩

theorem selectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSpec_of_splitSpec
    {cleanup : MachineDescription}
    (hsplit :
      SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitSpec
        cleanup) :
    SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSpec
      cleanup := by
  rcases hsplit with ⟨hnil, hcons⟩
  rcases hnil with ⟨hready, hnilRun⟩
  rcases hcons with ⟨_hreadyCons, hconsRun⟩
  refine ⟨hready, ?_⟩
  intro target padding encodedPrefix
  cases padding with
  | nil =>
      exact hnilRun target encodedPrefix
  | cons pad padding =>
      exact hconsRun target pad padding encodedPrefix

theorem selectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardConstruction_of_split
    (hsplit :
      SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitConstruction) :
    exists cleanup : MachineDescription,
      SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSpec
        cleanup := by
  rcases hsplit with ⟨cleanup, hsplitSpec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSpec_of_splitSpec
        hsplitSpec⟩

theorem selectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitConstruction_of_cleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderPaddedExactCleanupConstruction) :
    SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitConstruction := by
  rcases hcleanup with ⟨cleanup, hcleanupSpec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitSpec_of_spec
        hcleanupSpec.forwardSpec⟩

theorem selectedSegmentLogicalTapeDecoderPaddedExactCleanupSpec_of_forwardSpec
    {cleanup : MachineDescription}
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSpec cleanup) :
    SelectedSegmentLogicalTapeDecoderPaddedExactCleanupSpec cleanup where
  subroutineReady := hcleanup.left
  forward := hcleanup.right
  closed := by
    intro target padding encodedPrefix
    exact
      exactClosedFromTape_of_haltsFromTape_of_subroutineReady
        hcleanup.left
        (hcleanup.right target padding encodedPrefix)

theorem selectedSegmentLogicalTapeDecoderPaddedExactCleanupConstruction_of_forward
    (hcleanup :
      exists cleanup : MachineDescription,
        SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSpec
          cleanup) :
    SelectedSegmentLogicalTapeDecoderPaddedExactCleanupConstruction := by
  rcases hcleanup with ⟨cleanup, hcleanupSpec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderPaddedExactCleanupSpec_of_forwardSpec
        hcleanupSpec⟩

theorem selectedSegmentLogicalTapeDecoderPaddedExactCleanupConstruction_of_forwardSplit
    (hsplit :
      SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitConstruction) :
    SelectedSegmentLogicalTapeDecoderPaddedExactCleanupConstruction :=
  selectedSegmentLogicalTapeDecoderPaddedExactCleanupConstruction_of_forward
    (selectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardConstruction_of_split
      hsplit)

theorem selectedSegmentLogicalTapeDecoderPaddedExactCleanupConstruction_iff_forwardSplit :
    SelectedSegmentLogicalTapeDecoderPaddedExactCleanupConstruction <->
      SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitConstruction := by
  constructor
  · exact
      selectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitConstruction_of_cleanup
  · exact
      selectedSegmentLogicalTapeDecoderPaddedExactCleanupConstruction_of_forwardSplit

/-- Cleanup needed after the padded selected-head bit decoder. -/
def SelectedSegmentLogicalTapeDecoderHeadCleanupSpec
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (target : Tape Bool) (rest : List (Tape Bool))
      (encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderHeadTargetTape
          target rest encodedPrefix)
        target

/-- Existence wrapper for the padded selected-head cleanup phase. -/
def SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction : Prop :=
  exists cleanup : MachineDescription,
    SelectedSegmentLogicalTapeDecoderHeadCleanupSpec cleanup

/--
Exact cleanup for a padded selected-head scanner target.

The input is the canonical primitive-sequence handoff tape for the scanner
target, because this cleanup runs as the right-hand component of
{lit}`selectedSegmentLogicalTapeDecoderHeadPipelineDescription`.
-/
def SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSpec
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (target : Tape Bool) (rest : List (Tape Bool))
      (encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape
          (selectedSegmentLogicalTapeDecoderHeadTargetTape
            target rest encodedPrefix))
        target

/--
Closed exact cleanup for padded selected-head scanner targets.
-/
def SelectedSegmentLogicalTapeDecoderHeadExactCleanupClosedSpec
    (cleanup : MachineDescription) : Prop :=
  forall (target : Tape Bool) (rest : List (Tape Bool))
      (encodedPrefix : List (Option Bool)),
    ExactClosedFromTape cleanup
      (canonicalPrimitiveSeqHandoffTape
        (selectedSegmentLogicalTapeDecoderHeadTargetTape
          target rest encodedPrefix))
      target

/--
Exact cleanup boundary for selected-head projection.

This is the construction target needed by literal endpoint projectors; the
older cleanup route below remains the equivalence-facing compatibility layer.
-/
structure SelectedSegmentLogicalTapeDecoderHeadExactCleanupSpec
    (cleanup : MachineDescription) : Prop where
  subroutineReady : cleanup.SubroutineReady
  forward :
    forall (target : Tape Bool) (rest : List (Tape Bool))
      (encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape
          (selectedSegmentLogicalTapeDecoderHeadTargetTape
            target rest encodedPrefix))
        target
  closed :
    forall (target : Tape Bool) (rest : List (Tape Bool))
      (encodedPrefix : List (Option Bool)),
      ExactClosedFromTape cleanup
        (canonicalPrimitiveSeqHandoffTape
          (selectedSegmentLogicalTapeDecoderHeadTargetTape
            target rest encodedPrefix))
        target

/-- Existence wrapper for the exact selected-head cleanup route. -/
def SelectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction :
    Prop :=
  exists cleanup : MachineDescription,
    SelectedSegmentLogicalTapeDecoderHeadExactCleanupSpec cleanup

namespace SelectedSegmentLogicalTapeDecoderHeadExactCleanupSpec

/-- Exact selected-head cleanup implies the older equivalence cleanup route. -/
theorem toCleanupSpec
    {cleanup : MachineDescription}
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadExactCleanupSpec cleanup) :
    SelectedSegmentLogicalTapeDecoderHeadCleanupSpec cleanup := by
  constructor
  · exact hcleanup.subroutineReady
  · intro target rest encodedPrefix
    exact
      HaltsFromTapeEquiv_of_input_equiv
        (D := cleanup)
        (Tin :=
          canonicalPrimitiveSeqHandoffTape
            (selectedSegmentLogicalTapeDecoderHeadTargetTape
              target rest encodedPrefix))
        (Tin' :=
          selectedSegmentLogicalTapeDecoderHeadTargetTape
            target rest encodedPrefix)
        (Tout := target)
        (canonicalPrimitiveSeqHandoffTape_equiv
          (selectedSegmentLogicalTapeDecoderHeadTargetTape
            target rest encodedPrefix))
        (hcleanup.forward target rest encodedPrefix)

/-- Forward-only view of an exact selected-head cleanup. -/
theorem forwardSpec
    {cleanup : MachineDescription}
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadExactCleanupSpec cleanup) :
    SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSpec
      cleanup := by
  exact ⟨hcleanup.subroutineReady, hcleanup.forward⟩

/-- Closed-only view of an exact selected-head cleanup. -/
theorem closedSpec
    {cleanup : MachineDescription}
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadExactCleanupSpec cleanup) :
    SelectedSegmentLogicalTapeDecoderHeadExactCleanupClosedSpec
      cleanup :=
  hcleanup.closed

end SelectedSegmentLogicalTapeDecoderHeadExactCleanupSpec

/--
Construction-level adapter from exact selected-head cleanup to the existing
equivalence cleanup construction.
-/
theorem selectedSegmentLogicalTapeDecoderHeadCleanupConstruction_of_exact
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction) :
    SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction := by
  rcases hcleanup with ⟨cleanup, hcleanupSpec⟩
  exact
    ⟨cleanup,
      hcleanupSpec.toCleanupSpec⟩

/--
Exact cleanup branch where there is no encoded structured suffix after the
selected segment.
-/
def SelectedSegmentLogicalTapeDecoderHeadExactCleanupNilRestSpec
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (target : Tape Bool) (encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape
          (selectedSegmentLogicalTapeDecoderHeadTargetTape
            target [] encodedPrefix))
        target

/--
Exact cleanup branch where the selected segment is followed by at least one
encoded structured tape.
-/
def SelectedSegmentLogicalTapeDecoderHeadExactCleanupConsRestSpec
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (target next : Tape Bool) (rest : List (Tape Bool))
      (encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape
          (selectedSegmentLogicalTapeDecoderHeadTargetTape
            target (next :: rest) encodedPrefix))
        target

/-- Branch split for exact selected-head cleanup forward behavior. -/
def SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitSpec
    (cleanup : MachineDescription) : Prop :=
  SelectedSegmentLogicalTapeDecoderHeadExactCleanupNilRestSpec cleanup ∧
    SelectedSegmentLogicalTapeDecoderHeadExactCleanupConsRestSpec cleanup

/-- Construction wrapper for the exact forward branch split. -/
def SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitConstruction :
    Prop :=
  exists cleanup : MachineDescription,
    SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitSpec cleanup

/-- Split exact cleanup forward behavior into nil-rest and cons-rest branches. -/
theorem selectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitSpec_of_spec
    {cleanup : MachineDescription}
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSpec cleanup) :
    SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitSpec
      cleanup := by
  constructor
  · constructor
    · exact hcleanup.left
    · intro target encodedPrefix
      exact hcleanup.right target [] encodedPrefix
  · constructor
    · exact hcleanup.left
    · intro target next rest encodedPrefix
      exact hcleanup.right target (next :: rest) encodedPrefix

/-- Reassemble exact cleanup forward behavior from branch cases. -/
theorem selectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSpec_of_splitSpec
    {cleanup : MachineDescription}
    (hsplit :
      SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitSpec
        cleanup) :
    SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSpec
      cleanup := by
  rcases hsplit with ⟨hnil, hcons⟩
  rcases hnil with ⟨hready, hnilRun⟩
  rcases hcons with ⟨_hreadyCons, hconsRun⟩
  refine ⟨hready, ?_⟩
  intro target rest encodedPrefix
  cases rest with
  | nil =>
      exact hnilRun target encodedPrefix
  | cons next rest =>
      exact hconsRun target next rest encodedPrefix

/-- Construction-level split adapter from exact cleanup forward behavior. -/
theorem selectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitConstruction_of_cleanup
    (hcleanup :
      exists cleanup : MachineDescription,
        SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSpec
          cleanup) :
    SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitConstruction := by
  rcases hcleanup with ⟨cleanup, hcleanupSpec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitSpec_of_spec
        hcleanupSpec⟩

/-- Construction-level exact cleanup forward behavior from branch cases. -/
theorem selectedSegmentLogicalTapeDecoderHeadExactCleanupForwardConstruction_of_split
    (hsplit :
      SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitConstruction) :
    exists cleanup : MachineDescription,
      SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSpec
        cleanup := by
  rcases hsplit with ⟨cleanup, hsplitSpec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSpec_of_splitSpec
        hsplitSpec⟩

/--
Forward exact selected-head cleanup already gives exact closedness.

The cleanup machine is subroutine-ready, so finite-control execution from the
same input tape is deterministic.  Any public halt from one of these cleanup
inputs therefore has the same literal target as the forward run.
-/
theorem selectedSegmentLogicalTapeDecoderHeadExactCleanupSpec_of_forwardSpec
    {cleanup : MachineDescription}
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSpec cleanup) :
    SelectedSegmentLogicalTapeDecoderHeadExactCleanupSpec cleanup where
  subroutineReady := hcleanup.left
  forward := hcleanup.right
  closed := by
    intro target rest encodedPrefix
    exact
      exactClosedFromTape_of_haltsFromTape_of_subroutineReady
        hcleanup.left
        (hcleanup.right target rest encodedPrefix)

/--
Construction-level exact selected-head cleanup from forward exact cleanup.
-/
theorem selectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction_of_forward
    (hcleanup :
      exists cleanup : MachineDescription,
        SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSpec
          cleanup) :
    SelectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction := by
  rcases hcleanup with ⟨cleanup, hcleanupSpec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderHeadExactCleanupSpec_of_forwardSpec
        hcleanupSpec⟩

/--
Construction-level exact selected-head cleanup from the forward branch split.
-/
theorem selectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction_of_forwardSplit
    (hsplit :
      SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitConstruction) :
    SelectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction :=
  selectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction_of_forward
    (selectedSegmentLogicalTapeDecoderHeadExactCleanupForwardConstruction_of_split
      hsplit)

/--
The forward split and full exact selected-head cleanup constructions are
equivalent construction targets.
-/
theorem selectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction_iff_forwardSplit :
    SelectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction <->
      SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitConstruction := by
  constructor
  · intro hcleanup
    rcases hcleanup with ⟨cleanup, hcleanupSpec⟩
    exact
      ⟨cleanup,
        selectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitSpec_of_spec
          hcleanupSpec.forwardSpec⟩
  · exact
      selectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction_of_forwardSplit

theorem selectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitSpec_of_paddedExactCleanupForwardSpec
    {cleanup : MachineDescription}
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSpec
        cleanup) :
    SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitSpec
      cleanup := by
  rcases hcleanup with ⟨hready, hrun⟩
  constructor
  · constructor
    · exact hready
    · intro target encodedPrefix
      simpa [
        selectedSegmentLogicalTapeDecoderHeadTargetTape_eq_paddedCleanupSourceTape] using
        hrun target
          (selectedSegmentLogicalTapeDecoderRestPadding [])
          encodedPrefix
  · constructor
    · exact hready
    · intro target next rest encodedPrefix
      simpa [
        selectedSegmentLogicalTapeDecoderHeadTargetTape_eq_paddedCleanupSourceTape] using
        hrun target
          (selectedSegmentLogicalTapeDecoderRestPadding (next :: rest))
          encodedPrefix

theorem selectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitConstruction_of_paddedExactCleanupForward
    (hcleanup :
      exists cleanup : MachineDescription,
        SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSpec
          cleanup) :
    SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitConstruction := by
  rcases hcleanup with ⟨cleanup, hcleanupSpec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitSpec_of_paddedExactCleanupForwardSpec
        hcleanupSpec⟩

theorem selectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitConstruction_of_paddedExactCleanupForwardSplit
    (hsplit :
      SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitConstruction) :
    SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitConstruction :=
  selectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitConstruction_of_paddedExactCleanupForward
    (selectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardConstruction_of_split
      hsplit)

theorem selectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction_of_paddedExactCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderPaddedExactCleanupConstruction) :
    SelectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction :=
  selectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction_of_forwardSplit
    (selectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitConstruction_of_paddedExactCleanupForwardSplit
      (selectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitConstruction_of_cleanup
        hcleanup))


end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC

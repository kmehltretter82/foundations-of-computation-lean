import FoC.Computability.Compiler.Structured.HeadRoutes.ExactCleanup

set_option doc.verso true

/-!
# Selected-head cleanup adapters

This module derives selected-head cleanup and projector-facing route contracts
from the tape-equivalence cleanup specifications.  These are conditional
historical adapters: the cleanup construction itself is refuted by the #17
guardrails, and the live projector starts from the marker-preserving encoding.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

theorem selectedSegmentLogicalTapeDecoderHeadCleanupSpec_of_paddedCleanupSpec
    {cleanup : MachineDescription}
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderPaddedCleanupSpec cleanup) :
    SelectedSegmentLogicalTapeDecoderHeadCleanupSpec cleanup := by
  rcases hcleanup with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro target rest encodedPrefix
  simpa [
    selectedSegmentLogicalTapeDecoderHeadTargetTape_eq_paddedCleanupSourceTape] using
    hrun target (selectedSegmentLogicalTapeDecoderRestPadding rest)
      encodedPrefix

theorem selectedSegmentLogicalTapeDecoderHeadCleanupConstruction_of_paddedCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderPaddedCleanupConstruction) :
    SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction := by
  rcases hcleanup with ⟨cleanup, hspec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderHeadCleanupSpec_of_paddedCleanupSpec
        hspec⟩

/-- Singleton cleanup follows from padded selected-head cleanup. -/
theorem selectedSegmentLogicalTapeDecoderCleanupSpec_of_headCleanupSpec
    {cleanup : MachineDescription}
    (hcleanup : SelectedSegmentLogicalTapeDecoderHeadCleanupSpec cleanup) :
    SelectedSegmentLogicalTapeDecoderCleanupSpec cleanup := by
  constructor
  · exact hcleanup.left
  · intro target encodedPrefix
    simpa [selectedSegmentLogicalTapeDecoderHeadTargetTape_nil] using
      hcleanup.right target [] encodedPrefix

/-- Construction-level singleton cleanup adapter. -/
theorem selectedSegmentLogicalTapeDecoderCleanupConstruction_of_headCleanup
    (hcleanup : SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction) :
    SelectedSegmentLogicalTapeDecoderCleanupConstruction := by
  rcases hcleanup with ⟨cleanup, hcleanupSpec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderCleanupSpec_of_headCleanupSpec
        hcleanupSpec⟩

/--
The converse is intentionally absent.  Singleton cleanup does not know how to
discard or preserve arbitrary encoded structured suffixes after the selected
segment.
-/
def SelectedSegmentLogicalTapeDecoderHeadCleanupNilRestSpec
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (target : Tape Bool) (encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderHeadTargetTape
          target [] encodedPrefix)
        target

/--
Cleanup branch where the selected segment is followed by at least one encoded
structured tape.
-/
def SelectedSegmentLogicalTapeDecoderHeadCleanupConsRestSpec
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (target next : Tape Bool) (rest : List (Tape Bool))
      (encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderHeadTargetTape
          target (next :: rest) encodedPrefix)
        target

/-- Branch split for padded selected-head cleanup. -/
def SelectedSegmentLogicalTapeDecoderHeadCleanupSplitSpec
    (cleanup : MachineDescription) : Prop :=
  SelectedSegmentLogicalTapeDecoderHeadCleanupNilRestSpec cleanup ∧
    SelectedSegmentLogicalTapeDecoderHeadCleanupConsRestSpec cleanup

/-- Construction wrapper for the branch-split cleanup view. -/
def SelectedSegmentLogicalTapeDecoderHeadCleanupSplitConstruction : Prop :=
  exists cleanup : MachineDescription,
    SelectedSegmentLogicalTapeDecoderHeadCleanupSplitSpec cleanup

/-- Split padded selected-head cleanup into nil-rest and cons-rest branches. -/
theorem selectedSegmentLogicalTapeDecoderHeadCleanupSplitSpec_of_spec
    {cleanup : MachineDescription}
    (hcleanup : SelectedSegmentLogicalTapeDecoderHeadCleanupSpec cleanup) :
    SelectedSegmentLogicalTapeDecoderHeadCleanupSplitSpec cleanup := by
  constructor
  · constructor
    · exact hcleanup.left
    · intro target encodedPrefix
      exact hcleanup.right target [] encodedPrefix
  · constructor
    · exact hcleanup.left
    · intro target next rest encodedPrefix
      exact hcleanup.right target (next :: rest) encodedPrefix

/-- Reassemble padded selected-head cleanup from nil-rest and cons-rest branches. -/
theorem selectedSegmentLogicalTapeDecoderHeadCleanupSpec_of_splitSpec
    {cleanup : MachineDescription}
    (hsplit : SelectedSegmentLogicalTapeDecoderHeadCleanupSplitSpec cleanup) :
    SelectedSegmentLogicalTapeDecoderHeadCleanupSpec cleanup := by
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

/-- Construction-level split adapter from the full cleanup view. -/
theorem selectedSegmentLogicalTapeDecoderHeadCleanupSplitConstruction_of_cleanup
    (hcleanup : SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction) :
    SelectedSegmentLogicalTapeDecoderHeadCleanupSplitConstruction := by
  rcases hcleanup with ⟨cleanup, hcleanupSpec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderHeadCleanupSplitSpec_of_spec
        hcleanupSpec⟩

/-- Construction-level full cleanup adapter from the branch-split view. -/
theorem selectedSegmentLogicalTapeDecoderHeadCleanupConstruction_of_split
    (hsplit : SelectedSegmentLogicalTapeDecoderHeadCleanupSplitConstruction) :
    SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction := by
  rcases hsplit with ⟨cleanup, hsplitSpec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderHeadCleanupSpec_of_splitSpec
        hsplitSpec⟩

/-- Full cleanup and branch-split cleanup are equivalent route boundaries. -/
theorem selectedSegmentLogicalTapeDecoderHeadCleanupConstruction_iff_split :
    SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction ↔
      SelectedSegmentLogicalTapeDecoderHeadCleanupSplitConstruction := by
  constructor
  · exact selectedSegmentLogicalTapeDecoderHeadCleanupSplitConstruction_of_cleanup
  · exact selectedSegmentLogicalTapeDecoderHeadCleanupConstruction_of_split


end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC

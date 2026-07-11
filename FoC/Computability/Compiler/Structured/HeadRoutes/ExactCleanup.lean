import FoC.Computability.Compiler.Structured.HeadRoutes.RawHeadNormalizer

set_option doc.verso true

/-!
# Selected-head cleanup contracts

This module records equivalence-facing padded and selected-head cleanup
contracts. Public endpoint construction uses canonical representative cleanup,
whose exact finite-machine result is related to these public contracts by tape
equivalence.
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

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC

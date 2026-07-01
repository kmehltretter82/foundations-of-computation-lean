import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.PostPaddingScratchWindow

set_option doc.verso true

/-!
# Post-padding scratch extender

This module names the base-source and layout-scratch source tapes used by the
post-padding scratch extender, the construction contracts for extending branch
scratch, and the reusable core that appends blanks once the scratch-count window
is exposed.  The closeout module consumes the exported allocator construction
instead of owning this branch-local obligation directly.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncodedRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

open CanonicalLayouts.DovetailLayoutScanner

def selectedProjectionPaddedTailCleanupAcceptLayoutScratchSourceTape
    (L : DovetailLayout) : Tape Bool :=
  tapeAtCells [none]
    (List.append
      ((selectedProjectionPaddedTailCleanupPostPaddingSourceBits
        true L).map some)
      (none ::
        List.append (List.replicate 5 (none : Option Bool))
          (List.replicate
            (selectedProjectionPaddedTailCleanupSentinelExtraScratch
              true L)
            (none : Option Bool))))

def selectedProjectionPaddedTailCleanupRejectLayoutScratchSourceTape
    (L : DovetailLayout) : Tape Bool :=
  tapeAtCells [none]
    (List.append
      (List.append
        (List.append
          ((selectedProjectionPaddedTailCleanupPrefixBits L).map some)
          ((selectedProjectionPaddedTailCleanupUnselectedConfigBits
            false L).map some))
        ((selectedProjectionPaddedTailCleanupSelectedConfigBits
          false L).map some))
      (List.append (List.replicate 4 (none : Option Bool))
        (List.append
          ((selectedProjectionPaddedTailCleanupSelectedHitBits
            false L).map some)
          (none :: none ::
            List.replicate
              (selectedProjectionPaddedTailCleanupSentinelExtraScratch
                false L)
              (none : Option Bool)))))

def selectedProjectionPaddedTailCleanupLayoutScratchSourceTape
    (useAccept : Bool) (L : DovetailLayout) : Tape Bool :=
  if useAccept then
    selectedProjectionPaddedTailCleanupAcceptLayoutScratchSourceTape L
  else
    selectedProjectionPaddedTailCleanupRejectLayoutScratchSourceTape L

def selectedProjectionPaddedTailCleanupAcceptBaseSourceTape
    (L : DovetailLayout) : Tape Bool :=
  tapeAtCells [none]
    (List.append
      ((selectedProjectionPaddedTailCleanupPostPaddingSourceBits
        true L).map some)
      (none :: List.replicate 5 (none : Option Bool)))

def selectedProjectionPaddedTailCleanupAcceptBaseSourceTapeWithExtraScratch
    (L : DovetailLayout) (extraScratch : Nat) : Tape Bool :=
  tapeAtCells [none]
    (List.append
      ((selectedProjectionPaddedTailCleanupPostPaddingSourceBits
        true L).map some)
      (none ::
        List.append (List.replicate 5 (none : Option Bool))
          (List.replicate extraScratch (none : Option Bool))))

def selectedProjectionPaddedTailCleanupRejectBaseSourceTape
    (L : DovetailLayout) : Tape Bool :=
  tapeAtCells [none]
    (List.append
      (List.append
        (List.append
          ((selectedProjectionPaddedTailCleanupPrefixBits L).map some)
          ((selectedProjectionPaddedTailCleanupUnselectedConfigBits
            false L).map some))
        ((selectedProjectionPaddedTailCleanupSelectedConfigBits
          false L).map some))
      (List.append (List.replicate 4 (none : Option Bool))
        (List.append
          ((selectedProjectionPaddedTailCleanupSelectedHitBits
            false L).map some)
          (none :: none :: []))))

def selectedProjectionPaddedTailCleanupRejectBaseSourceTapeWithExtraScratch
    (L : DovetailLayout) (extraScratch : Nat) : Tape Bool :=
  tapeAtCells [none]
    (List.append
      (List.append
        (List.append
          ((selectedProjectionPaddedTailCleanupPrefixBits L).map some)
          ((selectedProjectionPaddedTailCleanupUnselectedConfigBits
            false L).map some))
        ((selectedProjectionPaddedTailCleanupSelectedConfigBits
          false L).map some))
      (List.append (List.replicate 4 (none : Option Bool))
        (List.append
          ((selectedProjectionPaddedTailCleanupSelectedHitBits
            false L).map some)
          (none :: none ::
            List.replicate extraScratch (none : Option Bool)))))

def selectedProjectionPaddedTailCleanupBaseSourceTape
    (useAccept : Bool) (L : DovetailLayout) : Tape Bool :=
  if useAccept then
    selectedProjectionPaddedTailCleanupAcceptBaseSourceTape L
  else
    selectedProjectionPaddedTailCleanupRejectBaseSourceTape L

def selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    Tape Bool :=
  if useAccept then
    selectedProjectionPaddedTailCleanupAcceptBaseSourceTapeWithExtraScratch
      L extraScratch
  else
    selectedProjectionPaddedTailCleanupRejectBaseSourceTapeWithExtraScratch
      L extraScratch

theorem selectedProjectionPaddedTailCleanupAcceptBaseSourceTapeWithExtraScratch_zero
    (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupAcceptBaseSourceTapeWithExtraScratch
        L 0 =
      selectedProjectionPaddedTailCleanupAcceptBaseSourceTape L := by
  simp [selectedProjectionPaddedTailCleanupAcceptBaseSourceTapeWithExtraScratch,
    selectedProjectionPaddedTailCleanupAcceptBaseSourceTape]

theorem selectedProjectionPaddedTailCleanupRejectBaseSourceTapeWithExtraScratch_zero
    (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupRejectBaseSourceTapeWithExtraScratch
        L 0 =
      selectedProjectionPaddedTailCleanupRejectBaseSourceTape L := by
  simp [selectedProjectionPaddedTailCleanupRejectBaseSourceTapeWithExtraScratch,
    selectedProjectionPaddedTailCleanupRejectBaseSourceTape]

theorem selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch_zero
    (useAccept : Bool) (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch
        useAccept L 0 =
      selectedProjectionPaddedTailCleanupBaseSourceTape useAccept L := by
  cases useAccept
  · exact
      selectedProjectionPaddedTailCleanupRejectBaseSourceTapeWithExtraScratch_zero
        L
  · exact
      selectedProjectionPaddedTailCleanupAcceptBaseSourceTapeWithExtraScratch_zero
        L

theorem selectedProjectionPaddedTailCleanupAcceptBaseSourceTapeWithLayoutExtraScratch
    (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupAcceptBaseSourceTapeWithExtraScratch
        L
        (selectedProjectionPaddedTailCleanupSentinelExtraScratch true L) =
      selectedProjectionPaddedTailCleanupAcceptLayoutScratchSourceTape L := by
  rfl

theorem selectedProjectionPaddedTailCleanupRejectBaseSourceTapeWithLayoutExtraScratch
    (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupRejectBaseSourceTapeWithExtraScratch
        L
        (selectedProjectionPaddedTailCleanupSentinelExtraScratch false L) =
      selectedProjectionPaddedTailCleanupRejectLayoutScratchSourceTape L := by
  rfl

theorem selectedProjectionPaddedTailCleanupBaseSourceTapeWithLayoutExtraScratch
    (useAccept : Bool) (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch
        useAccept L
        (selectedProjectionPaddedTailCleanupSentinelExtraScratch
          useAccept L) =
      selectedProjectionPaddedTailCleanupLayoutScratchSourceTape
        useAccept L := by
  cases useAccept
  · exact
      selectedProjectionPaddedTailCleanupRejectBaseSourceTapeWithLayoutExtraScratch
        L
  · exact
      selectedProjectionPaddedTailCleanupAcceptBaseSourceTapeWithLayoutExtraScratch
        L

def SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorSpec
    (useAccept : Bool) (allocator : MachineDescription) : Prop :=
  allocator.SubroutineReady ∧
    forall L : DovetailLayout,
      allocator.HaltsFromTape
        (selectedProjectionPaddedTailCleanupBaseSourceTape useAccept L)
        (selectedProjectionPaddedTailCleanupLayoutScratchSourceTape
          useAccept L)

def SelectedProjectionPaddedTailCleanupPostPaddingScratchExtenderSpec
    (useAccept : Bool) (extender : MachineDescription) : Prop :=
  extender.SubroutineReady ∧
    forall L : DovetailLayout,
      extender.HaltsFromTape
        (selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch
          useAccept L 0)
        (selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch
          useAccept L
          (selectedProjectionPaddedTailCleanupSentinelExtraScratch
            useAccept L))

def SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderSpec
    (useAccept : Bool) (extender : MachineDescription) : Prop :=
  extender.SubroutineReady ∧
    forall L : DovetailLayout,
      extender.HaltsFromTape
        (selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch
          useAccept L 0)
        (selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch
          useAccept L
          (selectedProjectionPaddedTailCleanupScratchCountBits
            useAccept L).length)

def SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction :
    Prop :=
  forall useAccept : Bool,
    exists allocator : MachineDescription,
      SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorSpec
        useAccept allocator

def SelectedProjectionPaddedTailCleanupPostPaddingScratchExtenderConstruction :
    Prop :=
  forall useAccept : Bool,
    exists extender : MachineDescription,
      SelectedProjectionPaddedTailCleanupPostPaddingScratchExtenderSpec
        useAccept extender

def SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction :
    Prop :=
  forall useAccept : Bool,
    exists extender : MachineDescription,
      SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderSpec
        useAccept extender

theorem selectedProjectionPaddedTailCleanupPostPaddingScratchExtenderSpec_of_countExtenderSpec
    {useAccept : Bool} {extender : MachineDescription}
    (hextender :
      SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderSpec
        useAccept extender) :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchExtenderSpec
      useAccept extender := by
  constructor
  · exact hextender.left
  · intro L
    simpa [
      selectedProjectionPaddedTailCleanupScratchCountBits_length]
      using hextender.right L

theorem selectedProjectionPaddedTailCleanupPostPaddingScratchExtenderConstruction_of_countExtenders
    (h :
      SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction) :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchExtenderConstruction := by
  intro useAccept
  rcases h useAccept with ⟨extender, hextender⟩
  exact
    ⟨extender,
      selectedProjectionPaddedTailCleanupPostPaddingScratchExtenderSpec_of_countExtenderSpec
        hextender⟩

theorem selectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorSpec_of_extenderSpec
    {useAccept : Bool} {extender : MachineDescription}
    (hextender :
      SelectedProjectionPaddedTailCleanupPostPaddingScratchExtenderSpec
        useAccept extender) :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorSpec
      useAccept extender := by
  constructor
  · exact hextender.left
  · intro L
    simpa [
      selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch_zero,
      selectedProjectionPaddedTailCleanupBaseSourceTapeWithLayoutExtraScratch]
      using hextender.right L

theorem selectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction_of_extenders
    (h :
      SelectedProjectionPaddedTailCleanupPostPaddingScratchExtenderConstruction) :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction := by
  intro useAccept
  rcases h useAccept with ⟨extender, hextender⟩
  exact
    ⟨extender,
      selectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorSpec_of_extenderSpec
        hextender⟩

def selectedProjectionPaddedTailCleanupScratchCountCounterSourceTape
    (useAccept : Bool) (L : DovetailLayout) : Tape Bool :=
  tapeAtCells
    (none ::
      (selectedProjectionPaddedTailCleanupScratchSkippedBits
        useAccept L).reverse.map some)
    (List.append
      ((selectedProjectionPaddedTailCleanupScratchCountBits
        useAccept L).map some)
      (none ::
        none ::
        List.replicate
          (selectedProjectionPaddedTailCleanupScratchCountBits
            useAccept L).length
          (none : Option Bool)))

def selectedProjectionPaddedTailCleanupScratchCountCounterTargetTape
    (useAccept : Bool) (L : DovetailLayout) : Tape Bool :=
  tapeAtCells
    (none ::
      (selectedProjectionPaddedTailCleanupScratchSkippedBits
        useAccept L).reverse.map some)
    (List.append
      ((selectedProjectionPaddedTailCleanupScratchCountBits
        useAccept L).map some)
      (none ::
        List.replicate
          ((selectedProjectionPaddedTailCleanupScratchCountBits
            useAccept L).length + 1)
          (none : Option Bool)))

/--
Executable core of the post-padding scratch extender after the branch-specific
navigation has exposed the scratch-count suffix under the head.
-/
theorem scratchCounterAppendBlanksDescription_haltsFrom_scratchCountWindow
    (useAccept : Bool) (L : DovetailLayout) :
    scratchCounterAppendBlanksDescription.HaltsFromTape
      (selectedProjectionPaddedTailCleanupScratchCountCounterSourceTape
        useAccept L)
      (selectedProjectionPaddedTailCleanupScratchCountCounterTargetTape
        useAccept L) := by
  simpa [
    selectedProjectionPaddedTailCleanupScratchCountCounterSourceTape,
    selectedProjectionPaddedTailCleanupScratchCountCounterTargetTape]
    using
      scratchCounterAppendBlanksDescription_haltsFrom_withRight
        ((selectedProjectionPaddedTailCleanupScratchSkippedBits
          useAccept L).reverse.map some)
        (selectedProjectionPaddedTailCleanupScratchCountBits useAccept L)
        []
        (selectedProjectionPaddedTailCleanupScratchCountBits_length_pos
          useAccept L)

/--
Finite-machine leaf that exposes the selected branch scratch-count window and
uses it to append the branch-specific scratch padding.
-/
theorem selectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction := by
  sorry

theorem selectedProjectionPaddedTailCleanupPostPaddingScratchExtenderConstruction :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchExtenderConstruction :=
  selectedProjectionPaddedTailCleanupPostPaddingScratchExtenderConstruction_of_countExtenders
    selectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction

theorem selectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction :=
  selectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction_of_extenders
    selectedProjectionPaddedTailCleanupPostPaddingScratchExtenderConstruction

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC

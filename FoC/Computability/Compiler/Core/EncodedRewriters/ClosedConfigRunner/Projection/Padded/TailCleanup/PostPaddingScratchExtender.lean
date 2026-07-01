import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.PostPaddingScratchWindow

set_option doc.verso true

/-!
# Post-padding scratch extender source shapes

This module names the base-source and layout-scratch source tapes used by the
post-padding scratch extender.  The actual closeout sequencing remains in the
closeout module, but it now depends on these reusable tape-shape facts instead
of owning them directly.
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

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC

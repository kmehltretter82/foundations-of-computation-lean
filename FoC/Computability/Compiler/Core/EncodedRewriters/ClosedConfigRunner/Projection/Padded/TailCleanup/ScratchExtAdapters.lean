import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.ScratchExtSpecs

set_option doc.verso true

/-!
# Post-padding scratch extender adapters

This module contains the logical adapters from count-sized scratch extension to
sentinel-sized scratch extension and then to the allocator contract consumed by
post-padding closeout.
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

theorem selectedProjectionPaddedTailCleanupScratchExtSpec_of_countExtenderSpec
    {useAccept : Bool} {extender : MachineDescription}
    (hextender :
      SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderSpec
        useAccept extender) :
    SelectedProjectionPaddedTailCleanupScratchExtSpec
      useAccept extender := by
  constructor
  · exact hextender.left
  · intro L
    simpa [
      selectedProjectionPaddedTailCleanupScratchCountBits_length]
      using hextender.right L

theorem selectedProjectionPaddedTailCleanupScratchExtConstruction_of_countExtenders
    (h :
      SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction) :
    SelectedProjectionPaddedTailCleanupScratchExtConstruction := by
  intro useAccept
  rcases h useAccept with ⟨extender, hextender⟩
  exact
    ⟨extender,
      selectedProjectionPaddedTailCleanupScratchExtSpec_of_countExtenderSpec
        hextender⟩

theorem selectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorSpec_of_extenderSpec
    {useAccept : Bool} {extender : MachineDescription}
    (hextender :
      SelectedProjectionPaddedTailCleanupScratchExtSpec
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
      SelectedProjectionPaddedTailCleanupScratchExtConstruction) :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction := by
  intro useAccept
  rcases h useAccept with ⟨extender, hextender⟩
  exact
    ⟨extender,
      selectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorSpec_of_extenderSpec
        hextender⟩

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC

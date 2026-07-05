import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.ScratchExtTapes

set_option doc.verso true

/-!
# Post-padding scratch extender specs

This module contains the construction-family contracts for the post-padding
scratch allocator, sentinel-sized scratch extender, and count-sized scratch
extender.
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

def SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorSpec
    (useAccept : Bool) (allocator : MachineDescription) : Prop :=
  allocator.SubroutineReady ∧
    forall L : DovetailLayout,
      allocator.HaltsFromTapeEquiv
        (selectedProjectionPaddedTailCleanupBaseSourceTape useAccept L)
        (selectedProjectionPaddedTailCleanupLayoutScratchSourceTape
          useAccept L)

def SelectedProjectionPaddedTailCleanupScratchExtSpec
    (useAccept : Bool) (extender : MachineDescription) : Prop :=
  extender.SubroutineReady ∧
    forall L : DovetailLayout,
      extender.HaltsFromTapeEquiv
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
      extender.HaltsFromTapeEquiv
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

def SelectedProjectionPaddedTailCleanupScratchExtConstruction :
    Prop :=
  forall useAccept : Bool,
    exists extender : MachineDescription,
      SelectedProjectionPaddedTailCleanupScratchExtSpec
        useAccept extender

def SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction :
    Prop :=
  forall useAccept : Bool,
    exists extender : MachineDescription,
      SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderSpec
        useAccept extender

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC

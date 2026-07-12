import FoC.Computability.Compiler.Structured.HeadRoutes.Base

set_option doc.verso true

/-!
# Retired selected-head cleanup guardrail contract

The post-scanner source has lost the logical head marker, so it cannot support cleanup to an
arbitrary logical tape.  This minimal contract preserves the checked impossibility result in
{lit}`ContractGuardrails.lean`; the retired
adapters remain recoverable from Git history.
-/

namespace FoC
namespace Computability

open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

def SelectedSegmentLogicalTapeDecoderPaddedCleanupSpec (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (target : Tape Bool) (padding : List (Option Bool)) (encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape target padding encodedPrefix)
        target

def SelectedSegmentLogicalTapeDecoderPaddedCleanupConstruction : Prop :=
  exists cleanup, SelectedSegmentLogicalTapeDecoderPaddedCleanupSpec cleanup

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC

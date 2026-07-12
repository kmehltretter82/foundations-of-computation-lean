import FoC.Computability.Compiler.ClosedCfg.ProjTail.SelectedFootprintCompaction.ContractGuardrails
import FoC.Computability.Compiler.ClosedCfg.ProjTail.SelectedFootprintCompaction.LiveIngress.EndMarker

set_option doc.verso true

/-!
# Live selected-footprint compactor frontier

The retired frontier quantified over arbitrary payloads, bits, and padding.
That family is inconsistent modulo {lit}`Tape.Equiv`; the guardrail module
records two concrete collisions.  The remaining construction is indexed only
by the count-window inputs that reach this phase.  Its target is functional on
source equivalence classes by the functionality theorem in the imported
guardrail module.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

open CanonicalLayouts.DovetailLayoutScanner

/--
The sole remaining selected-footprint construction obligation.

For each live branch and parsed layout, compact the decoder footprint to the
right-edge rewind tape.  {name}`ParsedLayoutBits` begins with two represented bits,
which is the clean source premise missing from the old arbitrary-payload
frontier.

The first live ingress phase is now checked in {lit}`LiveIngress/EndMarker.lean`:
it marks the two blank right-boundary cells and aligns the head with the final
pair-encoded payload cell.  The remaining obligation must traverse that marked
pair stream, build the retained three-tape compactor input, and compose the
already-proved compactor/focus/projector phases.
-/
theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorConstruction_core :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorConstruction := by
  -- Classified finite-machine obligation: construct one subroutine for the
  -- live `(useAccept, DovetailLayout)` source family.  Do not generalize this
  -- back to arbitrary payloads; ContractGuardrails proves that claim false.
  sorry

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC

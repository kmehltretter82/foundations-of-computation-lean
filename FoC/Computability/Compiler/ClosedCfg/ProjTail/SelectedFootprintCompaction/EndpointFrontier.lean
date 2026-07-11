import FoC.Computability.Compiler.ClosedCfg.ProjTail.SelectedFootprintCompaction.ContractGuardrails

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

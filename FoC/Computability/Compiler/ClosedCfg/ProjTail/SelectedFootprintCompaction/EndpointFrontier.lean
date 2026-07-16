import FoC.Computability.Compiler.ClosedCfg.ProjTail.SelectedFootprintCompaction.ContractGuardrails
import FoC.Computability.Compiler.ClosedCfg.ProjTail.SelectedFootprintCompaction.LiveIngress.MarkerCompactor
import FoC.Computability.Compiler.ClosedCfg.ProjTail.StructuredPrefixEraserHandoff.Impl.MarkerHandoff

set_option doc.verso true

/-!
# Marker-bearing selected-footprint compactor

The retired contract quantified over arbitrary payloads, bits, and padding.
That family is inconsistent modulo {lit}`Tape.Equiv`; the guardrail module
records two concrete collisions. The completed construction is indexed only
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
The marker-bearing selected-footprint construction.

For each selected branch and parsed layout, compact the decoder footprint to the
right-edge rewind tape.  {name}`ParsedLayoutBits` begins with two represented bits,
which is the clean source premise missing from the old arbitrary-payload
contract.

The repaired boundary is marker-bearing. The upstream pair-parity eraser keeps
its final two represented prefix cells as {lit}`[true, false]`; decoder pairs
cannot contain adjacent represented cells, so this is a detectable left
sentinel. The direct moving-marker compactor consumes that source and halts on
the interior payload separator. This target is separate from the narrow
{lit}`StructuredTape2ProjectorConstruction`; neither contract is duplicated or widened.
-/
theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorConstruction_core :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorConstruction :=
  ⟨LiveIngress.MarkerCompactor.description,
    LiveIngress.MarkerCompactor.description_liveSpec⟩

/-- The structured-prefix densifier composes the marker-preserving upstream
handoff with the marker-bearing compactor. Keeping this integration beside the
completed compactor contract distinguishes it from the historical unmarked
component wrappers. -/
theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierConstruction_core :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierConstruction := by
  refine
    ⟨countWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierDescription
        LiveIngress.MarkerHandoff.description
        LiveIngress.MarkerCompactor.description,
      ?_⟩
  constructor
  · exact
      countWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierDescription_subroutineReady
        LiveIngress.MarkerHandoff.description_subroutineReady
        LiveIngress.MarkerCompactor.description_subroutineReady
  · intro useAccept L deletedTail
    let T0 :=
      structuredBoolWordRawBitsDecoderSourceTargetTape
        (ParsedLayoutBits L)
        (countWindowPostFieldDecodedPrefixStructuredSuffixTail
          useAccept L)
        (countWindowPostFieldDecodedPrefixStructuredSourcePadding
          useAccept L deletedTail)
    let T1 :=
      structuredBoolWordRawBitsDecoderCounterDecodeTape 0
        ((ParsedLayoutBits L).length + 1)
    let Tmid :=
      countWindowPostFieldDecodedPrefixSelectedSegmentMarkedFootprintCompactorSourceTape
        useAccept L
    have hmarker :=
      LiveIngress.MarkerHandoff.description_spec.2
        T0 T1 (ParsedLayoutBits L)
          (postFieldDecodedPrefixScanPadding useAccept L)
    rw [LiveIngress.MarkerHandoff.guardedMarkerTargetTape_eq_liveSource]
      at hmarker
    have hhandoff :
        LiveIngress.MarkerHandoff.description.HaltsFromTapeEquiv
          (selectedSegmentLogicalTapeDecoderTargetTape
            (postFieldDecodedPrefixScanSourceTape useAccept L)
            (countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix
              useAccept L deletedTail))
          Tmid := by
      have hsource :
          selectedSegmentLogicalTapeDecoderTargetTape
              (postFieldDecodedPrefixScanSourceTape useAccept L)
              (countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix
                useAccept L deletedTail) =
            guardedTwoTapeStructuredPrefixEraserSourceTape
              T0 T1 (ParsedLayoutBits L)
                (postFieldDecodedPrefixScanPadding useAccept L) := by
        cases useAccept with
        | false =>
            rw [countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix_reject_eq_prefixCells]
            rfl
        | true =>
            rw [countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix_accept_eq_prefixCells]
            rfl
      rw [hsource]
      simpa [Tmid] using hmarker
    have hcompactor :=
      LiveIngress.MarkerCompactor.description_liveSpec.2 useAccept L
    have hcompactorFromBridge :
        LiveIngress.MarkerCompactor.description.HaltsFromTapeEquiv
          (Tape.move Direction.left (Tape.move Direction.right Tmid))
          (rightEdgeRewindSourceTape (ParsedLayoutBits L)
            (postFieldDecodedPrefixScanPadding useAccept L)) := by
      rcases hcompactor with ⟨Tactual, hactual, hactualEquiv⟩
      rcases
        HaltsFromTapeEquiv_of_input_equiv
          (D := LiveIngress.MarkerCompactor.description)
          (Tin := Tmid)
          (Tin' :=
            Tape.move Direction.left (Tape.move Direction.right Tmid))
          (Tape.Equiv.symm (moveLeft_moveRight_equiv_self Tmid))
          hactual with
        ⟨Ttransported, htransported, htransportedEquiv⟩
      exact
        ⟨Ttransported, htransported,
          Tape.Equiv.trans htransportedEquiv hactualEquiv⟩
    exact
      canonicalSeqDescription_haltsFromTapeEquiv_of_haltsFromTapeEquiv
        LiveIngress.MarkerHandoff.description_subroutineReady
        LiveIngress.MarkerCompactor.description_subroutineReady
        hhandoff rfl hcompactorFromBridge

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC

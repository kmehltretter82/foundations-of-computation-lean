import FoC.Computability.Compiler.ClosedCfg.PostTrans.ParsedInnerWindows
import FoC.Computability.Compiler.ClosedCfg.PostTrans.Specs
import FoC.Computability.Compiler.ClosedCfg.PostTrans.ParsedInnerTransport.AcceptOuterPull
import FoC.Computability.Compiler.ClosedCfg.PostTrans.ParsedInnerTransport.RejectSchedule

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner

/-!
# Merge post-transition parsed inner emitter

This module contains the branch-parametric finite-machine leaf that rewrites a
parsed nested layout plus the restored outer source fields into the decoded
merge field order for either padded branch.
-/

/--
Branch-parametric finite-machine obligation that transports the restored
source fields after the parsed inner prefix gap has been closed.
-/
theorem selectedMergePaddedEmitterParsedInnerPostPrefixFieldTransportConstruction
    (useAccept : Bool) :
    exists transport : MachineDescription,
      SelectedMergePaddedEmitterParsedInnerPostPrefixFieldTransportSpec
        useAccept transport := by
  cases useAccept
  · exact ⟨ParsedInnerTransport.rejectFieldTransportDescription,
      ParsedInnerTransport.rejectFieldTransportDescription_spec⟩
  · exact ⟨ParsedInnerTransport.acceptFieldTransportDescription,
      ParsedInnerTransport.acceptFieldTransportDescription_spec⟩

/--
Finite-machine leaf that rewrites the parsed nested layout plus outer source
fields into the decoded merge field order selected by {name}`useAccept`.
-/
theorem selectedMergePaddedEmitterAfterHitPaddedParsedInnerConstruction
    (useAccept : Bool) :
    SelectedMergePaddedEmitterAfterHitPaddedParsedInnerConstruction
      useAccept := by
  rcases
      selectedMergePaddedEmitterParsedInnerPostPrefixFieldTransportConstruction
        useAccept with
    ⟨transport, htransport⟩
  let closer :=
    SelectedMergePaddedEmitterParsedInnerPostPrefixGapCloseDescription
  have hcloser :
      SelectedMergePaddedEmitterParsedInnerPostPrefixGapCloseSpec closer := by
    simpa [closer] using
      selectedMergePaddedEmitterParsedInnerPostPrefixGapCloseSpec
  have hprefixCloser :
      (CommonGround.FiniteTransducers.canonicalSeqDescription
        SelectedMergePaddedEmitterParsedInnerPrefixCleanupDescription
        closer).SubroutineReady ∧
        forall p : SelectedMergeEmitterPayload,
          (CommonGround.FiniteTransducers.canonicalSeqDescription
            SelectedMergePaddedEmitterParsedInnerPrefixCleanupDescription
            closer).HaltsFromTape
            (SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape p)
            (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p) := by
    constructor
    · exact
        CommonGround.FiniteTransducers.canonicalSeqDescription_subroutineReady
          selectedMergePaddedEmitterParsedInnerPrefixCleanupDescription_subroutineReady
          hcloser.left
    · intro p
      exact
        CommonGround.FiniteTransducers.canonicalSeqDescription_haltsFromTape_of_haltsFromTape
          selectedMergePaddedEmitterParsedInnerPrefixCleanupDescription_subroutineReady
          hcloser.left
          (selectedMergePaddedEmitterParsedInnerPrefixCleanupDescription_haltsFromParsedTape
            p)
          (SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape_move_left_move_right
            p)
          (hcloser.right p)
  refine
    ⟨CommonGround.FiniteTransducers.canonicalSeqDescription
        (CommonGround.FiniteTransducers.canonicalSeqDescription
          SelectedMergePaddedEmitterParsedInnerPrefixCleanupDescription
          closer)
        transport,
      ?_⟩
  constructor
  · exact
      CommonGround.FiniteTransducers.canonicalSeqDescription_subroutineReady
        hprefixCloser.left
        htransport.left
  · intro p
    exact
      CommonGround.FiniteTransducers.canonicalSeqDescription_haltsFromTapeEquiv_of_haltsFromTape
        hprefixCloser.left
        htransport.left
        (hprefixCloser.right p)
        (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape_move_left_move_right
          p)
        (htransport.right p)

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC

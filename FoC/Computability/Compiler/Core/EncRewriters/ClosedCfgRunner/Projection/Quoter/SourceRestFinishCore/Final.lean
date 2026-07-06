import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Quoter.SourceRestFinishCore.LTEmitterConstruction
import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Quoter.SourceRestFinishCore.LTJoinerConstruction
import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Quoter.SourceRestFinishCore.LTGapOutput
import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Quoter.SourceRestFinishCore.LTStructuredOutputBridge

set_option doc.verso true

/-!
This module closes the source-rest finisher construction used by the input
quoter. It combines the live-tail emitter and joiner construction routes with
the reusable and raw-bool source-start routes, then exposes the final
finite-leaf construction the quoter assembly imports.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner

namespace SelectedProjectionInputQuoterFiniteLeaf

open DovetailInitialLayoutInitializer
open DovetailInitialLayoutInitializer.StageInputMarkedScanner

/--
Final finite-machine obligation for the source-rest finish phase. The raw source
word has no general delimiter for arbitrary Bool-word splits, so the live-tail
emitter/joiner route first closes the parsed internal-marker layout, then the
existing exact-tape adapters rewrite the mixed parser-stack/source-rest layout
into
{name}`assemblySourceRestFinishTargetTape`.
-/
theorem assemblySourceRestFinishConstruction :
    AssemblySourceRestFinishConstruction := by
  apply assemblySourceRestFinishConstruction_of_quoteBoundary
  apply assemblySourceRestFinishQuoteBoundaryConstruction_of_leftBoundary
  apply assemblySourceRestFinishLeftBoundaryCoreConstruction_of_mixedParserStackFinisher
  apply MixedParserStackFinisherConstructionForAssemblySourceRest_of_trueLeftBoundary
  apply MixedParserStackTrueLeftBoundaryFinisherConstructionForAssemblySourceRest_of_defaultedInternalMarker
  apply MixedParserStackDefaultedInternalMarkerFinisherConstructionForAssemblySourceRest_of_wholeSource
  rcases mixedParserStackPrefixQuotedSeparatedFinisherConstruction_for_assemblySourceRest with
    ⟨prefixFinish, hprefixFinish⟩
  rcases mixedParserStackAfterRawTailScanJoinFinisherConstruction_for_assemblySourceRest with
    ⟨joinFinish, hjoinFinish⟩
  refine
    ⟨SeqViaCanonical prefixFinish
      (SeqViaCanonical
        CommonGround.FiniteTransducers.rightBlankGapPayloadScanDescription
        joinFinish), ?_⟩
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        hprefixFinish.left
        (SeqViaCanonical_subroutineReady
          CommonGround.FiniteTransducers.rightBlankGapPayloadScanDescription_subroutineReady
          hjoinFinish.left)
  · intro w sourceRestBits stage
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        hprefixFinish.left
        (SeqViaCanonical_subroutineReady
          CommonGround.FiniteTransducers.rightBlankGapPayloadScanDescription_subroutineReady
          hjoinFinish.left)
        (hprefixFinish.right w sourceRestBits stage)
        (MixedParserStackWholeSourcePrefixQuotedSeparatedTape_move_left_move_right
          w sourceRestBits stage)
        (SeqViaCanonical_haltsFromTape_of_haltsFromTape
          CommonGround.FiniteTransducers.rightBlankGapPayloadScanDescription_subroutineReady
          hjoinFinish.left
          (rightBlankGapPayloadScanDescription_haltsFrom_prefixQuotedSeparatedTape_to_afterRawTailScan
            w sourceRestBits stage)
          (MixedParserStackWholeSourceAfterRawTailScanTape_move_left_move_right
            w sourceRestBits stage)
          (hjoinFinish.right w sourceRestBits stage))

end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC

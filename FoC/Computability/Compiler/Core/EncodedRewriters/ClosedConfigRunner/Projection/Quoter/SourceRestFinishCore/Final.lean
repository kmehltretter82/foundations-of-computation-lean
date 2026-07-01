import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Quoter.SourceRestFinishCore.LiveTailAdapters

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

namespace SelectedProjectionInputQuoterFiniteLeaf

open DovetailInitialLayoutInitializer
open DovetailInitialLayoutInitializer.StageInputMarkedScanner

theorem
    MixedParserStackWholeSourceFinisherConstructionForAssemblySourceRest_of_prefixSeparated_and_join
    (hprefix :
      MixedParserStackPrefixQuotedSeparatedFinisherConstructionForAssemblySourceRest)
    (hjoin :
      MixedParserStackAfterRawTailScanJoinFinisherConstructionForAssemblySourceRest) :
    MixedParserStackWholeSourceFinisherConstructionForAssemblySourceRest := by
  rcases hprefix with ⟨prefixFinish, hprefixFinish⟩
  rcases hjoin with ⟨joinFinish, hjoinFinish⟩
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

/--
Core finite-machine obligation for the mixed parser-stack whole-source finisher.
The raw source word has no general delimiter for arbitrary Bool-word splits, so
the remaining leaf is stated at the parsed internal-marker layout where the live
tail boundary is part of the encoded assembly/source-rest structure.
-/
theorem
    mixedParserStackWholeSourceFinisherConstruction_for_assemblySourceRest :
    MixedParserStackWholeSourceFinisherConstructionForAssemblySourceRest :=
  MixedParserStackWholeSourceFinisherConstructionForAssemblySourceRest_of_prefixSeparated_and_join
    mixedParserStackPrefixQuotedSeparatedFinisherConstruction_for_assemblySourceRest
    mixedParserStackAfterRawTailScanJoinFinisherConstruction_for_assemblySourceRest

theorem
    mixedParserStackDefaultedInternalMarkerFinisherConstruction_for_assemblySourceRest :
    MixedParserStackDefaultedInternalMarkerFinisherConstructionForAssemblySourceRest :=
  MixedParserStackDefaultedInternalMarkerFinisherConstructionForAssemblySourceRest_of_wholeSource
    mixedParserStackWholeSourceFinisherConstruction_for_assemblySourceRest

theorem
    mixedParserStackTrueLeftBoundaryFinisherConstruction_for_assemblySourceRest :
    MixedParserStackTrueLeftBoundaryFinisherConstructionForAssemblySourceRest :=
  MixedParserStackTrueLeftBoundaryFinisherConstructionForAssemblySourceRest_of_defaultedInternalMarker
    mixedParserStackDefaultedInternalMarkerFinisherConstruction_for_assemblySourceRest

theorem
    mixedParserStackSentinelSourceFinisherConstruction_for_assemblySourceRest :
    MixedParserStackSentinelSourceFinisherConstructionForAssemblySourceRest :=
  MixedParserStackSentinelSourceFinisherConstructionForAssemblySourceRest_of_trueLeftBoundary
    mixedParserStackTrueLeftBoundaryFinisherConstruction_for_assemblySourceRest

theorem
    assemblySourceRestReusableQuoteAfterSourceRestScanFinisherConstruction :
    AssemblySourceRestReusableQuoteAfterSourceRestScanFinisherConstruction := by
  exact
    AssemblySourceRestReusableQuoteAfterSourceRestScanFinisherConstruction_of_sentinelSource
      mixedParserStackSentinelSourceFinisherConstruction_for_assemblySourceRest

theorem
    assemblySourceRestReusableQuoteSourceRestBoundaryFinisherConstruction :
    AssemblySourceRestReusableQuoteSourceRestBoundaryFinisherConstruction := by
  exact
    AssemblySourceRestReusableQuoteSourceRestBoundaryFinisherConstruction_of_afterSourceRestScan
      assemblySourceRestReusableQuoteAfterSourceRestScanFinisherConstruction

theorem assemblySourceRestReusableQuoteSourceStartFinisherConstruction :
    AssemblySourceRestReusableQuoteSourceStartFinisherConstruction :=
  AssemblySourceRestReusableQuoteSourceStartFinisherConstruction_of_sourceRestBoundary
    assemblySourceRestReusableQuoteSourceRestBoundaryFinisherConstruction

theorem assemblySourceRestRawBoolSourceStartFinisherConstruction :
    AssemblySourceRestRawBoolSourceStartFinisherConstruction :=
  AssemblySourceRestRawBoolSourceStartFinisherConstruction_of_reusableQuote
    assemblySourceRestReusableQuoteSourceStartFinisherConstruction

theorem
    mixedParserStackSourceStartFinisherConstruction_for_assemblySourceRest :
    MixedParserStackSourceStartFinisherConstructionForAssemblySourceRest :=
  MixedParserStackSourceStartFinisherConstructionForAssemblySourceRest_of_rawBool
    assemblySourceRestRawBoolSourceStartFinisherConstruction

theorem
    mixedParserStackRightBoundaryFinisherConstruction_for_assemblySourceRest :
    MixedParserStackRightBoundaryFinisherConstructionForAssemblySourceRest :=
  MixedParserStackRightBoundaryFinisherConstructionForAssemblySourceRest_of_sourceStart
    mixedParserStackSourceStartFinisherConstruction_for_assemblySourceRest

theorem mixedParserStackFinisherConstruction_for_assemblySourceRest :
    MixedParserStackFinisherConstructionForAssemblySourceRest :=
  MixedParserStackFinisherConstructionForAssemblySourceRest_of_trueLeftBoundary
    mixedParserStackTrueLeftBoundaryFinisherConstruction_for_assemblySourceRest

/--
Core finite-machine obligation for the left-boundary source-rest finish phase.
All surrounding results are exact-tape adapters; this leaf is responsible for
rewriting the mixed parser-stack/source-rest layout into
{name}`assemblySourceRestFinishTargetTape`.
-/
theorem assemblySourceRestFinishLeftBoundaryCoreConstruction :
    AssemblySourceRestFinishLeftBoundaryCoreConstruction :=
  assemblySourceRestFinishLeftBoundaryCoreConstruction_of_mixedParserStackFinisher
    mixedParserStackFinisherConstruction_for_assemblySourceRest

theorem assemblySourceRestFinishLeftBoundaryConstruction :
    AssemblySourceRestFinishLeftBoundaryConstruction :=
  assemblySourceRestFinishLeftBoundaryConstruction_of_core
    assemblySourceRestFinishLeftBoundaryCoreConstruction

theorem assemblySourceRestFinishQuoteBoundaryConstruction :
    AssemblySourceRestFinishQuoteBoundaryConstruction :=
  assemblySourceRestFinishQuoteBoundaryConstruction_of_leftBoundary
    assemblySourceRestFinishLeftBoundaryConstruction

theorem assemblySourceRestFinishConstruction :
    AssemblySourceRestFinishConstruction :=
  assemblySourceRestFinishConstruction_of_quoteBoundary
    assemblySourceRestFinishQuoteBoundaryConstruction

end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC

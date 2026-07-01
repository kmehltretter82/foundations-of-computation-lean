import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Quoter.SourceRestFinishCore.LiveTail

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

def MixedParserStackPrefixQuotedSeparatedFinisherAssemblySourceRestSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTape
        (MixedParserStackRewriterDefaultedInternalMarkerTape
          w sourceRestBits
          (preservingCellPassCellBits sourceRestBits)
          stage)
        (MixedParserStackWholeSourcePrefixQuotedSeparatedTape
          w sourceRestBits stage)

def
    MixedParserStackPrefixQuotedSeparatedFinisherConstructionForAssemblySourceRest :
    Prop :=
  exists finish : MachineDescription,
    MixedParserStackPrefixQuotedSeparatedFinisherAssemblySourceRestSpec finish

theorem
    MixedParserStackPrefixQuotedSeparatedFinisherConstructionForAssemblySourceRest_of_mixedOptionCellQuoteLiveTailEmitter
    (hemitter :
      MixedOptionCellQuoteLiveTailEmitterConstructionForAssemblySourceRest) :
    MixedParserStackPrefixQuotedSeparatedFinisherConstructionForAssemblySourceRest := by
  rcases hemitter with ⟨finish, hfinish⟩
  refine ⟨finish, hfinish.left, ?_⟩
  intro w sourceRestBits stage
  rw [MixedParserStackRewriterDefaultedInternalMarkerTape_eq_mixedOptionCellQuoteLiveTailEmitterSplitSourceTape]
  rw [MixedParserStackWholeSourcePrefixQuotedSeparatedTape_eq_mixedOptionCellQuoteLiveTailEmitterTargetTape]
  exact hfinish.right w sourceRestBits stage

def MixedParserStackAfterRawTailScanJoinFinisherAssemblySourceRestSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTape
        (MixedParserStackWholeSourceAfterRawTailScanTape
          w sourceRestBits stage)
        (MixedParserStackRewriterWholeSourceTargetTape
          (MixedParserStackRewriterTrueSourceCells
            w sourceRestBits stage)
          (assemblySourceRestFinishRawTailBits sourceRestBits stage))

def
    MixedParserStackAfterRawTailScanJoinFinisherConstructionForAssemblySourceRest :
    Prop :=
  exists finish : MachineDescription,
    MixedParserStackAfterRawTailScanJoinFinisherAssemblySourceRestSpec finish

theorem
    MixedParserStackAfterRawTailScanJoinFinisherConstructionForAssemblySourceRest_of_mixedOptionCellQuoteLiveTailJoiner
    (hjoin :
      MixedOptionCellQuoteLiveTailJoinerConstructionForAssemblySourceRest) :
    MixedParserStackAfterRawTailScanJoinFinisherConstructionForAssemblySourceRest := by
  rcases hjoin with ⟨finish, hfinish⟩
  refine ⟨finish, hfinish.left, ?_⟩
  intro w sourceRestBits stage
  rw [MixedParserStackWholeSourceAfterRawTailScanTape_eq_mixedOptionCellQuoteLiveTailSeparatedTape]
  rw [MixedParserStackRewriterWholeSourceTargetTape_eq_quoteRestJoinedTape]
  rw [← mixedOptionCellQuoteLiveTailJoinedTape_eq_assemblyQuoteRestJoinedTape]
  exact hfinish.right w sourceRestBits stage

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
Finite-machine obligation for Phase 1 and Phase 2 of the mixed parser-stack
finisher.  It emits the header and quoted parser-prefix/stage prefix, leaves
the live raw tail on the right, and keeps the reusable source-rest quote behind
the structural blank for the final join phase.
-/
theorem
    mixedParserStackPrefixQuotedSeparatedFinisherConstruction_for_assemblySourceRest :
    MixedParserStackPrefixQuotedSeparatedFinisherConstructionForAssemblySourceRest :=
  MixedParserStackPrefixQuotedSeparatedFinisherConstructionForAssemblySourceRest_of_mixedOptionCellQuoteLiveTailEmitter
    mixedOptionCellQuoteLiveTailEmitterConstruction_for_assemblySourceRest

/--
Finite-machine obligation for Phase 3 of the mixed parser-stack finisher.  It
joins the already-computed quoted source-rest field onto the emitted prefix and
leaves {lit}`stageBits ++ sourceRestBits` as the live right tail.
-/
theorem
    mixedParserStackAfterRawTailScanJoinFinisherConstruction_for_assemblySourceRest :
    MixedParserStackAfterRawTailScanJoinFinisherConstructionForAssemblySourceRest :=
  MixedParserStackAfterRawTailScanJoinFinisherConstructionForAssemblySourceRest_of_mixedOptionCellQuoteLiveTailJoiner
    mixedOptionCellQuoteLiveTailJoinerConstruction

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

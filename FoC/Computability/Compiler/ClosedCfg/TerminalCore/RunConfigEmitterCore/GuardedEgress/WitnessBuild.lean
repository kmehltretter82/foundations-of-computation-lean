import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.GuardedEgress.WitnessDispatch
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.GuardedEgress.WitnessKnownRuns
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.GuardedEgress.WitnessStageRuns

set_option doc.verso true

/-!
# Completed metadata-witness bridge

This module composes the located guarded payload, the branch-sensitive suffix
parser/normalizer, and the fixed right-marker installer.  Its public result is
the unconditional tape-equivalence construction consumed by guarded egress.
-/

namespace FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
namespace GuardedEgress.MetadataWitnessBuild

open Languages MachineDescription
open CommonGround.FiniteTransducers
open MetadataWitnessBridge MetadataWitnessBridgeLocate MetadataWitnessStage

/-!
## Exact parser sources
-/

theorem locatedTape_eq_knownSource
    (i : Index) (finalState : Nat)
    (hwitness :
      loopDispatcherDoneWitness i.description i.sourceLayout =
        .known finalState) :
    MetadataWitnessBridgeLocate.locatedTape i =
      MetadataWitnessSuffixParser.sourceTape
        (MetadataWitnessStage.locatedLeft i)
        (MetadataWitnessStage.rawMetadataTokens i)
        i.scratchWidth i.finalHit
        (List.append (MetadataTokenCopy.encodedTokenCells .one)
          (MetadataTokenCopy.encodedTokens
            (MetadataWitnessBridge.natTokens finalState))) [] := by
  rw [MetadataWitnessStage.locatedTape_eq_payload]
  unfold MetadataWitnessStage.locatedPayload
    MetadataWitnessSuffixParser.sourceTape
  rw [MetadataWitnessStage.witnessCells_known i finalState hwitness]
  unfold MetadataWitnessStage.scratchCells Index.scratchWidth
    RunConfigEmitterTheory.scratchWidthMarkers
  simp [List.append_assoc]

theorem locatedTape_eq_otherSource
    (i : Index)
    (hwitness :
      loopDispatcherDoneWitness i.description i.sourceLayout = .other) :
    MetadataWitnessBridgeLocate.locatedTape i =
      MetadataWitnessSuffixParser.sourceTape
        (MetadataWitnessStage.locatedLeft i)
        (MetadataWitnessStage.rawMetadataTokens i)
        i.scratchWidth i.finalHit
        (MetadataTokenCopy.encodedTokenCells .zero) [] := by
  rw [MetadataWitnessStage.locatedTape_eq_payload]
  unfold MetadataWitnessStage.locatedPayload
    MetadataWitnessSuffixParser.sourceTape
  rw [MetadataWitnessStage.witnessCells_other i hwitness]
  unfold MetadataWitnessStage.scratchCells Index.scratchWidth
    RunConfigEmitterTheory.scratchWidthMarkers
  simp [List.append_assoc]

theorem otherTargetTape_eq_otherEntryTape
    (i : Index) (scratchCount : Nat) :
    MetadataWitnessSuffixParser.otherTargetTape
        (MetadataWitnessStage.locatedLeft i)
        (MetadataWitnessStage.rawMetadataTokens i)
        scratchCount [] =
      MetadataWitnessStage.Normalizer.otherEntryTape i scratchCount := by
  unfold MetadataWitnessSuffixParser.otherTargetTape
    MetadataWitnessStage.Normalizer.otherEntryTape
  rw [MetadataWitnessStage.encodedTokens_eq_map_physicalTokenBits]
  rw [show some false :: none :: MetadataWitnessStage.locatedLeft i =
      List.append [some false, none]
        (MetadataWitnessStage.locatedLeft i) by rfl]
  rw [MetadataWitnessStage.markerLocatedLeft_eq]
  simp only [List.map_reverse]

/-!
## Other-branch dispatch
-/

theorem dispatch_haltsFromTapeEquiv_other
    (i : Index)
    (hwitness :
      loopDispatcherDoneWitness i.description i.sourceLayout = .other) :
    MetadataWitnessDispatch.description.HaltsFromTapeEquiv
      (MetadataWitnessBridgeLocate.locatedTape i)
      (MetadataWitnessStage.preMarkerTape i
        (MetadataWitnessStage.rawMetadataTokens i)
        (18 + 2 * i.scratchWidth)) := by
  rw [locatedTape_eq_otherSource i hwitness]
  apply MetadataWitnessDispatch.description_haltsFromTapeEquiv_other_of_normalizer
  rw [otherTargetTape_eq_otherEntryTape]
  exact MetadataWitnessStage.Normalizer.description_runsFrom_other
    i i.scratchWidth

/-!
## Locator, dispatch, and marker assembly
-/

def preMarkerDescription : MachineDescription :=
  SeqViaCanonical MetadataWitnessBridgeLocate.description
    MetadataWitnessDispatch.description

def description : MachineDescription :=
  SeqViaCanonical preMarkerDescription MetadataWitnessMarker.description

theorem preMarkerDescription_subroutineReady :
    preMarkerDescription.SubroutineReady := by
  exact SeqViaCanonical_subroutineReady
    MetadataWitnessBridgeLocate.description_subroutineReady
    MetadataWitnessDispatch.description_subroutineReady

theorem description_subroutineReady : description.SubroutineReady := by
  exact SeqViaCanonical_subroutineReady
    preMarkerDescription_subroutineReady
    MetadataWitnessMarker.description_subroutineReady

theorem preMarkerDescription_haltsFromTapeEquiv_other
    (i : Index)
    (hwitness :
      loopDispatcherDoneWitness i.description i.sourceLayout = .other)
    (actual : Tape Bool)
    (hactual : Tape.Equiv actual
      (TapeFieldSerializer.correctedSerializedTapeFieldTarget i)) :
    preMarkerDescription.HaltsFromTapeEquiv actual
      (MetadataWitnessStage.preMarkerTape i
        (MetadataWitnessStage.rawMetadataTokens i)
        (18 + 2 * i.scratchWidth)) := by
  exact SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
    MetadataWitnessBridgeLocate.description_subroutineReady
    MetadataWitnessDispatch.description_subroutineReady
    (MetadataWitnessBridgeLocate.description_haltsFromTapeEquiv
      i actual hactual)
    (moveLeft_moveRight_equiv_self
      (MetadataWitnessBridgeLocate.locatedTape i))
    (dispatch_haltsFromTapeEquiv_other i hwitness)

theorem description_haltsFromTapeEquiv_other_marked
    (i : Index)
    (hwitness :
      loopDispatcherDoneWitness i.description i.sourceLayout = .other)
    (actual : Tape Bool)
    (hactual : Tape.Equiv actual
      (TapeFieldSerializer.correctedSerializedTapeFieldTarget i)) :
    description.HaltsFromTapeEquiv actual
      (MetadataWitnessStage.markedTape i
        (MetadataWitnessStage.rawMetadataTokens i)
        (18 + 2 * i.scratchWidth)) := by
  exact SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
    preMarkerDescription_subroutineReady
    MetadataWitnessMarker.description_subroutineReady
    (preMarkerDescription_haltsFromTapeEquiv_other
      i hwitness actual hactual)
    (moveLeft_moveRight_equiv_self
      (MetadataWitnessStage.preMarkerTape i
        (MetadataWitnessStage.rawMetadataTokens i)
        (18 + 2 * i.scratchWidth)))
    (MetadataWitnessStage.marker_haltsFromTape i
      (MetadataWitnessStage.rawMetadataTokens i)
      (18 + 2 * i.scratchWidth)).toEquiv

theorem rawMetadataTokens_eq_sourceMetadataTokens_other
    (i : Index)
    (hwitness :
      loopDispatcherDoneWitness i.description i.sourceLayout = .other) :
    MetadataWitnessStage.rawMetadataTokens i =
      MetadataWitnessBridge.sourceMetadataTokens i := by
  rw [MetadataWitnessBridge.sourceMetadataTokens_other i hwitness]
  rfl

theorem description_other
    (i : Index)
    (hwitness :
      loopDispatcherDoneWitness i.description i.sourceLayout = .other)
    (actual : Tape Bool)
    (hactual : Tape.Equiv actual
      (TapeFieldSerializer.correctedSerializedTapeFieldTarget i)) :
    exists layout : MetadataWitnessBridge.ReadyLayout,
      description.HaltsFromTapeEquiv actual
        (MetadataWitnessBridge.readyTape i layout) := by
  refine ⟨MetadataWitnessStage.stagedReadyLayout i
    (18 + 2 * i.scratchWidth), ?_⟩
  have hmarked := description_haltsFromTapeEquiv_other_marked
    i hwitness actual hactual
  rw [rawMetadataTokens_eq_sourceMetadataTokens_other i hwitness] at hmarked
  rcases hmarked with ⟨output, houtput, hequiv⟩
  exact ⟨output, houtput,
    Tape.Equiv.trans hequiv
      (MetadataWitnessStage.markedTape_equiv_readyTape
        i (18 + 2 * i.scratchWidth))⟩

/-!
## Known-branch composition from its finite normalizer run

The finite known-branch execution lives in the sibling run module.  Keeping
the assembly below parameterized by that single run isolates the long table
proof from the locator and marker composition.
-/

def KnownNormalizerRun
    (i : Index) (finalState rightPadding : Nat) : Prop :=
  CommonGround.FiniteTransducers.Structured.MultiTapeLowering.RunsFromStateTapeEquiv
    MetadataWitnessStage.Normalizer.description
    (MetadataWitnessStage.Normalizer.knownSeekWitnessState i.finalHit)
    MetadataWitnessStage.Normalizer.description.halt
    (MetadataWitnessSuffixParser.knownTargetTape
      (MetadataWitnessStage.locatedLeft i)
      (MetadataWitnessStage.rawMetadataTokens i)
      i.scratchWidth finalState [])
    (MetadataWitnessStage.preMarkerTape i
      (MetadataWitnessBridge.sourceMetadataTokens i) rightPadding)

theorem knownNormalizerRun
    (i : Index) (finalState : Nat)
    (hwitness :
      loopDispatcherDoneWitness i.description i.sourceLayout =
        .known finalState) :
    KnownNormalizerRun i finalState
      (MetadataWitnessStage.Normalizer.knownRightPadding i.scratchWidth
        i.sourceLayout.config.state) := by
  unfold KnownNormalizerRun
  exact MetadataWitnessStage.Normalizer.description_runsFrom_known
    i i.scratchWidth finalState hwitness

theorem dispatch_haltsFromTapeEquiv_known_of_normalizer
    (i : Index) (finalState rightPadding : Nat)
    (hwitness :
      loopDispatcherDoneWitness i.description i.sourceLayout =
        .known finalState)
    (hnormalizer : KnownNormalizerRun i finalState rightPadding) :
    MetadataWitnessDispatch.description.HaltsFromTapeEquiv
      (MetadataWitnessBridgeLocate.locatedTape i)
      (MetadataWitnessStage.preMarkerTape i
        (MetadataWitnessBridge.sourceMetadataTokens i) rightPadding) := by
  rw [locatedTape_eq_knownSource i finalState hwitness]
  unfold KnownNormalizerRun at hnormalizer
  exact MetadataWitnessDispatch.description_haltsFromTapeEquiv_known_of_normalizer
    (MetadataWitnessStage.locatedLeft i)
    (MetadataWitnessStage.rawMetadataTokens i)
    i.scratchWidth i.finalHit finalState [] hnormalizer

theorem preMarkerDescription_haltsFromTapeEquiv_known_of_normalizer
    (i : Index) (finalState rightPadding : Nat)
    (hwitness :
      loopDispatcherDoneWitness i.description i.sourceLayout =
        .known finalState)
    (hnormalizer : KnownNormalizerRun i finalState rightPadding)
    (actual : Tape Bool)
    (hactual : Tape.Equiv actual
      (TapeFieldSerializer.correctedSerializedTapeFieldTarget i)) :
    preMarkerDescription.HaltsFromTapeEquiv actual
      (MetadataWitnessStage.preMarkerTape i
        (MetadataWitnessBridge.sourceMetadataTokens i) rightPadding) := by
  exact SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
    MetadataWitnessBridgeLocate.description_subroutineReady
    MetadataWitnessDispatch.description_subroutineReady
    (MetadataWitnessBridgeLocate.description_haltsFromTapeEquiv
      i actual hactual)
    (moveLeft_moveRight_equiv_self
      (MetadataWitnessBridgeLocate.locatedTape i))
    (dispatch_haltsFromTapeEquiv_known_of_normalizer
      i finalState rightPadding hwitness hnormalizer)

theorem description_haltsFromTapeEquiv_known_marked_of_normalizer
    (i : Index) (finalState rightPadding : Nat)
    (hwitness :
      loopDispatcherDoneWitness i.description i.sourceLayout =
        .known finalState)
    (hnormalizer : KnownNormalizerRun i finalState rightPadding)
    (actual : Tape Bool)
    (hactual : Tape.Equiv actual
      (TapeFieldSerializer.correctedSerializedTapeFieldTarget i)) :
    description.HaltsFromTapeEquiv actual
      (MetadataWitnessStage.markedTape i
        (MetadataWitnessBridge.sourceMetadataTokens i) rightPadding) := by
  exact SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
    preMarkerDescription_subroutineReady
    MetadataWitnessMarker.description_subroutineReady
    (preMarkerDescription_haltsFromTapeEquiv_known_of_normalizer
      i finalState rightPadding hwitness hnormalizer actual hactual)
    (moveLeft_moveRight_equiv_self
      (MetadataWitnessStage.preMarkerTape i
        (MetadataWitnessBridge.sourceMetadataTokens i) rightPadding))
    (MetadataWitnessStage.marker_haltsFromTape i
      (MetadataWitnessBridge.sourceMetadataTokens i) rightPadding).toEquiv

theorem description_known_of_normalizer
    (i : Index) (finalState rightPadding : Nat)
    (hwitness :
      loopDispatcherDoneWitness i.description i.sourceLayout =
        .known finalState)
    (hnormalizer : KnownNormalizerRun i finalState rightPadding)
    (actual : Tape Bool)
    (hactual : Tape.Equiv actual
      (TapeFieldSerializer.correctedSerializedTapeFieldTarget i)) :
    exists layout : MetadataWitnessBridge.ReadyLayout,
      description.HaltsFromTapeEquiv actual
        (MetadataWitnessBridge.readyTape i layout) := by
  refine ⟨MetadataWitnessStage.stagedReadyLayout i rightPadding, ?_⟩
  have hmarked :=
    description_haltsFromTapeEquiv_known_marked_of_normalizer
      i finalState rightPadding hwitness hnormalizer actual hactual
  rcases hmarked with ⟨output, houtput, hequiv⟩
  exact ⟨output, houtput,
    Tape.Equiv.trans hequiv
      (MetadataWitnessStage.markedTape_equiv_readyTape i rightPadding)⟩

theorem description_known
    (i : Index) (finalState : Nat)
    (hwitness :
      loopDispatcherDoneWitness i.description i.sourceLayout =
        .known finalState)
    (actual : Tape Bool)
    (hactual : Tape.Equiv actual
      (TapeFieldSerializer.correctedSerializedTapeFieldTarget i)) :
    exists layout : MetadataWitnessBridge.ReadyLayout,
      description.HaltsFromTapeEquiv actual
        (MetadataWitnessBridge.readyTape i layout) := by
  exact description_known_of_normalizer i finalState
    (MetadataWitnessStage.Normalizer.knownRightPadding i.scratchWidth
      i.sourceLayout.config.state)
    hwitness (knownNormalizerRun i finalState hwitness) actual hactual

/-!
## Public construction
-/

theorem spec : MetadataWitnessBridge.Spec description := by
  constructor
  · exact description_subroutineReady
  · intro i finalState hwitness actual hactual
    exact description_known i finalState hwitness actual hactual
  · intro i hwitness actual hactual
    exact description_other i hwitness actual hactual

theorem construction : MetadataWitnessBridge.Construction := by
  exact ⟨description, spec⟩

end GuardedEgress.MetadataWitnessBuild
end FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore

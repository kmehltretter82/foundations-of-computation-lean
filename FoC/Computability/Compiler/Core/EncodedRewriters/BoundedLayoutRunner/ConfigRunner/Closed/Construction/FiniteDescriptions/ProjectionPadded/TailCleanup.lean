import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Closed.Construction.FiniteDescriptions.ProjectionPadded.Shape

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

def SelectedProjectionPaddedTailEmitterSpec
    (useAccept : Bool)
    (tail : MachineDescription) : Prop :=
  RightScratchPaddedEmitterSpec
    (fun L : DovetailLayout =>
        (SelectedProjectionTailProjector.sourceTape L
          ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
            some)))
    (fun L : DovetailLayout =>
      encodeCodeWordAsInput
        (SelectedProjectionOutputCode useAccept L))
    (fun L : DovetailLayout =>
      (ParsedLayoutBits L).length)
    (SelectedProjectionOutputTape useAccept)
    tail

def SelectedProjectionPaddedTailEmitterConstruction : Prop :=
  forall useAccept : Bool,
    exists tail : MachineDescription,
      SelectedProjectionPaddedTailEmitterSpec useAccept tail

def SelectedProjectionPaddedTailCleanupSpec
    (useAccept : Bool)
    (cleanup : MachineDescription) : Prop :=
  RightScratchPaddedEmitterSpec
    (fun L : DovetailLayout =>
        (SelectedProjectionTailProjector.sourceScannerRightHandoffTape L
          ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
            some)))
    (fun L : DovetailLayout =>
      encodeCodeWordAsInput
        (SelectedProjectionOutputCode useAccept L))
    (fun L : DovetailLayout =>
      (ParsedLayoutBits L).length)
    (SelectedProjectionOutputTape useAccept)
    cleanup

def SelectedProjectionPaddedTailCleanupConstruction : Prop :=
  forall useAccept : Bool,
    exists cleanup : MachineDescription,
      SelectedProjectionPaddedTailCleanupSpec useAccept cleanup

def SelectedProjectionPaddedTailCleanupExactShapeSpec
    (useAccept : Bool)
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall L : DovetailLayout,
      cleanup.HaltsFromTape
        (SelectedProjectionTailProjector.sourceScannerRightHandoffTape L
          ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
            some))
        (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L)

def SelectedProjectionPaddedTailCleanupExactShapeConstruction : Prop :=
  forall useAccept : Bool,
    exists cleanup : MachineDescription,
      SelectedProjectionPaddedTailCleanupExactShapeSpec useAccept cleanup

theorem selectedProjectionPaddedTailCleanupSpec_of_exactShape
    {useAccept : Bool} {cleanup : MachineDescription}
    (hcleanup :
      SelectedProjectionPaddedTailCleanupExactShapeSpec useAccept cleanup) :
    SelectedProjectionPaddedTailCleanupSpec useAccept cleanup := by
  constructor
  · exact hcleanup.left
  constructor
  · intro L
    simpa [SelectedProjectionPaddedTailCleanupSpec,
      SelectedProjectionEquivEmitterPaddedOutputTape] using
      hcleanup.right L
  · intro L
    exact SelectedProjectionEquivEmitterPaddedOutputTape_equiv useAccept L

theorem selectedProjectionPaddedTailCleanupConstruction_of_exactShape
    (hcleanup :
      SelectedProjectionPaddedTailCleanupExactShapeConstruction) :
    SelectedProjectionPaddedTailCleanupConstruction := by
  intro useAccept
  rcases hcleanup useAccept with ⟨cleanup, hcleanup⟩
  exact
    ⟨cleanup,
      selectedProjectionPaddedTailCleanupSpec_of_exactShape hcleanup⟩

def SelectedProjectionPaddedTailEmitterFromCleanup
    (_useAccept : Bool)
    (cleanup : MachineDescription) : MachineDescription :=
  seqSubroutine
    CanonicalLayouts.DovetailLayoutScanner.StageConfigurationsAndFinalFlagsScannerDescription
    cleanup Direction.right

theorem selectedProjectionPaddedTailEmitterSpec_of_cleanup
    {useAccept : Bool} {cleanup : MachineDescription}
    (hcleanup : SelectedProjectionPaddedTailCleanupSpec useAccept cleanup) :
    SelectedProjectionPaddedTailEmitterSpec useAccept
      (SelectedProjectionPaddedTailEmitterFromCleanup useAccept
        cleanup) := by
  let baseLeft :=
    fun L : DovetailLayout =>
      (SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
        some
  constructor
  · exact
      seqSubroutine_subroutineReady
        CanonicalLayouts.DovetailLayoutScanner.stageConfigurationsAndFinalFlagsScannerDescription_subroutineReady
        hcleanup.left
  constructor
  · intro L
    have hscanner :
        CanonicalLayouts.DovetailLayoutScanner.StageConfigurationsAndFinalFlagsScannerDescription.HaltsFromTape
          (SelectedProjectionTailProjector.sourceTape L (baseLeft L))
          (SelectedProjectionTailProjector.sourceScannerHandoffTape L
            (baseLeft L)) :=
      SelectedProjectionTailProjector.sourceScanner_haltsFromTape_withBase
        L (baseLeft L)
    have hcleanupRun :
        exists nB : Nat,
          cleanup.runConfig nB
              { state := cleanup.start
                tape :=
                  Tape.move Direction.right
                    (SelectedProjectionTailProjector.sourceScannerHandoffTape
                      L (baseLeft L)) } =
            { state := cleanup.halt
              tape := SelectedProjectionEquivEmitterPaddedOutputTape
                useAccept L } := by
      simpa [baseLeft,
        SelectedProjectionTailProjector.sourceScannerRightHandoffTape,
        List.map_reverse]
        using
          runConfig_eq_halt_of_haltsFromTape
            (hcleanup.right.left L)
    simpa [SelectedProjectionPaddedTailEmitterFromCleanup, baseLeft,
      List.map_reverse] using
      seqSubroutine_haltsFromTape_of_haltsFromTape
        (A :=
          CanonicalLayouts.DovetailLayoutScanner.StageConfigurationsAndFinalFlagsScannerDescription)
        (B := cleanup)
        (handoffMove := Direction.right)
        CanonicalLayouts.DovetailLayoutScanner.stageConfigurationsAndFinalFlagsScannerDescription_subroutineReady
        hcleanup.left hscanner hcleanupRun
  · intro L
    exact SelectedProjectionEquivEmitterPaddedOutputTape_equiv useAccept L

theorem selectedProjectionPaddedTailEmitterConstruction_of_cleanup
    (hcleanup : SelectedProjectionPaddedTailCleanupConstruction) :
    SelectedProjectionPaddedTailEmitterConstruction := by
  intro useAccept
  rcases hcleanup useAccept with ⟨cleanup, hcleanup⟩
  exact
    ⟨SelectedProjectionPaddedTailEmitterFromCleanup useAccept cleanup,
      selectedProjectionPaddedTailEmitterSpec_of_cleanup hcleanup⟩

namespace SelectedProjectionPaddedTailCleanup

def sourceBits (L : DovetailLayout) : Word Bool :=
  List.append
    (SelectedProjectionTailProjector.outputPrefixBits L)
    (SelectedProjectionTailProjector.sourceFieldBits L)

def sourceRewindDescription : MachineDescription where
  stateCount := 3
  start := 0
  halt := 2
  transitions :=
    [ transition 0 none none Direction.left 1
    , transition 0 (some false) (some false) Direction.left 1
    , transition 0 (some true) (some true) Direction.left 1
    , transition 1 (some false) (some false) Direction.left 1
    , transition 1 (some true) (some true) Direction.left 1
    , transition 1 none none Direction.right 2 ]

def rewindSourceTape (bits : Word Bool) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells
    (bits.reverse.map some) []

def rewindTargetTape (bits : Word Bool) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells
    [none] (List.append (bits.map some) [none])

theorem sourceRewindDescription_wellFormed :
    sourceRewindDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := sourceRewindDescription.transitions)
      (stateCount := sourceRewindDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := sourceRewindDescription.transitions)
      (by decide)

theorem sourceRewindDescription_haltTransitionFree :
    sourceRewindDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := sourceRewindDescription.transitions)
    (state := sourceRewindDescription.halt)
    (by decide)

theorem sourceRewindDescription_subroutineReady :
    sourceRewindDescription.SubroutineReady :=
  ⟨sourceRewindDescription_wellFormed,
    sourceRewindDescription_haltTransitionFree⟩

theorem sourceRewindDescription_run_scan
    (leftBits : Word Bool) (current : Bool)
    (rightCells : List (Option Bool)) :
    sourceRewindDescription.runConfig (leftBits.length + 1)
        { state := 1
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              (leftBits.map some)
              (some current :: rightCells) } =
      { state := 1
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells []
            (none ::
              List.append
                ((List.append leftBits.reverse [current]).map some)
                rightCells) } := by
  induction leftBits generalizing current rightCells with
  | nil =>
      cases current <;>
        simp [sourceRewindDescription,
          DovetailInitialLayoutInitializer.tapeAtCells, runConfig,
          stepConfig, lookupTransition, Matches, transition,
          Tape.read, Tape.move, Tape.moveLeft, Tape.write]
  | cons next rest ih =>
      rw [show (next :: rest).length + 1 = 1 + (rest.length + 1) by
        simp
        omega]
      rw [runConfig_add]
      have hstep :
          sourceRewindDescription.runConfig 1
              { state := 1
                tape :=
                  DovetailInitialLayoutInitializer.tapeAtCells
                    ((next :: rest).map some)
                    (some current :: rightCells) } =
            { state := 1
              tape :=
                DovetailInitialLayoutInitializer.tapeAtCells
                  (rest.map some)
                  (some next :: some current :: rightCells) } := by
        cases current <;>
          simp [sourceRewindDescription,
            DovetailInitialLayoutInitializer.tapeAtCells, runConfig,
            stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.move, Tape.moveLeft, Tape.write]
      rw [hstep]
      simpa [List.append_assoc] using
        ih next (some current :: rightCells)

theorem sourceRewindDescription_step_finish
    (bits : Word Bool) :
    sourceRewindDescription.runConfig 1
        { state := 1
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells []
              (none :: List.append (bits.map some) [none]) } =
      { state := sourceRewindDescription.halt
        tape := rewindTargetTape bits } := by
  cases bits with
  | nil =>
      simp [sourceRewindDescription, rewindTargetTape,
        DovetailInitialLayoutInitializer.tapeAtCells, runConfig,
        stepConfig, lookupTransition, Matches, transition,
        Tape.read, Tape.move, Tape.moveRight, Tape.write]
  | cons bit rest =>
      cases bit <;>
        simp [sourceRewindDescription, rewindTargetTape,
          DovetailInitialLayoutInitializer.tapeAtCells, runConfig,
          stepConfig, lookupTransition, Matches, transition,
          Tape.read, Tape.move, Tape.moveRight, Tape.write]

theorem sourceRewindDescription_run_from_leftStack
    (leftStack : Word Bool) :
    sourceRewindDescription.runConfig (leftStack.length + 2)
        { state := sourceRewindDescription.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              (leftStack.map some) [] } =
      { state := sourceRewindDescription.halt
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells [none]
            (List.append (leftStack.reverse.map some) [none]) } := by
  cases leftStack with
  | nil =>
      simp [sourceRewindDescription, DovetailInitialLayoutInitializer.tapeAtCells,
        runConfig, stepConfig, lookupTransition, Matches, transition,
        Tape.read, Tape.move, Tape.moveLeft, Tape.moveRight, Tape.write]
  | cons current rest =>
      rw [show (current :: rest).length + 2 =
        1 + ((rest.length + 1) + 1) by
        simp
        omega]
      rw [runConfig_add]
      have hstart :
          sourceRewindDescription.runConfig 1
              { state := sourceRewindDescription.start
                tape :=
                  DovetailInitialLayoutInitializer.tapeAtCells
                    ((current :: rest).map some) [] } =
            { state := 1
              tape :=
                DovetailInitialLayoutInitializer.tapeAtCells
                  (rest.map some) [some current, none] } := by
        cases current <;>
          simp [sourceRewindDescription,
            DovetailInitialLayoutInitializer.tapeAtCells, runConfig,
            stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.move, Tape.moveLeft, Tape.write]
      rw [hstart]
      rw [show (rest.length + 1) + 1 = (rest.length + 1) + 1 by rfl]
      rw [runConfig_add]
      rw [sourceRewindDescription_run_scan rest current [none]]
      simpa [rewindTargetTape, List.map_append, List.append_assoc] using
        sourceRewindDescription_step_finish
          (List.append rest.reverse [current])

theorem sourceRewindDescription_run
    (bits : Word Bool) :
    sourceRewindDescription.runConfig (bits.length + 2)
        { state := sourceRewindDescription.start
          tape := rewindSourceTape bits } =
      { state := sourceRewindDescription.halt
        tape := rewindTargetTape bits } := by
  simpa [rewindSourceTape, rewindTargetTape] using
    sourceRewindDescription_run_from_leftStack bits.reverse

theorem sourceRewindDescription_haltsFromTape
    (bits : Word Bool) :
    sourceRewindDescription.HaltsFromTape
      (rewindSourceTape bits) (rewindTargetTape bits) := by
  refine ⟨bits.length + 2, ?_⟩
  constructor
  · rw [sourceRewindDescription_run]
  · rw [sourceRewindDescription_run]

theorem sourceScannerRightHandoffTape_eq_rewindSourceTape
    (L : DovetailLayout) :
    SelectedProjectionTailProjector.sourceScannerRightHandoffTape L
        ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
          some) =
      rewindSourceTape (sourceBits L) := by
  rw [SelectedProjectionTailProjector.sourceScannerRightHandoffTape_eq,
    rewindSourceTape, sourceBits,
    SelectedProjectionTailProjector.sourceFieldBits]
  rw [←
    CanonicalLayouts.DovetailLayoutScanner.configurationRestoredBitsRev_map_some_withBase
      L.acceptConfig
      (List.append
        ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            L.stage).reverse.map some)
        ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
          some))]
  rw [←
    CanonicalLayouts.DovetailLayoutScanner.configurationRestoredBitsRev_map_some_withBase
      L.rejectConfig]
  have hacceptBits :
      (CanonicalLayouts.DovetailLayoutScanner.configurationRestoredBitsRev
          L.acceptConfig).map some =
        (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
          L.acceptConfig []).reverse.map some := by
    have h :=
      congrArg (fun xs : Word Bool => xs.reverse.map some)
        (CanonicalLayouts.DovetailLayoutScanner.configurationRestoredBitsRev_reverse
          L.acceptConfig)
    simpa using h
  have hrejectBits :
      (CanonicalLayouts.DovetailLayoutScanner.configurationRestoredBitsRev
          L.rejectConfig).map some =
        (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
          L.rejectConfig []).reverse.map some := by
    have h :=
      congrArg (fun xs : Word Bool => xs.reverse.map some)
        (CanonicalLayouts.DovetailLayoutScanner.configurationRestoredBitsRev_reverse
          L.rejectConfig)
    simpa using h
  rw [hacceptBits, hrejectBits]
  rw [←
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil
      L.rejectConfig
      (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits L.acceptHit
        (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          L.rejectHit []))]
  rw [←
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil
      L.acceptConfig
      (List.append
        (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
          L.rejectConfig [])
        (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits L.acceptHit
          (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
            L.rejectHit [])))]
  simp [CanonicalLayouts.DovetailLayoutScanner.finalHitFlagsRestoredLeftWithBase,
    CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
    List.map_append, List.map_reverse, List.reverse_append,
    List.append_assoc]

theorem sourceRewindDescription_haltsFrom_sourceScannerRightHandoffTape
    (L : DovetailLayout) :
    sourceRewindDescription.HaltsFromTape
      (SelectedProjectionTailProjector.sourceScannerRightHandoffTape L
        ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
          some))
      (rewindTargetTape (sourceBits L)) := by
  rw [sourceScannerRightHandoffTape_eq_rewindSourceTape L]
  exact sourceRewindDescription_haltsFromTape (sourceBits L)

end SelectedProjectionPaddedTailCleanup



/--
Finite-machine leaf for the selected-projection tail cleanup.  The reusable
stage/configuration/final-flag scanner has already consumed the remaining
layout fields and handed off one cell to the right; this cleanup may leave
trailing blank padding while emitting a tape equivalent to the right-shifted
selected simulator-layout output.
-/
theorem selectedProjectionPaddedTailCleanupExactShapeConstruction_scaffold :
    SelectedProjectionPaddedTailCleanupExactShapeConstruction := by
  sorry

theorem selectedProjectionPaddedTailCleanupConstruction_scaffold :
    SelectedProjectionPaddedTailCleanupConstruction :=
  selectedProjectionPaddedTailCleanupConstruction_of_exactShape
    selectedProjectionPaddedTailCleanupExactShapeConstruction_scaffold

theorem selectedProjectionPaddedTailEmitterConstruction_scaffold :
    SelectedProjectionPaddedTailEmitterConstruction :=
  selectedProjectionPaddedTailEmitterConstruction_of_cleanup
    selectedProjectionPaddedTailCleanupConstruction_scaffold

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC

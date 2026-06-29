import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.Shape

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

def sourceRightEndDescription : MachineDescription where
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [ transition 0 (some false) (some false) Direction.right 0
    , transition 0 (some true) (some true) Direction.right 0
    , transition 0 none none Direction.left 1 ]

def sourceRightEndTape (bits : Word Bool) : Tape Bool :=
  Tape.move Direction.left
    (DovetailInitialLayoutInitializer.tapeAtCells
      (List.append (bits.reverse.map some) [none]) [none])

theorem sourceRightEndDescription_wellFormed :
    sourceRightEndDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := sourceRightEndDescription.transitions)
      (stateCount := sourceRightEndDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := sourceRightEndDescription.transitions)
      (by decide)

theorem sourceRightEndDescription_haltTransitionFree :
    sourceRightEndDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := sourceRightEndDescription.transitions)
    (state := sourceRightEndDescription.halt)
    (by decide)

theorem sourceRightEndDescription_subroutineReady :
    sourceRightEndDescription.SubroutineReady :=
  ⟨sourceRightEndDescription_wellFormed,
    sourceRightEndDescription_haltTransitionFree⟩

theorem sourceRightEndDescription_step_bit
    (left right : List (Option Bool)) (bit : Bool) :
    sourceRightEndDescription.runConfig 1
        { state := sourceRightEndDescription.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              left (some bit :: right) } =
      { state := sourceRightEndDescription.start
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells
            (some bit :: left) right } := by
  cases bit <;> cases right <;>
    simp [sourceRightEndDescription,
      DovetailInitialLayoutInitializer.tapeAtCells,
      runConfig, stepConfig, lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

theorem sourceRightEndDescription_step_finish
    (left : List (Option Bool)) :
    sourceRightEndDescription.runConfig 1
        { state := sourceRightEndDescription.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              left [none] } =
      { state := sourceRightEndDescription.halt
        tape :=
          Tape.move Direction.left
            (DovetailInitialLayoutInitializer.tapeAtCells left [none]) } := by
  cases left <;>
    simp [sourceRightEndDescription,
      DovetailInitialLayoutInitializer.tapeAtCells,
      runConfig, stepConfig, lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft]

theorem sourceRightEndDescription_run_scan
    (bits : Word Bool) (left : List (Option Bool)) :
    sourceRightEndDescription.runConfig bits.length
        { state := sourceRightEndDescription.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              left (List.append (bits.map some) [none]) } =
      { state := sourceRightEndDescription.start
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells
            (List.append (bits.reverse.map some) left) [none] } := by
  induction bits generalizing left with
  | nil =>
      simp [runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        omega]
      rw [runConfig_add]
      change
        sourceRightEndDescription.runConfig rest.length
            (sourceRightEndDescription.runConfig 1
              { state := sourceRightEndDescription.start
                tape :=
                  DovetailInitialLayoutInitializer.tapeAtCells
                    left
                    (some bit :: List.append (rest.map some) [none]) }) =
          { state := sourceRightEndDescription.start
            tape :=
              DovetailInitialLayoutInitializer.tapeAtCells
                (List.append ((bit :: rest).reverse.map some) left)
                [none] }
      rw [sourceRightEndDescription_step_bit left
        (List.append (rest.map some) [none]) bit]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: left)

theorem sourceRightEndDescription_run
    (bits : Word Bool) :
    sourceRightEndDescription.runConfig (bits.length + 1)
        { state := sourceRightEndDescription.start
          tape := rewindTargetTape bits } =
      { state := sourceRightEndDescription.halt
        tape := sourceRightEndTape bits } := by
  rw [rewindTargetTape]
  rw [runConfig_add]
  rw [sourceRightEndDescription_run_scan bits [none]]
  simpa [sourceRightEndTape, rewindTargetTape, List.append_assoc] using
    sourceRightEndDescription_step_finish
      (List.append (bits.reverse.map some) [none])

theorem sourceRightEndDescription_haltsFromTape
    (bits : Word Bool) :
    sourceRightEndDescription.HaltsFromTape
      (rewindTargetTape bits) (sourceRightEndTape bits) := by
  refine ⟨bits.length + 1, ?_⟩
  constructor
  · rw [sourceRightEndDescription_run]
  · rw [sourceRightEndDescription_run]

theorem sourceRightEndDescription_haltsFrom_rewindTarget_sourceBits
    (L : DovetailLayout) :
    sourceRightEndDescription.HaltsFromTape
      (rewindTargetTape (sourceBits L))
      (sourceRightEndTape (sourceBits L)) :=
  sourceRightEndDescription_haltsFromTape (sourceBits L)

theorem tapeAtCells_move_left_move_right_cons_cons
    (left : List (Option Bool)) (head next : Option Bool)
    (right : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (DovetailInitialLayoutInitializer.tapeAtCells left
            (head :: next :: right))) =
      DovetailInitialLayoutInitializer.tapeAtCells left
        (head :: next :: right) := by
  simp [DovetailInitialLayoutInitializer.tapeAtCells, Tape.move,
    Tape.moveLeft, Tape.moveRight]

theorem rewindTargetTape_sourceBits_move_left_move_right
    (L : DovetailLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (rewindTargetTape (sourceBits L))) =
      rewindTargetTape (sourceBits L) := by
  simp [rewindTargetTape, sourceBits,
    SelectedProjectionTailProjector.outputPrefixBits,
    encodeCodeSymbolAsInput,
    DovetailInitialLayoutInitializer.tapeAtCells,
    Tape.move, Tape.moveLeft, Tape.moveRight]

theorem tape_move_left_tapeAtCells_single_move_left_move_right
    (left : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (Tape.move Direction.left
            (DovetailInitialLayoutInitializer.tapeAtCells left [none]))) =
      Tape.move Direction.left
        (DovetailInitialLayoutInitializer.tapeAtCells left [none]) := by
  cases left with
  | nil =>
      simp [DovetailInitialLayoutInitializer.tapeAtCells,
        Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons cell rest =>
      simp [DovetailInitialLayoutInitializer.tapeAtCells,
        Tape.move, Tape.moveLeft, Tape.moveRight]

theorem sourceRightEndTape_move_left_move_right
    (bits : Word Bool) :
    Tape.move Direction.left
        (Tape.move Direction.right (sourceRightEndTape bits)) =
      sourceRightEndTape bits := by
  simp [sourceRightEndTape,
    tape_move_left_tapeAtCells_single_move_left_move_right]

def sourceRightEndLeftFields
    (L : DovetailLayout) : List (Option Bool) :=
  List.append
    ((CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
      L.rejectHit []).reverse.map some)
    (List.append
      ((CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
        L.acceptHit []).reverse.map some)
      (List.append
        ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
          L.rejectConfig []).reverse.map some)
        (List.append
          ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
            L.acceptConfig []).reverse.map some)
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              L.stage).reverse.map some)
            (List.append
              ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
                some)
              [none])))))

theorem sourceRightEndTape_sourceBits_eq_fields
    (L : DovetailLayout) :
    sourceRightEndTape (sourceBits L) =
      Tape.move Direction.left
        (DovetailInitialLayoutInitializer.tapeAtCells
          (sourceRightEndLeftFields L) [none]) := by
  rw [sourceRightEndTape, sourceBits,
    SelectedProjectionTailProjector.sourceFieldBits,
    sourceRightEndLeftFields]
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
  simp [CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
    List.map_append, List.reverse_append, List.append_assoc]

def skipOneBoolFieldLeftDescription : MachineDescription where
  stateCount := 5
  start := 0
  halt := 4
  transitions :=
    [ transition 0 (some false) (some false) Direction.left 1
    , transition 0 (some true) (some true) Direction.left 1
    , transition 1 (some false) (some false) Direction.left 2
    , transition 1 (some true) (some true) Direction.left 2
    , transition 2 (some false) (some false) Direction.left 3
    , transition 2 (some true) (some true) Direction.left 3
    , transition 3 (some false) (some false) Direction.left 4
    , transition 3 (some true) (some true) Direction.left 4 ]

theorem skipOneBoolFieldLeftDescription_wellFormed :
    skipOneBoolFieldLeftDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := skipOneBoolFieldLeftDescription.transitions)
      (stateCount := skipOneBoolFieldLeftDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := skipOneBoolFieldLeftDescription.transitions)
      (by decide)

theorem skipOneBoolFieldLeftDescription_haltTransitionFree :
    skipOneBoolFieldLeftDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := skipOneBoolFieldLeftDescription.transitions)
    (state := skipOneBoolFieldLeftDescription.halt)
    (by decide)

theorem skipOneBoolFieldLeftDescription_subroutineReady :
    skipOneBoolFieldLeftDescription.SubroutineReady :=
  ⟨skipOneBoolFieldLeftDescription_wellFormed,
    skipOneBoolFieldLeftDescription_haltTransitionFree⟩

theorem skipOneBoolFieldLeftDescription_run
    (b0 b1 b2 b3 b4 : Bool)
    (left right : List (Option Bool)) :
    skipOneBoolFieldLeftDescription.runConfig 4
        { state := skipOneBoolFieldLeftDescription.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              (some b1 :: some b2 :: some b3 :: some b4 :: left)
              (some b0 :: right) } =
      { state := skipOneBoolFieldLeftDescription.halt
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells
            left
            (some b4 :: some b3 :: some b2 :: some b1 ::
              some b0 :: right) } := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    simp [skipOneBoolFieldLeftDescription,
      DovetailInitialLayoutInitializer.tapeAtCells,
      runConfig, stepConfig, lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft]

def selectedHitRightEndTape
    (useAccept : Bool) (L : DovetailLayout) : Tape Bool :=
  if useAccept then
    Tape.move Direction.left
      (DovetailInitialLayoutInitializer.tapeAtCells
        (List.append
          ((CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
            L.acceptHit []).reverse.map some)
          (List.append
            ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
              L.rejectConfig []).reverse.map some)
            (List.append
              ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                L.acceptConfig []).reverse.map some)
              (List.append
                ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                  L.stage).reverse.map some)
                (List.append
                  ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
                    some)
                  [none])))))
        (List.append
          ((CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
            L.rejectHit []).map some)
          [none]))
  else
    sourceRightEndTape (sourceBits L)

def selectedHitPositionDescription
    (useAccept : Bool) : MachineDescription :=
  if useAccept then
    skipOneBoolFieldLeftDescription
  else
    ExactIdentityDescription

theorem selectedHitPositionDescription_subroutineReady
    (useAccept : Bool) :
    (selectedHitPositionDescription useAccept).SubroutineReady := by
  cases useAccept
  · simpa [selectedHitPositionDescription] using
      ⟨exactIdentityDescription_wellFormed,
        exactIdentityDescription_haltTransitionFree⟩
  · simpa [selectedHitPositionDescription] using
      skipOneBoolFieldLeftDescription_subroutineReady

theorem selectedHitPositionDescription_haltsFromTape
    (useAccept : Bool) (L : DovetailLayout) :
    (selectedHitPositionDescription useAccept).HaltsFromTape
      (sourceRightEndTape (sourceBits L))
      (selectedHitRightEndTape useAccept L) := by
  cases useAccept
  · refine ⟨0, ?_⟩
    constructor <;>
      simp [selectedHitPositionDescription, selectedHitRightEndTape,
        ExactIdentityDescription, runConfig]
  · refine ⟨4, ?_⟩
    constructor <;>
      by_cases hreject : L.rejectHit <;>
      by_cases haccept : L.acceptHit <;>
        simp [selectedHitPositionDescription, selectedHitRightEndTape,
          sourceRightEndTape_sourceBits_eq_fields,
          sourceRightEndLeftFields,
          skipOneBoolFieldLeftDescription,
          hreject, haccept,
          CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
          CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
          CanonicalLayouts.DovetailLayoutScanner.cellCodeBits,
          encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
          DovetailInitialLayoutInitializer.tapeAtCells,
          runConfig, stepConfig, lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft]

def acceptHitFromRewindDescription : MachineDescription where
  stateCount := 6
  start := 0
  halt := 5
  transitions :=
    [ transition 0 (some false) (some false) Direction.right 0
    , transition 0 (some true) (some true) Direction.right 0
    , transition 0 none none Direction.left 1
    , transition 1 (some false) (some false) Direction.left 2
    , transition 1 (some true) (some true) Direction.left 2
    , transition 2 (some false) (some false) Direction.left 3
    , transition 2 (some true) (some true) Direction.left 3
    , transition 3 (some false) (some false) Direction.left 4
    , transition 3 (some true) (some true) Direction.left 4
    , transition 4 (some false) (some false) Direction.left 5
    , transition 4 (some true) (some true) Direction.left 5 ]

theorem acceptHitFromRewindDescription_wellFormed :
    acceptHitFromRewindDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := acceptHitFromRewindDescription.transitions)
      (stateCount := acceptHitFromRewindDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := acceptHitFromRewindDescription.transitions)
      (by decide)

theorem acceptHitFromRewindDescription_haltTransitionFree :
    acceptHitFromRewindDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := acceptHitFromRewindDescription.transitions)
    (state := acceptHitFromRewindDescription.halt)
    (by decide)

theorem acceptHitFromRewindDescription_subroutineReady :
    acceptHitFromRewindDescription.SubroutineReady :=
  ⟨acceptHitFromRewindDescription_wellFormed,
    acceptHitFromRewindDescription_haltTransitionFree⟩

theorem acceptHitFromRewindDescription_step_scan_bit
    (left right : List (Option Bool)) (bit : Bool) :
    acceptHitFromRewindDescription.runConfig 1
        { state := acceptHitFromRewindDescription.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              left (some bit :: right) } =
      { state := acceptHitFromRewindDescription.start
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells
            (some bit :: left) right } := by
  cases bit <;> cases right <;>
    simp [acceptHitFromRewindDescription,
      DovetailInitialLayoutInitializer.tapeAtCells,
      runConfig, stepConfig, lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

theorem acceptHitFromRewindDescription_step_scan_finish
    (left : List (Option Bool)) :
    acceptHitFromRewindDescription.runConfig 1
        { state := acceptHitFromRewindDescription.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              left [none] } =
      { state := 1
        tape :=
          Tape.move Direction.left
            (DovetailInitialLayoutInitializer.tapeAtCells left [none]) } := by
  cases left <;>
    simp [acceptHitFromRewindDescription,
      DovetailInitialLayoutInitializer.tapeAtCells,
      runConfig, stepConfig, lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft]

theorem acceptHitFromRewindDescription_run_scan
    (bits : Word Bool) (left : List (Option Bool)) :
    acceptHitFromRewindDescription.runConfig bits.length
        { state := acceptHitFromRewindDescription.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              left (List.append (bits.map some) [none]) } =
      { state := acceptHitFromRewindDescription.start
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells
            (List.append (bits.reverse.map some) left) [none] } := by
  induction bits generalizing left with
  | nil =>
      simp [runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        omega]
      rw [runConfig_add]
      change
        acceptHitFromRewindDescription.runConfig rest.length
            (acceptHitFromRewindDescription.runConfig 1
              { state := acceptHitFromRewindDescription.start
                tape :=
                  DovetailInitialLayoutInitializer.tapeAtCells
                    left
                    (some bit :: List.append (rest.map some) [none]) }) =
          { state := acceptHitFromRewindDescription.start
            tape :=
              DovetailInitialLayoutInitializer.tapeAtCells
                (List.append ((bit :: rest).reverse.map some) left)
                [none] }
      rw [acceptHitFromRewindDescription_step_scan_bit left
        (List.append (rest.map some) [none]) bit]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: left)

theorem acceptHitFromRewindDescription_run_to_rejectHit
    (bits : Word Bool) :
    acceptHitFromRewindDescription.runConfig (bits.length + 1)
        { state := acceptHitFromRewindDescription.start
          tape := rewindTargetTape bits } =
      { state := 1
        tape := sourceRightEndTape bits } := by
  rw [rewindTargetTape]
  rw [runConfig_add]
  rw [acceptHitFromRewindDescription_run_scan bits [none]]
  simpa [sourceRightEndTape, rewindTargetTape, List.append_assoc] using
    acceptHitFromRewindDescription_step_scan_finish
      (List.append (bits.reverse.map some) [none])

theorem acceptHitFromRewindDescription_run_skip_rejectHit
    (b0 b1 b2 b3 b4 : Bool)
    (left right : List (Option Bool)) :
    acceptHitFromRewindDescription.runConfig 4
        { state := 1
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              (some b1 :: some b2 :: some b3 :: some b4 :: left)
              (some b0 :: right) } =
      { state := acceptHitFromRewindDescription.halt
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells
            left
            (some b4 :: some b3 :: some b2 :: some b1 ::
              some b0 :: right) } := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    simp [acceptHitFromRewindDescription,
      DovetailInitialLayoutInitializer.tapeAtCells,
      runConfig, stepConfig, lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft]

theorem acceptHitFromRewindDescription_run_to_selectedHit
    (L : DovetailLayout) :
    acceptHitFromRewindDescription.runConfig
        ((sourceBits L).length + 5)
        { state := acceptHitFromRewindDescription.start
          tape := rewindTargetTape (sourceBits L) } =
      { state := acceptHitFromRewindDescription.halt
        tape := selectedHitRightEndTape true L } := by
  rw [show (sourceBits L).length + 5 =
      ((sourceBits L).length + 1) + 4 by omega]
  rw [runConfig_add]
  rw [acceptHitFromRewindDescription_run_to_rejectHit]
  by_cases hreject : L.rejectHit <;>
  by_cases haccept : L.acceptHit <;>
    simp [selectedHitRightEndTape,
      sourceRightEndTape_sourceBits_eq_fields,
      sourceRightEndLeftFields,
      acceptHitFromRewindDescription,
      hreject, haccept,
      CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellCodeBits,
      encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
      DovetailInitialLayoutInitializer.tapeAtCells,
      runConfig, stepConfig, lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft]

theorem acceptHitFromRewindDescription_haltsFrom_rewindTarget_sourceBits
    (L : DovetailLayout) :
    acceptHitFromRewindDescription.HaltsFromTape
      (rewindTargetTape (sourceBits L))
      (selectedHitRightEndTape true L) := by
  refine ⟨(sourceBits L).length + 5, ?_⟩
  constructor <;>
    rw [acceptHitFromRewindDescription_run_to_selectedHit]

def selectedHitFromRewindDescription
    (useAccept : Bool) : MachineDescription :=
  if useAccept then
    acceptHitFromRewindDescription
  else
    sourceRightEndDescription

theorem selectedHitFromRewindDescription_subroutineReady
    (useAccept : Bool) :
    (selectedHitFromRewindDescription useAccept).SubroutineReady := by
  cases useAccept
  · simpa [selectedHitFromRewindDescription] using
      sourceRightEndDescription_subroutineReady
  · simpa [selectedHitFromRewindDescription] using
      acceptHitFromRewindDescription_subroutineReady

theorem selectedHitFromRewindDescription_haltsFrom_rewindTarget_sourceBits
    (useAccept : Bool) (L : DovetailLayout) :
    (selectedHitFromRewindDescription useAccept).HaltsFromTape
      (rewindTargetTape (sourceBits L))
      (selectedHitRightEndTape useAccept L) := by
  cases useAccept
  · simpa [selectedHitFromRewindDescription, selectedHitRightEndTape] using
      sourceRightEndDescription_haltsFrom_rewindTarget_sourceBits L
  · simpa [selectedHitFromRewindDescription] using
      acceptHitFromRewindDescription_haltsFrom_rewindTarget_sourceBits L

def eraseRightBoolFieldAfterCurrentDescription : MachineDescription where
  stateCount := 6
  start := 0
  halt := 5
  transitions :=
    [ transition 0 (some false) (some false) Direction.right 1
    , transition 0 (some true) (some true) Direction.right 1
    , transition 1 (some false) none Direction.right 2
    , transition 1 (some true) none Direction.right 2
    , transition 2 (some false) none Direction.right 3
    , transition 2 (some true) none Direction.right 3
    , transition 3 (some false) none Direction.right 4
    , transition 3 (some true) none Direction.right 4
    , transition 4 (some false) none Direction.right 5
    , transition 4 (some true) none Direction.right 5 ]

theorem eraseRightBoolFieldAfterCurrentDescription_wellFormed :
    eraseRightBoolFieldAfterCurrentDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := eraseRightBoolFieldAfterCurrentDescription.transitions)
      (stateCount :=
        eraseRightBoolFieldAfterCurrentDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := eraseRightBoolFieldAfterCurrentDescription.transitions)
      (by decide)

theorem eraseRightBoolFieldAfterCurrentDescription_haltTransitionFree :
    eraseRightBoolFieldAfterCurrentDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := eraseRightBoolFieldAfterCurrentDescription.transitions)
    (state := eraseRightBoolFieldAfterCurrentDescription.halt)
    (by decide)

theorem eraseRightBoolFieldAfterCurrentDescription_subroutineReady :
    eraseRightBoolFieldAfterCurrentDescription.SubroutineReady :=
  ⟨eraseRightBoolFieldAfterCurrentDescription_wellFormed,
    eraseRightBoolFieldAfterCurrentDescription_haltTransitionFree⟩

theorem eraseRightBoolFieldAfterCurrentDescription_run
    (current b0 b1 b2 b3 : Bool)
    (left right : List (Option Bool)) :
    eraseRightBoolFieldAfterCurrentDescription.runConfig 5
        { state := eraseRightBoolFieldAfterCurrentDescription.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              left
              (some current :: some b0 :: some b1 ::
                some b2 :: some b3 :: right) } =
      { state := eraseRightBoolFieldAfterCurrentDescription.halt
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells
            (List.append (List.replicate 4 (none : Option Bool))
              (some current :: left))
            right } := by
  cases current <;> cases b0 <;> cases b1 <;> cases b2 <;>
    cases b3 <;> cases right <;>
    simp [eraseRightBoolFieldAfterCurrentDescription,
      DovetailInitialLayoutInitializer.tapeAtCells,
      runConfig, stepConfig, lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

def eraseLeftBoolFieldBeforeCurrentDescription : MachineDescription where
  stateCount := 9
  start := 0
  halt := 8
  transitions :=
    [ transition 0 (some false) (some false) Direction.left 1
    , transition 0 (some true) (some true) Direction.left 1
    , transition 1 (some false) (some false) Direction.left 2
    , transition 1 (some true) (some true) Direction.left 2
    , transition 2 (some false) (some false) Direction.left 3
    , transition 2 (some true) (some true) Direction.left 3
    , transition 3 (some false) (some false) Direction.left 4
    , transition 3 (some true) (some true) Direction.left 4
    , transition 4 (some false) none Direction.left 5
    , transition 4 (some true) none Direction.left 5
    , transition 5 (some false) none Direction.left 6
    , transition 5 (some true) none Direction.left 6
    , transition 6 (some false) none Direction.left 7
    , transition 6 (some true) none Direction.left 7
    , transition 7 (some false) none Direction.left 8
    , transition 7 (some true) none Direction.left 8 ]

theorem eraseLeftBoolFieldBeforeCurrentDescription_wellFormed :
    eraseLeftBoolFieldBeforeCurrentDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := eraseLeftBoolFieldBeforeCurrentDescription.transitions)
      (stateCount :=
        eraseLeftBoolFieldBeforeCurrentDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := eraseLeftBoolFieldBeforeCurrentDescription.transitions)
      (by decide)

theorem eraseLeftBoolFieldBeforeCurrentDescription_haltTransitionFree :
    eraseLeftBoolFieldBeforeCurrentDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := eraseLeftBoolFieldBeforeCurrentDescription.transitions)
    (state := eraseLeftBoolFieldBeforeCurrentDescription.halt)
    (by decide)

theorem eraseLeftBoolFieldBeforeCurrentDescription_subroutineReady :
    eraseLeftBoolFieldBeforeCurrentDescription.SubroutineReady :=
  ⟨eraseLeftBoolFieldBeforeCurrentDescription_wellFormed,
    eraseLeftBoolFieldBeforeCurrentDescription_haltTransitionFree⟩

def skipCurrentAndFourBlankPaddingLeftDescription :
    MachineDescription where
  stateCount := 6
  start := 0
  halt := 5
  transitions :=
    [ transition 0 none none Direction.left 1
    , transition 1 none none Direction.left 2
    , transition 2 none none Direction.left 3
    , transition 3 none none Direction.left 4
    , transition 4 none none Direction.left 5 ]

theorem skipCurrentAndFourBlankPaddingLeftDescription_wellFormed :
    skipCurrentAndFourBlankPaddingLeftDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := skipCurrentAndFourBlankPaddingLeftDescription.transitions)
      (stateCount :=
        skipCurrentAndFourBlankPaddingLeftDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := skipCurrentAndFourBlankPaddingLeftDescription.transitions)
      (by decide)

theorem skipCurrentAndFourBlankPaddingLeftDescription_haltTransitionFree :
    skipCurrentAndFourBlankPaddingLeftDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := skipCurrentAndFourBlankPaddingLeftDescription.transitions)
    (state := skipCurrentAndFourBlankPaddingLeftDescription.halt)
    (by decide)

theorem skipCurrentAndFourBlankPaddingLeftDescription_subroutineReady :
    skipCurrentAndFourBlankPaddingLeftDescription.SubroutineReady :=
  ⟨skipCurrentAndFourBlankPaddingLeftDescription_wellFormed,
    skipCurrentAndFourBlankPaddingLeftDescription_haltTransitionFree⟩

theorem skipCurrentAndFourBlankPaddingLeftDescription_run
    (current : Bool) (left right : List (Option Bool)) :
    skipCurrentAndFourBlankPaddingLeftDescription.runConfig 5
        { state := skipCurrentAndFourBlankPaddingLeftDescription.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              (none :: none :: none :: none ::
                some current :: left)
              (none :: right) } =
      { state := skipCurrentAndFourBlankPaddingLeftDescription.halt
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells
            left
            (some current :: none :: none :: none :: none ::
              none :: right) } := by
  cases current <;>
    simp [skipCurrentAndFourBlankPaddingLeftDescription,
      DovetailInitialLayoutInitializer.tapeAtCells,
      runConfig, stepConfig, lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft]

theorem skipCurrentAndFourBlankPaddingLeftDescription_haltsFromTape
    (current : Bool) (left right : List (Option Bool)) :
    skipCurrentAndFourBlankPaddingLeftDescription.HaltsFromTape
      (DovetailInitialLayoutInitializer.tapeAtCells
        (none :: none :: none :: none :: some current :: left)
        (none :: right))
      (DovetailInitialLayoutInitializer.tapeAtCells
        left
        (some current :: none :: none :: none :: none ::
          none :: right)) := by
  refine ⟨5, ?_⟩
  constructor <;>
    rw [skipCurrentAndFourBlankPaddingLeftDescription_run]

def skipCurrentAndFourBlankPaddingRightDescription :
    MachineDescription where
  stateCount := 6
  start := 0
  halt := 5
  transitions :=
    [ transition 0 (some false) (some false) Direction.right 1
    , transition 0 (some true) (some true) Direction.right 1
    , transition 1 none none Direction.right 2
    , transition 2 none none Direction.right 3
    , transition 3 none none Direction.right 4
    , transition 4 none none Direction.right 5 ]

theorem skipCurrentAndFourBlankPaddingRightDescription_wellFormed :
    skipCurrentAndFourBlankPaddingRightDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := skipCurrentAndFourBlankPaddingRightDescription.transitions)
      (stateCount :=
        skipCurrentAndFourBlankPaddingRightDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := skipCurrentAndFourBlankPaddingRightDescription.transitions)
      (by decide)

theorem skipCurrentAndFourBlankPaddingRightDescription_haltTransitionFree :
    skipCurrentAndFourBlankPaddingRightDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := skipCurrentAndFourBlankPaddingRightDescription.transitions)
    (state := skipCurrentAndFourBlankPaddingRightDescription.halt)
    (by decide)

theorem skipCurrentAndFourBlankPaddingRightDescription_subroutineReady :
    skipCurrentAndFourBlankPaddingRightDescription.SubroutineReady :=
  ⟨skipCurrentAndFourBlankPaddingRightDescription_wellFormed,
    skipCurrentAndFourBlankPaddingRightDescription_haltTransitionFree⟩

theorem skipCurrentAndFourBlankPaddingRightDescription_run
    (current target : Bool) (left right : List (Option Bool)) :
    skipCurrentAndFourBlankPaddingRightDescription.runConfig 5
        { state := skipCurrentAndFourBlankPaddingRightDescription.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              left
              (some current :: none :: none :: none :: none ::
                some target :: right) } =
      { state := skipCurrentAndFourBlankPaddingRightDescription.halt
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells
            (none :: none :: none :: none :: some current :: left)
            (some target :: right) } := by
  cases current <;> cases target <;>
    simp [skipCurrentAndFourBlankPaddingRightDescription,
      DovetailInitialLayoutInitializer.tapeAtCells,
      runConfig, stepConfig, lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

theorem skipCurrentAndFourBlankPaddingRightDescription_haltsFromTape
    (current target : Bool) (left right : List (Option Bool)) :
    skipCurrentAndFourBlankPaddingRightDescription.HaltsFromTape
      (DovetailInitialLayoutInitializer.tapeAtCells
        left
        (some current :: none :: none :: none :: none ::
          some target :: right))
      (DovetailInitialLayoutInitializer.tapeAtCells
        (none :: none :: none :: none :: some current :: left)
        (some target :: right)) := by
  refine ⟨5, ?_⟩
  constructor <;>
    rw [skipCurrentAndFourBlankPaddingRightDescription_run]

def selectedHitOtherFlagErasedTape
    (useAccept : Bool) (L : DovetailLayout) : Tape Bool :=
  if useAccept then
    DovetailInitialLayoutInitializer.tapeAtCells
      (List.append (List.replicate 4 (none : Option Bool))
        (List.append
          ((CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
            L.acceptHit []).reverse.map some)
          (List.append
            ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
              L.rejectConfig []).reverse.map some)
            (List.append
              ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                L.acceptConfig []).reverse.map some)
              (List.append
                ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                  L.stage).reverse.map some)
                (List.append
                  ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
                    some)
                  [none]))))))
      [none]
  else
    Tape.move Direction.left
      (DovetailInitialLayoutInitializer.tapeAtCells
        (List.append
          ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
            L.rejectConfig []).reverse.map some)
          (List.append
            ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
              L.acceptConfig []).reverse.map some)
            (List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                L.stage).reverse.map some)
              (List.append
                ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
                  some)
                [none]))))
        (List.append (List.replicate 4 (none : Option Bool))
          (List.append
            ((CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
              L.rejectHit []).map some)
            [none])))

def selectedHitOtherFlagErasedAcceptLeftRev
    (L : DovetailLayout) : List (Option Bool) :=
  List.append (List.replicate 4 (none : Option Bool))
    (List.append
      ((CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
        L.acceptHit []).reverse.map some)
      (List.append
        ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
          L.rejectConfig []).reverse.map some)
        (List.append
          ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
            L.acceptConfig []).reverse.map some)
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              L.stage).reverse.map some)
            (List.append
              ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
                some)
              [none])))))

def selectedHitOtherFlagErasedAcceptHitHead
    (hit : Bool) : Bool :=
  if hit then false else true

def selectedHitOtherFlagErasedAcceptHitRestLeftRev
    (L : DovetailLayout) : List (Option Bool) :=
  List.append
    (if L.acceptHit then
      [some true, some true, some false]
    else
      [some false, some true, some false])
    (List.append
      ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
        L.rejectConfig []).reverse.map some)
      (List.append
        ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
          L.acceptConfig []).reverse.map some)
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            L.stage).reverse.map some)
          (List.append
            ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
              some)
            [none]))))

def selectedHitOtherFlagErasedAcceptAfterPaddingTape
    (L : DovetailLayout) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells
    (selectedHitOtherFlagErasedAcceptHitRestLeftRev L)
    (some (selectedHitOtherFlagErasedAcceptHitHead L.acceptHit) ::
      none :: none :: none :: none :: none :: [none])

theorem selectedHitOtherFlagErasedAcceptLeftRev_eq_hitHead
    (L : DovetailLayout) :
    selectedHitOtherFlagErasedAcceptLeftRev L =
      none :: none :: none :: none ::
        some (selectedHitOtherFlagErasedAcceptHitHead L.acceptHit) ::
          selectedHitOtherFlagErasedAcceptHitRestLeftRev L := by
  by_cases haccept : L.acceptHit <;>
    simp [selectedHitOtherFlagErasedAcceptLeftRev,
      selectedHitOtherFlagErasedAcceptHitHead,
      selectedHitOtherFlagErasedAcceptHitRestLeftRev,
      haccept,
      CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellCodeBits,
      encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput]

def selectedHitOtherFlagErasedRejectBaseLeftRev
    (L : DovetailLayout) : List (Option Bool) :=
  List.append
    ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
      L.rejectConfig []).reverse.map some)
    (List.append
      ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
        L.acceptConfig []).reverse.map some)
      (List.append
        ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          L.stage).reverse.map some)
        (List.append
          ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
            some)
          [none])))

def selectedHitOtherFlagErasedRejectBaseCells
    (L : DovetailLayout) : List (Option Bool) :=
  none :: none :: none :: none ::
    List.append
      ((CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
        L.rejectHit []).map some)
      [none]

theorem selectedHitOtherFlagErasedRejectBaseLeftRev_cons
    (L : DovetailLayout) :
    exists current : Bool,
    exists rest : List (Option Bool),
      selectedHitOtherFlagErasedRejectBaseLeftRev L =
        some current :: rest := by
  rcases
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_cons_false
        L.rejectConfig [] with
    ⟨tail, htail⟩
  cases hrev : tail.reverse with
  | nil =>
      refine
        ⟨false,
          List.append
            ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
              L.acceptConfig []).reverse.map some)
            (List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                L.stage).reverse.map some)
              (List.append
                ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
                  some)
                [none])), ?_⟩
      simp [selectedHitOtherFlagErasedRejectBaseLeftRev, htail, hrev]
  | cons bit rest =>
      refine
        ⟨bit,
          List.append (rest.map some)
            (List.append [some false]
              (List.append
                ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                  L.acceptConfig []).reverse.map some)
                (List.append
                  ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                    L.stage).reverse.map some)
                  (List.append
                    ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
                      some)
                    [none])))), ?_⟩
      simp [selectedHitOtherFlagErasedRejectBaseLeftRev, htail,
        hrev, List.map_append, List.append_assoc]

theorem selectedHitOtherFlagErasedRejectBaseCells_eq_hitHead
    (L : DovetailLayout) :
    exists hitTail : Word Bool,
      selectedHitOtherFlagErasedRejectBaseCells L =
        none :: none :: none :: none ::
          some false :: List.append (hitTail.map some) [none] := by
  by_cases hreject : L.rejectHit
  · refine ⟨[true, true, false], ?_⟩
    simp [selectedHitOtherFlagErasedRejectBaseCells, hreject,
      CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellCodeBits,
      encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput]
  · refine ⟨[true, false, true], ?_⟩
    simp [selectedHitOtherFlagErasedRejectBaseCells, hreject,
      CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellCodeBits,
      encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput]

theorem selectedHitOtherFlagErasedTape_true_normalizedOutput
    (L : DovetailLayout) :
    Tape.normalizedOutput (selectedHitOtherFlagErasedTape true L) =
      List.append (SelectedProjectionTailProjector.outputPrefixBits L)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            L.stage)
          (List.append
            (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
              L.acceptConfig [])
            (List.append
              (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                L.rejectConfig [])
              (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
                L.acceptHit [])))) := by
  simp [selectedHitOtherFlagErasedTape,
    DovetailInitialLayoutInitializer.tapeAtCells,
    Tape.normalizedOutput, Tape.cells, List.filterMap_append,
    Function.comp_def, List.reverse_append,
    CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
    List.append_assoc]

theorem tapeAtCells_move_left_append_none_normalizedOutput
    (leftRev right : List (Option Bool)) :
    Tape.normalizedOutput
        (Tape.move Direction.left
          (DovetailInitialLayoutInitializer.tapeAtCells
            (List.append leftRev [none]) right)) =
      Tape.normalizedOutput
        (DovetailInitialLayoutInitializer.tapeAtCells
          (List.append leftRev [none]) right) := by
  cases leftRev <;>
    cases right <;>
      simp [DovetailInitialLayoutInitializer.tapeAtCells,
        Tape.normalizedOutput, Tape.cells, Tape.move, Tape.moveLeft]

theorem tapeAtCells_move_left_right_left_append_none_cons_cells
    (leftRev : List (Option Bool)) (head next : Option Bool)
    (right : List (Option Bool)) :
    Tape.cells
        (Tape.move Direction.left
          (Tape.move Direction.right
            (Tape.move Direction.left
              (DovetailInitialLayoutInitializer.tapeAtCells
                (List.append leftRev [none]) (head :: next :: right))))) =
      List.append [none]
        (List.append leftRev.reverse (head :: next :: right)) := by
  cases leftRev <;>
    simp [DovetailInitialLayoutInitializer.tapeAtCells,
      Tape.cells, Tape.move, Tape.moveLeft, Tape.moveRight,
      List.reverse_append, List.append_assoc]

theorem tapeAtCells_move_left_right_left_cons_cons
    (leftRev : List (Option Bool)) (head next : Option Bool)
    (right : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (Tape.move Direction.left
            (DovetailInitialLayoutInitializer.tapeAtCells
              leftRev (head :: next :: right)))) =
      Tape.move Direction.left
        (DovetailInitialLayoutInitializer.tapeAtCells
          leftRev (head :: next :: right)) := by
  cases leftRev <;>
    simp [DovetailInitialLayoutInitializer.tapeAtCells,
      Tape.move, Tape.moveLeft, Tape.moveRight]

theorem selectedHitOtherFlagErasedTape_true_eq_tapeAtCells
    (L : DovetailLayout) :
    selectedHitOtherFlagErasedTape true L =
      DovetailInitialLayoutInitializer.tapeAtCells
        (selectedHitOtherFlagErasedAcceptLeftRev L)
        [none] := by
  simp [selectedHitOtherFlagErasedTape,
    selectedHitOtherFlagErasedAcceptLeftRev]

theorem selectedHitOtherFlagErasedTape_false_eq_moveLeft_tapeAtCells
    (L : DovetailLayout) :
    selectedHitOtherFlagErasedTape false L =
      Tape.move Direction.left
        (DovetailInitialLayoutInitializer.tapeAtCells
          (selectedHitOtherFlagErasedRejectBaseLeftRev L)
          (selectedHitOtherFlagErasedRejectBaseCells L)) := by
  simp [selectedHitOtherFlagErasedTape,
    selectedHitOtherFlagErasedRejectBaseLeftRev,
    selectedHitOtherFlagErasedRejectBaseCells]

theorem selectedHitOtherFlagErasedTape_false_normalizedOutput
    (L : DovetailLayout) :
    Tape.normalizedOutput (selectedHitOtherFlagErasedTape false L) =
      List.append (SelectedProjectionTailProjector.outputPrefixBits L)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            L.stage)
          (List.append
            (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
              L.acceptConfig [])
            (List.append
              (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                L.rejectConfig [])
              (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
                L.rejectHit [])))) := by
  rw [show
      selectedHitOtherFlagErasedTape false L =
        Tape.move Direction.left
          (DovetailInitialLayoutInitializer.tapeAtCells
            (List.append
              (List.append
                ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                  L.rejectConfig []).reverse.map some)
                (List.append
                  ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                    L.acceptConfig []).reverse.map some)
                  (List.append
                    ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                      L.stage).reverse.map some)
                    ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
                      some))))
              [none])
            (List.append (List.replicate 4 (none : Option Bool))
              (List.append
                ((CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
                  L.rejectHit []).map some)
                [none]))) by
    simp [selectedHitOtherFlagErasedTape, List.append_assoc]]
  rw [tapeAtCells_move_left_append_none_normalizedOutput]
  simp [DovetailInitialLayoutInitializer.tapeAtCells,
    Tape.normalizedOutput, Tape.cells, List.filterMap_append,
    Function.comp_def, List.reverse_append,
    CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
    List.append_assoc]

theorem selectedProjectionPaddedTarget_true_normalizedOutput
    (L : DovetailLayout) :
    Tape.normalizedOutput
        (SelectedProjectionEquivEmitterPaddedOutputTape true L) =
      List.append (SelectedProjectionTailProjector.outputPrefixBits L)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            L.stage)
          (List.append
            (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
              L.acceptConfig [])
            (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
              L.acceptHit []))) := by
  rw [SelectedProjectionEquivEmitterPaddedOutputTape_normalizedOutput_eq_tail]
  rw [SelectedProjectionTailProjector.outputAllBits,
    SelectedProjectionTailProjector.outputBits_true_eq_fields]
  rw [←
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil]

theorem selectedProjectionPaddedTarget_false_normalizedOutput
    (L : DovetailLayout) :
    Tape.normalizedOutput
        (SelectedProjectionEquivEmitterPaddedOutputTape false L) =
      List.append (SelectedProjectionTailProjector.outputPrefixBits L)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            L.stage)
          (List.append
            (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
              L.rejectConfig [])
            (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
              L.rejectHit []))) := by
  rw [SelectedProjectionEquivEmitterPaddedOutputTape_normalizedOutput_eq_tail]
  rw [SelectedProjectionTailProjector.outputAllBits,
    SelectedProjectionTailProjector.outputBits_false_eq_fields]
  rw [←
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil]

def selectedProjectionPaddedTailCleanupTargetBits
    (useAccept : Bool) (L : DovetailLayout) : Word Bool :=
  if useAccept then
    List.append (SelectedProjectionTailProjector.outputPrefixBits L)
      (List.append
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          L.stage)
        (List.append
          (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
            L.acceptConfig [])
          (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
            L.acceptHit [])))
  else
    List.append (SelectedProjectionTailProjector.outputPrefixBits L)
      (List.append
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          L.stage)
        (List.append
          (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
            L.rejectConfig [])
          (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
            L.rejectHit [])))

def selectedProjectionPaddedTailCleanupPrefixBits
    (L : DovetailLayout) : Word Bool :=
  List.append (SelectedProjectionTailProjector.outputPrefixBits L)
    (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
      L.stage)

def selectedProjectionPaddedTailCleanupSelectedConfigBits
    (useAccept : Bool) (L : DovetailLayout) : Word Bool :=
  if useAccept then
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
      L.acceptConfig []
  else
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
      L.rejectConfig []

def selectedProjectionPaddedTailCleanupUnselectedConfigBits
    (useAccept : Bool) (L : DovetailLayout) : Word Bool :=
  if useAccept then
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
      L.rejectConfig []
  else
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
      L.acceptConfig []

def selectedProjectionPaddedTailCleanupSelectedHitBits
    (useAccept : Bool) (L : DovetailLayout) : Word Bool :=
  if useAccept then
    CanonicalLayouts.DovetailLayoutScanner.boolFieldBits L.acceptHit []
  else
    CanonicalLayouts.DovetailLayoutScanner.boolFieldBits L.rejectHit []

def selectedProjectionPaddedTailCleanupPostPaddingSourceBits
    (useAccept : Bool) (L : DovetailLayout) : Word Bool :=
  if useAccept then
    List.append (selectedProjectionPaddedTailCleanupPrefixBits L)
      (List.append
        (selectedProjectionPaddedTailCleanupSelectedConfigBits true L)
        (List.append
          (selectedProjectionPaddedTailCleanupUnselectedConfigBits true L)
          (selectedProjectionPaddedTailCleanupSelectedHitBits true L)))
  else
    List.append (selectedProjectionPaddedTailCleanupPrefixBits L)
      (List.append
        (selectedProjectionPaddedTailCleanupUnselectedConfigBits false L)
        (List.append
          (selectedProjectionPaddedTailCleanupSelectedConfigBits false L)
          (selectedProjectionPaddedTailCleanupSelectedHitBits false L)))

theorem selectedProjectionPaddedTailCleanupPostPaddingSourceBits_true_eq_selected_unselected
    (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupPostPaddingSourceBits true L =
      List.append (selectedProjectionPaddedTailCleanupPrefixBits L)
        (List.append
          (selectedProjectionPaddedTailCleanupSelectedConfigBits true L)
          (List.append
            (selectedProjectionPaddedTailCleanupUnselectedConfigBits true L)
            (selectedProjectionPaddedTailCleanupSelectedHitBits true L))) := by
  rfl

theorem selectedProjectionPaddedTailCleanupPostPaddingSourceBits_false_eq_unselected_selected
    (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupPostPaddingSourceBits false L =
      List.append (selectedProjectionPaddedTailCleanupPrefixBits L)
        (List.append
          (selectedProjectionPaddedTailCleanupUnselectedConfigBits false L)
          (List.append
            (selectedProjectionPaddedTailCleanupSelectedConfigBits false L)
            (selectedProjectionPaddedTailCleanupSelectedHitBits false L))) := by
  rfl

theorem selectedProjectionPaddedTailCleanupTargetBits_eq_selectedFields
    (useAccept : Bool) (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupTargetBits useAccept L =
      List.append (selectedProjectionPaddedTailCleanupPrefixBits L)
        (List.append
          (selectedProjectionPaddedTailCleanupSelectedConfigBits useAccept L)
          (selectedProjectionPaddedTailCleanupSelectedHitBits useAccept L)) := by
  cases useAccept <;>
    simp [selectedProjectionPaddedTailCleanupTargetBits,
      selectedProjectionPaddedTailCleanupPrefixBits,
      selectedProjectionPaddedTailCleanupSelectedConfigBits,
      selectedProjectionPaddedTailCleanupSelectedHitBits,
      List.append_assoc]

theorem selectedProjectionPaddedTailCleanupPostPaddingSourceBits_true
    (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupPostPaddingSourceBits true L =
      List.append (selectedProjectionPaddedTailCleanupPrefixBits L)
        (List.append
          (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
            L.acceptConfig [])
          (List.append
            (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
              L.rejectConfig [])
            (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
              L.acceptHit []))) := by
  simp [selectedProjectionPaddedTailCleanupPostPaddingSourceBits,
    selectedProjectionPaddedTailCleanupPrefixBits,
    selectedProjectionPaddedTailCleanupSelectedConfigBits,
    selectedProjectionPaddedTailCleanupUnselectedConfigBits,
    selectedProjectionPaddedTailCleanupSelectedHitBits,
    List.append_assoc]

theorem selectedProjectionPaddedTailCleanupPostPaddingSourceBits_false
    (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupPostPaddingSourceBits false L =
      List.append (selectedProjectionPaddedTailCleanupPrefixBits L)
        (List.append
          (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
            L.acceptConfig [])
          (List.append
            (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
              L.rejectConfig [])
            (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
              L.rejectHit []))) := by
  simp [selectedProjectionPaddedTailCleanupPostPaddingSourceBits,
    selectedProjectionPaddedTailCleanupPrefixBits,
    selectedProjectionPaddedTailCleanupSelectedConfigBits,
    selectedProjectionPaddedTailCleanupUnselectedConfigBits,
    selectedProjectionPaddedTailCleanupSelectedHitBits,
    List.append_assoc]

theorem selectedProjectionPaddedTailCleanupTargetBits_eq_normalizedOutput
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.normalizedOutput
        (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L) =
      selectedProjectionPaddedTailCleanupTargetBits useAccept L := by
  cases useAccept
  · simpa [selectedProjectionPaddedTailCleanupTargetBits] using
      selectedProjectionPaddedTarget_false_normalizedOutput L
  · simpa [selectedProjectionPaddedTailCleanupTargetBits] using
      selectedProjectionPaddedTarget_true_normalizedOutput L

theorem selectedProjectionPaddedTailCleanupTargetTape_cells_eq_bits
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.cells (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L) =
      List.append
        ((selectedProjectionPaddedTailCleanupTargetBits useAccept L).map
          some)
        (List.replicate (ParsedLayoutBits L).length none) := by
  cases useAccept
  · simpa [selectedProjectionPaddedTailCleanupTargetBits,
      List.map_append, List.append_assoc] using
      SelectedProjectionEquivEmitterPaddedOutputTape_false_cells L
  · simpa [selectedProjectionPaddedTailCleanupTargetBits,
      List.map_append, List.append_assoc] using
      SelectedProjectionEquivEmitterPaddedOutputTape_true_cells L

theorem selectedProjectionPaddedTailCleanupTargetTape_true_cells_eq_fields
    (L : DovetailLayout) :
    Tape.cells (SelectedProjectionEquivEmitterPaddedOutputTape true L) =
      List.append
        ((List.append (SelectedProjectionTailProjector.outputPrefixBits L)
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              L.stage)
            (List.append
              (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                L.acceptConfig [])
              (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
                L.acceptHit [])))).map some)
        (List.replicate (ParsedLayoutBits L).length none) := by
  simpa [selectedProjectionPaddedTailCleanupTargetBits,
    List.map_append, List.append_assoc] using
    selectedProjectionPaddedTailCleanupTargetTape_cells_eq_bits true L

theorem selectedProjectionPaddedTailCleanupTargetTape_false_cells_eq_fields
    (L : DovetailLayout) :
    Tape.cells (SelectedProjectionEquivEmitterPaddedOutputTape false L) =
      List.append
        ((List.append (SelectedProjectionTailProjector.outputPrefixBits L)
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              L.stage)
            (List.append
              (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                L.rejectConfig [])
              (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
                L.rejectHit [])))).map some)
        (List.replicate (ParsedLayoutBits L).length none) := by
  simpa [selectedProjectionPaddedTailCleanupTargetBits,
    List.map_append, List.append_assoc] using
    selectedProjectionPaddedTailCleanupTargetTape_cells_eq_bits false L

def eraseOtherHitFlagDescription
    (useAccept : Bool) : MachineDescription :=
  if useAccept then
    eraseRightBoolFieldAfterCurrentDescription
  else
    eraseLeftBoolFieldBeforeCurrentDescription

theorem eraseOtherHitFlagDescription_subroutineReady
    (useAccept : Bool) :
    (eraseOtherHitFlagDescription useAccept).SubroutineReady := by
  cases useAccept
  · simpa [eraseOtherHitFlagDescription] using
      eraseLeftBoolFieldBeforeCurrentDescription_subroutineReady
  · simpa [eraseOtherHitFlagDescription] using
      eraseRightBoolFieldAfterCurrentDescription_subroutineReady

theorem eraseOtherHitFlagDescription_haltsFrom_selectedHitRightEndTape
    (useAccept : Bool) (L : DovetailLayout) :
    (eraseOtherHitFlagDescription useAccept).HaltsFromTape
      (selectedHitRightEndTape useAccept L)
      (selectedHitOtherFlagErasedTape useAccept L) := by
  cases useAccept
  · refine ⟨8, ?_⟩
    constructor <;>
      by_cases hreject : L.rejectHit <;>
      by_cases haccept : L.acceptHit <;>
        simp [eraseOtherHitFlagDescription,
          selectedHitRightEndTape, selectedHitOtherFlagErasedTape,
          sourceRightEndTape_sourceBits_eq_fields,
          sourceRightEndLeftFields,
          eraseLeftBoolFieldBeforeCurrentDescription,
          hreject, haccept,
          CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
          CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
          CanonicalLayouts.DovetailLayoutScanner.cellCodeBits,
          encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
          DovetailInitialLayoutInitializer.tapeAtCells,
          runConfig, stepConfig, lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft]
  · refine ⟨5, ?_⟩
    constructor <;>
      by_cases hreject : L.rejectHit <;>
      by_cases haccept : L.acceptHit <;>
        simp [eraseOtherHitFlagDescription,
          selectedHitRightEndTape, selectedHitOtherFlagErasedTape,
          eraseRightBoolFieldAfterCurrentDescription,
          hreject, haccept,
          CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
          CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
          CanonicalLayouts.DovetailLayoutScanner.cellCodeBits,
          encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
          DovetailInitialLayoutInitializer.tapeAtCells,
          runConfig, stepConfig, lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, Tape.moveRight]

theorem selectedHitRightEndTape_move_left_move_right
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (selectedHitRightEndTape useAccept L)) =
      selectedHitRightEndTape useAccept L := by
  cases useAccept
  · simpa [selectedHitRightEndTape] using
      sourceRightEndTape_move_left_move_right (sourceBits L)
  · by_cases hreject : L.rejectHit
    · by_cases haccept : L.acceptHit
      · simp [selectedHitRightEndTape, hreject, haccept,
          CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
          CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
          CanonicalLayouts.DovetailLayoutScanner.cellCodeBits,
          encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
          DovetailInitialLayoutInitializer.tapeAtCells,
          Tape.move, Tape.moveLeft, Tape.moveRight]
      · simp [selectedHitRightEndTape, hreject, haccept,
          CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
          CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
          CanonicalLayouts.DovetailLayoutScanner.cellCodeBits,
          encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
          DovetailInitialLayoutInitializer.tapeAtCells,
          Tape.move, Tape.moveLeft, Tape.moveRight]
    · by_cases haccept : L.acceptHit
      · simp [selectedHitRightEndTape, hreject, haccept,
          CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
          CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
          CanonicalLayouts.DovetailLayoutScanner.cellCodeBits,
          encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
          DovetailInitialLayoutInitializer.tapeAtCells,
          Tape.move, Tape.moveLeft, Tape.moveRight]
      · simp [selectedHitRightEndTape, hreject, haccept,
          CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
          CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
          CanonicalLayouts.DovetailLayoutScanner.cellCodeBits,
          encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
          DovetailInitialLayoutInitializer.tapeAtCells,
          Tape.move, Tape.moveLeft, Tape.moveRight]

def selectedHitFromScannerDescription
    (useAccept : Bool) : MachineDescription :=
  SeqViaCanonical sourceRewindDescription
    (selectedHitFromRewindDescription useAccept)

theorem selectedHitFromScannerDescription_subroutineReady
    (useAccept : Bool) :
    (selectedHitFromScannerDescription useAccept).SubroutineReady :=
  SeqViaCanonical_subroutineReady
    sourceRewindDescription_subroutineReady
    (selectedHitFromRewindDescription_subroutineReady useAccept)

theorem selectedHitFromScannerDescription_haltsFrom_sourceScannerRightHandoffTape
    (useAccept : Bool) (L : DovetailLayout) :
    (selectedHitFromScannerDescription useAccept).HaltsFromTape
      (SelectedProjectionTailProjector.sourceScannerRightHandoffTape L
        ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
          some))
      (selectedHitRightEndTape useAccept L) :=
  SeqViaCanonical_haltsFromTape_of_haltsFromTape
    sourceRewindDescription_subroutineReady
    (selectedHitFromRewindDescription_subroutineReady useAccept)
    (sourceRewindDescription_haltsFrom_sourceScannerRightHandoffTape L)
    (rewindTargetTape_sourceBits_move_left_move_right L)
    (selectedHitFromRewindDescription_haltsFrom_rewindTarget_sourceBits
      useAccept L)

def selectedHitOtherFlagErasedFromScannerDescription
    (useAccept : Bool) : MachineDescription :=
  SeqViaCanonical (selectedHitFromScannerDescription useAccept)
    (eraseOtherHitFlagDescription useAccept)

theorem selectedHitOtherFlagErasedFromScannerDescription_subroutineReady
    (useAccept : Bool) :
    (selectedHitOtherFlagErasedFromScannerDescription useAccept).SubroutineReady :=
  SeqViaCanonical_subroutineReady
    (selectedHitFromScannerDescription_subroutineReady useAccept)
    (eraseOtherHitFlagDescription_subroutineReady useAccept)

theorem selectedHitOtherFlagErasedFromScannerDescription_haltsFrom_sourceScannerRightHandoffTape
    (useAccept : Bool) (L : DovetailLayout) :
    (selectedHitOtherFlagErasedFromScannerDescription useAccept).HaltsFromTape
      (SelectedProjectionTailProjector.sourceScannerRightHandoffTape L
        ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
          some))
      (selectedHitOtherFlagErasedTape useAccept L) :=
  SeqViaCanonical_haltsFromTape_of_haltsFromTape
    (selectedHitFromScannerDescription_subroutineReady useAccept)
    (eraseOtherHitFlagDescription_subroutineReady useAccept)
    (selectedHitFromScannerDescription_haltsFrom_sourceScannerRightHandoffTape
      useAccept L)
    (selectedHitRightEndTape_move_left_move_right useAccept L)
    (eraseOtherHitFlagDescription_haltsFrom_selectedHitRightEndTape
      useAccept L)

def selectedHitOtherFlagErasedRightLeftHandoffTape
    (useAccept : Bool) (L : DovetailLayout) : Tape Bool :=
  Tape.move Direction.left
    (Tape.move Direction.right
      (selectedHitOtherFlagErasedTape useAccept L))

theorem selectedHitOtherFlagErasedRightLeftHandoffTape_true_eq_tapeAtCells
    (L : DovetailLayout) :
    selectedHitOtherFlagErasedRightLeftHandoffTape true L =
      DovetailInitialLayoutInitializer.tapeAtCells
        (selectedHitOtherFlagErasedAcceptLeftRev L)
        [none, none] := by
  rw [selectedHitOtherFlagErasedRightLeftHandoffTape,
    selectedHitOtherFlagErasedTape_true_eq_tapeAtCells]
  simp [DovetailInitialLayoutInitializer.tapeAtCells,
    Tape.move, Tape.moveLeft, Tape.moveRight]

theorem skipCurrentAndFourBlankPaddingLeftDescription_haltsFrom_acceptHandoff
    (L : DovetailLayout) :
    skipCurrentAndFourBlankPaddingLeftDescription.HaltsFromTape
      (selectedHitOtherFlagErasedRightLeftHandoffTape true L)
      (selectedHitOtherFlagErasedAcceptAfterPaddingTape L) := by
  rw [selectedHitOtherFlagErasedRightLeftHandoffTape_true_eq_tapeAtCells,
    selectedHitOtherFlagErasedAcceptLeftRev_eq_hitHead,
    selectedHitOtherFlagErasedAcceptAfterPaddingTape]
  exact
    skipCurrentAndFourBlankPaddingLeftDescription_haltsFromTape
      (selectedHitOtherFlagErasedAcceptHitHead L.acceptHit)
      (selectedHitOtherFlagErasedAcceptHitRestLeftRev L)
      [none]

theorem selectedHitOtherFlagErasedRightLeftHandoffTape_false_eq_erasedTape
    (L : DovetailLayout) :
    selectedHitOtherFlagErasedRightLeftHandoffTape false L =
      selectedHitOtherFlagErasedTape false L := by
  rw [selectedHitOtherFlagErasedRightLeftHandoffTape,
    selectedHitOtherFlagErasedTape_false_eq_moveLeft_tapeAtCells]
  rw [selectedHitOtherFlagErasedRejectBaseCells]
  rw [tapeAtCells_move_left_right_left_cons_cons]

def selectedHitOtherFlagErasedRejectAfterPaddingTape
    (L : DovetailLayout) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells
    (List.append (List.replicate 4 (none : Option Bool))
      (selectedHitOtherFlagErasedRejectBaseLeftRev L))
    (List.drop 4 (selectedHitOtherFlagErasedRejectBaseCells L))

theorem skipCurrentAndFourBlankPaddingRightDescription_haltsFrom_rejectHandoff_named
    (L : DovetailLayout) :
    skipCurrentAndFourBlankPaddingRightDescription.HaltsFromTape
      (selectedHitOtherFlagErasedRightLeftHandoffTape false L)
      (selectedHitOtherFlagErasedRejectAfterPaddingTape L) := by
  rcases selectedHitOtherFlagErasedRejectBaseLeftRev_cons L with
    ⟨current, left, hleft⟩
  rcases selectedHitOtherFlagErasedRejectBaseCells_eq_hitHead L with
    ⟨hitTail, hcells⟩
  rw [selectedHitOtherFlagErasedRightLeftHandoffTape_false_eq_erasedTape,
    selectedHitOtherFlagErasedTape_false_eq_moveLeft_tapeAtCells,
    selectedHitOtherFlagErasedRejectAfterPaddingTape,
    hleft, hcells]
  simpa [DovetailInitialLayoutInitializer.tapeAtCells,
    Tape.move, Tape.moveLeft, List.append_assoc] using
    skipCurrentAndFourBlankPaddingRightDescription_haltsFromTape
      current false left (List.append (hitTail.map some) [none])

def selectedHitOtherFlagErasedAfterPaddingTape
    (useAccept : Bool) (L : DovetailLayout) : Tape Bool :=
  if useAccept then
    selectedHitOtherFlagErasedAcceptAfterPaddingTape L
  else
    selectedHitOtherFlagErasedRejectAfterPaddingTape L

theorem selectedHitOtherFlagErasedAcceptAfterPaddingTape_move_left_move_right
    (L : DovetailLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (selectedHitOtherFlagErasedAcceptAfterPaddingTape L)) =
      selectedHitOtherFlagErasedAcceptAfterPaddingTape L := by
  simpa [selectedHitOtherFlagErasedAcceptAfterPaddingTape] using
    tapeAtCells_move_left_move_right_cons_cons
      (selectedHitOtherFlagErasedAcceptHitRestLeftRev L)
      (some (selectedHitOtherFlagErasedAcceptHitHead L.acceptHit))
      none
      (none :: none :: none :: none :: [none])

theorem selectedHitOtherFlagErasedRejectAfterPaddingTape_move_left_move_right
    (L : DovetailLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (selectedHitOtherFlagErasedRejectAfterPaddingTape L)) =
      selectedHitOtherFlagErasedRejectAfterPaddingTape L := by
  rcases selectedHitOtherFlagErasedRejectBaseCells_eq_hitHead L with
    ⟨hitTail, hcells⟩
  rw [selectedHitOtherFlagErasedRejectAfterPaddingTape, hcells]
  cases hitTail with
  | nil =>
      simpa using
        tapeAtCells_move_left_move_right_cons_cons
          (List.append (List.replicate 4 (none : Option Bool))
            (selectedHitOtherFlagErasedRejectBaseLeftRev L))
          (some false) none []
  | cons bit rest =>
      simpa [List.append_assoc] using
        tapeAtCells_move_left_move_right_cons_cons
          (List.append (List.replicate 4 (none : Option Bool))
            (selectedHitOtherFlagErasedRejectBaseLeftRev L))
          (some false) (some bit)
          (List.append (rest.map some) [none])

theorem selectedHitOtherFlagErasedAcceptAfterPaddingTape_cells
    (L : DovetailLayout) :
    Tape.cells (selectedHitOtherFlagErasedAcceptAfterPaddingTape L) =
      List.append [none]
        (List.append
          ((SelectedProjectionTailProjector.outputPrefixBits L).map some)
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              L.stage).map some)
            (List.append
              ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                L.acceptConfig []).map some)
              (List.append
                ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                  L.rejectConfig []).map some)
                (List.append
                  ((CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
                    L.acceptHit []).map some)
                  (List.replicate 6 (none : Option Bool))))))) := by
  by_cases haccept : L.acceptHit <;>
    simp [selectedHitOtherFlagErasedAcceptAfterPaddingTape,
      selectedHitOtherFlagErasedAcceptHitRestLeftRev,
      selectedHitOtherFlagErasedAcceptHitHead,
      haccept,
      DovetailInitialLayoutInitializer.tapeAtCells,
      Tape.cells,
      CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellCodeBits,
      encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
      List.reverse_append, List.append_assoc]

theorem selectedHitOtherFlagErasedRejectAfterPaddingTape_cells
    (L : DovetailLayout) :
    Tape.cells (selectedHitOtherFlagErasedRejectAfterPaddingTape L) =
      List.append [none]
        (List.append
          ((SelectedProjectionTailProjector.outputPrefixBits L).map some)
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              L.stage).map some)
            (List.append
              ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                L.acceptConfig []).map some)
              (List.append
                ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                  L.rejectConfig []).map some)
                (List.append
                  (List.replicate 4 (none : Option Bool))
                  (List.append
                    ((CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
                      L.rejectHit []).map some)
                    [none])))))) := by
  by_cases hreject : L.rejectHit <;>
    simp [selectedHitOtherFlagErasedRejectAfterPaddingTape,
      selectedHitOtherFlagErasedRejectBaseLeftRev,
      selectedHitOtherFlagErasedRejectBaseCells,
      hreject,
      DovetailInitialLayoutInitializer.tapeAtCells,
      Tape.cells,
      CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellCodeBits,
      encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
      List.drop, List.reverse_append, List.map_reverse,
      List.append_assoc]

theorem selectedHitOtherFlagErasedAcceptAfterPaddingTape_normalizedOutput
    (L : DovetailLayout) :
    Tape.normalizedOutput
        (selectedHitOtherFlagErasedAcceptAfterPaddingTape L) =
      List.append (SelectedProjectionTailProjector.outputPrefixBits L)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            L.stage)
          (List.append
            (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
              L.acceptConfig [])
            (List.append
              (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                L.rejectConfig [])
              (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
                L.acceptHit [])))) := by
  rw [Tape.normalizedOutput]
  rw [selectedHitOtherFlagErasedAcceptAfterPaddingTape_cells]
  simp [Function.comp_def, List.filterMap_append]

theorem selectedHitOtherFlagErasedRejectAfterPaddingTape_normalizedOutput
    (L : DovetailLayout) :
    Tape.normalizedOutput
        (selectedHitOtherFlagErasedRejectAfterPaddingTape L) =
      List.append (SelectedProjectionTailProjector.outputPrefixBits L)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            L.stage)
          (List.append
            (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
              L.acceptConfig [])
            (List.append
              (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                L.rejectConfig [])
              (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
                L.rejectHit [])))) := by
  rw [Tape.normalizedOutput]
  rw [selectedHitOtherFlagErasedRejectAfterPaddingTape_cells]
  simp [Function.comp_def, List.filterMap_append]

theorem selectedHitOtherFlagErasedAcceptAfterPaddingTape_normalizedOutput_eq_sourceBits
    (L : DovetailLayout) :
    Tape.normalizedOutput
        (selectedHitOtherFlagErasedAcceptAfterPaddingTape L) =
      selectedProjectionPaddedTailCleanupPostPaddingSourceBits true L := by
  rw [selectedHitOtherFlagErasedAcceptAfterPaddingTape_normalizedOutput,
    selectedProjectionPaddedTailCleanupPostPaddingSourceBits_true]
  simp [selectedProjectionPaddedTailCleanupPrefixBits, List.append_assoc]

theorem selectedHitOtherFlagErasedRejectAfterPaddingTape_normalizedOutput_eq_sourceBits
    (L : DovetailLayout) :
    Tape.normalizedOutput
        (selectedHitOtherFlagErasedRejectAfterPaddingTape L) =
      selectedProjectionPaddedTailCleanupPostPaddingSourceBits false L := by
  rw [selectedHitOtherFlagErasedRejectAfterPaddingTape_normalizedOutput,
    selectedProjectionPaddedTailCleanupPostPaddingSourceBits_false]
  simp [selectedProjectionPaddedTailCleanupPrefixBits, List.append_assoc]

theorem selectedHitOtherFlagErasedAfterPaddingTape_normalizedOutput_eq_sourceBits
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.normalizedOutput
        (selectedHitOtherFlagErasedAfterPaddingTape useAccept L) =
      selectedProjectionPaddedTailCleanupPostPaddingSourceBits
        useAccept L := by
  cases useAccept
  · simpa [selectedHitOtherFlagErasedAfterPaddingTape] using
      selectedHitOtherFlagErasedRejectAfterPaddingTape_normalizedOutput_eq_sourceBits
        L
  · simpa [selectedHitOtherFlagErasedAfterPaddingTape] using
      selectedHitOtherFlagErasedAcceptAfterPaddingTape_normalizedOutput_eq_sourceBits
        L

theorem selectedHitOtherFlagErasedRightLeftHandoffTape_normalizedOutput
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.normalizedOutput
        (selectedHitOtherFlagErasedRightLeftHandoffTape useAccept L) =
      Tape.normalizedOutput (selectedHitOtherFlagErasedTape useAccept L) := by
  rw [selectedHitOtherFlagErasedRightLeftHandoffTape]
  rw [Tape.normalizedOutput_move]
  rw [Tape.normalizedOutput_move]

def selectedHitOtherFlagErasedRightLeftHandoffBits
    (useAccept : Bool) (L : DovetailLayout) : Word Bool :=
  if useAccept then
    List.append (SelectedProjectionTailProjector.outputPrefixBits L)
      (List.append
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          L.stage)
        (List.append
          (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
            L.acceptConfig [])
          (List.append
            (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
              L.rejectConfig [])
            (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
              L.acceptHit []))))
  else
    List.append (SelectedProjectionTailProjector.outputPrefixBits L)
      (List.append
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          L.stage)
        (List.append
          (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
            L.acceptConfig [])
          (List.append
            (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
              L.rejectConfig [])
            (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
              L.rejectHit []))))

def selectedProjectionPaddedTailCleanupBothConfigBits
    (L : DovetailLayout) : Word Bool :=
  List.append
    (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
      L.acceptConfig [])
    (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
      L.rejectConfig [])

theorem selectedHitOtherFlagErasedRightLeftHandoffBits_eq_bothConfigs_selectedHit
    (useAccept : Bool) (L : DovetailLayout) :
    selectedHitOtherFlagErasedRightLeftHandoffBits useAccept L =
      List.append (selectedProjectionPaddedTailCleanupPrefixBits L)
        (List.append
          (selectedProjectionPaddedTailCleanupBothConfigBits L)
          (selectedProjectionPaddedTailCleanupSelectedHitBits
            useAccept L)) := by
  cases useAccept <;>
    simp [selectedHitOtherFlagErasedRightLeftHandoffBits,
      selectedProjectionPaddedTailCleanupPrefixBits,
      selectedProjectionPaddedTailCleanupBothConfigBits,
      selectedProjectionPaddedTailCleanupSelectedHitBits,
      List.append_assoc]

theorem selectedHitOtherFlagErasedRightLeftHandoffTape_true_normalizedOutput
    (L : DovetailLayout) :
    Tape.normalizedOutput
        (selectedHitOtherFlagErasedRightLeftHandoffTape true L) =
      List.append (SelectedProjectionTailProjector.outputPrefixBits L)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            L.stage)
          (List.append
            (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
              L.acceptConfig [])
            (List.append
              (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                L.rejectConfig [])
              (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
                L.acceptHit [])))) := by
  rw [selectedHitOtherFlagErasedRightLeftHandoffTape_normalizedOutput,
    selectedHitOtherFlagErasedTape_true_normalizedOutput]

theorem selectedHitOtherFlagErasedRightLeftHandoffTape_true_cells
    (L : DovetailLayout) :
    Tape.cells (selectedHitOtherFlagErasedRightLeftHandoffTape true L) =
      List.append [none]
        (List.append
          ((SelectedProjectionTailProjector.outputPrefixBits L).map some)
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              L.stage).map some)
            (List.append
              ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                L.acceptConfig []).map some)
              (List.append
                ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                  L.rejectConfig []).map some)
                (List.append
                  ((CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
                    L.acceptHit []).map some)
                  (List.append
                    (List.replicate 4 (none : Option Bool))
                    [none, none])))))) := by
  simp [selectedHitOtherFlagErasedRightLeftHandoffTape,
    selectedHitOtherFlagErasedTape,
    DovetailInitialLayoutInitializer.tapeAtCells,
    Tape.cells, Tape.move, Tape.moveLeft, Tape.moveRight,
    List.reverse_append, List.map_reverse, List.append_assoc]

theorem selectedHitOtherFlagErasedRightLeftHandoffTape_false_normalizedOutput
    (L : DovetailLayout) :
    Tape.normalizedOutput
        (selectedHitOtherFlagErasedRightLeftHandoffTape false L) =
      List.append (SelectedProjectionTailProjector.outputPrefixBits L)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            L.stage)
          (List.append
            (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
              L.acceptConfig [])
            (List.append
              (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                L.rejectConfig [])
              (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
                L.rejectHit [])))) := by
  rw [selectedHitOtherFlagErasedRightLeftHandoffTape_normalizedOutput,
    selectedHitOtherFlagErasedTape_false_normalizedOutput]

theorem selectedHitOtherFlagErasedRightLeftHandoffTape_normalizedOutput_eq_bits
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.normalizedOutput
        (selectedHitOtherFlagErasedRightLeftHandoffTape useAccept L) =
      selectedHitOtherFlagErasedRightLeftHandoffBits useAccept L := by
  cases useAccept
  · simpa [selectedHitOtherFlagErasedRightLeftHandoffBits] using
      selectedHitOtherFlagErasedRightLeftHandoffTape_false_normalizedOutput L
  · simpa [selectedHitOtherFlagErasedRightLeftHandoffBits] using
      selectedHitOtherFlagErasedRightLeftHandoffTape_true_normalizedOutput L

theorem selectedHitOtherFlagErasedRightLeftHandoffTape_false_cells
    (L : DovetailLayout) :
    Tape.cells (selectedHitOtherFlagErasedRightLeftHandoffTape false L) =
      List.append [none]
        (List.append
          ((SelectedProjectionTailProjector.outputPrefixBits L).map some)
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              L.stage).map some)
            (List.append
              ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                L.acceptConfig []).map some)
              (List.append
                ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                  L.rejectConfig []).map some)
                (List.append
                  (List.replicate 4 (none : Option Bool))
                  (List.append
                    ((CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
                      L.rejectHit []).map some)
                    [none])))))) := by
  rw [show
      selectedHitOtherFlagErasedRightLeftHandoffTape false L =
        Tape.move Direction.left
          (Tape.move Direction.right
            (Tape.move Direction.left
              (DovetailInitialLayoutInitializer.tapeAtCells
                (List.append
                  (List.append
                    ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                      L.rejectConfig []).reverse.map some)
                    (List.append
                      ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                        L.acceptConfig []).reverse.map some)
                      (List.append
                        ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                          L.stage).reverse.map some)
                        ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
                          some))))
                  [none])
                (none :: none :: none :: none ::
                  (List.append
                    ((CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
                      L.rejectHit []).map some)
                    [none]))))) by
    simp [selectedHitOtherFlagErasedRightLeftHandoffTape,
      selectedHitOtherFlagErasedTape, List.append_assoc]]
  rw [tapeAtCells_move_left_right_left_append_none_cons_cells]
  simp [List.reverse_append, List.map_reverse, List.append_assoc]

def SelectedProjectionPaddedTailCleanupPostEraseSpec
    (useAccept : Bool)
    (postErase : MachineDescription) : Prop :=
  postErase.SubroutineReady ∧
    forall L : DovetailLayout,
      postErase.HaltsFromTape
        (selectedHitOtherFlagErasedRightLeftHandoffTape useAccept L)
        (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L)

def SelectedProjectionPaddedTailCleanupPostEraseConstruction : Prop :=
  forall useAccept : Bool,
    exists postErase : MachineDescription,
      SelectedProjectionPaddedTailCleanupPostEraseSpec useAccept postErase

def SelectedProjectionPaddedTailCleanupPostPaddingSpec
    (useAccept : Bool) (postPadding : MachineDescription) : Prop :=
  postPadding.SubroutineReady ∧
    forall L : DovetailLayout,
      postPadding.HaltsFromTape
        (selectedHitOtherFlagErasedAfterPaddingTape useAccept L)
        (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L)

def SelectedProjectionPaddedTailCleanupPostPaddingConstruction :
    Prop :=
  forall useAccept : Bool,
    exists postPadding : MachineDescription,
      SelectedProjectionPaddedTailCleanupPostPaddingSpec
        useAccept postPadding

def SelectedProjectionPaddedTailCleanupPostPaddingBranchConstruction
    (useAccept : Bool) : Prop :=
  exists postPadding : MachineDescription,
    SelectedProjectionPaddedTailCleanupPostPaddingSpec
      useAccept postPadding

theorem selectedProjectionPaddedTailCleanupPostPaddingConstruction_of_branches
    (hAccept :
      SelectedProjectionPaddedTailCleanupPostPaddingBranchConstruction true)
    (hReject :
      SelectedProjectionPaddedTailCleanupPostPaddingBranchConstruction false) :
    SelectedProjectionPaddedTailCleanupPostPaddingConstruction := by
  intro useAccept
  cases useAccept
  · exact hReject
  · exact hAccept

/--
Combined post-padding finite-machine leaf for selected-projection tail cleanup.
The branch wrappers below project this single obligation into the accepting and
rejecting branch contracts.
-/
theorem selectedProjectionPaddedTailCleanupPostPaddingCoreConstruction :
    SelectedProjectionPaddedTailCleanupPostPaddingConstruction := by
  sorry

def selectedHitOtherFlagErasedPostEraseFromPostPadding
    (useAccept : Bool) (postPadding : MachineDescription) :
    MachineDescription :=
  if useAccept then
    SeqViaCanonical skipCurrentAndFourBlankPaddingLeftDescription
      postPadding
  else
    SeqViaCanonical skipCurrentAndFourBlankPaddingRightDescription
      postPadding

theorem selectedProjectionPaddedTailCleanupPostEraseSpec_of_postPadding
    {useAccept : Bool} {postPadding : MachineDescription}
    (hpostPadding :
      SelectedProjectionPaddedTailCleanupPostPaddingSpec
        useAccept postPadding) :
    SelectedProjectionPaddedTailCleanupPostEraseSpec useAccept
      (selectedHitOtherFlagErasedPostEraseFromPostPadding
        useAccept postPadding) := by
  cases useAccept
  · constructor
    · simpa [selectedHitOtherFlagErasedPostEraseFromPostPadding] using
        SeqViaCanonical_subroutineReady
          skipCurrentAndFourBlankPaddingRightDescription_subroutineReady
          hpostPadding.left
    · intro L
      exact
        SeqViaCanonical_haltsFromTape_of_haltsFromTape
          skipCurrentAndFourBlankPaddingRightDescription_subroutineReady
          hpostPadding.left
          (skipCurrentAndFourBlankPaddingRightDescription_haltsFrom_rejectHandoff_named
            L)
          (selectedHitOtherFlagErasedRejectAfterPaddingTape_move_left_move_right
            L)
          (by
            simpa [selectedHitOtherFlagErasedAfterPaddingTape] using
              hpostPadding.right L)
  · constructor
    · simpa [selectedHitOtherFlagErasedPostEraseFromPostPadding] using
        SeqViaCanonical_subroutineReady
          skipCurrentAndFourBlankPaddingLeftDescription_subroutineReady
          hpostPadding.left
    · intro L
      exact
        SeqViaCanonical_haltsFromTape_of_haltsFromTape
          skipCurrentAndFourBlankPaddingLeftDescription_subroutineReady
          hpostPadding.left
          (skipCurrentAndFourBlankPaddingLeftDescription_haltsFrom_acceptHandoff
            L)
          (selectedHitOtherFlagErasedAcceptAfterPaddingTape_move_left_move_right
            L)
          (by
            simpa [selectedHitOtherFlagErasedAfterPaddingTape] using
              hpostPadding.right L)

theorem selectedProjectionPaddedTailCleanupPostEraseConstruction_of_postPadding
    (h :
      SelectedProjectionPaddedTailCleanupPostPaddingConstruction) :
    SelectedProjectionPaddedTailCleanupPostEraseConstruction := by
  intro useAccept
  rcases h useAccept with ⟨postPadding, hpostPadding⟩
  exact
    ⟨selectedHitOtherFlagErasedPostEraseFromPostPadding
        useAccept postPadding,
      selectedProjectionPaddedTailCleanupPostEraseSpec_of_postPadding
        hpostPadding⟩

/--
Post-padding finite-machine leaf for selected-projection tail cleanup on the
accepting projection branch.
-/
theorem selectedProjectionPaddedTailCleanupPostPaddingAcceptConstruction :
    SelectedProjectionPaddedTailCleanupPostPaddingBranchConstruction true := by
  exact selectedProjectionPaddedTailCleanupPostPaddingCoreConstruction true

/--
Post-padding finite-machine leaf for selected-projection tail cleanup on the
rejecting projection branch.
-/
theorem selectedProjectionPaddedTailCleanupPostPaddingRejectConstruction :
    SelectedProjectionPaddedTailCleanupPostPaddingBranchConstruction false := by
  exact selectedProjectionPaddedTailCleanupPostPaddingCoreConstruction false

theorem selectedProjectionPaddedTailCleanupPostPaddingConstruction :
    SelectedProjectionPaddedTailCleanupPostPaddingConstruction :=
  selectedProjectionPaddedTailCleanupPostPaddingConstruction_of_branches
    selectedProjectionPaddedTailCleanupPostPaddingAcceptConstruction
    selectedProjectionPaddedTailCleanupPostPaddingRejectConstruction

theorem selectedProjectionPaddedTailCleanupPostEraseConstruction :
    SelectedProjectionPaddedTailCleanupPostEraseConstruction :=
  selectedProjectionPaddedTailCleanupPostEraseConstruction_of_postPadding
    selectedProjectionPaddedTailCleanupPostPaddingConstruction

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
  intro useAccept
  rcases
      SelectedProjectionPaddedTailCleanup.selectedProjectionPaddedTailCleanupPostEraseConstruction
        useAccept with
    ⟨postErase, hpostErase⟩
  refine
    ⟨SeqViaCanonical
      (SelectedProjectionPaddedTailCleanup.selectedHitOtherFlagErasedFromScannerDescription
        useAccept)
      postErase, ?_⟩
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        (SelectedProjectionPaddedTailCleanup.selectedHitOtherFlagErasedFromScannerDescription_subroutineReady
          useAccept)
        hpostErase.left
  · intro L
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        (SelectedProjectionPaddedTailCleanup.selectedHitOtherFlagErasedFromScannerDescription_subroutineReady
          useAccept)
        hpostErase.left
        (SelectedProjectionPaddedTailCleanup.selectedHitOtherFlagErasedFromScannerDescription_haltsFrom_sourceScannerRightHandoffTape
          useAccept L)
        (by
          rfl)
        (hpostErase.right L)

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

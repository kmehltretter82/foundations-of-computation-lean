import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Closed.Construction.FiniteDescriptions.MergePadded.Scanners

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

namespace SelectedMergePaddedEmitterCleanup

def sourceBits (p : SelectedMergeEmitterPayload) : Word Bool :=
  SelectedMergePaddedEmitterAfterHitSourceBits p

def sourceLeftBitsRev
    (p : SelectedMergeEmitterPayload) : Word Bool :=
  List.append
    (SelectedMergePaddedEmitterOuterHitSuffixBits p).reverse
    (List.append
      (CanonicalLayouts.DovetailLayoutScanner.configurationRestoredBitsRev
        p.S.config)
      (List.append
        (FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          p.S.stage).reverse
        (List.append
          (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredBitsRev
            ((ParsedLayoutBits p.L).map some))
          (encodeCodeSymbolAsInput MachineCodeSymbol.transition).reverse)))

def sourceRewindDescription : MachineDescription where
  stateCount := 3
  start := 0
  halt := 2
  transitions :=
    [ MachineDescription.transition 0 none none Direction.left 1
    , MachineDescription.transition 0 (some false) (some false)
        Direction.left 1
    , MachineDescription.transition 0 (some true) (some true)
        Direction.left 1
    , MachineDescription.transition 1 (some false) (some false)
        Direction.left 1
    , MachineDescription.transition 1 (some true) (some true)
        Direction.left 1
    , MachineDescription.transition 1 none none Direction.right 2
    ]

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
          DovetailInitialLayoutInitializer.tapeAtCells,
          MachineDescription.runConfig,
          MachineDescription.stepConfig,
          MachineDescription.lookupTransition,
          MachineDescription.Matches,
          MachineDescription.transition,
          Tape.read, Tape.move, Tape.moveLeft, Tape.write]
  | cons next rest ih =>
      rw [show (next :: rest).length + 1 = 1 + (rest.length + 1) by
        simp
        omega]
      rw [MachineDescription.runConfig_add]
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
            DovetailInitialLayoutInitializer.tapeAtCells,
            MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition,
            MachineDescription.Matches,
            MachineDescription.transition,
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
        DovetailInitialLayoutInitializer.tapeAtCells,
        MachineDescription.runConfig,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition,
        MachineDescription.Matches,
        MachineDescription.transition,
        Tape.read, Tape.move, Tape.moveRight, Tape.write]
  | cons bit rest =>
      cases bit <;>
        simp [sourceRewindDescription, rewindTargetTape,
          DovetailInitialLayoutInitializer.tapeAtCells,
          MachineDescription.runConfig,
          MachineDescription.stepConfig,
          MachineDescription.lookupTransition,
          MachineDescription.Matches,
          MachineDescription.transition,
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
      simp [sourceRewindDescription,
        DovetailInitialLayoutInitializer.tapeAtCells,
        MachineDescription.runConfig,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition,
        MachineDescription.Matches,
        MachineDescription.transition,
        Tape.read, Tape.move, Tape.moveLeft, Tape.moveRight, Tape.write]
  | cons current rest =>
      rw [show (current :: rest).length + 2 =
        1 + ((rest.length + 1) + 1) by
        simp
        omega]
      rw [MachineDescription.runConfig_add]
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
            DovetailInitialLayoutInitializer.tapeAtCells,
            MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition,
            MachineDescription.Matches,
            MachineDescription.transition,
            Tape.read, Tape.move, Tape.moveLeft, Tape.write]
      rw [hstart]
      rw [show (rest.length + 1) + 1 = (rest.length + 1) + 1 by rfl]
      rw [MachineDescription.runConfig_add]
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

theorem SelectedMergePaddedEmitterAfterHitTape_eq_rewindSourceTape
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterAfterHitTape p =
      rewindSourceTape (sourceLeftBitsRev p).reverse := by
  rw [SelectedMergePaddedEmitterAfterHitTape, rewindSourceTape,
    sourceLeftBitsRev]
  rw [←
    CanonicalLayouts.DovetailLayoutScanner.configurationRestoredBitsRev_map_some_withBase
      p.S.config
      (List.append
        ((FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          p.S.stage).reverse.map some)
        (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
          ((ParsedLayoutBits p.L).map some)
          (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse)))]
  rw [←
    CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredBitsRev_map_some_withBase
      ((ParsedLayoutBits p.L).map some)
      (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse)]
  simp [List.map_append, List.append_assoc]

theorem sourceLeftBitsRev_reverse_eq_sourceBits
    (p : SelectedMergeEmitterPayload) :
    (sourceLeftBitsRev p).reverse = sourceBits p := by
  have hnorm := SelectedMergePaddedEmitterAfterHitTape_normalizedOutput p
  rw [SelectedMergePaddedEmitterAfterHitTape_eq_rewindSourceTape p] at hnorm
  simpa [sourceBits, rewindSourceTape,
    DovetailInitialLayoutInitializer.tapeAtCells,
    Tape.normalizedOutput, Tape.cells, Function.comp_def] using hnorm

theorem sourceRewindDescription_haltsFrom_afterHitTape
    (p : SelectedMergeEmitterPayload) :
    sourceRewindDescription.HaltsFromTape
      (SelectedMergePaddedEmitterAfterHitTape p)
      (rewindTargetTape (sourceBits p)) := by
  rw [SelectedMergePaddedEmitterAfterHitTape_eq_rewindSourceTape p]
  rw [sourceLeftBitsRev_reverse_eq_sourceBits p]
  exact sourceRewindDescription_haltsFromTape (sourceBits p)

end SelectedMergePaddedEmitterCleanup

theorem selectedMergePaddedEmitterHitScanner_haltsFromAfterConfigHandoff
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterHitScannerDescription.HaltsFromTape
      (SelectedMergePaddedEmitterAfterConfigHandoffTape p)
      (SelectedMergePaddedEmitterAfterHitTape p) := by
  refine ⟨4, ?_⟩
  constructor
  · simpa [MachineDescription.HaltsFromTapeIn,
      SelectedMergePaddedEmitterAfterConfigHandoffTape,
      SelectedMergePaddedEmitterAfterHitTape,
      SelectedMergePaddedEmitterOuterHitSuffixBits,
      SelectedMergePaddedEmitterOuterHitSuffixCode,
      DovetailInitialLayoutInitializer.config]
      using
        congrArg MachineDescription.Configuration.state
          (selectedMergePaddedEmitterHitScanner_runConfig
            p.S.hit
            (CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase
              p.S.config
              (List.append
                ((FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                  p.S.stage).reverse.map some)
                (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
                  ((ParsedLayoutBits p.L).map some)
                  (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse)))))
  · simpa [MachineDescription.HaltsFromTapeIn,
      SelectedMergePaddedEmitterAfterConfigHandoffTape,
      SelectedMergePaddedEmitterAfterHitTape,
      SelectedMergePaddedEmitterOuterHitSuffixBits,
      SelectedMergePaddedEmitterOuterHitSuffixCode,
      DovetailInitialLayoutInitializer.config]
      using
        congrArg MachineDescription.Configuration.tape
          (selectedMergePaddedEmitterHitScanner_runConfig
            p.S.hit
            (CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase
              p.S.config
              (List.append
                ((FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                  p.S.stage).reverse.map some)
                (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
                  ((ParsedLayoutBits p.L).map some)
                  (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse)))))

def SelectedMergePaddedEmitterAfterHitSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      emitter.HaltsFromTape
        (SelectedMergePaddedEmitterAfterHitTape p)
        (SelectedMergeEquivEmitterPaddedOutputTape useAccept p)

def SelectedMergePaddedEmitterSourceScannerDescription :
    MachineDescription :=
  seqSubroutine
    SelectedMergePaddedEmitterInputScannerDescription
    (seqSubroutine
      SelectedMergePaddedEmitterStageScannerDescription
      (seqSubroutine
        SelectedMergePaddedEmitterConfigScannerDescription
        SelectedMergePaddedEmitterHitScannerDescription
        Direction.right)
      Direction.right)
    Direction.right

theorem selectedMergePaddedEmitterSourceScanner_subroutineReady :
    SelectedMergePaddedEmitterSourceScannerDescription.SubroutineReady := by
  have hinput :
      SelectedMergePaddedEmitterInputScannerDescription.SubroutineReady :=
    selectedMergePaddedEmitterInputScanner_subroutineReady
  have hstage :
      SelectedMergePaddedEmitterStageScannerDescription.SubroutineReady :=
    selectedMergePaddedEmitterStageScanner_subroutineReady
  have hconfig :
      SelectedMergePaddedEmitterConfigScannerDescription.SubroutineReady :=
    selectedMergePaddedEmitterConfigScanner_subroutineReady
  have hhit :
      SelectedMergePaddedEmitterHitScannerDescription.SubroutineReady :=
    selectedMergePaddedEmitterHitScanner_subroutineReady
  simpa [SelectedMergePaddedEmitterSourceScannerDescription] using
    seqSubroutine_subroutineReady
      hinput
      (seqSubroutine_subroutineReady
        hstage
        (seqSubroutine_subroutineReady hconfig hhit))

theorem selectedMergePaddedEmitterStageScanner_haltsFromAfterInputHandoff
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterStageScannerDescription.HaltsFromTape
      (SelectedMergePaddedEmitterAfterInputHandoffTape p)
      (SelectedMergePaddedEmitterAfterStageTape p) := by
  rcases SelectedMergePaddedEmitterOuterStageSuffixBits_cons_false p with
    ⟨suffixTail, hsuffix⟩
  rcases
      CanonicalLayouts.DovetailStagePrefix.run_nonemptyNatSuffix_raw_to_handoff_withBase
          p.S.stage
          (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
            ((ParsedLayoutBits p.L).map some)
            (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse))
          false suffixTail with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  constructor
  · simpa [MachineDescription.HaltsFromTapeIn,
      SelectedMergePaddedEmitterStageScannerDescription,
      CanonicalLayouts.DovetailStagePrefix.NonemptyNatSuffixScannerDescription,
      SelectedMergePaddedEmitterAfterInputHandoffTape,
      SelectedMergePaddedEmitterOuterSuffixBits_eq_stageFieldBits,
      hsuffix,
      DovetailInitialLayoutInitializer.config]
      using congrArg MachineDescription.Configuration.state hsteps
  · simpa [MachineDescription.HaltsFromTapeIn,
      SelectedMergePaddedEmitterStageScannerDescription,
      CanonicalLayouts.DovetailStagePrefix.NonemptyNatSuffixScannerDescription,
      SelectedMergePaddedEmitterAfterInputHandoffTape,
      SelectedMergePaddedEmitterAfterStageTape,
      SelectedMergePaddedEmitterOuterSuffixBits_eq_stageFieldBits,
      hsuffix,
      DovetailInitialLayoutInitializer.config]
      using congrArg MachineDescription.Configuration.tape hsteps

theorem selectedMergePaddedEmitterInputScanner_haltsFromPayload
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterInputScannerDescription.HaltsFromTape
      (SelectedMergePaddedEmitterAfterHeaderTape p)
      (SelectedMergePaddedEmitterAfterInputTape p) := by
  rcases SelectedMergePaddedEmitterOuterSuffixBits_cons_false p with
    ⟨suffixTail, hsuffix⟩
  rcases
      CanonicalLayouts.DovetailLayoutScanner.run_boolWord_raw_to_canonical_handoff_withBase
          (ParsedLayoutBits p.L)
          (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse)
          suffixTail with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  constructor
  · simpa [MachineDescription.HaltsFromTapeIn,
      SelectedMergePaddedEmitterInputScannerDescription,
      SelectedMergePaddedEmitterAfterHeaderTape,
      SelectedMergePaddedEmitterOuterTailBits_eq_boolWordFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellListFieldBits,
      hsuffix,
      DovetailInitialLayoutInitializer.config]
      using congrArg MachineDescription.Configuration.state hsteps
  · simpa [MachineDescription.HaltsFromTapeIn,
      SelectedMergePaddedEmitterInputScannerDescription,
      SelectedMergePaddedEmitterAfterHeaderTape,
      SelectedMergePaddedEmitterAfterInputTape,
      SelectedMergePaddedEmitterOuterTailBits_eq_boolWordFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellListFieldBits,
      hsuffix,
      DovetailInitialLayoutInitializer.config]
      using congrArg MachineDescription.Configuration.tape hsteps

theorem selectedMergePaddedEmitterSourceScanner_haltsFromPayload
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterSourceScannerDescription.HaltsFromTape
      (SelectedMergePaddedEmitterAfterHeaderTape p)
      (SelectedMergePaddedEmitterAfterHitTape p) := by
  rcases MachineDescription.runConfig_eq_halt_of_haltsFromTape
      (selectedMergePaddedEmitterInputScanner_haltsFromPayload p) with
    ⟨inputSteps, hinput⟩
  rcases MachineDescription.runConfig_eq_halt_of_haltsFromTape
      (selectedMergePaddedEmitterStageScanner_haltsFromAfterInputHandoff p) with
    ⟨stageSteps, hstage⟩
  rcases MachineDescription.runConfig_eq_halt_of_haltsFromTape
      (selectedMergePaddedEmitterConfigScanner_haltsFromAfterStageHandoff p) with
    ⟨configSteps, hconfig⟩
  rcases MachineDescription.runConfig_eq_halt_of_haltsFromTape
      (selectedMergePaddedEmitterHitScanner_haltsFromAfterConfigHandoff p) with
    ⟨hitSteps, hhit⟩
  have hconfigHit :
      exists steps : Nat,
        (seqSubroutine
            SelectedMergePaddedEmitterConfigScannerDescription
            SelectedMergePaddedEmitterHitScannerDescription
            Direction.right).runConfig steps
            { state :=
                (seqSubroutine
                  SelectedMergePaddedEmitterConfigScannerDescription
                  SelectedMergePaddedEmitterHitScannerDescription
                  Direction.right).start
              tape := SelectedMergePaddedEmitterAfterStageHandoffTape p } =
          { state :=
              (seqSubroutine
                SelectedMergePaddedEmitterConfigScannerDescription
                SelectedMergePaddedEmitterHitScannerDescription
                Direction.right).halt
            tape := SelectedMergePaddedEmitterAfterHitTape p } := by
    exact
      CommonGround.SeqComposition.seqSubroutine_runConfig_exists
        (A := SelectedMergePaddedEmitterConfigScannerDescription)
        (B := SelectedMergePaddedEmitterHitScannerDescription)
        (handoffMove := Direction.right)
        selectedMergePaddedEmitterConfigScanner_subroutineReady
        selectedMergePaddedEmitterHitScanner_subroutineReady
        hconfig
        (CommonGround.SeqComposition.runConfig_reaches_from_move_eq
          (B := SelectedMergePaddedEmitterHitScannerDescription)
          (handoffMove := Direction.right)
          (selectedMergePaddedEmitterAfterConfigTape_move_right p)
          hhit)
  have hstageConfigHit :
      exists steps : Nat,
        (seqSubroutine
            SelectedMergePaddedEmitterStageScannerDescription
            (seqSubroutine
              SelectedMergePaddedEmitterConfigScannerDescription
              SelectedMergePaddedEmitterHitScannerDescription
              Direction.right)
            Direction.right).runConfig steps
            { state :=
                (seqSubroutine
                  SelectedMergePaddedEmitterStageScannerDescription
                  (seqSubroutine
                    SelectedMergePaddedEmitterConfigScannerDescription
                    SelectedMergePaddedEmitterHitScannerDescription
                    Direction.right)
                  Direction.right).start
              tape := SelectedMergePaddedEmitterAfterInputHandoffTape p } =
          { state :=
              (seqSubroutine
                SelectedMergePaddedEmitterStageScannerDescription
                (seqSubroutine
                  SelectedMergePaddedEmitterConfigScannerDescription
                  SelectedMergePaddedEmitterHitScannerDescription
                  Direction.right)
                Direction.right).halt
            tape := SelectedMergePaddedEmitterAfterHitTape p } := by
    refine
      CommonGround.SeqComposition.seqSubroutine_runConfig_exists
        (A := SelectedMergePaddedEmitterStageScannerDescription)
        (B :=
          seqSubroutine
            SelectedMergePaddedEmitterConfigScannerDescription
            SelectedMergePaddedEmitterHitScannerDescription
            Direction.right)
        (handoffMove := Direction.right)
        selectedMergePaddedEmitterStageScanner_subroutineReady
        (seqSubroutine_subroutineReady
          selectedMergePaddedEmitterConfigScanner_subroutineReady
          selectedMergePaddedEmitterHitScanner_subroutineReady)
        hstage ?_
    rcases hconfigHit with ⟨configHitSteps, hconfigHitSteps⟩
    exact
      CommonGround.SeqComposition.runConfig_reaches_from_move_eq
        (B :=
          seqSubroutine
            SelectedMergePaddedEmitterConfigScannerDescription
            SelectedMergePaddedEmitterHitScannerDescription
            Direction.right)
        (handoffMove := Direction.right)
        (selectedMergePaddedEmitterAfterStageTape_move_right p)
        hconfigHitSteps
  rcases
      CommonGround.SeqComposition.seqSubroutine_runConfig_exists
        (A := SelectedMergePaddedEmitterInputScannerDescription)
        (B :=
          seqSubroutine
            SelectedMergePaddedEmitterStageScannerDescription
            (seqSubroutine
              SelectedMergePaddedEmitterConfigScannerDescription
              SelectedMergePaddedEmitterHitScannerDescription
              Direction.right)
            Direction.right)
        (handoffMove := Direction.right)
        selectedMergePaddedEmitterInputScanner_subroutineReady
        (seqSubroutine_subroutineReady
          selectedMergePaddedEmitterStageScanner_subroutineReady
          (seqSubroutine_subroutineReady
            selectedMergePaddedEmitterConfigScanner_subroutineReady
            selectedMergePaddedEmitterHitScanner_subroutineReady))
        hinput
        (by
          rcases hstageConfigHit with
            ⟨stageConfigHitSteps, hstageConfigHitSteps⟩
          exact
            CommonGround.SeqComposition.runConfig_reaches_from_move_eq
              (B :=
                seqSubroutine
                  SelectedMergePaddedEmitterStageScannerDescription
                  (seqSubroutine
                    SelectedMergePaddedEmitterConfigScannerDescription
                    SelectedMergePaddedEmitterHitScannerDescription
                    Direction.right)
                  Direction.right)
              (handoffMove := Direction.right)
              (selectedMergePaddedEmitterAfterInputTape_move_right p)
              hstageConfigHitSteps) with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  constructor
  · simpa [MachineDescription.HaltsFromTapeIn,
      SelectedMergePaddedEmitterSourceScannerDescription]
      using congrArg MachineDescription.Configuration.state hsteps
  · simpa [MachineDescription.HaltsFromTapeIn,
      SelectedMergePaddedEmitterSourceScannerDescription]
      using congrArg MachineDescription.Configuration.tape hsteps

/--
Finite-machine leaf for selected merge under the equivalence-based phase
contract.  It emits the merged dovetail-layout code at the left edge and leaves
blank padding in the old simulator-layout window, so the exact tape is
equivalent to the unshifted merged dovetail-layout tape without requiring a
context-length decrease.
-/
theorem selectedMergePaddedEmitterExactShapeConstruction_scaffold :
    SelectedMergePaddedEmitterExactShapeConstruction := by
  sorry

theorem selectedMergeEquivPaddedEmitterConstruction_scaffold :
    SelectedMergeEquivPaddedEmitterConstruction :=
  selectedMergeEquivPaddedEmitterConstruction_of_exactShape
    selectedMergePaddedEmitterExactShapeConstruction_scaffold

theorem selectedMergeEquivEmitterConstruction_scaffold :
    SelectedMergeEquivEmitterConstruction :=
  selectedMergeEquivEmitterConstruction_of_padded
    selectedMergeEquivPaddedEmitterConstruction_scaffold

theorem selectedMergeEquivConstruction_scaffold :
    SelectedMergeEquivConstruction :=
  selectedMergeEquivConstruction_of_forwardParser_paddedEmitter
    selectedMergeForwardParserConstruction_scaffold
    selectedMergeEquivPaddedEmitterConstruction_scaffold


end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC

import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Merge.Padded.Scanners

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

namespace SelectedMergePaddedEmitterCleanup

def leftMoveOnceDescription : MachineDescription where
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [ MachineDescription.transition 0 none none Direction.left 1
    , MachineDescription.transition 0 (some false) (some false)
        Direction.left 1
    , MachineDescription.transition 0 (some true) (some true)
        Direction.left 1
    ]

theorem leftMoveOnceDescription_wellFormed :
    leftMoveOnceDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := leftMoveOnceDescription.transitions)
      (stateCount := leftMoveOnceDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := leftMoveOnceDescription.transitions)
      (by decide)

theorem leftMoveOnceDescription_haltTransitionFree :
    leftMoveOnceDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := leftMoveOnceDescription.transitions)
    (state := leftMoveOnceDescription.halt)
    (by decide)

theorem leftMoveOnceDescription_subroutineReady :
    leftMoveOnceDescription.SubroutineReady :=
  ⟨leftMoveOnceDescription_wellFormed,
    leftMoveOnceDescription_haltTransitionFree⟩

theorem leftMoveOnceDescription_haltsFromTape
    (T : Tape Bool) :
    leftMoveOnceDescription.HaltsFromTape T
      (Tape.move Direction.left T) := by
  have hrun :
      leftMoveOnceDescription.runConfig 1
          { state := leftMoveOnceDescription.start
            tape := T } =
        { state := leftMoveOnceDescription.halt
          tape := Tape.move Direction.left T } := by
    cases T with
    | mk left head right =>
        cases head with
        | none =>
            simp [leftMoveOnceDescription, MachineDescription.runConfig,
              MachineDescription.stepConfig,
              MachineDescription.lookupTransition,
              MachineDescription.Matches,
              MachineDescription.transition, Tape.read, Tape.write]
        | some b =>
            cases b <;>
              simp [leftMoveOnceDescription, MachineDescription.runConfig,
                MachineDescription.stepConfig,
                MachineDescription.lookupTransition,
                MachineDescription.Matches,
                MachineDescription.transition, Tape.read, Tape.write]
  refine ⟨1, ?_⟩
  constructor
  · simpa [MachineDescription.HaltsFromTapeIn] using
      congrArg MachineDescription.Configuration.state hrun
  · simpa [MachineDescription.HaltsFromTapeIn] using
      congrArg MachineDescription.Configuration.tape hrun

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

def rewindTargetPaddedTape (bits : Word Bool) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells
    [none] (List.append (bits.map some) [none, none])

theorem rewindTargetPaddedTape_cells
    (bits : Word Bool) :
    Tape.cells (rewindTargetPaddedTape bits) =
      none :: List.append (bits.map some) [none, none] := by
  cases bits <;>
    simp [rewindTargetPaddedTape,
      DovetailInitialLayoutInitializer.tapeAtCells, Tape.cells]

theorem rewindTargetPaddedTape_normalizedOutput
    (bits : Word Bool) :
    Tape.normalizedOutput (rewindTargetPaddedTape bits) = bits := by
  rw [Tape.normalizedOutput, rewindTargetPaddedTape_cells]
  simp [Function.comp_def]

def skipTransitionPrefixDescription : MachineDescription where
  stateCount := 5
  start := 0
  halt := 4
  transitions :=
    [ MachineDescription.transition 0 (some false) (some false)
        Direction.right 1
    , MachineDescription.transition 1 (some false) (some false)
        Direction.right 2
    , MachineDescription.transition 2 (some false) (some false)
        Direction.right 3
    , MachineDescription.transition 3 (some true) (some true)
        Direction.right 4 ]

theorem skipTransitionPrefixDescription_wellFormed :
    skipTransitionPrefixDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := skipTransitionPrefixDescription.transitions)
      (stateCount := skipTransitionPrefixDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := skipTransitionPrefixDescription.transitions)
      (by decide)

theorem skipTransitionPrefixDescription_haltTransitionFree :
    skipTransitionPrefixDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := skipTransitionPrefixDescription.transitions)
    (state := skipTransitionPrefixDescription.halt)
    (by decide)

theorem skipTransitionPrefixDescription_subroutineReady :
    skipTransitionPrefixDescription.SubroutineReady :=
  ⟨skipTransitionPrefixDescription_wellFormed,
    skipTransitionPrefixDescription_haltTransitionFree⟩

theorem skipTransitionPrefixDescription_run
    (left rest : List (Option Bool)) :
    skipTransitionPrefixDescription.runConfig 4
        { state := skipTransitionPrefixDescription.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells left
              (List.append
                ((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map
                  some)
                rest) } =
      { state := skipTransitionPrefixDescription.halt
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells
            (List.append
              ((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map
                some).reverse
              left)
            rest } := by
  cases rest <;>
    simp [skipTransitionPrefixDescription,
      encodeCodeSymbolAsInput,
      DovetailInitialLayoutInitializer.tapeAtCells,
      runConfig, stepConfig, lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

theorem skipTransitionPrefixDescription_haltsFromTape
    (left rest : List (Option Bool)) :
    skipTransitionPrefixDescription.HaltsFromTape
      (DovetailInitialLayoutInitializer.tapeAtCells left
        (List.append
          ((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some)
          rest))
      (DovetailInitialLayoutInitializer.tapeAtCells
        (List.append
          ((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse
          left)
        rest) := by
  refine ⟨4, ?_⟩
  constructor <;>
    rw [skipTransitionPrefixDescription_run]

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

theorem sourceRewindDescription_step_finish_padded
    (bits : Word Bool) :
    sourceRewindDescription.runConfig 1
        { state := 1
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells []
              (none :: List.append (bits.map some) [none, none]) } =
      { state := sourceRewindDescription.halt
        tape := rewindTargetPaddedTape bits } := by
  cases bits with
  | nil =>
      simp [sourceRewindDescription, rewindTargetPaddedTape,
        DovetailInitialLayoutInitializer.tapeAtCells,
        MachineDescription.runConfig,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition,
        MachineDescription.Matches,
        MachineDescription.transition,
        Tape.read, Tape.move, Tape.moveRight, Tape.write]
  | cons bit rest =>
      cases bit <;>
        simp [sourceRewindDescription, rewindTargetPaddedTape,
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

theorem sourceRewindDescription_run_from_leftStack_padded
    (leftStack : Word Bool) :
    sourceRewindDescription.runConfig (leftStack.length + 2)
        { state := sourceRewindDescription.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              (leftStack.map some) [none, none] } =
      { state := sourceRewindDescription.halt
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells [none]
            (List.append (leftStack.reverse.map some) [none, none]) } := by
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
                    ((current :: rest).map some) [none, none] } =
            { state := 1
              tape :=
                DovetailInitialLayoutInitializer.tapeAtCells
                  (rest.map some) (some current :: [none, none]) } := by
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
      rw [sourceRewindDescription_run_scan rest current [none, none]]
      simpa [rewindTargetPaddedTape, List.map_append,
        List.append_assoc] using
        sourceRewindDescription_step_finish_padded
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

theorem sourceRewindDescription_run_padded
    (bits : Word Bool) :
    sourceRewindDescription.runConfig (bits.length + 2)
        { state := sourceRewindDescription.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              (bits.reverse.map some) [none, none] } =
      { state := sourceRewindDescription.halt
        tape := rewindTargetPaddedTape bits } := by
  simpa [rewindTargetPaddedTape] using
    sourceRewindDescription_run_from_leftStack_padded bits.reverse

theorem sourceRewindDescription_haltsFromTape
    (bits : Word Bool) :
    sourceRewindDescription.HaltsFromTape
      (rewindSourceTape bits) (rewindTargetTape bits) := by
  refine ⟨bits.length + 2, ?_⟩
  constructor
  · rw [sourceRewindDescription_run]
  · rw [sourceRewindDescription_run]

theorem sourceRewindDescription_haltsFromPaddedTape
    (bits : Word Bool) :
    sourceRewindDescription.HaltsFromTape
      (DovetailInitialLayoutInitializer.tapeAtCells
        (bits.reverse.map some) [none, none])
      (rewindTargetPaddedTape bits) := by
  refine ⟨bits.length + 2, ?_⟩
  constructor
  · rw [sourceRewindDescription_run_padded]
  · rw [sourceRewindDescription_run_padded]

theorem rewindTargetPaddedTape_move_left_move_right
    (bits : Word Bool) :
    Tape.move Direction.left
        (Tape.move Direction.right (rewindTargetPaddedTape bits)) =
      rewindTargetPaddedTape bits := by
  cases bits with
  | nil =>
      simp [rewindTargetPaddedTape,
        DovetailInitialLayoutInitializer.tapeAtCells,
        Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons first rest =>
      cases first <;> cases rest <;>
        simp [rewindTargetPaddedTape,
          DovetailInitialLayoutInitializer.tapeAtCells,
          Tape.move, Tape.moveLeft, Tape.moveRight]

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

theorem SelectedMergePaddedEmitterAfterHitTape_eq_sourceLeftBitsRev_tapeAtCells
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterAfterHitTape p =
      DovetailInitialLayoutInitializer.tapeAtCells
        ((sourceLeftBitsRev p).map some) [] := by
  rw [SelectedMergePaddedEmitterAfterHitTape_eq_rewindSourceTape]
  simp [rewindSourceTape]

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

def SelectedMergePaddedEmitterAfterHitRightLeftHandoffTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  Tape.move Direction.left
    (Tape.move Direction.right
      (SelectedMergePaddedEmitterAfterHitTape p))

theorem SelectedMergePaddedEmitterAfterHitRightLeftHandoffTape_eq_tapeAtCells
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterAfterHitRightLeftHandoffTape p =
      DovetailInitialLayoutInitializer.tapeAtCells
        ((SelectedMergePaddedEmitterCleanup.sourceLeftBitsRev p).map some)
        [none, none] := by
  rw [SelectedMergePaddedEmitterAfterHitRightLeftHandoffTape,
    SelectedMergePaddedEmitterCleanup.SelectedMergePaddedEmitterAfterHitTape_eq_sourceLeftBitsRev_tapeAtCells]
  simp [DovetailInitialLayoutInitializer.tapeAtCells,
    Tape.move, Tape.moveLeft, Tape.moveRight]

theorem sourceRewindDescription_haltsFrom_afterHitRightLeftHandoffTape
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterCleanup.sourceRewindDescription.HaltsFromTape
      (SelectedMergePaddedEmitterAfterHitRightLeftHandoffTape p)
      (SelectedMergePaddedEmitterCleanup.rewindTargetPaddedTape
        (SelectedMergePaddedEmitterCleanup.sourceBits p)) := by
  have hleft :
      (SelectedMergePaddedEmitterCleanup.sourceBits p).reverse =
        SelectedMergePaddedEmitterCleanup.sourceLeftBitsRev p := by
    rw [←
      SelectedMergePaddedEmitterCleanup.sourceLeftBitsRev_reverse_eq_sourceBits
        p]
    simp
  rw [SelectedMergePaddedEmitterAfterHitRightLeftHandoffTape_eq_tapeAtCells,
    ← hleft]
  exact
    SelectedMergePaddedEmitterCleanup.sourceRewindDescription_haltsFromPaddedTape
      (SelectedMergePaddedEmitterCleanup.sourceBits p)

theorem SelectedMergePaddedEmitterAfterHitRewindSource_normalizedOutput
    (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput
        (SelectedMergePaddedEmitterCleanup.rewindTargetPaddedTape
          (SelectedMergePaddedEmitterCleanup.sourceBits p)) =
      SelectedMergePaddedEmitterAfterHitSourceBits p := by
  exact
    SelectedMergePaddedEmitterCleanup.rewindTargetPaddedTape_normalizedOutput
      (SelectedMergePaddedEmitterCleanup.sourceBits p)

theorem SelectedMergePaddedEmitterAfterHitRightLeftHandoffTape_normalizedOutput
    (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput
        (SelectedMergePaddedEmitterAfterHitRightLeftHandoffTape p) =
      SelectedMergePaddedEmitterAfterHitSourceBits p := by
  rw [SelectedMergePaddedEmitterAfterHitRightLeftHandoffTape]
  rw [Tape.normalizedOutput_move]
  rw [Tape.normalizedOutput_move]
  exact SelectedMergePaddedEmitterAfterHitTape_normalizedOutput p

def SelectedMergePaddedEmitterTargetBits
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) : Word Bool :=
  encodeCodeWordAsInput
    (MachineCodeSymbol.transition ::
      encodeBoolWordAppend p.L.input
        (encodeNatAppend p.L.stage
          (encodeConfigurationAppend
            (SelectedMergeOutputAcceptConfig useAccept p.S p.L)
            (encodeConfigurationAppend
              (SelectedMergeOutputRejectConfig useAccept p.S p.L)
              (encodeBoolAppend
                (SelectedMergeOutputAcceptHit useAccept p.S p.L)
                  (encodeBoolAppend
                    (SelectedMergeOutputRejectHit useAccept p.S p.L)
                  []))))))

theorem SelectedMergePaddedEmitterTargetBits_eq_transition_outputTail
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterTargetBits useAccept p =
      List.append (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
        (SelectedMergePaddedEmitterOutputTailBits useAccept p) := by
  simp [SelectedMergePaddedEmitterTargetBits,
    SelectedMergePaddedEmitterOutputTailBits,
    encodeCodeWordAsInput, encodeCodeSymbolAsInput]

theorem SelectedMergePaddedEmitterOutputTailBits_true
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterOutputTailBits true p =
      encodeCodeWordAsInput
        (encodeBoolWordAppend p.L.input
          (encodeNatAppend p.L.stage
            (encodeConfigurationAppend p.S.config
              (encodeConfigurationAppend p.L.rejectConfig
                (encodeBoolAppend p.S.hit
                  (encodeBoolAppend p.L.rejectHit [])))))) := by
  simp [SelectedMergePaddedEmitterOutputTailBits,
    SelectedMergeOutputAcceptConfig,
    SelectedMergeOutputRejectConfig,
    SelectedMergeOutputAcceptHit,
    SelectedMergeOutputRejectHit]

theorem SelectedMergePaddedEmitterOutputTailBits_false
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterOutputTailBits false p =
      encodeCodeWordAsInput
        (encodeBoolWordAppend p.L.input
          (encodeNatAppend p.L.stage
            (encodeConfigurationAppend p.L.acceptConfig
              (encodeConfigurationAppend p.S.config
                (encodeBoolAppend p.L.acceptHit
                  (encodeBoolAppend p.S.hit [])))))) := by
  simp [SelectedMergePaddedEmitterOutputTailBits,
    SelectedMergeOutputAcceptConfig,
    SelectedMergeOutputRejectConfig,
    SelectedMergeOutputAcceptHit,
    SelectedMergeOutputRejectHit]

theorem SelectedMergePaddedEmitterTargetBits_true_eq_fields
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterTargetBits true p =
      encodeCodeWordAsInput
        (MachineCodeSymbol.transition ::
          encodeBoolWordAppend p.L.input
            (encodeNatAppend p.L.stage
              (encodeConfigurationAppend p.S.config
                (encodeConfigurationAppend p.L.rejectConfig
                  (encodeBoolAppend p.S.hit
                    (encodeBoolAppend p.L.rejectHit [])))))) := by
  rw [SelectedMergePaddedEmitterTargetBits_eq_transition_outputTail,
    SelectedMergePaddedEmitterOutputTailBits_true]
  rfl

theorem SelectedMergePaddedEmitterTargetBits_false_eq_fields
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterTargetBits false p =
      encodeCodeWordAsInput
        (MachineCodeSymbol.transition ::
          encodeBoolWordAppend p.L.input
            (encodeNatAppend p.L.stage
              (encodeConfigurationAppend p.L.acceptConfig
                (encodeConfigurationAppend p.S.config
                  (encodeBoolAppend p.L.acceptHit
                    (encodeBoolAppend p.S.hit [])))))) := by
  rw [SelectedMergePaddedEmitterTargetBits_eq_transition_outputTail,
    SelectedMergePaddedEmitterOutputTailBits_false]
  rfl

theorem SelectedMergeEquivEmitterPaddedOutputTape_normalizedOutput_eq_targetBits
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput
        (SelectedMergeEquivEmitterPaddedOutputTape useAccept p) =
      SelectedMergePaddedEmitterTargetBits useAccept p := by
  simpa [SelectedMergePaddedEmitterTargetBits] using
    SelectedMergeEquivEmitterPaddedOutputTape_normalizedOutput_eq_fields
      useAccept p

theorem SelectedMergeEquivEmitterPaddedOutputTape_true_normalizedOutput_eq_fields
    (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput
        (SelectedMergeEquivEmitterPaddedOutputTape true p) =
      encodeCodeWordAsInput
        (MachineCodeSymbol.transition ::
          encodeBoolWordAppend p.L.input
            (encodeNatAppend p.L.stage
              (encodeConfigurationAppend p.S.config
                (encodeConfigurationAppend p.L.rejectConfig
                  (encodeBoolAppend p.S.hit
                    (encodeBoolAppend p.L.rejectHit [])))))) := by
  rw [SelectedMergeEquivEmitterPaddedOutputTape_normalizedOutput_eq_targetBits,
    SelectedMergePaddedEmitterTargetBits_true_eq_fields]

theorem SelectedMergeEquivEmitterPaddedOutputTape_false_normalizedOutput_eq_fields
    (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput
        (SelectedMergeEquivEmitterPaddedOutputTape false p) =
      encodeCodeWordAsInput
        (MachineCodeSymbol.transition ::
          encodeBoolWordAppend p.L.input
            (encodeNatAppend p.L.stage
              (encodeConfigurationAppend p.L.acceptConfig
                (encodeConfigurationAppend p.S.config
                  (encodeBoolAppend p.L.acceptHit
                    (encodeBoolAppend p.S.hit [])))))) := by
  rw [SelectedMergeEquivEmitterPaddedOutputTape_normalizedOutput_eq_targetBits,
    SelectedMergePaddedEmitterTargetBits_false_eq_fields]

theorem SelectedMergePaddedEmitterTargetBits_eq_parsedLayoutBits
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterTargetBits useAccept p =
      ParsedLayoutBits (SelectedMergeOutputLayout useAccept p.S p.L) := by
  exact
    (SelectedMergeEquivEmitterPaddedOutputTape_normalizedOutput_eq_targetBits
      useAccept p).symm.trans
      (SelectedMergeEquivEmitterPaddedOutputTape_normalizedOutput_eq_parsedLayoutBits
        useAccept p)

theorem SelectedMergeEquivEmitterPaddedOutputTape_cells_eq_targetBits
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    Tape.cells (SelectedMergeEquivEmitterPaddedOutputTape useAccept p) =
      List.append
        ((SelectedMergePaddedEmitterTargetBits useAccept p).map some)
        (List.replicate (SimulatorLayout.asBoolInput p.S).length none) := by
  simp [SelectedMergePaddedEmitterTargetBits,
    SelectedMergeEquivEmitterPaddedOutputTape_eq_fields,
    inputWithTrailingBlankPadding, Tape.cells,
    encodeCodeWordAsInput, encodeCodeSymbolAsInput]

theorem
    SelectedMergeEquivEmitterPaddedOutputTape_cells_eq_transition_outputTail
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    Tape.cells (SelectedMergeEquivEmitterPaddedOutputTape useAccept p) =
      List.append
        ((List.append (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
          (SelectedMergePaddedEmitterOutputTailBits useAccept p)).map some)
        (List.replicate (SimulatorLayout.asBoolInput p.S).length none) := by
  rw [SelectedMergeEquivEmitterPaddedOutputTape_cells_eq_targetBits,
    SelectedMergePaddedEmitterTargetBits_eq_transition_outputTail]

theorem SelectedMergeEquivEmitterPaddedOutputTape_eq_tapeAtCells_targetBits
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    SelectedMergeEquivEmitterPaddedOutputTape useAccept p =
      DovetailInitialLayoutInitializer.tapeAtCells []
        (List.append
          ((SelectedMergePaddedEmitterTargetBits useAccept p).map some)
          (List.replicate (SimulatorLayout.asBoolInput p.S).length none)) := by
  rw [SelectedMergeEquivEmitterPaddedOutputTape_eq_tapeAtCells_fields]
  simp [SelectedMergePaddedEmitterTargetBits,
    inputWithTrailingBlankPaddingCells,
    encodeCodeWordAsInput, encodeCodeSymbolAsInput]

theorem SelectedMergeEquivEmitterPaddedOutputTape_true_eq_tapeAtCells_fields
    (p : SelectedMergeEmitterPayload) :
    SelectedMergeEquivEmitterPaddedOutputTape true p =
      DovetailInitialLayoutInitializer.tapeAtCells []
        (List.append
          ((encodeCodeWordAsInput
            (MachineCodeSymbol.transition ::
              encodeBoolWordAppend p.L.input
                (encodeNatAppend p.L.stage
                  (encodeConfigurationAppend p.S.config
                    (encodeConfigurationAppend p.L.rejectConfig
                      (encodeBoolAppend p.S.hit
                        (encodeBoolAppend p.L.rejectHit []))))))).map some)
          (List.replicate (SimulatorLayout.asBoolInput p.S).length none)) := by
  rw [SelectedMergeEquivEmitterPaddedOutputTape_eq_tapeAtCells_targetBits,
    SelectedMergePaddedEmitterTargetBits_true_eq_fields]

theorem SelectedMergeEquivEmitterPaddedOutputTape_false_eq_tapeAtCells_fields
    (p : SelectedMergeEmitterPayload) :
    SelectedMergeEquivEmitterPaddedOutputTape false p =
      DovetailInitialLayoutInitializer.tapeAtCells []
        (List.append
          ((encodeCodeWordAsInput
            (MachineCodeSymbol.transition ::
              encodeBoolWordAppend p.L.input
                (encodeNatAppend p.L.stage
                  (encodeConfigurationAppend p.L.acceptConfig
                    (encodeConfigurationAppend p.S.config
                      (encodeBoolAppend p.L.acceptHit
                        (encodeBoolAppend p.S.hit []))))))).map some)
          (List.replicate (SimulatorLayout.asBoolInput p.S).length none)) := by
  rw [SelectedMergeEquivEmitterPaddedOutputTape_eq_tapeAtCells_targetBits,
    SelectedMergePaddedEmitterTargetBits_false_eq_fields]

theorem SelectedMergeEquivEmitterPaddedOutputTape_true_cells_eq_fields
    (p : SelectedMergeEmitterPayload) :
    Tape.cells (SelectedMergeEquivEmitterPaddedOutputTape true p) =
      List.append
        ((encodeCodeWordAsInput
          (MachineCodeSymbol.transition ::
            encodeBoolWordAppend p.L.input
              (encodeNatAppend p.L.stage
                (encodeConfigurationAppend p.S.config
                  (encodeConfigurationAppend p.L.rejectConfig
                    (encodeBoolAppend p.S.hit
                      (encodeBoolAppend p.L.rejectHit []))))))).map some)
        (List.replicate (SimulatorLayout.asBoolInput p.S).length none) := by
  rw [SelectedMergeEquivEmitterPaddedOutputTape_cells_eq_targetBits,
    SelectedMergePaddedEmitterTargetBits_true_eq_fields]

theorem SelectedMergeEquivEmitterPaddedOutputTape_false_cells_eq_fields
    (p : SelectedMergeEmitterPayload) :
    Tape.cells (SelectedMergeEquivEmitterPaddedOutputTape false p) =
      List.append
        ((encodeCodeWordAsInput
          (MachineCodeSymbol.transition ::
            encodeBoolWordAppend p.L.input
              (encodeNatAppend p.L.stage
                (encodeConfigurationAppend p.L.acceptConfig
                  (encodeConfigurationAppend p.S.config
                    (encodeBoolAppend p.L.acceptHit
                      (encodeBoolAppend p.S.hit []))))))).map some)
        (List.replicate (SimulatorLayout.asBoolInput p.S).length none) := by
  rw [SelectedMergeEquivEmitterPaddedOutputTape_cells_eq_targetBits,
    SelectedMergePaddedEmitterTargetBits_false_eq_fields]

def SelectedMergePaddedEmitterAfterHitRightLeftHandoffSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      emitter.HaltsFromTape
        (SelectedMergePaddedEmitterAfterHitRightLeftHandoffTape p)
        (SelectedMergeEquivEmitterPaddedOutputTape useAccept p)

def SelectedMergePaddedEmitterAfterHitRightLeftHandoffConstruction :
    Prop :=
  forall useAccept : Bool,
    exists emitter : MachineDescription,
      SelectedMergePaddedEmitterAfterHitRightLeftHandoffSpec
        useAccept emitter

def SelectedMergePaddedEmitterAfterHitRewindSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      emitter.HaltsFromTape
        (SelectedMergePaddedEmitterCleanup.rewindTargetPaddedTape
          (SelectedMergePaddedEmitterCleanup.sourceBits p))
        (SelectedMergeEquivEmitterPaddedOutputTape useAccept p)

def SelectedMergePaddedEmitterAfterHitRewindConstruction :
    Prop :=
  forall useAccept : Bool,
    exists emitter : MachineDescription,
      SelectedMergePaddedEmitterAfterHitRewindSpec useAccept emitter

def SelectedMergePaddedEmitterAfterHitRightLeftHandoffFromRewind
    (postRewind : MachineDescription) : MachineDescription :=
  SeqViaCanonical
    SelectedMergePaddedEmitterCleanup.sourceRewindDescription
    postRewind

theorem SelectedMergePaddedEmitterAfterHitRightLeftHandoffSpec_of_rewind
    {useAccept : Bool} {postRewind : MachineDescription}
    (hpostRewind :
      SelectedMergePaddedEmitterAfterHitRewindSpec useAccept postRewind) :
    SelectedMergePaddedEmitterAfterHitRightLeftHandoffSpec useAccept
      (SelectedMergePaddedEmitterAfterHitRightLeftHandoffFromRewind
        postRewind) := by
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        SelectedMergePaddedEmitterCleanup.sourceRewindDescription_subroutineReady
        hpostRewind.left
  · intro p
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        SelectedMergePaddedEmitterCleanup.sourceRewindDescription_subroutineReady
        hpostRewind.left
        (sourceRewindDescription_haltsFrom_afterHitRightLeftHandoffTape p)
        (SelectedMergePaddedEmitterCleanup.rewindTargetPaddedTape_move_left_move_right
          (SelectedMergePaddedEmitterCleanup.sourceBits p))
        (hpostRewind.right p)

theorem SelectedMergePaddedEmitterAfterHitRightLeftHandoffConstruction_of_rewind
    (h :
      SelectedMergePaddedEmitterAfterHitRewindConstruction) :
    SelectedMergePaddedEmitterAfterHitRightLeftHandoffConstruction := by
  intro useAccept
  rcases h useAccept with ⟨postRewind, hpostRewind⟩
  exact
    ⟨SelectedMergePaddedEmitterAfterHitRightLeftHandoffFromRewind
        postRewind,
      SelectedMergePaddedEmitterAfterHitRightLeftHandoffSpec_of_rewind
        hpostRewind⟩

def SelectedMergePaddedEmitterAfterHeaderRightHandoffTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  Tape.move Direction.right
    (SelectedMergePaddedEmitterAfterHeaderTape p)

def SelectedMergePaddedEmitterAfterHeaderRightHandoffSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      emitter.HaltsFromTape
        (SelectedMergePaddedEmitterAfterHeaderRightHandoffTape p)
        (SelectedMergeEquivEmitterPaddedOutputTape useAccept p)

def SelectedMergePaddedEmitterAfterHeaderRightHandoffConstruction :
    Prop :=
  forall useAccept : Bool,
    exists emitter : MachineDescription,
      SelectedMergePaddedEmitterAfterHeaderRightHandoffSpec
        useAccept emitter

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
  have hconfigHit :
      (seqSubroutine
        SelectedMergePaddedEmitterConfigScannerDescription
        SelectedMergePaddedEmitterHitScannerDescription
        Direction.right).HaltsFromTape
        (SelectedMergePaddedEmitterAfterStageHandoffTape p)
        (SelectedMergePaddedEmitterAfterHitTape p) := by
    exact
      CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
        (A := SelectedMergePaddedEmitterConfigScannerDescription)
        (B := SelectedMergePaddedEmitterHitScannerDescription)
        (handoffMove := Direction.right)
        selectedMergePaddedEmitterConfigScanner_subroutineReady
        selectedMergePaddedEmitterHitScanner_subroutineReady
        (selectedMergePaddedEmitterConfigScanner_haltsFromAfterStageHandoff p)
        (selectedMergePaddedEmitterAfterConfigTape_move_right p)
        (selectedMergePaddedEmitterHitScanner_haltsFromAfterConfigHandoff p)
  have hstageConfigHit :
      (seqSubroutine
        SelectedMergePaddedEmitterStageScannerDescription
        (seqSubroutine
          SelectedMergePaddedEmitterConfigScannerDescription
          SelectedMergePaddedEmitterHitScannerDescription
          Direction.right)
        Direction.right).HaltsFromTape
        (SelectedMergePaddedEmitterAfterInputHandoffTape p)
        (SelectedMergePaddedEmitterAfterHitTape p) := by
    exact
      CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
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
        (selectedMergePaddedEmitterStageScanner_haltsFromAfterInputHandoff p)
        (selectedMergePaddedEmitterAfterStageTape_move_right p)
        hconfigHit
  simpa [SelectedMergePaddedEmitterSourceScannerDescription] using
    CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
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
      (selectedMergePaddedEmitterInputScanner_haltsFromPayload p)
      (selectedMergePaddedEmitterAfterInputTape_move_right p)
      hstageConfigHit

theorem SelectedMergePaddedEmitterOuterTailBits_cons_cons_false_false
    (p : SelectedMergeEmitterPayload) :
    exists tail : Word Bool,
      SelectedMergePaddedEmitterOuterTailBits p =
        false :: false :: tail := by
  rw [SelectedMergePaddedEmitterOuterTailBits_eq_boolWordFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.cellListFieldBits]
  cases hlength : (ParsedLayoutBits p.L).map some |>.length with
  | zero =>
      refine
        ⟨true :: true ::
          List.append
            (CanonicalLayouts.DovetailLayoutScanner.cellsCodeBits
              ((ParsedLayoutBits p.L).map some))
            (SelectedMergePaddedEmitterOuterSuffixBits p), ?_⟩
      simp
  | succ n =>
      refine
        ⟨true :: false ::
          List.append
            (FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits n)
            (List.append
              (CanonicalLayouts.DovetailLayoutScanner.cellsCodeBits
                ((ParsedLayoutBits p.L).map some))
              (SelectedMergePaddedEmitterOuterSuffixBits p)), ?_⟩
      simp [
        FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_succ]

theorem tapeAtCells_move_left_move_right_cons_cons
    (left : List (Option Bool)) (cell next : Option Bool)
    (rest : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (DovetailInitialLayoutInitializer.tapeAtCells left
            (cell :: next :: rest))) =
      DovetailInitialLayoutInitializer.tapeAtCells left
        (cell :: next :: rest) := by
  rfl

theorem selectedMergePaddedEmitterAfterHeaderTape_move_left_move_right
    (p : SelectedMergeEmitterPayload) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (SelectedMergePaddedEmitterAfterHeaderTape p)) =
      SelectedMergePaddedEmitterAfterHeaderTape p := by
  rcases
      SelectedMergePaddedEmitterOuterTailBits_cons_cons_false_false p with
    ⟨tail, htail⟩
  rw [SelectedMergePaddedEmitterAfterHeaderTape, htail]
  simpa using
    tapeAtCells_move_left_move_right_cons_cons
      ((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse
      (some false) (some false) (tail.map some)

def SelectedMergePaddedEmitterAfterTransitionPaddedTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells
    (List.append
      ((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse
      [none])
    (List.append ((SelectedMergePaddedEmitterOuterTailBits p).map some)
      [none, none])

theorem SelectedMergePaddedEmitterAfterTransitionPaddedTape_cells
    (p : SelectedMergeEmitterPayload) :
    Tape.cells (SelectedMergePaddedEmitterAfterTransitionPaddedTape p) =
      List.append [none]
        (List.append
          ((List.append (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
            (SelectedMergePaddedEmitterOuterTailBits p)).map some)
          [none, none]) := by
  rcases
      SelectedMergePaddedEmitterOuterTailBits_cons_cons_false_false p with
    ⟨tail, htail⟩
  rw [SelectedMergePaddedEmitterAfterTransitionPaddedTape, htail]
  simp [
    DovetailInitialLayoutInitializer.tapeAtCells,
    Tape.cells, List.map_append, List.append_assoc]

theorem SelectedMergePaddedEmitterAfterHitSourceBits_eq_transition_outerTail
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterCleanup.sourceBits p =
      List.append (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
        (SelectedMergePaddedEmitterOuterTailBits p) := by
  rw [SelectedMergePaddedEmitterCleanup.sourceBits,
    SelectedMergePaddedEmitterAfterHitSourceBits,
    SelectedMergePaddedEmitterOuterTailBits_eq_boolWordFieldBits,
    SelectedMergePaddedEmitterOuterSuffixBits_eq_stageFieldBits,
    SelectedMergePaddedEmitterOuterStageSuffixBits_eq_configurationFieldBits]
  simp [SelectedMergePaddedEmitterOuterHitSuffixBits,
    SelectedMergePaddedEmitterOuterHitSuffixCode,
    CanonicalLayouts.DovetailLayoutScanner.boolBits_eq_encodeBoolAppend,
    CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
    encodeCodeWordAsInput]

theorem SelectedMergePaddedEmitterAfterTransitionPaddedTape_normalizedOutput
    (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput
        (SelectedMergePaddedEmitterAfterTransitionPaddedTape p) =
      SelectedMergePaddedEmitterCleanup.sourceBits p := by
  rw [Tape.normalizedOutput,
    SelectedMergePaddedEmitterAfterTransitionPaddedTape_cells,
    SelectedMergePaddedEmitterAfterHitSourceBits_eq_transition_outerTail]
  simp [Function.comp_def, List.map_append]

theorem
    SelectedMergePaddedEmitterAfterTransitionPaddedTape_normalizedOutput_eq_fields
    (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput
        (SelectedMergePaddedEmitterAfterTransitionPaddedTape p) =
      encodeCodeWordAsInput
        (MachineCodeSymbol.transition ::
          encodeBoolWordAppend (ParsedLayoutBits p.L)
            (encodeNatAppend p.S.stage
              (encodeConfigurationAppend p.S.config
                (encodeBoolAppend p.S.hit [])))) := by
  rw [SelectedMergePaddedEmitterAfterTransitionPaddedTape_normalizedOutput,
    SelectedMergePaddedEmitterAfterHitSourceBits_eq_transition_outerTail]
  simp [SelectedMergePaddedEmitterOuterTailBits,
    encodeCodeWordAsInput, encodeCodeSymbolAsInput]

theorem SelectedMergePaddedEmitterAfterTransitionPaddedTape_cells_eq_sourceBits
    (p : SelectedMergeEmitterPayload) :
    Tape.cells (SelectedMergePaddedEmitterAfterTransitionPaddedTape p) =
      List.append [none]
        (List.append
          ((SelectedMergePaddedEmitterCleanup.sourceBits p).map some)
          [none, none]) := by
  rw [SelectedMergePaddedEmitterAfterTransitionPaddedTape_cells,
    SelectedMergePaddedEmitterAfterHitSourceBits_eq_transition_outerTail]

theorem SelectedMergePaddedEmitterAfterTransitionPaddedTape_cells_eq_fields
    (p : SelectedMergeEmitterPayload) :
    Tape.cells (SelectedMergePaddedEmitterAfterTransitionPaddedTape p) =
      List.append [none]
        (List.append
          ((encodeCodeWordAsInput
            (MachineCodeSymbol.transition ::
              encodeBoolWordAppend (ParsedLayoutBits p.L)
                (encodeNatAppend p.S.stage
                  (encodeConfigurationAppend p.S.config
                    (encodeBoolAppend p.S.hit []))))).map some)
          [none, none]) := by
  rw [SelectedMergePaddedEmitterAfterTransitionPaddedTape_cells_eq_sourceBits,
    SelectedMergePaddedEmitterAfterHitSourceBits_eq_transition_outerTail]
  simp [SelectedMergePaddedEmitterOuterTailBits,
    encodeCodeWordAsInput, encodeCodeSymbolAsInput]

theorem skipTransitionPrefixDescription_haltsFrom_afterHitRewindSource
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterCleanup.skipTransitionPrefixDescription.HaltsFromTape
      (SelectedMergePaddedEmitterCleanup.rewindTargetPaddedTape
        (SelectedMergePaddedEmitterCleanup.sourceBits p))
      (SelectedMergePaddedEmitterAfterTransitionPaddedTape p) := by
  rw [SelectedMergePaddedEmitterCleanup.rewindTargetPaddedTape,
    SelectedMergePaddedEmitterAfterTransitionPaddedTape,
    SelectedMergePaddedEmitterAfterHitSourceBits_eq_transition_outerTail]
  simpa [List.map_append, List.append_assoc] using
    SelectedMergePaddedEmitterCleanup.skipTransitionPrefixDescription_haltsFromTape
      [none]
      (List.append ((SelectedMergePaddedEmitterOuterTailBits p).map some)
        [none, none])

theorem SelectedMergePaddedEmitterAfterTransitionPaddedTape_move_left_move_right
    (p : SelectedMergeEmitterPayload) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (SelectedMergePaddedEmitterAfterTransitionPaddedTape p)) =
      SelectedMergePaddedEmitterAfterTransitionPaddedTape p := by
  rcases
      SelectedMergePaddedEmitterOuterTailBits_cons_cons_false_false p with
    ⟨tail, htail⟩
  rw [SelectedMergePaddedEmitterAfterTransitionPaddedTape, htail]
  simpa [List.map_append, List.append_assoc] using
    tapeAtCells_move_left_move_right_cons_cons
      (List.append
        ((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse
        [none])
      (some false) (some false)
      (List.append (tail.map some) [none, none])

def SelectedMergePaddedEmitterAfterTransitionPaddedSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      emitter.HaltsFromTape
        (SelectedMergePaddedEmitterAfterTransitionPaddedTape p)
        (SelectedMergeEquivEmitterPaddedOutputTape useAccept p)

def SelectedMergePaddedEmitterAfterTransitionPaddedConstruction :
    Prop :=
  forall useAccept : Bool,
    exists emitter : MachineDescription,
      SelectedMergePaddedEmitterAfterTransitionPaddedSpec useAccept emitter

def SelectedMergePaddedEmitterAfterTransitionPaddedBranchConstruction
    (useAccept : Bool) : Prop :=
  exists emitter : MachineDescription,
    SelectedMergePaddedEmitterAfterTransitionPaddedSpec useAccept emitter

def SelectedMergePaddedEmitterAfterHitRewindFromTransition
    (afterTransition : MachineDescription) : MachineDescription :=
  SeqViaCanonical
    SelectedMergePaddedEmitterCleanup.skipTransitionPrefixDescription
    afterTransition

theorem SelectedMergePaddedEmitterAfterHitRewindSpec_of_afterTransition
    {useAccept : Bool} {afterTransition : MachineDescription}
    (hafterTransition :
      SelectedMergePaddedEmitterAfterTransitionPaddedSpec
        useAccept afterTransition) :
    SelectedMergePaddedEmitterAfterHitRewindSpec useAccept
      (SelectedMergePaddedEmitterAfterHitRewindFromTransition
        afterTransition) := by
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        SelectedMergePaddedEmitterCleanup.skipTransitionPrefixDescription_subroutineReady
        hafterTransition.left
  · intro p
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        SelectedMergePaddedEmitterCleanup.skipTransitionPrefixDescription_subroutineReady
        hafterTransition.left
        (skipTransitionPrefixDescription_haltsFrom_afterHitRewindSource p)
        (SelectedMergePaddedEmitterAfterTransitionPaddedTape_move_left_move_right
          p)
        (hafterTransition.right p)

theorem SelectedMergePaddedEmitterAfterHitRewindConstruction_of_afterTransition
    (h :
      SelectedMergePaddedEmitterAfterTransitionPaddedConstruction) :
    SelectedMergePaddedEmitterAfterHitRewindConstruction := by
  intro useAccept
  rcases h useAccept with ⟨afterTransition, hafterTransition⟩
  exact
    ⟨SelectedMergePaddedEmitterAfterHitRewindFromTransition
        afterTransition,
      SelectedMergePaddedEmitterAfterHitRewindSpec_of_afterTransition
        hafterTransition⟩

theorem selectedMergePaddedEmitterAfterTransitionPaddedConstruction_of_branches
    (hAccept :
      SelectedMergePaddedEmitterAfterTransitionPaddedBranchConstruction true)
    (hReject :
      SelectedMergePaddedEmitterAfterTransitionPaddedBranchConstruction false) :
    SelectedMergePaddedEmitterAfterTransitionPaddedConstruction := by
  intro useAccept
  cases useAccept
  · exact hReject
  · exact hAccept

/--
Combined post-transition finite-machine leaf for selected merge under the
padded equivalence contract.  The branch wrappers below project this single
obligation into the accepting and rejecting branch contracts.
-/
theorem selectedMergePaddedEmitterAfterTransitionPaddedCoreConstruction :
    SelectedMergePaddedEmitterAfterTransitionPaddedConstruction := by
  sorry

def SelectedMergePaddedEmitterAfterHeaderScannerDescription :
    MachineDescription :=
  SeqViaCanonical SelectedMergePaddedEmitterCleanup.leftMoveOnceDescription
    SelectedMergePaddedEmitterSourceScannerDescription

theorem selectedMergePaddedEmitterAfterHeaderScanner_subroutineReady :
    SelectedMergePaddedEmitterAfterHeaderScannerDescription.SubroutineReady :=
  SeqViaCanonical_subroutineReady
    SelectedMergePaddedEmitterCleanup.leftMoveOnceDescription_subroutineReady
    selectedMergePaddedEmitterSourceScanner_subroutineReady

theorem selectedMergePaddedEmitterAfterHeaderScanner_haltsFromPayload
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterAfterHeaderScannerDescription.HaltsFromTape
      (SelectedMergePaddedEmitterAfterHeaderRightHandoffTape p)
      (SelectedMergePaddedEmitterAfterHitTape p) := by
  exact
    SeqViaCanonical_haltsFromTape_of_haltsFromTape
      SelectedMergePaddedEmitterCleanup.leftMoveOnceDescription_subroutineReady
      selectedMergePaddedEmitterSourceScanner_subroutineReady
      (SelectedMergePaddedEmitterCleanup.leftMoveOnceDescription_haltsFromTape
        (SelectedMergePaddedEmitterAfterHeaderRightHandoffTape p))
      (by
        simpa [SelectedMergePaddedEmitterAfterHeaderRightHandoffTape] using
          selectedMergePaddedEmitterAfterHeaderTape_move_left_move_right p)
      (selectedMergePaddedEmitterSourceScanner_haltsFromPayload p)

/--
Post-transition finite-machine leaf for selected merge under the padded
equivalence contract.  The restored source has been rewound to the left edge
and the leading transition code has been consumed, with the extra trailing
blank padding retained from the canonical handoff.
-/
theorem selectedMergePaddedEmitterAfterTransitionPaddedAcceptConstruction :
    SelectedMergePaddedEmitterAfterTransitionPaddedBranchConstruction true := by
  exact selectedMergePaddedEmitterAfterTransitionPaddedCoreConstruction true

/--
Post-transition finite-machine leaf for selected merge under the rejecting
padded equivalence branch.
-/
theorem selectedMergePaddedEmitterAfterTransitionPaddedRejectConstruction :
    SelectedMergePaddedEmitterAfterTransitionPaddedBranchConstruction false := by
  exact selectedMergePaddedEmitterAfterTransitionPaddedCoreConstruction false

theorem selectedMergePaddedEmitterAfterTransitionPaddedConstruction :
    SelectedMergePaddedEmitterAfterTransitionPaddedConstruction :=
  selectedMergePaddedEmitterAfterTransitionPaddedConstruction_of_branches
    selectedMergePaddedEmitterAfterTransitionPaddedAcceptConstruction
    selectedMergePaddedEmitterAfterTransitionPaddedRejectConstruction

/--
Post-rewind finite-machine leaf for selected merge under the padded equivalence
contract.  A checked transition-prefix skipper reduces this to the
post-transition padded obligation above.
-/
theorem selectedMergePaddedEmitterAfterHitRewindConstruction :
    SelectedMergePaddedEmitterAfterHitRewindConstruction :=
  SelectedMergePaddedEmitterAfterHitRewindConstruction_of_afterTransition
    selectedMergePaddedEmitterAfterTransitionPaddedConstruction

/--
Post-scan finite-machine leaf for selected merge under the padded equivalence
contract.  The source fields have been scanned and restored; the sequential
adapter has performed its canonical right-left handoff from the after-hit tape.
The reusable rewind prefix reduces the remaining machine to the post-rewind
emitter obligation above.
-/
theorem selectedMergePaddedEmitterAfterHitRightLeftHandoffConstruction :
    SelectedMergePaddedEmitterAfterHitRightLeftHandoffConstruction :=
  SelectedMergePaddedEmitterAfterHitRightLeftHandoffConstruction_of_rewind
    selectedMergePaddedEmitterAfterHitRewindConstruction

theorem selectedMergePaddedEmitterAfterHeaderRightHandoffConstruction :
    SelectedMergePaddedEmitterAfterHeaderRightHandoffConstruction := by
  intro useAccept
  rcases
      selectedMergePaddedEmitterAfterHitRightLeftHandoffConstruction
        useAccept with
    ⟨afterHit, hafterHit⟩
  refine
    ⟨SeqViaCanonical
      SelectedMergePaddedEmitterAfterHeaderScannerDescription
      afterHit, ?_⟩
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        selectedMergePaddedEmitterAfterHeaderScanner_subroutineReady
        hafterHit.left
  · intro p
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        selectedMergePaddedEmitterAfterHeaderScanner_subroutineReady
        hafterHit.left
        (selectedMergePaddedEmitterAfterHeaderScanner_haltsFromPayload p)
        (by
          rfl)
        (hafterHit.right p)

/--
Finite-machine leaf for selected merge under the equivalence-based phase
contract.  It emits the merged dovetail-layout code at the left edge and leaves
blank padding in the old simulator-layout window, so the exact tape is
equivalent to the unshifted merged dovetail-layout tape without requiring a
context-length decrease.
-/
theorem selectedMergePaddedEmitterExactShapeConstruction_scaffold :
    SelectedMergePaddedEmitterExactShapeConstruction := by
  intro useAccept
  rcases
      selectedMergePaddedEmitterAfterHeaderRightHandoffConstruction
        useAccept with
    ⟨postHeader, hpostHeader⟩
  refine
    ⟨seqSubroutine
      SelectedMergePaddedEmitterHeaderRewriterDescription
      postHeader Direction.right, ?_⟩
  constructor
  · exact
      seqSubroutine_subroutineReady
        selectedMergePaddedEmitterHeaderRewriter_subroutineReady
        hpostHeader.left
  · intro p
    exact
      CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
        selectedMergePaddedEmitterHeaderRewriter_subroutineReady
        hpostHeader.left
        (selectedMergePaddedEmitterHeaderRewriter_haltsFromPayload p)
        (by
          rfl)
        (hpostHeader.right p)

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

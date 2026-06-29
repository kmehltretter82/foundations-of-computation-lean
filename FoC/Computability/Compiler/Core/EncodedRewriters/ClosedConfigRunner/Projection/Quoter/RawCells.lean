import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Quoter.SourceRestFinishCore

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

theorem assemblyPrefixDescription_lookupTransition_eq_scanner_of_state_lt_210
    (state : Nat) (read : Option Bool) (hstate : state < 210) :
    AssemblyPrefixDescription.lookupTransition state read =
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription.lookupTransition
        state read := by
  have hne : state ≠ 210 := by omega
  have hlt : state < 1800 := by omega
  rw [assemblyPrefixDescription_lookupTransition_eq_skeleton
    state read hne]
  exact assemblySkeletonDescription_lookupTransition_eq_scanner
    state read hlt

theorem assemblyPrefixDescription_stepConfig_eq_scanner_of_state_lt_210
    (c : Configuration) (hstate : c.state < 210) :
    AssemblyPrefixDescription.stepConfig c =
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription.stepConfig c := by
  unfold stepConfig
  rw [assemblyPrefixDescription_lookupTransition_eq_scanner_of_state_lt_210
    c.state (Tape.read c.tape) hstate]

theorem assemblyPrefixDescription_runConfig_eq_scanner_of_trace_lt_210
    (n : Nat) (c : Configuration)
    (htrace :
      forall k : Nat, k < n ->
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription.runConfig
          k c).state < 210) :
    AssemblyPrefixDescription.runConfig n c =
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription.runConfig
        n c := by
  induction n generalizing c with
  | zero =>
      rfl
  | succ n ih =>
      have hstate : c.state < 210 := by
        simpa [runConfig] using htrace 0 (Nat.zero_lt_succ n)
      simp only [runConfig]
      rw [assemblyPrefixDescription_stepConfig_eq_scanner_of_state_lt_210
        c hstate]
      cases hstep :
          DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription.stepConfig
            c with
      | none =>
          rfl
      | some next =>
          exact ih next (by
            intro k hk
            have htrace' := htrace (k + 1) (Nat.succ_lt_succ hk)
            have hrun :
                DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription.runConfig
                    (k + 1) c =
                  DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription.runConfig
                    k next := by
              simp [runConfig, hstep]
            simpa [hrun] using htrace')

theorem assemblyPrefixDescription_run_state100_tick
    (left tail : List (Option Bool)) :
    AssemblyPrefixDescription.runConfig 4
        (config 100 left
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits.map
              some)
            tail)) =
      config 120
        (List.append
          DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedTickRev
          left)
        tail := by
  cases tail <;>
    simp [AssemblyPrefixDescription,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedTickRev,
      encodeCodeSymbolAsInput, config, tapeAtCells,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keep,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.writeMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelRestart,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelHalt,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem assemblyPrefixDescription_run_state100_done
    (left tail : List (Option Bool)) :
    AssemblyPrefixDescription.runConfig 4
        (config 100 left
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.doneBits.map
              some)
            tail)) =
      config 150
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.doneBits.reverse.map
            some)
          left)
        tail := by
  cases tail <;>
    simp [AssemblyPrefixDescription,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.doneBits,
      encodeCodeSymbolAsInput, config, tapeAtCells,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keep,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.writeMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelRestart,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelHalt,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem assemblyPrefixDescription_run_state120_tick
    (left right : List (Option Bool)) :
    AssemblyPrefixDescription.runConfig 4
        (config 120 left (List.append (tickBits.map some) right)) =
      config 120 (List.append (tickBits.reverse.map some) left) right := by
  cases right <;>
  simp [AssemblyPrefixDescription, StageInputMarkedScannerDescription,
    tickBits, config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart, scanLeftToSentinelHalt,
    runConfig, stepConfig, lookupTransition, Matches, transition,
    encodeCodeSymbolAsInput, Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem assemblyPrefixDescription_run_state120_done
    (left right : List (Option Bool)) :
    AssemblyPrefixDescription.runConfig 4
        (config 120 left (List.append (doneBits.map some) right)) =
      config 130 (List.append (doneBits.reverse.map some) left) right := by
  cases right <;>
  simp [AssemblyPrefixDescription, StageInputMarkedScannerDescription,
    doneBits, config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart, scanLeftToSentinelHalt,
    runConfig, stepConfig, lookupTransition, Matches, transition,
    encodeCodeSymbolAsInput, Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem assemblyPrefixDescription_run_state120_stageNat
    (n : Nat) (left right : List (Option Bool)) :
    AssemblyPrefixDescription.runConfig (4 * n + 4)
        (config 120 left
          (List.append ((stageNatBits n).map some) right)) =
      config 130 (List.append ((stageNatBits n).reverse.map some) left)
        right := by
  induction n generalizing left with
  | zero =>
      simpa [stageNatBits_zero] using
        assemblyPrefixDescription_run_state120_done left right
  | succ n ih =>
      rw [show 4 * (n + 1) + 4 = 4 + (4 * n + 4) by
        omega]
      rw [runConfig_add]
      rw [show
          List.append ((stageNatBits (n + 1)).map some) right =
            List.append (tickBits.map some)
              (List.append ((stageNatBits n).map some) right) by
        simp [stageNatBits_succ, tickBits, encodeCodeSymbolAsInput]]
      rw [assemblyPrefixDescription_run_state120_tick]
      rw [ih]
      simp [stageNatBits_succ, tickBits, encodeCodeSymbolAsInput,
        List.map_append, List.append_assoc]

theorem assemblyPrefixDescription_run_state130_markedCell
    (b : Bool) (left right : List (Option Bool)) :
    AssemblyPrefixDescription.runConfig 4
        (config 130 left
          (List.append ((markedCellBits b).map some) right)) =
      config 130
        (List.append ((markedCellBits b).reverse.map some) left)
        right := by
  cases b <;> cases right <;>
  simp [AssemblyPrefixDescription, StageInputMarkedScannerDescription,
    markedCellBits, config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart, scanLeftToSentinelHalt,
    runConfig, stepConfig, lookupTransition, Matches, transition,
    Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem assemblyPrefixDescription_run_state130_markedCells
    (processed : Word Bool) (left right : List (Option Bool)) :
    AssemblyPrefixDescription.runConfig (4 * processed.length)
        (config 130 left
          (List.append ((markedCellsBits processed).map some) right)) =
      config 130
        (List.append ((markedCellsBits processed).reverse.map some) left)
        right := by
  induction processed generalizing left with
  | nil =>
      rfl
  | cons b rest ih =>
      rw [show 4 * (b :: rest).length = 4 + 4 * rest.length by
        simp
        omega]
      rw [runConfig_add]
      rw [show
          List.append ((markedCellsBits (b :: rest)).map some) right =
            List.append ((markedCellBits b).map some)
              (List.append ((markedCellsBits rest).map some) right) by
        simp [markedCellsBits, List.map_append, List.append_assoc]]
      rw [assemblyPrefixDescription_run_state130_markedCell]
      rw [ih]
      simp [markedCellsBits, List.reverse_append, List.map_append,
        List.append_assoc]

theorem assemblyPrefixDescription_run_state130_currentCell
    (b : Bool) (left right : List (Option Bool)) :
    AssemblyPrefixDescription.runConfig 6
        (config 130 left (List.append ((cellBits b).map some) right)) =
      config 140 (some true :: some true :: left)
        (some b :: some (!b) :: right) := by
  cases b <;> cases right <;>
  simp [AssemblyPrefixDescription, StageInputMarkedScannerDescription,
    cellBits, config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart, scanLeftToSentinelHalt,
    runConfig, stepConfig, lookupTransition, Matches, transition,
    encodeCodeSymbolAsInput, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    Tape.moveRight]

theorem assemblyPrefixDescription_run_state140_returnToLengthMarker
    (scanRev : Word Bool) (headBit : Bool)
    (leftTail right : List (Option Bool)) :
    AssemblyPrefixDescription.runConfig (scanRev.length + 4)
        (config 140
          (List.append (scanRev.map some)
            (none :: some true :: leftTail))
          (some headBit :: right)) =
      config 100 (some false :: some true :: leftTail)
        (List.append (scanRev.reverse.map some)
          (some headBit :: right)) := by
  induction scanRev generalizing headBit right with
  | nil =>
      cases headBit <;> cases right <;>
      simp [AssemblyPrefixDescription, StageInputMarkedScannerDescription,
        config, tapeAtCells, keep, keepMove, writeMove,
        scanLeftToSentinelRestart, scanLeftToSentinelHalt,
        runConfig, stepConfig, lookupTransition, Matches, transition,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons b rest ih =>
      rw [show (b :: rest).length + 4 = 1 + (rest.length + 4) by
        simp
        omega]
      rw [runConfig_add]
      change
        AssemblyPrefixDescription.runConfig (rest.length + 4)
          (AssemblyPrefixDescription.runConfig 1
            (config 140
              (some b :: List.append (List.map some rest)
                (none :: some true :: leftTail))
              (some headBit :: right))) =
          config 100 (some false :: some true :: leftTail)
            (List.append (List.map some (b :: rest).reverse)
              (some headBit :: right))
      rw [show
          AssemblyPrefixDescription.runConfig 1
            (config 140
              (some b :: List.append (List.map some rest)
                (none :: some true :: leftTail))
              (some headBit :: right)) =
          config 140
            (List.append (List.map some rest)
              (none :: some true :: leftTail))
            (some b :: some headBit :: right) by
        cases headBit <;> cases b <;> cases right <;>
        simp [AssemblyPrefixDescription, StageInputMarkedScannerDescription,
          config, tapeAtCells, keep, keepMove, writeMove,
          scanLeftToSentinelRestart, scanLeftToSentinelHalt,
          runConfig, stepConfig, lookupTransition, Matches, transition,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft]]
      rw [ih]
      simp [List.map_append, List.append_assoc]

theorem assemblyPrefixDescription_run_mark_current_to_state100_withBase_cells
    (processed : Word Bool) (b : Bool) (rest : Word Bool)
    (tailCells leftTail : List (Option Bool)) :
    exists steps : Nat,
      AssemblyPrefixDescription.runConfig steps
          (markingState120WithTailCellsAndBase
            processed b rest tailCells leftTail) =
        state100AfterMarkedWithTailCellsAndBase
          processed b rest tailCells leftTail := by
  let scanRev := markingReturnScanRev processed rest
  refine
    ⟨(4 * rest.length + 4) +
        (4 * processed.length + (6 + (scanRev.length + 4))), ?_⟩
  rw [runConfig_add]
  unfold markingState120WithTailCellsAndBase
  rw [assemblyPrefixDescription_run_state120_stageNat]
  rw [runConfig_add]
  rw [assemblyPrefixDescription_run_state130_markedCells]
  rw [runConfig_add]
  rw [assemblyPrefixDescription_run_state130_currentCell]
  have hreturn :=
    assemblyPrefixDescription_run_state140_returnToLengthMarker
      scanRev b
      (List.append
        (activeLengthPrefixTail processed.length)
        leftTail)
      (some (!b) ::
        List.append ((cellsBits rest).map some) tailCells)
  have hprefix :
      some false :: some true ::
          List.append (activeLengthPrefixTail processed.length) leftTail =
        List.append (finishLengthPrefixRev processed.length) leftTail := by
    have h :=
      congrArg (fun xs => List.append xs leftTail)
        (activeLengthPrefixRestored processed.length)
    simpa [List.append_assoc] using h
  rw [hprefix] at hreturn
  cases b <;>
  simpa [state100AfterMarkedWithTailCellsAndBase, scanRev,
    markingReturnScanRev, activeLengthPrefixRev,
    activeLengthPrefixRestored, markedCellBits,
    List.map_append, List.reverse_append, List.append_assoc]
    using hreturn

theorem assemblyPrefixDescription_run_marking_loop_from_state120_withBase_cells
    (processed : Word Bool) (b : Bool) (rest : Word Bool)
    (tailCells leftTail : List (Option Bool)) :
    exists steps : Nat,
      AssemblyPrefixDescription.runConfig steps
          (markingState120WithTailCellsAndBase
            processed b rest tailCells leftTail) =
        finishStartConfigWithTailCellsAndBase
          (List.append processed (b :: rest)) tailCells leftTail := by
  induction rest generalizing processed b with
  | nil =>
      rcases assemblyPrefixDescription_run_mark_current_to_state100_withBase_cells
          processed b [] tailCells leftTail with
        ⟨markSteps, hmark⟩
      refine ⟨markSteps + 4, ?_⟩
      rw [runConfig_add]
      rw [hmark]
      unfold state100AfterMarkedWithTailCellsAndBase
      change
        AssemblyPrefixDescription.runConfig 4
            (config 100
              (List.append (finishLengthPrefixRev processed.length) leftTail)
              (List.append (doneBits.map some)
                (List.append ((markedCellsBits processed).map some)
                  (List.append ((markedCellBits b).map some) tailCells)))) =
          finishStartConfigWithTailCellsAndBase
            (List.append processed [b]) tailCells leftTail
      rw [assemblyPrefixDescription_run_state100_done]
      unfold finishStartConfigWithTailCellsAndBase
      rw [markedCellsBits_append_single_map]
      simp [finishStartLeft, List.length_append, List.append_assoc]
  | cons next rest ih =>
      rcases assemblyPrefixDescription_run_mark_current_to_state100_withBase_cells
          processed b (next :: rest) tailCells leftTail with
        ⟨markSteps, hmark⟩
      rcases ih (List.append processed [b]) next with
        ⟨recSteps, hrec⟩
      refine ⟨markSteps + 4 + recSteps, ?_⟩
      rw [show markSteps + 4 + recSteps = markSteps + (4 + recSteps) by
        omega]
      rw [runConfig_add]
      rw [hmark]
      rw [runConfig_add]
      unfold state100AfterMarkedWithTailCellsAndBase
      rw [show
          (stageNatBits (next :: rest).length).map some =
            List.append (tickBits.map some)
              ((stageNatBits rest.length).map some) by
        simp [stageNatBits_succ, tickBits, encodeCodeSymbolAsInput]]
      change
        AssemblyPrefixDescription.runConfig recSteps
            (AssemblyPrefixDescription.runConfig 4
              (config 100
                (List.append (finishLengthPrefixRev processed.length) leftTail)
                (List.append (tickBits.map some)
                  (List.append ((stageNatBits rest.length).map some)
                    (List.append ((markedCellsBits processed).map some)
                      (List.append ((markedCellBits b).map some)
                        (List.append ((cellsBits (next :: rest)).map some)
                          tailCells))))))) =
          finishStartConfigWithTailCellsAndBase
            (List.append processed (b :: next :: rest)) tailCells leftTail
      rw [assemblyPrefixDescription_run_state100_tick]
      unfold markingState120WithTailCellsAndBase at hrec
      rw [markedCellsBits_append_single_map] at hrec
      simpa [activeLengthPrefixRev_succ, cellsBits_cons,
        List.length_append, List.map_append, List.append_assoc] using hrec

theorem assemblyPrefixDescription_run_state120_bool_tail_to_finish_withBase_cells
    (b : Bool) (rest : Word Bool) (tailCells leftTail : List (Option Bool)) :
    exists steps : Nat,
      AssemblyPrefixDescription.runConfig steps
          (config 120
            (List.append [none, some true, none, some false] leftTail)
            (List.append
              ((stageNatBits rest.length).map some)
              (List.append
                ((cellBits b).map some)
                (List.append ((cellsBits rest).map some) tailCells)))) =
        finishStartConfigWithTailCellsAndBase
          (b :: rest) tailCells leftTail := by
  rcases assemblyPrefixDescription_run_marking_loop_from_state120_withBase_cells
      ([] : Word Bool) b rest tailCells leftTail with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  simpa [markingState120WithTailCellsAndBase,
    activeLengthPrefixRev_zero] using hsteps

theorem assemblyPrefixDescription_run_state150_markedCell
    (b : Bool) (left right : List (Option Bool)) :
    AssemblyPrefixDescription.runConfig 4
        (config 150 left
          (List.append ((markedCellBits b).map some) right)) =
      config 150 (List.append ((cellBits b).reverse.map some) left)
        right := by
  cases b <;> cases right <;>
  simp [AssemblyPrefixDescription, StageInputMarkedScannerDescription,
    markedCellBits, cellBits, config, tapeAtCells, keep, keepMove,
    writeMove, scanLeftToSentinelRestart, scanLeftToSentinelHalt,
    runConfig, stepConfig, lookupTransition, Matches, transition,
    encodeCodeSymbolAsInput, Tape.read, Tape.write, Tape.move,
    Tape.moveRight]

theorem assemblyPrefixDescription_run_state150_markedCells
    (processed : Word Bool) (left right : List (Option Bool)) :
    AssemblyPrefixDescription.runConfig (4 * processed.length)
        (config 150 left
          (List.append ((markedCellsBits processed).map some) right)) =
      config 150
        (List.append ((cellsBits processed).reverse.map some) left)
        right := by
  induction processed generalizing left with
  | nil =>
      rfl
  | cons b rest ih =>
      rw [show 4 * (b :: rest).length = 4 + 4 * rest.length by
        simp
        omega]
      rw [runConfig_add]
      rw [show
          List.append ((markedCellsBits (b :: rest)).map some) right =
            List.append ((markedCellBits b).map some)
              (List.append ((markedCellsBits rest).map some) right) by
        simp [markedCellsBits, List.map_append, List.append_assoc]]
      rw [assemblyPrefixDescription_run_state150_markedCell]
      rw [ih]
      simp [List.reverse_append, List.map_append, List.append_assoc]

theorem assemblyPrefixDescription_run_state150_to_state160
    (left tail : List (Option Bool)) :
    AssemblyPrefixDescription.runConfig 2
        (config 150 left (some false :: some false :: tail)) =
      config 160 left (some false :: none :: tail) := by
  cases tail <;>
  simp [AssemblyPrefixDescription, StageInputMarkedScannerDescription,
    config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart, scanLeftToSentinelHalt,
    runConfig, stepConfig, lookupTransition, Matches, transition,
    Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem assemblyPrefixDescription_run_finish_restore_cells_tailCells_withBase
    (w : Word Bool) (tailCells leftTail : List (Option Bool)) :
    AssemblyPrefixDescription.runConfig (4 * w.length + 2)
        (finishStartConfigWithTailCellsAndBase w
          (some false :: some false :: tailCells) leftTail) =
      state160AfterRestoreWithTailCellsAndBase w tailCells leftTail := by
  rw [runConfig_add]
  change
    AssemblyPrefixDescription.runConfig 2
        (AssemblyPrefixDescription.runConfig (4 * w.length)
          (config 150
            (List.append (finishStartLeft w) leftTail)
            (List.append ((markedCellsBits w).map some)
              (some false :: some false :: tailCells)))) =
      state160AfterRestoreWithTailCellsAndBase w tailCells leftTail
  rw [assemblyPrefixDescription_run_state150_markedCells]
  rw [assemblyPrefixDescription_run_state150_to_state160]
  simp [state160AfterRestoreWithTailCellsAndBase]

theorem assemblyPrefixDescription_run_state160_some_cons
    (b : Bool) (cell : Option Bool)
    (left right : List (Option Bool)) :
    AssemblyPrefixDescription.runConfig 1
        (config 160 (cell :: left) (some b :: right)) =
      config 160 left (cell :: some b :: right) := by
  cases b <;> cases cell <;> cases right <;>
  simp [AssemblyPrefixDescription, StageInputMarkedScannerDescription,
    config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart, scanLeftToSentinelHalt,
    runConfig, stepConfig, lookupTransition, Matches, transition,
    Tape.read, Tape.write, Tape.move, Tape.moveLeft]

theorem assemblyPrefixDescription_run_state160_bits_to_boundary
    (bitsToRight : Word Bool) (boundary : Option Bool)
    (leftTail right : List (Option Bool)) :
    AssemblyPrefixDescription.runConfig bitsToRight.length
        (state160ScanConfig bitsToRight boundary leftTail right) =
      config 160 leftTail
        (boundary :: List.append (bitsToRight.reverse.map some) right) := by
  induction bitsToRight generalizing boundary leftTail right with
  | nil =>
      rfl
  | cons b rest ih =>
      rw [show (b :: rest).length = 1 + rest.length by
        simp
        omega]
      rw [runConfig_add]
      cases rest with
      | nil =>
          change
            AssemblyPrefixDescription.runConfig 0
                (AssemblyPrefixDescription.runConfig 1
                  (config 160 (boundary :: leftTail) (some b :: right))) =
              config 160 leftTail (boundary :: some b :: right)
          rw [assemblyPrefixDescription_run_state160_some_cons]
          rfl
      | cons b' rest =>
          change
            AssemblyPrefixDescription.runConfig (b' :: rest).length
                (AssemblyPrefixDescription.runConfig 1
                  (config 160
                    (some b' :: List.append (rest.map some)
                      (boundary :: leftTail))
                    (some b :: right))) =
              config 160 leftTail
                (boundary ::
                  List.append ((b :: b' :: rest).reverse.map some) right)
          rw [assemblyPrefixDescription_run_state160_some_cons]
          have h := ih boundary leftTail (some b :: right)
          simp [state160ScanConfig] at h
          simpa [List.map_append, List.append_assoc] using h

theorem assemblyPrefixDescription_run_state160_none_to_state161
    (cell : Option Bool) (left right : List (Option Bool)) :
    AssemblyPrefixDescription.runConfig 1
        (config 160 (cell :: left) (none :: right)) =
      config 161 left (cell :: none :: right) := by
  cases cell <;> cases right <;>
  simp [AssemblyPrefixDescription, StageInputMarkedScannerDescription,
    config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart, scanLeftToSentinelHalt,
    runConfig, stepConfig, lookupTransition, Matches, transition,
    Tape.read, Tape.write, Tape.move, Tape.moveLeft]

theorem assemblyPrefixDescription_run_state161_false_to_state170_withBase
    (left right : List (Option Bool)) :
    AssemblyPrefixDescription.runConfig 1
        (config 161 left (some false :: right)) =
      config 170 (some false :: left) right := by
  cases right <;>
  simp [AssemblyPrefixDescription, StageInputMarkedScannerDescription,
    config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart, scanLeftToSentinelHalt,
    runConfig, stepConfig, lookupTransition, Matches, transition,
    Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem assemblyPrefixDescription_run_state170_none_to_state180_withBase
    (left right : List (Option Bool)) :
    AssemblyPrefixDescription.runConfig 1
        (config 170 (some false :: left) (none :: right)) =
      config 180 (none :: some false :: left) right := by
  cases right <;>
  simp [AssemblyPrefixDescription, StageInputMarkedScannerDescription,
    config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart, scanLeftToSentinelHalt,
    runConfig, stepConfig, lookupTransition, Matches, transition,
    Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem assemblyPrefixDescription_run_finish_scan_left_to_append_tailCells_withBase
    (b : Bool) (rest : Word Bool) (tailCells leftTail : List (Option Bool)) :
    exists steps : Nat,
      AssemblyPrefixDescription.runConfig steps
          (state160AfterRestoreWithTailCellsAndBase
            (b :: rest) tailCells leftTail) =
        appendBlankStartConfigWithTailCellsAndBase
          (b :: rest) tailCells leftTail := by
  let bits := finishScanBits (b :: rest)
  let scanRight := none :: tailCells
  have hstart :
      state160AfterRestoreWithTailCellsAndBase
          (b :: rest) tailCells leftTail =
        state160ScanConfig bits none (some false :: leftTail) scanRight := by
    cases b <;>
    simp [bits, scanRight, finishScanBits,
      state160AfterRestoreWithTailCellsAndBase, finishStartLeft,
      finishLengthPrefixRev_eq_scanBits, state160ScanConfig,
      cellsBits_cons, cellBits,
      List.map_append, List.reverse_append, List.append_assoc]
  refine ⟨bits.length + 3, ?_⟩
  rw [show bits.length + 3 = bits.length + (1 + (1 + 1)) by
    omega]
  rw [runConfig_add]
  rw [hstart]
  rw [assemblyPrefixDescription_run_state160_bits_to_boundary]
  rw [runConfig_add]
  rw [assemblyPrefixDescription_run_state160_none_to_state161]
  rw [runConfig_add]
  rw [assemblyPrefixDescription_run_state161_false_to_state170_withBase]
  rw [assemblyPrefixDescription_run_state170_none_to_state180_withBase]
  simp [appendBlankStartConfigWithTailCellsAndBase, bits, scanRight,
    finishScanBits_reverse_nonempty, List.map_append, List.append_assoc]

theorem assemblyPrefixDescription_run_state180_some
    (b : Bool) (left right : List (Option Bool)) :
    AssemblyPrefixDescription.runConfig 1
        (config 180 left (some b :: right)) =
      config 180 (some b :: left) right := by
  cases b <;> cases right <;>
  simp [AssemblyPrefixDescription, StageInputMarkedScannerDescription,
    config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart, scanLeftToSentinelHalt,
    runConfig, stepConfig, lookupTransition, Matches, transition,
    Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem assemblyPrefixDescription_run_state180_bits
    (bits : Word Bool) (left right : List (Option Bool)) :
    AssemblyPrefixDescription.runConfig bits.length
        (config 180 left (List.append (bits.map some) right)) =
      config 180 (List.append (bits.reverse.map some) left) right := by
  induction bits generalizing left right with
  | nil =>
      rfl
  | cons b rest ih =>
      change
        AssemblyPrefixDescription.runConfig (rest.length + 1)
            (config 180 left
              (some b :: List.append (rest.map some) right)) =
          config 180
            (List.append ((b :: rest).reverse.map some) left) right
      rw [show rest.length + 1 = 1 + rest.length by
        omega]
      rw [runConfig_add]
      rw [assemblyPrefixDescription_run_state180_some]
      rw [ih]
      simp [List.map_append, List.append_assoc]

theorem assemblyPrefixDescription_run_state180_none_cons
    (cell : Option Bool) (left right : List (Option Bool)) :
    AssemblyPrefixDescription.runConfig 1
        (config 180 (cell :: left) (none :: right)) =
      config 200 left (cell :: some false :: right) := by
  cases cell <;>
  simp [AssemblyPrefixDescription, StageInputMarkedScannerDescription,
    config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart, scanLeftToSentinelHalt,
    runConfig, stepConfig, lookupTransition, Matches, transition,
    Tape.read, Tape.write, Tape.move, Tape.moveLeft]

theorem assemblyPrefixDescription_run_append_blank_to_state200_tailCells_withBase
    (b : Bool) (rest : Word Bool) (tailCells leftTail : List (Option Bool)) :
    exists steps : Nat,
      AssemblyPrefixDescription.runConfig steps
          (appendBlankStartConfigWithTailCellsAndBase
            (b :: rest) tailCells leftTail) =
        config 200
          (List.append ((stageInputSecondBitTailPrefix (b :: rest)).reverse.map some)
            (none :: some false :: leftTail))
          (some false :: some false :: tailCells) := by
  let tailPrefix := stageInputSecondBitTailPrefix (b :: rest)
  refine ⟨tailPrefix.length + 2, ?_⟩
  rw [show tailPrefix.length + 2 = tailPrefix.length + (1 + 1) by
    omega]
  rw [runConfig_add]
  unfold appendBlankStartConfigWithTailCellsAndBase
  change
    AssemblyPrefixDescription.runConfig (1 + 1)
        (AssemblyPrefixDescription.runConfig tailPrefix.length
          (config 180 (List.append [none, some false] leftTail)
            (List.append (tailPrefix.map some)
              (some false :: none :: tailCells)))) =
      config 200
        (List.append (tailPrefix.reverse.map some)
          (none :: some false :: leftTail))
        (some false :: some false :: tailCells)
  rw [assemblyPrefixDescription_run_state180_bits]
  rw [runConfig_add]
  rw [assemblyPrefixDescription_run_state180_some]
  rw [assemblyPrefixDescription_run_state180_none_cons]
  simp

theorem assemblyPrefixDescription_run_finish_cells_false_false_to_state200_withBase
    (b : Bool) (rest : Word Bool) (tailCells leftTail : List (Option Bool)) :
    exists steps : Nat,
      AssemblyPrefixDescription.runConfig steps
          (finishStartConfigWithTailCellsAndBase
            (b :: rest) (some false :: some false :: tailCells) leftTail) =
        config 200
          (List.append
            ((stageInputSecondBitTailPrefix (b :: rest)).reverse.map some)
            (none :: some false :: leftTail))
          (some false :: some false :: tailCells) := by
  rcases assemblyPrefixDescription_run_finish_scan_left_to_append_tailCells_withBase
      b rest tailCells leftTail with
    ⟨scanSteps, hscan⟩
  rcases assemblyPrefixDescription_run_append_blank_to_state200_tailCells_withBase
      b rest tailCells leftTail with
    ⟨appendSteps, happend⟩
  refine
    ⟨(4 * (b :: rest).length + 2) + scanSteps + appendSteps, ?_⟩
  rw [show
      (4 * (b :: rest).length + 2) + scanSteps + appendSteps =
        (4 * (b :: rest).length + 2) +
          (scanSteps + appendSteps) by
    omega]
  rw [runConfig_add]
  rw [assemblyPrefixDescription_run_finish_restore_cells_tailCells_withBase]
  rw [runConfig_add]
  rw [hscan]
  exact happend

theorem assemblyPrefixDescription_run_nonempty_stageInput_to_sourceRest_boundary_cells
    (b : Bool) (rest : Word Bool) (stage : Nat)
    (sourceRestCells : List (Option Bool)) :
    exists steps : Nat,
      AssemblyPrefixDescription.runConfig steps
          (config AssemblyPrefixDescription.start []
            (List.append
              (List.map some
                (List.append
                  (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
                  (DovetailInitialLayoutInitializer.stageInputBits
                    (b :: rest) stage)))
              sourceRestCells)) =
        config 210
          (List.append
            ((stageNatBits stage).reverse.map some)
            (List.append
              ((stageInputSecondBitTailPrefix (b :: rest)).reverse.map some)
              (List.append [none, some false] transitionPrefixLeftTail)))
          sourceRestCells := by
  rcases stageNatBits_false_false_tail stage with
    ⟨stageTail, hstageTail⟩
  rcases assemblyPrefixDescription_run_state120_bool_tail_to_finish_withBase_cells
      b rest
      (List.append ((stageNatBits stage).map some) sourceRestCells)
      transitionPrefixLeftTail with
    ⟨markSteps, hmark⟩
  rcases assemblyPrefixDescription_run_finish_cells_false_false_to_state200_withBase
      b rest (List.append (stageTail.map some) sourceRestCells)
      transitionPrefixLeftTail with
    ⟨finishSteps, hfinish⟩
  refine ⟨6 + (6 + (markSteps + finishSteps + (4 * stage + 4))), ?_⟩
  rw [show
      6 + (6 + (markSteps + finishSteps + (4 * stage + 4))) =
        6 + (6 + (markSteps + (finishSteps + (4 * stage + 4)))) by
    omega]
  rw [runConfig_add]
  rw [assemblyPrefixDescription_run_prefix_to_stageInput_tail_cells]
  rw [stageInputSecondBitTail_cons]
  rw [show
      List.append
          ((true :: false ::
            List.append (stageNatBits rest.length)
              (List.append (cellBits b)
                (List.append (cellsBits rest) (stageNatBits stage)))).map some)
          sourceRestCells =
        some true :: some false ::
          List.append ((stageNatBits rest.length).map some)
            (List.append ((cellBits b).map some)
              (List.append ((cellsBits rest).map some)
                (List.append ((stageNatBits stage).map some)
                  sourceRestCells))) by
    simp [List.map_append, List.append_assoc]]
  change
    AssemblyPrefixDescription.runConfig
        (6 + (markSteps + (finishSteps + (4 * stage + 4))))
        (markedTailStartConfigWithBaseCells transitionPrefixLeftTail
          (some true :: some false ::
            List.append ((stageNatBits rest.length).map some)
              (List.append ((cellBits b).map some)
                (List.append ((cellsBits rest).map some)
                  (List.append ((stageNatBits stage).map some)
                    sourceRestCells))))) =
      config 210
        (List.append ((stageNatBits stage).reverse.map some)
          (List.append ((stageInputSecondBitTailPrefix (b :: rest)).reverse.map some)
            (List.append [none, some false] transitionPrefixLeftTail)))
        sourceRestCells
  rw [runConfig_add]
  rw [assemblyPrefixDescription_run_marked_tail_tick_to_state120_withBase_cells]
  rw [runConfig_add]
  rw [hmark]
  rw [hstageTail]
  rw [runConfig_add]
  have htailCells :
      List.append (List.map some (false :: false :: stageTail))
          sourceRestCells =
        some false :: some false ::
          List.append (stageTail.map some) sourceRestCells := by
    simp
  rw [htailCells]
  rw [hfinish]
  rw [← hstageTail]
  have hright :
      some false :: some false ::
          List.append (stageTail.map some) sourceRestCells =
        List.append ((stageNatBits stage).map some) sourceRestCells := by
    rw [hstageTail]
    simp
  rw [hright]
  rw [assemblyPrefixDescription_run_state200_stageNat_to_state210]
  simp

theorem assemblyPrefixDescription_haltsFrom_empty_stageInput_to_sourceRest_boundary_checked
    (stage : Nat) (sourceRestBits : Word Bool) :
    AssemblyPrefixDescription.HaltsFromTape
      (tapeAtCells []
        (List.append
          (List.map some
            (List.append
              (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
              (List.append
                (DovetailInitialLayoutInitializer.stageInputBits
                  ([] : Word Bool) stage)
                sourceRestBits)))
          [none]))
      (tapeAtCells
        (assemblySourceRestBoundaryLeftRev ([] : Word Bool) stage)
        (List.append (sourceRestBits.map some) [none])) := by
  rcases
      assemblyPrefixDescription_run_empty_stageInput_to_sourceRest_boundary_cells
        stage (List.append (sourceRestBits.map some) [none]) with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  unfold MachineDescription.HaltsFromTapeIn
  constructor
  · simpa [AssemblyPrefixDescription, config,
      assemblySourceRestBoundaryLeftRev, List.map_append,
      List.append_assoc] using
      congrArg Configuration.state hsteps
  · simpa [AssemblyPrefixDescription, config,
      assemblySourceRestBoundaryLeftRev, List.map_append,
      List.append_assoc] using
      congrArg Configuration.tape hsteps

theorem assemblyPrefixDescription_haltsFrom_nonempty_stageInput_to_sourceRest_boundary_checked
    (b : Bool) (rest : Word Bool) (stage : Nat)
    (sourceRestBits : Word Bool) :
    AssemblyPrefixDescription.HaltsFromTape
      (tapeAtCells []
        (List.append
          (List.map some
            (List.append
              (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
              (List.append
                (DovetailInitialLayoutInitializer.stageInputBits
                  (b :: rest) stage)
                sourceRestBits)))
          [none]))
      (tapeAtCells
        (assemblySourceRestBoundaryLeftRev (b :: rest) stage)
        (List.append (sourceRestBits.map some) [none])) := by
  rcases assemblyPrefixDescription_run_nonempty_stageInput_to_sourceRest_boundary_cells
      b rest stage (List.append (sourceRestBits.map some) [none]) with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  unfold MachineDescription.HaltsFromTapeIn
  constructor
  · simpa [AssemblyPrefixDescription, config,
      assemblySourceRestBoundaryLeftRev, List.map_append,
      List.append_assoc] using congrArg Configuration.state hsteps
  · simpa [AssemblyPrefixDescription, config,
      assemblySourceRestBoundaryLeftRev, List.map_append,
      List.append_assoc] using congrArg Configuration.tape hsteps

theorem assemblyPrefixDescription_haltsFrom_stageInput_to_sourceRest_boundary_checked
    (w : Word Bool) (stage : Nat) (sourceRestBits : Word Bool) :
    AssemblyPrefixDescription.HaltsFromTape
      (tapeAtCells []
        (List.append
          (List.map some
            (List.append
              (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
              (List.append
                (DovetailInitialLayoutInitializer.stageInputBits w stage)
                sourceRestBits)))
          [none]))
      (tapeAtCells (assemblySourceRestBoundaryLeftRev w stage)
        (List.append (sourceRestBits.map some) [none])) := by
  cases w with
  | nil =>
      exact assemblyPrefixDescription_haltsFrom_empty_stageInput_to_sourceRest_boundary_checked
        stage sourceRestBits
  | cons b rest =>
      exact assemblyPrefixDescription_haltsFrom_nonempty_stageInput_to_sourceRest_boundary_checked
        b rest stage sourceRestBits

def selectedProjectionInputQuoterPrefixBoundaryTape
    (L : DovetailLayout) : Tape Bool :=
  tapeAtCells
    (assemblySourceRestBoundaryLeftRev L.input L.stage)
    (List.append
      ((SelectedProjectionTailProjector.sourceRestFieldBits L).map some)
      [none])

theorem assemblyPrefixDescription_haltsFrom_exactSourceTape_to_prefixBoundary
    (L : DovetailLayout) :
    AssemblyPrefixDescription.HaltsFromTape
      (SelectedProjectionInputQuoterExactSourceTape L)
      (selectedProjectionInputQuoterPrefixBoundaryTape L) := by
  rw [SelectedProjectionInputQuoterExactSourceTape,
    selectedProjectionInputQuoterPrefixBoundaryTape]
  exact
    assemblyPrefixDescription_haltsFrom_stageInput_to_sourceRest_boundary_checked
      L.input L.stage
      (SelectedProjectionTailProjector.sourceRestFieldBits L)

def SelectedProjectionInputQuoterPrefixSpec
    (pref : MachineDescription) : Prop :=
  pref.SubroutineReady ∧
    forall L : DovetailLayout,
      pref.HaltsFromTape
        (SelectedProjectionInputQuoterExactSourceTape L)
        (selectedProjectionInputQuoterPrefixBoundaryTape L)

def SelectedProjectionInputQuoterPrefixConstruction : Prop :=
  exists pref : MachineDescription,
    SelectedProjectionInputQuoterPrefixSpec pref

theorem selectedProjectionInputQuoterPrefixConstruction :
    SelectedProjectionInputQuoterPrefixConstruction := by
  refine ⟨AssemblyPrefixDescription, ?_⟩
  constructor
  · exact assemblyPrefixDescription_subroutineReady
  · exact assemblyPrefixDescription_haltsFrom_exactSourceTape_to_prefixBoundary

def selectedProjectionInputQuoterPostBoundarySourceTape
    (L : DovetailLayout) : Tape Bool :=
  Tape.move Direction.left
    (Tape.move Direction.right
      (selectedProjectionInputQuoterPrefixBoundaryTape L))

def SelectedProjectionInputQuoterPostBoundarySpec
    (post : MachineDescription) : Prop :=
  post.SubroutineReady ∧
    forall L : DovetailLayout,
      post.HaltsFromTape
        (selectedProjectionInputQuoterPostBoundarySourceTape L)
        (SelectedProjectionInputQuoterExactTargetTape L)

def SelectedProjectionInputQuoterPostBoundaryConstruction : Prop :=
  exists post : MachineDescription,
    SelectedProjectionInputQuoterPostBoundarySpec post

theorem tapeAtCells_move_left_move_right_cons_cons
    (left : List (Option Bool)) (head next : Option Bool)
    (right : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (tapeAtCells left (head :: next :: right))) =
      tapeAtCells left (head :: next :: right) := by
  simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem sourceRestFieldBits_cons_cons
    (L : DovetailLayout) :
    exists head : Bool,
    exists next : Bool,
    exists right : Word Bool,
      SelectedProjectionTailProjector.sourceRestFieldBits L =
        head :: next :: right := by
  rcases
      SelectedProjectionTailProjector.stageNatBits_cons_cons
        L.acceptConfig.state with
    ⟨head, next, stateTail, hstate⟩
  refine
    ⟨head, next,
      List.append stateTail
        (CanonicalLayouts.DovetailLayoutScanner.tapeFieldBits
          L.acceptConfig.tape
          (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
            L.rejectConfig
            (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
              L.acceptHit
              (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
                L.rejectHit [])))), ?_⟩
  simp [SelectedProjectionTailProjector.sourceRestFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits,
    hstate]

theorem selectedProjectionInputQuoterPostBoundarySourceTape_eq_prefixBoundaryTape
    (L : DovetailLayout) :
    selectedProjectionInputQuoterPostBoundarySourceTape L =
      selectedProjectionInputQuoterPrefixBoundaryTape L := by
  rcases sourceRestFieldBits_cons_cons L with
    ⟨head, next, right, hsource⟩
  rw [selectedProjectionInputQuoterPostBoundarySourceTape,
    selectedProjectionInputQuoterPrefixBoundaryTape, hsource]
  simp [List.map_cons]
  exact
    tapeAtCells_move_left_move_right_cons_cons
      (assemblySourceRestBoundaryLeftRev L.input L.stage)
      (some head) (some next)
      (List.append (right.map some) [none])

theorem selectedProjectionInputQuoterPostBoundarySourceTape_eq_sourceRestBoundary
    (L : DovetailLayout) :
    selectedProjectionInputQuoterPostBoundarySourceTape L =
      tapeAtCells
        (assemblySourceRestBoundaryLeftRev L.input L.stage)
        (List.append
          ((SelectedProjectionTailProjector.sourceRestFieldBits L).map some)
          [none]) := by
  rw [selectedProjectionInputQuoterPostBoundarySourceTape_eq_prefixBoundaryTape,
    selectedProjectionInputQuoterPrefixBoundaryTape]

theorem preservingCellPassDescription_haltsFrom_postBoundarySourceTape
    (L : DovetailLayout) :
    PreservingCellPassDescription.HaltsFromTape
      (selectedProjectionInputQuoterPostBoundarySourceTape L)
      (preservingCellPassHaltTape
        (assemblySourceRestBoundaryLeftRev L.input L.stage)
        (SelectedProjectionTailProjector.sourceRestFieldBits L) []) := by
  rw [selectedProjectionInputQuoterPostBoundarySourceTape_eq_sourceRestBoundary]
  rcases sourceRestFieldBits_cons_cons L with
    ⟨head, next, right, hsource⟩
  rw [hsource]
  simpa [List.map_cons] using
    preservingCellPassDescription_haltsFrom_nonempty_cells_oneBlank
      (assemblySourceRestBoundaryLeftRev L.input L.stage)
      head (next :: right)

theorem selectedProjectionInputQuoterExactTargetTape_eq_sourceTape_outputPrefix
    (L : DovetailLayout) :
    SelectedProjectionInputQuoterExactTargetTape L =
      SelectedProjectionTailProjector.sourceTape L
        ((SelectedProjectionTailProjector.outputPrefixStageInputSourceRestFieldBits
          L).reverse.map some) := by
  rw [SelectedProjectionInputQuoterExactTargetTape,
    SelectedProjectionTailProjector.sourceTape,
    SelectedProjectionTailProjector.sourceFieldBits_eq_stageNatBits_sourceRestFieldBits]

def selectedProjectionInputQuoterRawCellQuoteTargetTape
    (L : DovetailLayout) : Tape Bool :=
  tapeAtCells
    ((List.append
      (encodeCodeSymbolAsInput MachineCodeSymbol.header)
      (List.append
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          (ParsedLayoutBits L).length)
        (preservingCellPassCellBits (ParsedLayoutBits L)))).reverse.map
      some)
    ((SelectedProjectionTailProjector.sourceFieldBits L).map some)

theorem selectedProjectionInputQuoterExactTargetTape_eq_rawCellQuoteTargetTape
    (L : DovetailLayout) :
    SelectedProjectionInputQuoterExactTargetTape L =
      selectedProjectionInputQuoterRawCellQuoteTargetTape L := by
  rw [selectedProjectionInputQuoterRawCellQuoteTargetTape]
  rw [SelectedProjectionInputQuoterExactTargetTape,
    SelectedProjectionTailProjector.sourceFieldBits_eq_stageNatBits_sourceRestFieldBits]
  congr 1
  rw [SelectedProjectionTailProjector.outputPrefixStageInputSourceRestFieldBits]
  rw [SelectedProjectionTailProjector.parsedLayoutBits_eq_transition_stageInput_sourceRestFieldBits]
  rw [← preservingCellPassQuoteBits_eq_encodeBoolWordAppend]

theorem selectedProjectionInputQuoterBoundaryDefaultBits_eq_parsedLayoutBits
    (L : DovetailLayout) :
    List.append
        (List.map optionBitDefaultFalse
          (List.reverse
            (assemblySourceRestBoundaryLeftRev L.input L.stage)))
        (SelectedProjectionTailProjector.sourceRestFieldBits L) =
      ParsedLayoutBits L :=
  assemblySourceRestBoundaryLeftRev_defaultBits_append_sourceRestFieldBits L

def selectedProjectionInputQuoterAfterSourceRestPassTape
    (L : DovetailLayout) : Tape Bool :=
  Tape.move Direction.left
    (Tape.move Direction.right
      (preservingCellPassHaltTape
        (assemblySourceRestBoundaryLeftRev L.input L.stage)
        (SelectedProjectionTailProjector.sourceRestFieldBits L) []))

def selectedProjectionInputQuoterAfterSourceRestSourceShapeTape
    (L : DovetailLayout) : Tape Bool :=
  tapeAtCells
    (none ::
      List.append
        ((SelectedProjectionTailProjector.sourceRestFieldBits L).reverse.map
          some)
        (assemblySourceRestBoundaryLeftRev L.input L.stage))
    (List.append
      ((preservingCellPassCellBits
        (SelectedProjectionTailProjector.sourceRestFieldBits L)).map some)
      [none])

def selectedProjectionInputQuoterRawCellQuoteTargetShapeTape
    (L : DovetailLayout) : Tape Bool :=
  tapeAtCells
    ((SelectedProjectionTailProjector.outputPrefixStageInputSourceRestFieldBits
      L).reverse.map some)
    ((SelectedProjectionTailProjector.sourceFieldBits L).map some)

theorem selectedProjectionInputQuoterAfterSourceRestPassTape_eq_haltTape
    (L : DovetailLayout) :
    selectedProjectionInputQuoterAfterSourceRestPassTape L =
      preservingCellPassHaltTape
        (assemblySourceRestBoundaryLeftRev L.input L.stage)
        (SelectedProjectionTailProjector.sourceRestFieldBits L) [] := by
  rw [selectedProjectionInputQuoterAfterSourceRestPassTape]
  rcases sourceRestFieldBits_cons_cons L with
    ⟨head, next, right, hsource⟩
  rw [hsource]
  rcases preservingCellPassHaltTape_right_cons_of_nonempty
      (assemblySourceRestBoundaryLeftRev L.input L.stage)
      head (next :: right) with
    ⟨cell, tail, hright⟩
  exact Tape.move_left_move_right_eq_self_of_right_cons _ hright

theorem selectedProjectionInputQuoterAfterSourceRestPassTape_eq_tapeAtCells
    (L : DovetailLayout) :
    selectedProjectionInputQuoterAfterSourceRestPassTape L =
      selectedProjectionInputQuoterAfterSourceRestSourceShapeTape L := by
  rw [selectedProjectionInputQuoterAfterSourceRestPassTape_eq_haltTape]
  rw [selectedProjectionInputQuoterAfterSourceRestSourceShapeTape]
  rcases sourceRestFieldBits_cons_cons L with
    ⟨head, next, right, hsource⟩
  rw [hsource]
  exact
    preservingCellPassHaltTape_nonempty_empty_output_eq_tapeAtCells
      (assemblySourceRestBoundaryLeftRev L.input L.stage)
      head (next :: right)

theorem selectedProjectionInputQuoterRawCellQuoteTargetTape_eq_shapeTape
    (L : DovetailLayout) :
    selectedProjectionInputQuoterRawCellQuoteTargetTape L =
      selectedProjectionInputQuoterRawCellQuoteTargetShapeTape L := by
  rw [← selectedProjectionInputQuoterExactTargetTape_eq_rawCellQuoteTargetTape]
  rw [selectedProjectionInputQuoterRawCellQuoteTargetShapeTape]
  rw [SelectedProjectionInputQuoterExactTargetTape,
    SelectedProjectionTailProjector.sourceFieldBits_eq_stageNatBits_sourceRestFieldBits]

theorem selectedProjectionInputQuoterAfterSourceRestPassTape_cells
    (L : DovetailLayout) :
    Tape.cells (selectedProjectionInputQuoterAfterSourceRestPassTape L) =
      List.append
        (List.reverse (assemblySourceRestBoundaryLeftRev L.input L.stage))
        (List.append
          ((SelectedProjectionTailProjector.sourceRestFieldBits L).map some)
          (none ::
            List.append
              ((preservingCellPassCellBits
                (SelectedProjectionTailProjector.sourceRestFieldBits L)).map
                some)
      [none])) := by
  rw [selectedProjectionInputQuoterAfterSourceRestPassTape_eq_tapeAtCells]
  rw [selectedProjectionInputQuoterAfterSourceRestSourceShapeTape]
  rcases sourceRestFieldBits_cons_cons L with
    ⟨head, next, right, hsource⟩
  rw [hsource]
  cases head <;>
    simp [tapeAtCells, Tape.cells, preservingCellPassCellBits,
      preservingCellPassZeroBits, preservingCellPassOneBits,
      List.map_append, List.append_assoc]

theorem selectedProjectionInputQuoterAfterSourceRestPassTape_defaultedCells
    (L : DovetailLayout) :
    List.map optionBitDefaultFalse
        (Tape.cells (selectedProjectionInputQuoterAfterSourceRestPassTape L)) =
      List.append (ParsedLayoutBits L)
        (false ::
          List.append
            (preservingCellPassCellBits
              (SelectedProjectionTailProjector.sourceRestFieldBits L))
            [false]) := by
  rw [selectedProjectionInputQuoterAfterSourceRestPassTape_cells]
  have hprefix :=
    selectedProjectionInputQuoterBoundaryDefaultBits_eq_parsedLayoutBits L
  simpa [optionBitDefaultFalse, Function.comp_def, List.map_append,
    List.append_assoc] using
    congrArg
      (fun pref =>
        List.append pref
          (false ::
            List.append
              (preservingCellPassCellBits
                (SelectedProjectionTailProjector.sourceRestFieldBits L))
              [false]))
      hprefix

theorem selectedProjectionInputQuoterRawCellQuoteTargetTape_normalizedOutput
    (L : DovetailLayout) :
    Tape.normalizedOutput
        (selectedProjectionInputQuoterRawCellQuoteTargetTape L) =
      List.append
        (SelectedProjectionTailProjector.outputPrefixStageInputSourceRestFieldBits
          L)
        (SelectedProjectionTailProjector.sourceFieldBits L) := by
  rw [← selectedProjectionInputQuoterExactTargetTape_eq_rawCellQuoteTargetTape]
  rw [selectedProjectionInputQuoterExactTargetTape_eq_sourceTape_outputPrefix]
  rw [SelectedProjectionTailProjector.sourceTape_normalizedOutput]
  simp [Function.comp_def, List.map_reverse]

theorem selectedProjectionInputQuoterRawCellQuoteTargetTape_cells
    (L : DovetailLayout) :
    Tape.cells (selectedProjectionInputQuoterRawCellQuoteTargetTape L) =
      List.append
        ((SelectedProjectionTailProjector.outputPrefixStageInputSourceRestFieldBits
          L).map some)
        ((SelectedProjectionTailProjector.sourceFieldBits L).map some) := by
  rw [selectedProjectionInputQuoterRawCellQuoteTargetTape]
  rcases SelectedProjectionTailProjector.stageNatBits_cons_cons L.stage with
    ⟨head, next, right, hstage⟩
  rw [SelectedProjectionTailProjector.sourceFieldBits_eq_stageNatBits_sourceRestFieldBits,
    hstage]
  simp [tapeAtCells, Tape.cells, List.reverse_append, List.map_append,
    List.append_assoc]
  rw [SelectedProjectionTailProjector.parsedLayoutBits_eq_transition_stageInput_sourceRestFieldBits]
  have hquote :=
    congrArg (List.map some)
      (preservingCellPassHeaderQuoteBits_eq_outputPrefixStageInputSourceRestFieldBits
        L)
  simpa [List.map_append, List.length_append, List.append_assoc] using
    congrArg
      (fun pref =>
        List.append pref
          (some head :: some next ::
            (List.append (right.map some)
              ((SelectedProjectionTailProjector.sourceRestFieldBits L).map
                some))))
      hquote

def SelectedProjectionInputQuoterAfterSourceRestPassSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall L : DovetailLayout,
      finish.HaltsFromTape
        (selectedProjectionInputQuoterAfterSourceRestPassTape L)
        (selectedProjectionInputQuoterRawCellQuoteTargetTape L)

def SelectedProjectionInputQuoterAfterSourceRestShapeSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall L : DovetailLayout,
      finish.HaltsFromTape
        (selectedProjectionInputQuoterAfterSourceRestSourceShapeTape L)
        (selectedProjectionInputQuoterRawCellQuoteTargetShapeTape L)

def SelectedProjectionInputQuoterAfterSourceRestPassConstruction :
    Prop :=
  exists finish : MachineDescription,
    SelectedProjectionInputQuoterAfterSourceRestPassSpec finish

def SelectedProjectionInputQuoterAfterSourceRestShapeConstruction :
    Prop :=
  exists finish : MachineDescription,
    SelectedProjectionInputQuoterAfterSourceRestShapeSpec finish


theorem assemblySourceRestFinishTargetPrefixBits_eq_outputPrefix
    (L : DovetailLayout) :
    assemblySourceRestFinishTargetPrefixBits L.input
        (SelectedProjectionTailProjector.sourceRestFieldBits L) L.stage =
      SelectedProjectionTailProjector.outputPrefixStageInputSourceRestFieldBits
        L := by
  simpa [assemblySourceRestFinishTargetPrefixBits,
    assemblySourceRestFinishSourceBits] using
    preservingCellPassHeaderQuoteBits_eq_outputPrefixStageInputSourceRestFieldBits
      L

theorem assemblySourceRestFinishSourceBits_eq_parsedLayoutBits
    (L : DovetailLayout) :
    assemblySourceRestFinishSourceBits L.input
        (SelectedProjectionTailProjector.sourceRestFieldBits L) L.stage =
      ParsedLayoutBits L := by
  rw [assemblySourceRestFinishSourceBits_eq]
  exact
    (SelectedProjectionTailProjector.parsedLayoutBits_eq_transition_stageInput_sourceRestFieldBits
      L).symm

theorem assemblySourceRestFinishSourceTape_cells
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (assemblySourceRestFinishSourceTape w sourceRestBits stage) =
      List.append
        (List.reverse (assemblySourceRestBoundaryLeftRev w stage))
        (List.append
          (sourceRestBits.map some)
          (none ::
            List.append
              ((preservingCellPassCellBits sourceRestBits).map some)
              [none])) := by
  rw [assemblySourceRestFinishSourceTape]
  cases preservingCellPassCellBits sourceRestBits <;>
    simp [tapeAtCells, Tape.cells,
      List.reverse_append, List.map_reverse, List.append_assoc]

theorem assemblySourceRestFinishSourceTape_defaultedCells
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (assemblySourceRestFinishSourceTape w sourceRestBits stage)) =
      List.append
        (assemblySourceRestFinishSourceBits w sourceRestBits stage)
        (false ::
          List.append (preservingCellPassCellBits sourceRestBits)
            [false]) := by
  rw [assemblySourceRestFinishSourceTape_cells]
  have hprefix :=
    assemblySourceRestBoundaryLeftRev_defaultBits_append
      w sourceRestBits stage
  simpa [assemblySourceRestFinishSourceBits, optionBitDefaultFalse,
    Function.comp_def, List.map_append,
    List.map_reverse, List.append_assoc] using
    congrArg
      (fun pref =>
        List.append pref
          (false ::
            List.append (preservingCellPassCellBits sourceRestBits)
              [false]))
      hprefix

theorem assemblySourceRestFinishBoundaryTape_cells
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (assemblySourceRestFinishBoundaryTape w sourceRestBits stage) =
      List.append
        (List.reverse (assemblySourceRestBoundaryLeftRev w stage))
        (List.append
          (sourceRestBits.map some)
          (none ::
            List.append
              ((preservingCellPassCellBits sourceRestBits).map some)
              [none])) := by
  rw [assemblySourceRestFinishBoundaryTape]
  cases preservingCellPassCellBits sourceRestBits <;>
    simp [tapeAtCells, Tape.cells,
      List.reverse_append, List.map_reverse, List.append_assoc]

theorem assemblySourceRestFinishBoundaryTape_cells_eq_sourceTape_cells
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (assemblySourceRestFinishBoundaryTape w sourceRestBits stage) =
      Tape.cells
        (assemblySourceRestFinishSourceTape w sourceRestBits stage) := by
  rw [assemblySourceRestFinishBoundaryTape_cells,
    assemblySourceRestFinishSourceTape_cells]

theorem assemblySourceRestFinishBoundaryTape_defaultedCells
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (assemblySourceRestFinishBoundaryTape w sourceRestBits stage)) =
      List.append
        (assemblySourceRestFinishSourceBits w sourceRestBits stage)
        (false ::
          List.append (preservingCellPassCellBits sourceRestBits)
            [false]) := by
  rw [assemblySourceRestFinishBoundaryTape_cells_eq_sourceTape_cells]
  exact assemblySourceRestFinishSourceTape_defaultedCells
    w sourceRestBits stage

theorem assemblySourceRestFinishBoundaryTape_defaultedCells_eq_prefix_sourceRest_quote
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (assemblySourceRestFinishBoundaryTape w sourceRestBits stage)) =
      List.append
        (assemblySourceRestFinishSourcePrefixBits w stage)
        (List.append sourceRestBits
          (false ::
            List.append (preservingCellPassCellBits sourceRestBits)
              [false])) := by
  rw [assemblySourceRestFinishBoundaryTape_defaultedCells,
    assemblySourceRestFinishSourceBits_eq_prefix_append_sourceRest]
  simp [List.append_assoc]

theorem assemblySourceRestFinishTargetTape_cells
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (assemblySourceRestFinishTargetTape w sourceRestBits stage) =
      List.append
        ((assemblySourceRestFinishTargetPrefixBits
          w sourceRestBits stage).map some)
        ((List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          sourceRestBits).map some) := by
  rcases SelectedProjectionTailProjector.stageNatBits_cons_cons stage with
    ⟨head, next, right, hstage⟩
  rw [assemblySourceRestFinishTargetTape, hstage]
  simp [tapeAtCells, Tape.cells,
    List.map_reverse, List.map_append]

theorem assemblySourceRestFinishTargetTape_cells_eq_headerQuote
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (assemblySourceRestFinishTargetTape w sourceRestBits stage) =
      List.append
        ((List.append
          (encodeCodeSymbolAsInput MachineCodeSymbol.header)
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              (assemblySourceRestFinishSourceBits w sourceRestBits stage).length)
            (preservingCellPassCellBits
              (assemblySourceRestFinishSourceBits
                w sourceRestBits stage)))).map some)
        ((List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          sourceRestBits).map some) := by
  rw [assemblySourceRestFinishTargetTape_cells]
  rw [assemblySourceRestFinishTargetPrefixBits_eq_headerQuote]

theorem assemblySourceRestFinishTargetTape_cells_eq_splitQuote
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (assemblySourceRestFinishTargetTape w sourceRestBits stage) =
      List.append
        ((List.append
          (encodeCodeSymbolAsInput MachineCodeSymbol.header)
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              (assemblySourceRestFinishSourceBits w sourceRestBits stage).length)
            (List.append
              (preservingCellPassCellBits
                (assemblySourceRestFinishSourcePrefixBits w stage))
              (preservingCellPassCellBits sourceRestBits)))).map some)
        ((List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          sourceRestBits).map some) := by
  rw [assemblySourceRestFinishTargetTape_cells]
  rw [assemblySourceRestFinishTargetPrefixBits_eq_splitQuote]

theorem assemblySourceRestFinishTargetTape_defaultedCells_eq_splitQuote
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (assemblySourceRestFinishTargetTape w sourceRestBits stage)) =
      List.append
        (List.append
          (encodeCodeSymbolAsInput MachineCodeSymbol.header)
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              (assemblySourceRestFinishSourceBits w sourceRestBits stage).length)
            (List.append
              (preservingCellPassCellBits
                (assemblySourceRestFinishSourcePrefixBits w stage))
              (preservingCellPassCellBits sourceRestBits))))
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          sourceRestBits) := by
  rw [assemblySourceRestFinishTargetTape_cells_eq_splitQuote]
  simp [optionBitDefaultFalse, Function.comp_def, List.map_append,
    List.append_assoc]

theorem assemblySourceRestFinishTargetTape_defaultedCells_eq_headerQuote
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (assemblySourceRestFinishTargetTape w sourceRestBits stage)) =
      List.append
        (List.append
          (encodeCodeSymbolAsInput MachineCodeSymbol.header)
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              (assemblySourceRestFinishSourceBits w sourceRestBits stage).length)
            (preservingCellPassCellBits
              (assemblySourceRestFinishSourceBits w sourceRestBits stage))))
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          sourceRestBits) := by
  rw [assemblySourceRestFinishTargetTape_cells_eq_headerQuote]
  simp [optionBitDefaultFalse, Function.comp_def, List.map_append,
    List.append_assoc]

theorem assemblySourceRestFinishTargetTape_normalizedOutput
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.normalizedOutput
        (assemblySourceRestFinishTargetTape w sourceRestBits stage) =
      List.append
        (assemblySourceRestFinishTargetPrefixBits w sourceRestBits stage)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          sourceRestBits) := by
  rw [Tape.normalizedOutput]
  rw [assemblySourceRestFinishTargetTape_cells]
  simp [Function.comp_def, List.map_append]

theorem assemblySourceRestFinishTargetTape_normalizedOutput_eq_encodeBoolWordAppend
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.normalizedOutput
        (assemblySourceRestFinishTargetTape w sourceRestBits stage) =
      List.append
        (encodeCodeWordAsInput
          (MachineCodeSymbol.header ::
            encodeBoolWordAppend
              (assemblySourceRestFinishSourceBits w sourceRestBits stage)
              []))
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          sourceRestBits) := by
  rw [assemblySourceRestFinishTargetTape_normalizedOutput]
  rw [assemblySourceRestFinishTargetPrefixBits_eq_encodeBoolWordAppend]

theorem assemblySourceRestFinishTargetTape_selected_normalizedOutput
    (L : DovetailLayout) :
    Tape.normalizedOutput
        (assemblySourceRestFinishTargetTape L.input
          (SelectedProjectionTailProjector.sourceRestFieldBits L)
          L.stage) =
      List.append
        (SelectedProjectionTailProjector.outputPrefixStageInputSourceRestFieldBits
          L)
        (SelectedProjectionTailProjector.sourceFieldBits L) := by
  rw [assemblySourceRestFinishTargetTape_normalizedOutput]
  rw [assemblySourceRestFinishTargetPrefixBits_eq_outputPrefix]
  rw [SelectedProjectionTailProjector.sourceFieldBits_eq_stageNatBits_sourceRestFieldBits]

theorem assemblySourceRestFinishSourceTape_selected_eq_shapeTape
    (L : DovetailLayout) :
    assemblySourceRestFinishSourceTape L.input
        (SelectedProjectionTailProjector.sourceRestFieldBits L) L.stage =
      selectedProjectionInputQuoterAfterSourceRestSourceShapeTape L := by
  rfl

theorem assemblySourceRestFinishTargetTape_selected_eq_shapeTape
    (L : DovetailLayout) :
    assemblySourceRestFinishTargetTape L.input
        (SelectedProjectionTailProjector.sourceRestFieldBits L) L.stage =
      selectedProjectionInputQuoterRawCellQuoteTargetShapeTape L := by
  rw [assemblySourceRestFinishTargetTape,
    selectedProjectionInputQuoterRawCellQuoteTargetShapeTape]
  rw [assemblySourceRestFinishTargetPrefixBits_eq_outputPrefix]
  rw [SelectedProjectionTailProjector.sourceFieldBits_eq_stageNatBits_sourceRestFieldBits]

theorem selectedProjectionInputQuoterAfterSourceRestShapeConstruction :
    SelectedProjectionInputQuoterAfterSourceRestShapeConstruction := by
  rcases assemblySourceRestFinishConstruction with ⟨finish, hfinish⟩
  refine ⟨finish, hfinish.left, ?_⟩
  intro L
  rw [← assemblySourceRestFinishSourceTape_selected_eq_shapeTape,
    ← assemblySourceRestFinishTargetTape_selected_eq_shapeTape]
  exact
    hfinish.right L.input
      (SelectedProjectionTailProjector.sourceRestFieldBits L) L.stage

theorem assemblySkeletonDescription_run_nonempty_stageInput_to_sourceRest_boundary_cells_pre
    (b : Bool) (rest : Word Bool) (stage : Nat)
    (sourceRestCells : List (Option Bool)) :
    exists steps : Nat,
      AssemblySkeletonDescription.runConfig steps
          (config AssemblySkeletonDescription.start []
            (List.append
              (List.map some
                (List.append
                  (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
                  (DovetailInitialLayoutInitializer.stageInputBits
                    (b :: rest) stage)))
              sourceRestCells)) =
        config 210
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage).reverse.map some)
            (List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
                (b :: rest)).reverse.map some)
              (List.append [none, some false] transitionPrefixLeftTail)))
          sourceRestCells := by
  rcases
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_false_false_tail
        stage with
    ⟨stageTail, hstageTail⟩
  rcases assemblySkeletonDescription_run_state120_bool_tail_to_finish_withBase_cells
      b rest
      (List.append
        ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          stage).map some)
        sourceRestCells)
      transitionPrefixLeftTail with
    ⟨markSteps, hmark⟩
  rcases assemblySkeletonDescription_run_finish_cells_false_false_to_state200_withBase
      b rest
      (List.append (stageTail.map some) sourceRestCells)
      transitionPrefixLeftTail with
    ⟨finishSteps, hfinish⟩
  refine
    ⟨6 + (6 + (markSteps + finishSteps + (4 * stage + 4))), ?_⟩
  rw [show
      6 + (6 + (markSteps + finishSteps + (4 * stage + 4))) =
        6 + (6 + (markSteps + (finishSteps + (4 * stage + 4)))) by
    omega]
  rw [runConfig_add]
  rw [assemblySkeletonDescription_run_prefix_to_stageInput_tail_cells]
  rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTail_cons]
  rw [show
      List.append
          ((true :: false ::
            List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                rest.length)
              (List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellBits
                  b)
                (List.append
                  (DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits
                    rest)
                  (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                    stage)))).map some)
          sourceRestCells =
        some true :: some false ::
          List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              rest.length).map some)
            (List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellBits
                b).map some)
              (List.append
                ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits
                  rest).map some)
                (List.append
                  ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                    stage).map some)
                  sourceRestCells))) by
    simp [List.map_append, List.append_assoc]]
  change
    AssemblySkeletonDescription.runConfig
        (6 + (markSteps + (finishSteps + (4 * stage + 4))))
        (markedTailStartConfigWithBaseCells transitionPrefixLeftTail
          (some true :: some false ::
            List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                rest.length).map some)
              (List.append
                ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellBits
                  b).map some)
                (List.append
                  ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits
                    rest).map some)
                  (List.append
                    ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                      stage).map some)
                    sourceRestCells))))) =
      config 210
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).reverse.map some)
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
              (b :: rest)).reverse.map some)
            (List.append [none, some false] transitionPrefixLeftTail)))
        sourceRestCells
  rw [runConfig_add]
  rw [assemblySkeletonDescription_run_marked_tail_tick_to_state120_withBase_cells]
  rw [runConfig_add]
  rw [hmark]
  rw [hstageTail]
  rw [runConfig_add]
  have htailCells :
      List.append (List.map some (false :: false :: stageTail))
          sourceRestCells =
        some false :: some false ::
          List.append (stageTail.map some) sourceRestCells := by
    simp
  rw [htailCells]
  rw [hfinish]
  rw [← hstageTail]
  have hright :
      some false :: some false ::
          List.append (stageTail.map some) sourceRestCells =
        List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).map some)
          sourceRestCells := by
    rw [hstageTail]
    simp
  rw [hright]
  rw [assemblySkeletonDescription_run_state200_stageNat_to_state210]
  simp

def selectedProjectionInputQuoterAfterSourceRestQuoteBoundaryTape
    (L : DovetailLayout) : Tape Bool :=
  scanRightToBlankLeftHaltTape
    (none ::
      List.append
        ((SelectedProjectionTailProjector.sourceRestFieldBits L).reverse.map
          some)
        (assemblySourceRestBoundaryLeftRev L.input L.stage))
    (preservingCellPassCellBits
      (SelectedProjectionTailProjector.sourceRestFieldBits L))

theorem scanRightToBlankLeftDescription_haltsFrom_afterSourceRestPassTape
    (L : DovetailLayout) :
    scanRightToBlankLeftDescription.HaltsFromTape
      (selectedProjectionInputQuoterAfterSourceRestPassTape L)
      (selectedProjectionInputQuoterAfterSourceRestQuoteBoundaryTape L) := by
  rw [selectedProjectionInputQuoterAfterSourceRestPassTape_eq_tapeAtCells,
    selectedProjectionInputQuoterAfterSourceRestSourceShapeTape,
    selectedProjectionInputQuoterAfterSourceRestQuoteBoundaryTape]
  exact
    scanRightToBlankLeftDescription_haltsFromTape
      (none ::
        List.append
          ((SelectedProjectionTailProjector.sourceRestFieldBits L).reverse.map
            some)
          (assemblySourceRestBoundaryLeftRev L.input L.stage))
      (preservingCellPassCellBits
        (SelectedProjectionTailProjector.sourceRestFieldBits L))

theorem selectedProjectionInputQuoterAfterSourceRestQuoteBoundaryTape_move_left_move_right
    (L : DovetailLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (selectedProjectionInputQuoterAfterSourceRestQuoteBoundaryTape L)) =
      selectedProjectionInputQuoterAfterSourceRestQuoteBoundaryTape L := by
  rcases sourceRestFieldBits_cons_cons L with
    ⟨head, next, right, hsource⟩
  rcases preservingCellPassCellBits_cons_exists head (next :: right) with
    ⟨quoteHead, quoteTail, hquote⟩
  rw [selectedProjectionInputQuoterAfterSourceRestQuoteBoundaryTape,
    hsource, hquote]
  exact
    scanRightToBlankLeftHaltTape_move_left_move_right_cons
      (none ::
        List.append (((head :: next :: right).reverse).map some)
          (assemblySourceRestBoundaryLeftRev L.input L.stage))
      quoteHead quoteTail

def selectedProjectionInputQuoterAfterSourceRestLeftBoundaryTape
    (L : DovetailLayout) : Tape Bool :=
  scanLeftToBlankLeftHaltTape
    (List.append
      ((SelectedProjectionTailProjector.sourceRestFieldBits L).reverse.map
        some)
      (assemblySourceRestBoundaryLeftRev L.input L.stage))
    (preservingCellPassCellBits
      (SelectedProjectionTailProjector.sourceRestFieldBits L))
    [none]

theorem scanLeftToBlankLeftDescription_haltsFrom_afterSourceRestQuoteBoundaryTape
    (L : DovetailLayout) :
    scanLeftToBlankLeftDescription.HaltsFromTape
      (selectedProjectionInputQuoterAfterSourceRestQuoteBoundaryTape L)
      (selectedProjectionInputQuoterAfterSourceRestLeftBoundaryTape L) := by
  rcases sourceRestFieldBits_cons_cons L with
    ⟨head, next, right, hsource⟩
  rcases preservingCellPassCellBits_cons_exists head (next :: right) with
    ⟨quoteHead, quoteTail, hquote⟩
  rcases exists_reverse_append_singleton_of_cons quoteHead quoteTail with
    ⟨scanRev, current, hscan⟩
  rw [selectedProjectionInputQuoterAfterSourceRestQuoteBoundaryTape,
    selectedProjectionInputQuoterAfterSourceRestLeftBoundaryTape,
    hsource, hquote, hscan]
  exact
    scanLeftToBlankLeftDescription_haltsFrom_scanRightToBlankLeftHaltTape
      (List.append (((head :: next :: right).reverse).map some)
        (assemblySourceRestBoundaryLeftRev L.input L.stage))
      scanRev current

theorem selectedProjectionInputQuoterAfterSourceRestLeftBoundaryTape_move_left_move_right
    (L : DovetailLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (selectedProjectionInputQuoterAfterSourceRestLeftBoundaryTape L)) =
      selectedProjectionInputQuoterAfterSourceRestLeftBoundaryTape L := by
  rw [selectedProjectionInputQuoterAfterSourceRestLeftBoundaryTape]
  exact
    scanLeftToBlankLeftHaltTape_move_left_move_right_none_right
      (List.append
        ((SelectedProjectionTailProjector.sourceRestFieldBits L).reverse.map
          some)
        (assemblySourceRestBoundaryLeftRev L.input L.stage))
      (preservingCellPassCellBits
        (SelectedProjectionTailProjector.sourceRestFieldBits L))
      []

def SelectedProjectionInputQuoterAfterSourceRestQuoteBoundarySpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall L : DovetailLayout,
      finish.HaltsFromTape
        (selectedProjectionInputQuoterAfterSourceRestQuoteBoundaryTape L)
        (selectedProjectionInputQuoterRawCellQuoteTargetTape L)

def SelectedProjectionInputQuoterAfterSourceRestQuoteBoundaryConstruction :
    Prop :=
  exists finish : MachineDescription,
    SelectedProjectionInputQuoterAfterSourceRestQuoteBoundarySpec finish

def SelectedProjectionInputQuoterAfterSourceRestLeftBoundarySpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall L : DovetailLayout,
      finish.HaltsFromTape
        (selectedProjectionInputQuoterAfterSourceRestLeftBoundaryTape L)
        (selectedProjectionInputQuoterRawCellQuoteTargetTape L)

def SelectedProjectionInputQuoterAfterSourceRestLeftBoundaryConstruction :
    Prop :=
  exists finish : MachineDescription,
    SelectedProjectionInputQuoterAfterSourceRestLeftBoundarySpec finish

theorem selectedProjectionInputQuoterAfterSourceRestQuoteBoundaryConstruction_of_leftBoundary
    (h : SelectedProjectionInputQuoterAfterSourceRestLeftBoundaryConstruction) :
    SelectedProjectionInputQuoterAfterSourceRestQuoteBoundaryConstruction := by
  rcases h with ⟨finish, hfinish⟩
  refine
    ⟨SeqViaCanonical scanLeftToBlankLeftDescription finish, ?_⟩
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        scanLeftToBlankLeftDescription_subroutineReady
        hfinish.left
  · intro L
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        scanLeftToBlankLeftDescription_subroutineReady
        hfinish.left
        (scanLeftToBlankLeftDescription_haltsFrom_afterSourceRestQuoteBoundaryTape
          L)
        (selectedProjectionInputQuoterAfterSourceRestLeftBoundaryTape_move_left_move_right
          L)
        (hfinish.right L)

theorem selectedProjectionInputQuoterAfterSourceRestPassConstruction_of_quoteBoundary
    (h : SelectedProjectionInputQuoterAfterSourceRestQuoteBoundaryConstruction) :
    SelectedProjectionInputQuoterAfterSourceRestPassConstruction := by
  rcases h with ⟨finish, hfinish⟩
  refine
    ⟨SeqViaCanonical scanRightToBlankLeftDescription finish, ?_⟩
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        scanRightToBlankLeftDescription_subroutineReady
        hfinish.left
  · intro L
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        scanRightToBlankLeftDescription_subroutineReady
        hfinish.left
        (scanRightToBlankLeftDescription_haltsFrom_afterSourceRestPassTape
          L)
        (selectedProjectionInputQuoterAfterSourceRestQuoteBoundaryTape_move_left_move_right
          L)
        (hfinish.right L)

theorem selectedProjectionInputQuoterAfterSourceRestPassConstruction :
    SelectedProjectionInputQuoterAfterSourceRestPassConstruction := by
  rcases selectedProjectionInputQuoterAfterSourceRestShapeConstruction with
    ⟨finish, hfinish⟩
  refine ⟨finish, hfinish.left, ?_⟩
  intro L
  simpa [selectedProjectionInputQuoterAfterSourceRestPassTape_eq_tapeAtCells,
    selectedProjectionInputQuoterRawCellQuoteTargetTape_eq_shapeTape] using
    hfinish.right L

def SelectedProjectionInputQuoterRawCellQuoteSpec
    (raw : MachineDescription) : Prop :=
  raw.SubroutineReady ∧
    forall L : DovetailLayout,
      raw.HaltsFromTape
        (selectedProjectionInputQuoterPostBoundarySourceTape L)
        (selectedProjectionInputQuoterRawCellQuoteTargetTape L)

def SelectedProjectionInputQuoterRawCellQuoteConstruction : Prop :=
  exists raw : MachineDescription,
    SelectedProjectionInputQuoterRawCellQuoteSpec raw

/--
Raw-cell quote/preserve finite-table leaf for the exact input quoter.  At the
source-rest boundary the parsed-layout prefix is split across the defaulted
left context and the remaining source-rest bits under the head.  This machine
must quote that whole defaulted parsed-layout word while preserving the exact
stage/source field expected by the selected-projection tail emitter.
-/
theorem selectedProjectionInputQuoterRawCellQuoteConstruction :
    SelectedProjectionInputQuoterRawCellQuoteConstruction := by
  rcases selectedProjectionInputQuoterAfterSourceRestPassConstruction with
    ⟨finish, hfinish⟩
  refine
    ⟨SeqViaCanonical PreservingCellPassDescription finish, ?_⟩
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        preservingCellPassDescription_subroutineReady
        hfinish.left
  · intro L
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        preservingCellPassDescription_subroutineReady
        hfinish.left
        (preservingCellPassDescription_haltsFrom_postBoundarySourceTape L)
        (by
          rfl)
        (hfinish.right L)

/--
The remaining post-boundary finite-table obligation for the exact input
quoter.  The prefix phase has already restored the source-rest boundary; this
phase must quote the defaulted parsed-layout bits and leave the exact source
field under the head.
-/
theorem selectedProjectionInputQuoterPostBoundaryConstruction :
    SelectedProjectionInputQuoterPostBoundaryConstruction := by
  rcases selectedProjectionInputQuoterRawCellQuoteConstruction with
    ⟨raw, hraw⟩
  refine ⟨raw, hraw.left, ?_⟩
  intro L
  rw [selectedProjectionInputQuoterExactTargetTape_eq_rawCellQuoteTargetTape]
  exact hraw.right L

theorem assemblySkeletonDescription_run_nonempty_stageInput_to_sourceRest_boundary_cells
    (b : Bool) (rest : Word Bool) (stage : Nat)
    (sourceRestCells : List (Option Bool)) :
    exists steps : Nat,
      AssemblySkeletonDescription.runConfig steps
          (config AssemblySkeletonDescription.start []
            (List.append
              (List.map some
                (List.append
                  (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
                  (DovetailInitialLayoutInitializer.stageInputBits
                    (b :: rest) stage)))
              sourceRestCells)) =
        config 210
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage).reverse.map some)
            (List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
                (b :: rest)).reverse.map some)
              (List.append [none, some false] transitionPrefixLeftTail)))
          sourceRestCells := by
  exact
    assemblySkeletonDescription_run_nonempty_stageInput_to_sourceRest_boundary_cells_pre
      b rest stage sourceRestCells

end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC

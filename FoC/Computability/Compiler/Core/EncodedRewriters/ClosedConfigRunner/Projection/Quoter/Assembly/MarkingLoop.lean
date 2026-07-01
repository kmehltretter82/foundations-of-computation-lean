import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Quoter.Assembly.MarkedTail

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

namespace SelectedProjectionInputQuoterFiniteLeaf

open DovetailInitialLayoutInitializer
private abbrev ASM := AssemblySkeletonDescription
private abbrev AP := AssemblyPrefixDescription

theorem assemblySkeletonDescription_run_mark_current_to_state100_withBase
    (processed : Word Bool) (b : Bool) (rest tailBits : Word Bool)
    (leftTail : List (Option Bool)) :
    exists steps : Nat,
      ASM.runConfig steps
          (markingState120WithTailBitsAndBase
            processed b rest tailBits leftTail) =
        state100AfterMarkedWithTailBitsAndBase
          processed b rest tailBits leftTail := by
  let scanRev :=
    DovetailInitialLayoutInitializer.StageInputMarkedScanner.markingReturnScanRev
      processed rest
  refine
    ⟨(4 * rest.length + 4) +
        (4 * processed.length + (6 + (scanRev.length + 4))), ?_⟩
  rw [assemblySkeletonDescription_runConfig_eq_scanner]
  · rw [runConfig_add]
    unfold markingState120WithTailBitsAndBase
    rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.run_state120_stageNat]
    rw [runConfig_add]
    rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.run_state130_markedCells]
    rw [runConfig_add]
    rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.run_state130_currentCell]
    have hreturn :=
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.run_state140_returnToLengthMarker
        scanRev b
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.activeLengthPrefixTail
            processed.length)
          leftTail)
        (some (!b) ::
          List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits
              rest).map some)
            (tailBits.map some))
    have hprefix :
        some false :: some true ::
            List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.activeLengthPrefixTail
                processed.length)
              leftTail =
          List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishLengthPrefixRev
              processed.length)
            leftTail := by
      have h :=
        congrArg (fun xs => List.append xs leftTail)
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.activeLengthPrefixRestored
            processed.length)
      simpa [List.append_assoc] using h
    rw [hprefix] at hreturn
    cases b <;>
    simpa [state100AfterMarkedWithTailBitsAndBase, scanRev,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.markingReturnScanRev,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.activeLengthPrefixRev,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.activeLengthPrefixRestored,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellBits,
      List.map_append, List.reverse_append, List.append_assoc]
      using hreturn
  · simp [markingState120WithTailBitsAndBase, config,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription]

theorem assemblySkeletonDescription_run_mark_current_to_state100_withBase_cells
    (processed : Word Bool) (b : Bool) (rest : Word Bool)
    (tailCells leftTail : List (Option Bool)) :
    exists steps : Nat,
      ASM.runConfig steps
          (markingState120WithTailCellsAndBase
            processed b rest tailCells leftTail) =
        state100AfterMarkedWithTailCellsAndBase
          processed b rest tailCells leftTail := by
  let scanRev :=
    DovetailInitialLayoutInitializer.StageInputMarkedScanner.markingReturnScanRev
      processed rest
  refine
    ⟨(4 * rest.length + 4) +
        (4 * processed.length + (6 + (scanRev.length + 4))), ?_⟩
  rw [assemblySkeletonDescription_runConfig_eq_scanner]
  · rw [runConfig_add]
    unfold markingState120WithTailCellsAndBase
    rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.run_state120_stageNat]
    rw [runConfig_add]
    rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.run_state130_markedCells]
    rw [runConfig_add]
    rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.run_state130_currentCell]
    have hreturn :=
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.run_state140_returnToLengthMarker
        scanRev b
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.activeLengthPrefixTail
            processed.length)
          leftTail)
        (some (!b) ::
          List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits
              rest).map some)
            tailCells)
    have hprefix :
        some false :: some true ::
            List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.activeLengthPrefixTail
                processed.length)
              leftTail =
          List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishLengthPrefixRev
              processed.length)
            leftTail := by
      have h :=
        congrArg (fun xs => List.append xs leftTail)
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.activeLengthPrefixRestored
            processed.length)
      simpa [List.append_assoc] using h
    rw [hprefix] at hreturn
    cases b <;>
    simpa [state100AfterMarkedWithTailCellsAndBase, scanRev,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.markingReturnScanRev,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.activeLengthPrefixRev,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.activeLengthPrefixRestored,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellBits,
      List.map_append, List.reverse_append, List.append_assoc]
      using hreturn
  · simp [markingState120WithTailCellsAndBase, config,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription]

theorem assemblySkeletonDescription_run_state100_tick
    (left tail : List (Option Bool)) :
    ASM.runConfig 4
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
  rw [assemblySkeletonDescription_runConfig_eq_scanner]
  · exact
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.run_state100_tick
        left tail
  · simp [config,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription]

theorem assemblySkeletonDescription_run_state100_done
    (left tail : List (Option Bool)) :
    ASM.runConfig 4
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
  rw [assemblySkeletonDescription_runConfig_eq_scanner]
  · exact
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.run_state100_done
        left tail
  · simp [config,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription]

theorem assemblySkeletonDescription_run_marking_loop_from_state120_withBase
    (processed : Word Bool) (b : Bool) (rest tailBits : Word Bool)
    (leftTail : List (Option Bool)) :
    exists steps : Nat,
      ASM.runConfig steps
          (markingState120WithTailBitsAndBase
            processed b rest tailBits leftTail) =
        finishStartConfigWithTailBitsAndBase
          (List.append processed (b :: rest)) tailBits leftTail := by
  induction rest generalizing processed b with
  | nil =>
      rcases assemblySkeletonDescription_run_mark_current_to_state100_withBase
          processed b [] tailBits leftTail with
        ⟨markSteps, hmark⟩
      refine ⟨markSteps + 4, ?_⟩
      rw [runConfig_add]
      rw [hmark]
      unfold state100AfterMarkedWithTailBitsAndBase
      change
        ASM.runConfig 4
            (config 100
              (List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishLengthPrefixRev
                  processed.length)
                leftTail)
              (List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.doneBits.map
                  some)
                (List.append
                  ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellsBits
                    processed).map some)
                  (List.append
                    ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellBits
                      b).map some)
                    (tailBits.map some))))) =
          finishStartConfigWithTailBitsAndBase
            (List.append processed [b]) tailBits leftTail
      rw [assemblySkeletonDescription_run_state100_done]
      unfold finishStartConfigWithTailBitsAndBase
      rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellsBits_append_single_map]
      simp [DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishStartLeft,
        List.length_append, List.append_assoc]
  | cons next rest ih =>
      rcases assemblySkeletonDescription_run_mark_current_to_state100_withBase
          processed b (next :: rest) tailBits leftTail with
        ⟨markSteps, hmark⟩
      rcases ih (List.append processed [b]) next with
        ⟨recSteps, hrec⟩
      refine ⟨markSteps + 4 + recSteps, ?_⟩
      rw [show markSteps + 4 + recSteps =
          markSteps + (4 + recSteps) by omega]
      rw [runConfig_add]
      rw [hmark]
      rw [runConfig_add]
      unfold state100AfterMarkedWithTailBitsAndBase
      rw [show
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              (next :: rest).length).map some =
            List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits.map
                some)
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                rest.length).map some) by
        simp [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_succ,
          DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits,
          encodeCodeSymbolAsInput]]
      change
        ASM.runConfig recSteps
            (ASM.runConfig 4
              (config 100
                (List.append
                  (DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishLengthPrefixRev
                    processed.length)
                  leftTail)
                (List.append
                  (DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits.map
                    some)
                  (List.append
                    ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                      rest.length).map some)
                    (List.append
                      ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellsBits
                        processed).map some)
                      (List.append
                        ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellBits
                          b).map some)
                        (List.append
                          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits
                            (next :: rest)).map some)
                          (tailBits.map some)))))))) =
          finishStartConfigWithTailBitsAndBase
            (List.append processed (b :: next :: rest)) tailBits leftTail
      rw [assemblySkeletonDescription_run_state100_tick]
      unfold markingState120WithTailBitsAndBase at hrec
      rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellsBits_append_single_map] at hrec
      simpa [DovetailInitialLayoutInitializer.StageInputMarkedScanner.activeLengthPrefixRev_succ,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits_cons,
        List.length_append, List.map_append, List.append_assoc] using hrec

theorem assemblySkeletonDescription_run_marking_loop_from_state120_withBase_cells
    (processed : Word Bool) (b : Bool) (rest : Word Bool)
    (tailCells leftTail : List (Option Bool)) :
    exists steps : Nat,
      ASM.runConfig steps
          (markingState120WithTailCellsAndBase
            processed b rest tailCells leftTail) =
        finishStartConfigWithTailCellsAndBase
          (List.append processed (b :: rest)) tailCells leftTail := by
  induction rest generalizing processed b with
  | nil =>
      rcases assemblySkeletonDescription_run_mark_current_to_state100_withBase_cells
          processed b [] tailCells leftTail with
        ⟨markSteps, hmark⟩
      refine ⟨markSteps + 4, ?_⟩
      rw [runConfig_add]
      rw [hmark]
      unfold state100AfterMarkedWithTailCellsAndBase
      change
        ASM.runConfig 4
            (config 100
              (List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishLengthPrefixRev
                  processed.length)
                leftTail)
              (List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.doneBits.map
                  some)
                (List.append
                  ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellsBits
                    processed).map some)
                  (List.append
                    ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellBits
                      b).map some)
                    tailCells)))) =
          finishStartConfigWithTailCellsAndBase
            (List.append processed [b]) tailCells leftTail
      rw [assemblySkeletonDescription_run_state100_done]
      unfold finishStartConfigWithTailCellsAndBase
      rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellsBits_append_single_map]
      simp [DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishStartLeft,
        List.length_append, List.append_assoc]
  | cons next rest ih =>
      rcases assemblySkeletonDescription_run_mark_current_to_state100_withBase_cells
          processed b (next :: rest) tailCells leftTail with
        ⟨markSteps, hmark⟩
      rcases ih (List.append processed [b]) next with
        ⟨recSteps, hrec⟩
      refine ⟨markSteps + 4 + recSteps, ?_⟩
      rw [show markSteps + 4 + recSteps =
          markSteps + (4 + recSteps) by omega]
      rw [runConfig_add]
      rw [hmark]
      rw [runConfig_add]
      unfold state100AfterMarkedWithTailCellsAndBase
      rw [show
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              (next :: rest).length).map some =
            List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits.map
                some)
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                rest.length).map some) by
        simp [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_succ,
          DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits,
          encodeCodeSymbolAsInput]]
      change
        ASM.runConfig recSteps
            (ASM.runConfig 4
              (config 100
                (List.append
                  (DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishLengthPrefixRev
                    processed.length)
                  leftTail)
                (List.append
                  (DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits.map
                    some)
                  (List.append
                    ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                      rest.length).map some)
                    (List.append
                      ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellsBits
                        processed).map some)
                      (List.append
                        ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellBits
                          b).map some)
                        (List.append
                          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits
                            (next :: rest)).map some)
                          tailCells))))))) =
          finishStartConfigWithTailCellsAndBase
            (List.append processed (b :: next :: rest)) tailCells leftTail
      rw [assemblySkeletonDescription_run_state100_tick]
      unfold markingState120WithTailCellsAndBase at hrec
      rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellsBits_append_single_map] at hrec
      simpa [DovetailInitialLayoutInitializer.StageInputMarkedScanner.activeLengthPrefixRev_succ,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits_cons,
        List.length_append, List.map_append, List.append_assoc] using hrec

theorem assemblySkeletonDescription_run_state120_bool_tail_to_finish_withBase
    (b : Bool) (rest tailBits : Word Bool)
    (leftTail : List (Option Bool)) :
    exists steps : Nat,
      ASM.runConfig steps
          (config 120
            (List.append [none, some true, none, some false] leftTail)
            (List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                rest.length).map some)
              (List.append
                ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellBits
                  b).map some)
                (List.append
                  ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits
                    rest).map some)
                  (tailBits.map some))))) =
        finishStartConfigWithTailBitsAndBase
          (b :: rest) tailBits leftTail := by
  rcases assemblySkeletonDescription_run_marking_loop_from_state120_withBase
      ([] : Word Bool) b rest tailBits leftTail with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  simpa [markingState120WithTailBitsAndBase,
    DovetailInitialLayoutInitializer.StageInputMarkedScanner.activeLengthPrefixRev_zero]
    using hsteps

theorem assemblySkeletonDescription_run_state120_bool_tail_to_finish_withBase_cells
    (b : Bool) (rest : Word Bool) (tailCells leftTail : List (Option Bool)) :
    exists steps : Nat,
      ASM.runConfig steps
          (config 120
            (List.append [none, some true, none, some false] leftTail)
            (List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                rest.length).map some)
              (List.append
                ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellBits
                  b).map some)
                (List.append
                  ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits
                    rest).map some)
                  tailCells)))) =
        finishStartConfigWithTailCellsAndBase
          (b :: rest) tailCells leftTail := by
  rcases assemblySkeletonDescription_run_marking_loop_from_state120_withBase_cells
      ([] : Word Bool) b rest tailCells leftTail with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  simpa [markingState120WithTailCellsAndBase,
    DovetailInitialLayoutInitializer.StageInputMarkedScanner.activeLengthPrefixRev_zero]
    using hsteps

section AssemblyPrefixCore

open DovetailInitialLayoutInitializer.StageInputMarkedScanner

theorem assemblyPrefixDescription_run_state100_tick_core
    (left tail : List (Option Bool)) :
    AP.runConfig 4
        (config 100 left
          (List.append (tickBits.map some) tail)) =
      config 120 (List.append markedTickRev left) tail := by
  cases tail <;>
    simp [AP, AssemblyPrefixDescription,
      StageInputMarkedScannerDescription, tickBits, markedTickRev,
      encodeCodeSymbolAsInput, config, tapeAtCells, keep, keepMove,
      writeMove, scanLeftToSentinelRestart, scanLeftToSentinelHalt,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem assemblyPrefixDescription_run_state100_done_core
    (left tail : List (Option Bool)) :
    AP.runConfig 4
        (config 100 left
          (List.append (doneBits.map some) tail)) =
      config 150 (List.append (doneBits.reverse.map some) left)
        tail := by
  cases tail <;>
    simp [AP, AssemblyPrefixDescription,
      StageInputMarkedScannerDescription, doneBits,
      encodeCodeSymbolAsInput, config, tapeAtCells, keep, keepMove,
      writeMove, scanLeftToSentinelRestart, scanLeftToSentinelHalt,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem assemblyPrefixDescription_run_state120_tick_core
    (left right : List (Option Bool)) :
    AP.runConfig 4
        (config 120 left (List.append (tickBits.map some) right)) =
      config 120 (List.append (tickBits.reverse.map some) left) right := by
  cases right <;>
  simp [AP, AssemblyPrefixDescription, StageInputMarkedScannerDescription,
    tickBits, config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart, scanLeftToSentinelHalt,
    runConfig, stepConfig, lookupTransition, Matches, transition,
    encodeCodeSymbolAsInput, Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem assemblyPrefixDescription_run_state120_done_core
    (left right : List (Option Bool)) :
    AP.runConfig 4
        (config 120 left (List.append (doneBits.map some) right)) =
      config 130 (List.append (doneBits.reverse.map some) left) right := by
  cases right <;>
  simp [AP, AssemblyPrefixDescription, StageInputMarkedScannerDescription,
    doneBits, config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart, scanLeftToSentinelHalt,
    runConfig, stepConfig, lookupTransition, Matches, transition,
    encodeCodeSymbolAsInput, Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem assemblyPrefixDescription_run_state120_stageNat_core
    (n : Nat) (left right : List (Option Bool)) :
    AP.runConfig (4 * n + 4)
        (config 120 left
          (List.append ((stageNatBits n).map some) right)) =
      config 130 (List.append ((stageNatBits n).reverse.map some) left)
        right := by
  induction n generalizing left with
  | zero =>
      simpa [stageNatBits_zero] using
        assemblyPrefixDescription_run_state120_done_core left right
  | succ n ih =>
      rw [show 4 * (n + 1) + 4 = 4 + (4 * n + 4) by omega]
      rw [runConfig_add]
      rw [show
          List.append ((stageNatBits (n + 1)).map some) right =
            List.append (tickBits.map some)
              (List.append ((stageNatBits n).map some) right) by
        simp [stageNatBits_succ, tickBits, encodeCodeSymbolAsInput]]
      rw [assemblyPrefixDescription_run_state120_tick_core]
      rw [ih]
      simp [stageNatBits_succ, tickBits, encodeCodeSymbolAsInput,
        List.map_append, List.append_assoc]

theorem assemblyPrefixDescription_run_state130_markedCell_core
    (b : Bool) (left right : List (Option Bool)) :
    AP.runConfig 4
        (config 130 left
          (List.append ((markedCellBits b).map some) right)) =
      config 130
        (List.append ((markedCellBits b).reverse.map some) left)
        right := by
  cases b <;> cases right <;>
  simp [AP, AssemblyPrefixDescription, StageInputMarkedScannerDescription,
    markedCellBits, config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart, scanLeftToSentinelHalt,
    runConfig, stepConfig, lookupTransition, Matches, transition,
    Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem assemblyPrefixDescription_run_state130_markedCells_core
    (processed : Word Bool) (left right : List (Option Bool)) :
    AP.runConfig (4 * processed.length)
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
      rw [assemblyPrefixDescription_run_state130_markedCell_core]
      rw [ih]
      simp [markedCellsBits, List.reverse_append, List.map_append,
        List.append_assoc]

theorem assemblyPrefixDescription_run_state130_currentCell_core
    (b : Bool) (left right : List (Option Bool)) :
    AP.runConfig 6
        (config 130 left (List.append ((cellBits b).map some) right)) =
      config 140 (some true :: some true :: left)
        (some b :: some (!b) :: right) := by
  cases b <;> cases right <;>
  simp [AP, AssemblyPrefixDescription, StageInputMarkedScannerDescription,
    cellBits, config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart, scanLeftToSentinelHalt,
    runConfig, stepConfig, lookupTransition, Matches, transition,
    encodeCodeSymbolAsInput, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    Tape.moveRight]

theorem assemblyPrefixDescription_run_state140_returnToLengthMarker_core
    (scanRev : Word Bool) (headBit : Bool)
    (leftTail right : List (Option Bool)) :
    AP.runConfig (scanRev.length + 4)
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
      simp [AP, AssemblyPrefixDescription, StageInputMarkedScannerDescription,
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
        AP.runConfig (rest.length + 4)
          (AP.runConfig 1
            (config 140
              (some b :: List.append (List.map some rest)
                (none :: some true :: leftTail))
              (some headBit :: right))) =
          config 100 (some false :: some true :: leftTail)
            (List.append (List.map some (b :: rest).reverse)
              (some headBit :: right))
      rw [show
          AP.runConfig 1
            (config 140
              (some b :: List.append (List.map some rest)
                (none :: some true :: leftTail))
              (some headBit :: right)) =
          config 140
            (List.append (List.map some rest)
              (none :: some true :: leftTail))
            (some b :: some headBit :: right) by
        cases headBit <;> cases b <;> cases right <;>
        simp [AP, AssemblyPrefixDescription, StageInputMarkedScannerDescription,
          config, tapeAtCells, keep, keepMove, writeMove,
          scanLeftToSentinelRestart, scanLeftToSentinelHalt,
          runConfig, stepConfig, lookupTransition, Matches, transition,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft]]
      rw [ih]
      simp [List.map_append, List.append_assoc]

theorem assemblyPrefixDescription_run_mark_current_to_state100_withBase_cells_core
    (processed : Word Bool) (b : Bool) (rest : Word Bool)
    (tailCells leftTail : List (Option Bool)) :
    exists steps : Nat,
      AP.runConfig steps
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
  rw [assemblyPrefixDescription_run_state120_stageNat_core]
  rw [runConfig_add]
  rw [assemblyPrefixDescription_run_state130_markedCells_core]
  rw [runConfig_add]
  rw [assemblyPrefixDescription_run_state130_currentCell_core]
  have hreturn :=
    assemblyPrefixDescription_run_state140_returnToLengthMarker_core
      scanRev b
      (List.append (activeLengthPrefixTail processed.length) leftTail)
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

theorem assemblyPrefixDescription_run_marking_loop_from_state120_withBase_cells_core
    (processed : Word Bool) (b : Bool) (rest : Word Bool)
    (tailCells leftTail : List (Option Bool)) :
    exists steps : Nat,
      AP.runConfig steps
          (markingState120WithTailCellsAndBase
            processed b rest tailCells leftTail) =
        finishStartConfigWithTailCellsAndBase
          (List.append processed (b :: rest)) tailCells leftTail := by
  induction rest generalizing processed b with
  | nil =>
      rcases assemblyPrefixDescription_run_mark_current_to_state100_withBase_cells_core
          processed b [] tailCells leftTail with
        ⟨markSteps, hmark⟩
      refine ⟨markSteps + 4, ?_⟩
      rw [runConfig_add]
      rw [hmark]
      unfold state100AfterMarkedWithTailCellsAndBase
      change
        AP.runConfig 4
            (config 100
              (List.append (finishLengthPrefixRev processed.length)
                leftTail)
              (List.append (doneBits.map some)
                (List.append ((markedCellsBits processed).map some)
                  (List.append ((markedCellBits b).map some) tailCells)))) =
          finishStartConfigWithTailCellsAndBase
            (List.append processed [b]) tailCells leftTail
      rw [assemblyPrefixDescription_run_state100_done_core]
      unfold finishStartConfigWithTailCellsAndBase
      rw [markedCellsBits_append_single_map]
      simp [finishStartLeft, List.length_append, List.append_assoc]
  | cons next rest ih =>
      rcases assemblyPrefixDescription_run_mark_current_to_state100_withBase_cells_core
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
        AP.runConfig recSteps
            (AP.runConfig 4
              (config 100
                (List.append (finishLengthPrefixRev processed.length)
                  leftTail)
                (List.append (tickBits.map some)
                  (List.append ((stageNatBits rest.length).map some)
                    (List.append ((markedCellsBits processed).map some)
                      (List.append ((markedCellBits b).map some)
                        (List.append ((cellsBits (next :: rest)).map some)
                          tailCells))))))) =
          finishStartConfigWithTailCellsAndBase
            (List.append processed (b :: next :: rest)) tailCells leftTail
      rw [assemblyPrefixDescription_run_state100_tick_core]
      unfold markingState120WithTailCellsAndBase at hrec
      rw [markedCellsBits_append_single_map] at hrec
      simpa [activeLengthPrefixRev_succ, cellsBits_cons,
        List.length_append, List.map_append, List.append_assoc] using hrec

theorem assemblyPrefixDescription_run_state120_bool_tail_to_finish_withBase_cells_core
    (b : Bool) (rest : Word Bool) (tailCells leftTail : List (Option Bool)) :
    exists steps : Nat,
      AP.runConfig steps
          (config 120
            (List.append [none, some true, none, some false] leftTail)
            (List.append
              ((stageNatBits rest.length).map some)
              (List.append
                ((cellBits b).map some)
                (List.append ((cellsBits rest).map some) tailCells)))) =
        finishStartConfigWithTailCellsAndBase
          (b :: rest) tailCells leftTail := by
  rcases assemblyPrefixDescription_run_marking_loop_from_state120_withBase_cells_core
      ([] : Word Bool) b rest tailCells leftTail with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  simpa [markingState120WithTailCellsAndBase,
    activeLengthPrefixRev_zero] using hsteps

end AssemblyPrefixCore


end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC

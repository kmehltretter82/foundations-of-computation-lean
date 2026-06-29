import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Quoter.Assembly.MarkingLoop

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

namespace SelectedProjectionInputQuoterFiniteLeaf

open DovetailInitialLayoutInitializer
private abbrev SIMS :=
  DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription

private abbrev ASM := AssemblySkeletonDescription
private abbrev AP := AssemblyPrefixDescription

def state160AfterRestoreWithTailBitsAndBase
    (w tailBits : Word Bool) (leftTail : List (Option Bool)) :
    Configuration :=
  config 160
    (List.append
      ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits
        w).reverse.map some)
      (List.append
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishStartLeft
          w)
        leftTail))
    (some false :: none :: tailBits.map some)

def appendBlankStartConfigWithTailBitsAndBase
    (w tailBits : Word Bool) (leftTail : List (Option Bool)) :
    Configuration :=
  config 180 (List.append [none, some false] leftTail)
    (List.append
      ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
        w).map some)
      (some false :: none :: tailBits.map some))

def state160AfterRestoreWithTailCellsAndBase
    (w : Word Bool) (tailCells leftTail : List (Option Bool)) :
    Configuration :=
  config 160
    (List.append
      ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits
        w).reverse.map some)
      (List.append
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishStartLeft
          w)
        leftTail))
    (some false :: none :: tailCells)

def appendBlankStartConfigWithTailCellsAndBase
    (w : Word Bool) (tailCells leftTail : List (Option Bool)) :
    Configuration :=
  config 180 (List.append [none, some false] leftTail)
    (List.append
      ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
        w).map some)
      (some false :: none :: tailCells))

theorem assemblySkeletonDescription_run_finish_restore_cells_tailBits_withBase
    (w tailBits : Word Bool) (leftTail : List (Option Bool)) :
    ASM.runConfig (4 * w.length + 2)
        (finishStartConfigWithTailBitsAndBase w
          (false :: false :: tailBits) leftTail) =
      state160AfterRestoreWithTailBitsAndBase w tailBits leftTail := by
  rw [assemblySkeletonDescription_runConfig_eq_scanner]
  · rw [runConfig_add]
    change
      SIMS.runConfig 2
          (SIMS.runConfig (4 * w.length)
            (config 150
              (List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishStartLeft
                  w)
                leftTail)
              (List.append
                ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellsBits
                  w).map some)
                (some false :: some false :: tailBits.map some)))) =
        state160AfterRestoreWithTailBitsAndBase w tailBits leftTail
    rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.run_state150_markedCells]
    rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.run_state150_to_state160]
    simp [state160AfterRestoreWithTailBitsAndBase]
  · simp [finishStartConfigWithTailBitsAndBase, config,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription]

theorem assemblySkeletonDescription_run_finish_restore_cells_tailCells_withBase
    (w : Word Bool) (tailCells leftTail : List (Option Bool)) :
    ASM.runConfig (4 * w.length + 2)
        (finishStartConfigWithTailCellsAndBase w
          (some false :: some false :: tailCells) leftTail) =
      state160AfterRestoreWithTailCellsAndBase w tailCells leftTail := by
  rw [assemblySkeletonDescription_runConfig_eq_scanner]
  · rw [runConfig_add]
    change
      SIMS.runConfig 2
          (SIMS.runConfig (4 * w.length)
            (config 150
              (List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishStartLeft
                  w)
                leftTail)
              (List.append
                ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellsBits
                  w).map some)
                (some false :: some false :: tailCells)))) =
        state160AfterRestoreWithTailCellsAndBase w tailCells leftTail
    rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.run_state150_markedCells]
    rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.run_state150_to_state160]
    simp [state160AfterRestoreWithTailCellsAndBase]
  · simp [finishStartConfigWithTailCellsAndBase, config,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription]

theorem assemblySkeletonDescription_run_state160_bits_to_boundary
    (bitsToRight : Word Bool) (boundary : Option Bool)
    (leftTail right : List (Option Bool)) :
    ASM.runConfig bitsToRight.length
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.state160ScanConfig
          bitsToRight boundary leftTail right) =
      config 160 leftTail
        (boundary ::
          List.append (bitsToRight.reverse.map some) right) := by
  rw [assemblySkeletonDescription_runConfig_eq_scanner]
  · exact
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.run_state160_bits_to_boundary
        bitsToRight boundary leftTail right
  · cases bitsToRight <;>
      simp [DovetailInitialLayoutInitializer.StageInputMarkedScanner.state160ScanConfig,
        config,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription]

theorem assemblySkeletonDescription_run_state160_none_to_state161
    (cell : Option Bool) (left right : List (Option Bool)) :
    ASM.runConfig 1
        (config 160 (cell :: left) (none :: right)) =
      config 161 left (cell :: none :: right) := by
  rw [assemblySkeletonDescription_runConfig_eq_scanner]
  · exact
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.run_state160_none_to_state161
        cell left right
  · simp [config,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription]

theorem assemblySkeletonDescription_run_state161_false_to_state170_withBase
    (left right : List (Option Bool)) :
    ASM.runConfig 1
        (config 161 left (some false :: right)) =
      config 170 (some false :: left) right := by
  rw [assemblySkeletonDescription_runConfig_eq_scanner]
  · cases right <;>
      simp [DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription,
        config, tapeAtCells,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.keep,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.writeMove,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelRestart,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelHalt,
        runConfig, stepConfig, lookupTransition, Matches, transition,
        Tape.read, Tape.write, Tape.move, Tape.moveRight]
  · simp [config,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription]

theorem assemblySkeletonDescription_run_state170_none_to_state180_withBase
    (left right : List (Option Bool)) :
    ASM.runConfig 1
        (config 170 (some false :: left) (none :: right)) =
      config 180 (none :: some false :: left) right := by
  rw [assemblySkeletonDescription_runConfig_eq_scanner]
  · cases right <;>
      simp [DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription,
        config, tapeAtCells,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.keep,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.writeMove,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelRestart,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelHalt,
        runConfig, stepConfig, lookupTransition, Matches, transition,
        Tape.read, Tape.write, Tape.move, Tape.moveRight]
  · simp [config,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription]

theorem assemblySkeletonDescription_run_finish_scan_left_to_append_tailBits_withBase
    (b : Bool) (rest tailBits : Word Bool)
    (leftTail : List (Option Bool)) :
    exists steps : Nat,
      ASM.runConfig steps
          (state160AfterRestoreWithTailBitsAndBase
            (b :: rest) tailBits leftTail) =
        appendBlankStartConfigWithTailBitsAndBase
          (b :: rest) tailBits leftTail := by
  let bits :=
    DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishScanBits
      (b :: rest)
  let scanRight := none :: tailBits.map some
  have hstart :
      state160AfterRestoreWithTailBitsAndBase
          (b :: rest) tailBits leftTail =
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.state160ScanConfig
          bits none (some false :: leftTail) scanRight := by
    cases b <;>
    simp [bits, scanRight,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishScanBits,
      state160AfterRestoreWithTailBitsAndBase,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishStartLeft,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishLengthPrefixRev_eq_scanBits,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.state160ScanConfig,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits_cons,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellBits,
      List.map_append, List.reverse_append, List.append_assoc]
  refine ⟨bits.length + 3, ?_⟩
  rw [show bits.length + 3 = bits.length + (1 + (1 + 1)) by
    omega]
  rw [runConfig_add]
  rw [hstart]
  rw [assemblySkeletonDescription_run_state160_bits_to_boundary]
  rw [runConfig_add]
  rw [assemblySkeletonDescription_run_state160_none_to_state161]
  rw [runConfig_add]
  rw [assemblySkeletonDescription_run_state161_false_to_state170_withBase]
  rw [assemblySkeletonDescription_run_state170_none_to_state180_withBase]
  simp [appendBlankStartConfigWithTailBitsAndBase, bits, scanRight,
    DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishScanBits_reverse_nonempty,
    List.map_append, List.append_assoc]

theorem assemblySkeletonDescription_run_finish_scan_left_to_append_tailCells_withBase
    (b : Bool) (rest : Word Bool) (tailCells leftTail : List (Option Bool)) :
    exists steps : Nat,
      ASM.runConfig steps
          (state160AfterRestoreWithTailCellsAndBase
            (b :: rest) tailCells leftTail) =
        appendBlankStartConfigWithTailCellsAndBase
          (b :: rest) tailCells leftTail := by
  let bits :=
    DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishScanBits
      (b :: rest)
  let scanRight := none :: tailCells
  have hstart :
      state160AfterRestoreWithTailCellsAndBase
          (b :: rest) tailCells leftTail =
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.state160ScanConfig
          bits none (some false :: leftTail) scanRight := by
    cases b <;>
    simp [bits, scanRight,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishScanBits,
      state160AfterRestoreWithTailCellsAndBase,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishStartLeft,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishLengthPrefixRev_eq_scanBits,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.state160ScanConfig,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits_cons,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellBits,
      List.map_append, List.reverse_append, List.append_assoc]
  refine ⟨bits.length + 3, ?_⟩
  rw [show bits.length + 3 = bits.length + (1 + (1 + 1)) by
    omega]
  rw [runConfig_add]
  rw [hstart]
  rw [assemblySkeletonDescription_run_state160_bits_to_boundary]
  rw [runConfig_add]
  rw [assemblySkeletonDescription_run_state160_none_to_state161]
  rw [runConfig_add]
  rw [assemblySkeletonDescription_run_state161_false_to_state170_withBase]
  rw [assemblySkeletonDescription_run_state170_none_to_state180_withBase]
  simp [appendBlankStartConfigWithTailCellsAndBase, bits, scanRight,
    DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishScanBits_reverse_nonempty,
    List.map_append, List.append_assoc]

theorem assemblySkeletonDescription_run_state180_some
    (b : Bool) (left right : List (Option Bool)) :
    ASM.runConfig 1
        (config 180 left (some b :: right)) =
      config 180 (some b :: left) right := by
  rw [assemblySkeletonDescription_runConfig_eq_scanner]
  · exact
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.run_state180_some
        b left right
  · simp [config,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription]

theorem assemblySkeletonDescription_run_state180_bits
    (bits : Word Bool) (left right : List (Option Bool)) :
    ASM.runConfig bits.length
        (config 180 left (List.append (bits.map some) right)) =
      config 180
        (List.append (bits.reverse.map some) left) right := by
  rw [assemblySkeletonDescription_runConfig_eq_scanner]
  · exact
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.run_state180_bits
        bits left right
  · cases bits <;>
      simp [config,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription]

theorem assemblySkeletonDescription_run_state180_none_cons
    (cell : Option Bool) (left right : List (Option Bool)) :
    ASM.runConfig 1
        (config 180 (cell :: left) (none :: right)) =
      config 200 left (cell :: some false :: right) := by
  rw [assemblySkeletonDescription_runConfig_eq_scanner]
  · exact
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.run_state180_none_cons
        cell left right
  · simp [config,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription]

theorem assemblySkeletonDescription_run_append_blank_to_state200_tailBits_withBase
    (b : Bool) (rest tailBits : Word Bool)
    (leftTail : List (Option Bool)) :
    exists steps : Nat,
      ASM.runConfig steps
          (appendBlankStartConfigWithTailBitsAndBase
            (b :: rest) tailBits leftTail) =
        config 200
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
              (b :: rest)).reverse.map some)
            (none :: some false :: leftTail))
          (some false :: some false :: tailBits.map some) := by
  let tailPrefix :=
    DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
      (b :: rest)
  refine ⟨tailPrefix.length + 2, ?_⟩
  rw [show tailPrefix.length + 2 = tailPrefix.length + (1 + 1) by
    omega]
  rw [runConfig_add]
  unfold appendBlankStartConfigWithTailBitsAndBase
  change
    ASM.runConfig (1 + 1)
        (ASM.runConfig tailPrefix.length
          (config 180 (List.append [none, some false] leftTail)
            (List.append (tailPrefix.map some)
              (some false :: none :: tailBits.map some)))) =
      config 200
        (List.append (tailPrefix.reverse.map some)
          (none :: some false :: leftTail))
        (some false :: some false :: tailBits.map some)
  rw [assemblySkeletonDescription_run_state180_bits]
  rw [runConfig_add]
  rw [assemblySkeletonDescription_run_state180_some]
  rw [assemblySkeletonDescription_run_state180_none_cons]
  simp

theorem assemblySkeletonDescription_run_append_blank_to_state200_tailCells_withBase
    (b : Bool) (rest : Word Bool) (tailCells leftTail : List (Option Bool)) :
    exists steps : Nat,
      ASM.runConfig steps
          (appendBlankStartConfigWithTailCellsAndBase
            (b :: rest) tailCells leftTail) =
        config 200
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
              (b :: rest)).reverse.map some)
            (none :: some false :: leftTail))
          (some false :: some false :: tailCells) := by
  let tailPrefix :=
    DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
      (b :: rest)
  refine ⟨tailPrefix.length + 2, ?_⟩
  rw [show tailPrefix.length + 2 = tailPrefix.length + (1 + 1) by
    omega]
  rw [runConfig_add]
  unfold appendBlankStartConfigWithTailCellsAndBase
  change
    ASM.runConfig (1 + 1)
        (ASM.runConfig tailPrefix.length
          (config 180 (List.append [none, some false] leftTail)
            (List.append (tailPrefix.map some)
              (some false :: none :: tailCells)))) =
      config 200
        (List.append (tailPrefix.reverse.map some)
          (none :: some false :: leftTail))
        (some false :: some false :: tailCells)
  rw [assemblySkeletonDescription_run_state180_bits]
  rw [runConfig_add]
  rw [assemblySkeletonDescription_run_state180_some]
  rw [assemblySkeletonDescription_run_state180_none_cons]
  simp

theorem assemblySkeletonDescription_run_finish_tail_false_false_to_state200_withBase
    (b : Bool) (rest tailBits : Word Bool)
    (leftTail : List (Option Bool)) :
    exists steps : Nat,
      ASM.runConfig steps
          (finishStartConfigWithTailBitsAndBase
            (b :: rest) (false :: false :: tailBits) leftTail) =
        config 200
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
              (b :: rest)).reverse.map some)
            (none :: some false :: leftTail))
          (some false :: some false :: tailBits.map some) := by
  rcases assemblySkeletonDescription_run_finish_scan_left_to_append_tailBits_withBase
      b rest tailBits leftTail with
    ⟨scanSteps, hscan⟩
  rcases assemblySkeletonDescription_run_append_blank_to_state200_tailBits_withBase
      b rest tailBits leftTail with
    ⟨appendSteps, happend⟩
  refine
    ⟨(4 * (b :: rest).length + 2) + scanSteps + appendSteps, ?_⟩
  rw [show
      (4 * (b :: rest).length + 2) + scanSteps + appendSteps =
        (4 * (b :: rest).length + 2) +
          (scanSteps + appendSteps) by
    omega]
  rw [runConfig_add]
  rw [assemblySkeletonDescription_run_finish_restore_cells_tailBits_withBase]
  rw [runConfig_add]
  rw [hscan]
  exact happend

theorem assemblySkeletonDescription_run_finish_cells_false_false_to_state200_withBase
    (b : Bool) (rest : Word Bool) (tailCells leftTail : List (Option Bool)) :
    exists steps : Nat,
      ASM.runConfig steps
          (finishStartConfigWithTailCellsAndBase
            (b :: rest) (some false :: some false :: tailCells) leftTail) =
        config 200
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
              (b :: rest)).reverse.map some)
            (none :: some false :: leftTail))
          (some false :: some false :: tailCells) := by
  rcases assemblySkeletonDescription_run_finish_scan_left_to_append_tailCells_withBase
      b rest tailCells leftTail with
    ⟨scanSteps, hscan⟩
  rcases assemblySkeletonDescription_run_append_blank_to_state200_tailCells_withBase
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
  rw [assemblySkeletonDescription_run_finish_restore_cells_tailCells_withBase]
  rw [runConfig_add]
  rw [hscan]
  exact happend

theorem assemblySkeletonDescription_run_empty_stageInput_to_sourceRest_boundary
    (stage : Nat) (sourceRestBits : Word Bool) :
    exists steps : Nat,
      ASM.runConfig steps
          (config ASM.start []
            (List.append
              (List.map some
                (List.append
                  (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
                  (DovetailInitialLayoutInitializer.stageInputBits
                    ([] : Word Bool) stage)))
              (sourceRestBits.map some))) =
        config 210
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage).reverse.map some)
            (List.append [some true, some true, none, some false]
              transitionPrefixLeftTail))
          (sourceRestBits.map some) := by
  refine ⟨6 + (18 + (4 * stage + 4)), ?_⟩
  rw [runConfig_add]
  rw [assemblySkeletonDescription_run_prefix_to_stageInput_tail]
  rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTail_nil]
  change
    ASM.runConfig (18 + (4 * stage + 4))
        (markedTailStartConfigWithBase transitionPrefixLeftTail
          (true :: true ::
            List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage)
              sourceRestBits)) =
      config 210
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).reverse.map some)
          (List.append [some true, some true, none, some false]
            transitionPrefixLeftTail))
        (sourceRestBits.map some)
  rw [runConfig_add]
  rw [assemblySkeletonDescription_run_marked_tail_done_stageNat_to_state200_withBase]
  rw [assemblySkeletonDescription_run_state200_stageNat_to_state210]

theorem assemblyPrefixDescription_run_empty_stageInput_to_sourceRest_boundary
    (stage : Nat) (sourceRestBits : Word Bool) :
    exists steps : Nat,
      AP.runConfig steps
          (config AP.start []
            (List.append
              (List.map some
                (List.append
                  (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
                  (DovetailInitialLayoutInitializer.stageInputBits
                    ([] : Word Bool) stage)))
              (sourceRestBits.map some))) =
        config 210
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage).reverse.map some)
            (List.append [some true, some true, none, some false]
              transitionPrefixLeftTail))
          (sourceRestBits.map some) := by
  refine ⟨6 + (18 + (4 * stage + 4)), ?_⟩
  rw [runConfig_add]
  rw [assemblyPrefixDescription_run_prefix_to_stageInput_tail]
  rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTail_nil]
  change
    AP.runConfig (18 + (4 * stage + 4))
        (markedTailStartConfigWithBase transitionPrefixLeftTail
          (true :: true ::
            List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage)
              sourceRestBits)) =
      config 210
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).reverse.map some)
          (List.append [some true, some true, none, some false]
            transitionPrefixLeftTail))
        (sourceRestBits.map some)
  rw [runConfig_add]
  rw [assemblyPrefixDescription_run_marked_tail_done_stageNat_to_state200_withBase]
  rw [assemblyPrefixDescription_run_state200_stageNat_to_state210]

theorem assemblyPrefixDescription_run_empty_stageInput_to_sourceRest_boundary_cells
    (stage : Nat) (sourceRestCells : List (Option Bool)) :
    exists steps : Nat,
      AP.runConfig steps
          (config AP.start []
            (List.append
              (List.map some
                (List.append
                  (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
                  (DovetailInitialLayoutInitializer.stageInputBits
                    ([] : Word Bool) stage)))
              sourceRestCells)) =
        config 210
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage).reverse.map some)
            (List.append [some true, some true, none, some false]
              transitionPrefixLeftTail))
          sourceRestCells := by
  refine ⟨6 + (18 + (4 * stage + 4)), ?_⟩
  rw [runConfig_add]
  rw [assemblyPrefixDescription_run_prefix_to_stageInput_tail_cells]
  rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTail_nil]
  change
    AP.runConfig (18 + (4 * stage + 4))
        (markedTailStartConfigWithBaseCells transitionPrefixLeftTail
          (List.append
            ((true :: true ::
              DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage).map some)
            sourceRestCells)) =
      config 210
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).reverse.map some)
          (List.append [some true, some true, none, some false]
            transitionPrefixLeftTail))
        sourceRestCells
  rw [runConfig_add]
  rw [assemblyPrefixDescription_run_marked_tail_done_stageNat_to_state200_withBase_cells]
  rw [assemblyPrefixDescription_run_state200_stageNat_to_state210]

theorem assemblySkeletonDescription_run_empty_stageInput_to_sourceRest_boundary_cells
    (stage : Nat) (sourceRestCells : List (Option Bool)) :
    exists steps : Nat,
      ASM.runConfig steps
          (config ASM.start []
            (List.append
              (List.map some
                (List.append
                  (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
                  (DovetailInitialLayoutInitializer.stageInputBits
                    ([] : Word Bool) stage)))
              sourceRestCells)) =
        config 210
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage).reverse.map some)
            (List.append [some true, some true, none, some false]
              transitionPrefixLeftTail))
          sourceRestCells := by
  refine ⟨6 + (18 + (4 * stage + 4)), ?_⟩
  rw [runConfig_add]
  rw [assemblySkeletonDescription_run_prefix_to_stageInput_tail_cells]
  rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTail_nil]
  change
    ASM.runConfig (18 + (4 * stage + 4))
        (markedTailStartConfigWithBaseCells transitionPrefixLeftTail
          (List.append
            ((true :: true ::
              DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage).map some)
            sourceRestCells)) =
      config 210
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).reverse.map some)
          (List.append [some true, some true, none, some false]
            transitionPrefixLeftTail))
        sourceRestCells
  rw [runConfig_add]
  rw [assemblySkeletonDescription_run_marked_tail_done_stageNat_to_state200_withBase_cells]
  rw [assemblySkeletonDescription_run_state200_stageNat_to_state210]

theorem assemblySkeletonDescription_run_nonempty_stageInput_to_sourceRest_boundary
    (b : Bool) (rest : Word Bool) (stage : Nat)
    (sourceRestBits : Word Bool) :
    exists steps : Nat,
      ASM.runConfig steps
          (config ASM.start []
            (List.append
              (List.map some
                (List.append
                  (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
                  (DovetailInitialLayoutInitializer.stageInputBits
                    (b :: rest) stage)))
              (sourceRestBits.map some))) =
        config 210
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage).reverse.map some)
            (List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
                (b :: rest)).reverse.map some)
              (List.append [none, some false] transitionPrefixLeftTail)))
          (sourceRestBits.map some) := by
  rcases
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_false_false_tail
        stage with
    ⟨stageTail, hstageTail⟩
  rcases assemblySkeletonDescription_run_state120_bool_tail_to_finish_withBase
      b rest
      (List.append
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          stage)
        sourceRestBits)
      transitionPrefixLeftTail with
    ⟨markSteps, hmark⟩
  rcases assemblySkeletonDescription_run_finish_tail_false_false_to_state200_withBase
      b rest
      (List.append stageTail sourceRestBits)
      transitionPrefixLeftTail with
    ⟨finishSteps, hfinish⟩
  refine
    ⟨6 + (6 + (markSteps + finishSteps + (4 * stage + 4))), ?_⟩
  rw [show
      6 + (6 + (markSteps + finishSteps + (4 * stage + 4))) =
        6 + (6 + (markSteps + (finishSteps + (4 * stage + 4)))) by
    omega]
  rw [runConfig_add]
  rw [assemblySkeletonDescription_run_prefix_to_stageInput_tail]
  rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTail_cons]
  rw [show
      List.append
          (true :: false ::
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
                    stage))))
          sourceRestBits =
        true :: false ::
          List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              rest.length)
            (List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellBits
                b)
              (List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits
                  rest)
                (List.append
                  (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                    stage)
                  sourceRestBits))) by
    simp [List.append_assoc]]
  change
    ASM.runConfig (6 + (markSteps + (finishSteps + (4 * stage + 4))))
        (markedTailStartConfigWithBase transitionPrefixLeftTail
          (true :: false ::
            List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                rest.length)
              (List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellBits
                  b)
                (List.append
                  (DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits
                    rest)
                  (List.append
                    (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                      stage)
                    sourceRestBits))))) =
      config 210
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).reverse.map some)
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
              (b :: rest)).reverse.map some)
            (List.append [none, some false] transitionPrefixLeftTail)))
        (sourceRestBits.map some)
  rw [runConfig_add]
  rw [assemblySkeletonDescription_run_marked_tail_tick_to_state120_withBase]
  rw [runConfig_add]
  simp [List.map_append] at hmark ⊢
  rw [hmark]
  rw [hstageTail]
  rw [runConfig_add]
  change
    ASM.runConfig (4 * stage + 4)
        (ASM.runConfig finishSteps
          (finishStartConfigWithTailBitsAndBase
            (b :: rest) (false :: false :: List.append stageTail sourceRestBits)
            transitionPrefixLeftTail)) =
      config 210
        (List.append
          ((List.map some (false :: false :: stageTail)).reverse)
          (List.append
            ((List.map some
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
                (b :: rest))).reverse)
            (none :: some false :: transitionPrefixLeftTail)))
        (sourceRestBits.map some)
  rw [hfinish]
  rw [← hstageTail]
  have hright :
      some false :: some false ::
          List.map some (List.append stageTail sourceRestBits) =
        List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).map some)
          (sourceRestBits.map some) := by
    rw [hstageTail]
    simp [List.map_append]
  rw [hright]
  rw [assemblySkeletonDescription_run_state200_stageNat_to_state210]
  simp

theorem assemblySkeletonDescription_run_nonempty_stageInput_to_sourceRest_boundary_cells_aux
    (b : Bool) (rest : Word Bool) (stage : Nat)
    (sourceRestCells : List (Option Bool)) :
    exists steps : Nat,
      ASM.runConfig steps
          (config ASM.start []
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
    ASM.runConfig
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

theorem assemblySkeletonDescription_run_stageInput_to_sourceRest_boundary_cells
    (w : Word Bool) (stage : Nat)
    (sourceRestCells : List (Option Bool)) :
    exists steps : Nat,
      ASM.runConfig steps
          (config ASM.start []
            (List.append
              (List.map some
                (List.append
                  (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
                  (DovetailInitialLayoutInitializer.stageInputBits
                    w stage)))
              sourceRestCells)) =
        config 210
          (assemblySourceRestBoundaryLeftRev w stage)
          sourceRestCells := by
  cases w with
  | nil =>
      simpa [assemblySourceRestBoundaryLeftRev] using
        assemblySkeletonDescription_run_empty_stageInput_to_sourceRest_boundary_cells
          stage sourceRestCells
  | cons b rest =>
      simpa [assemblySourceRestBoundaryLeftRev] using
        assemblySkeletonDescription_run_nonempty_stageInput_to_sourceRest_boundary_cells_aux
          b rest stage sourceRestCells

theorem assemblySkeletonDescription_run_stageInput_to_sourceRest_boundary
    (w : Word Bool) (stage : Nat) (sourceRestBits : Word Bool) :
    exists steps : Nat,
      ASM.runConfig steps
          (config ASM.start []
            (List.append
              (List.map some
                (List.append
                  (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
                  (DovetailInitialLayoutInitializer.stageInputBits
                    w stage)))
              (sourceRestBits.map some))) =
        config 210
          (assemblySourceRestBoundaryLeftRev w stage)
          (sourceRestBits.map some) := by
  cases w with
  | nil =>
      simpa [assemblySourceRestBoundaryLeftRev] using
        assemblySkeletonDescription_run_empty_stageInput_to_sourceRest_boundary
          stage sourceRestBits
  | cons b rest =>
      simpa [assemblySourceRestBoundaryLeftRev] using
        assemblySkeletonDescription_run_nonempty_stageInput_to_sourceRest_boundary
          b rest stage sourceRestBits


end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC

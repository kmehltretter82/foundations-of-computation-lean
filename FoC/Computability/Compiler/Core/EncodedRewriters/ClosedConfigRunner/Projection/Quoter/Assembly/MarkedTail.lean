import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Quoter.Assembly.Prefix

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

theorem assemblySkeletonDescription_run_marked_tail_done_stageNat_to_state200_withBase
    (stage : Nat) (suffixBits : Word Bool)
    (leftTail : List (Option Bool)) :
    ASM.runConfig 18
        (markedTailStartConfigWithBase leftTail
          (true :: true ::
            List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage)
              suffixBits)) =
      config 200
        (List.append [some true, some true, none, some false]
          leftTail)
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).map some)
          (suffixBits.map some)) := by
  cases stage <;>
    simp [ASM, AssemblySkeletonDescription, markedTailStartConfigWithBase,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits,
      encodeNat, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
      config, tapeAtCells,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keep,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.writeMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelRestart,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelHalt,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem assemblySkeletonDescription_run_marked_tail_done_stageNat_to_state200_withBase_cells
    (stage : Nat) (suffixCells : List (Option Bool))
    (leftTail : List (Option Bool)) :
    ASM.runConfig 18
        (markedTailStartConfigWithBaseCells leftTail
          (List.append
            ((true :: true ::
              DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage).map some)
            suffixCells)) =
      config 200
        (List.append [some true, some true, none, some false]
          leftTail)
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).map some)
          suffixCells) := by
  cases stage <;>
    cases suffixCells <;>
    simp [ASM, AssemblySkeletonDescription, markedTailStartConfigWithBaseCells,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits,
      encodeNat, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
      config, tapeAtCells,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keep,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.writeMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelRestart,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelHalt,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem assemblyPrefixDescription_run_marked_tail_done_stageNat_to_state200_withBase
    (stage : Nat) (suffixBits : Word Bool)
    (leftTail : List (Option Bool)) :
    AP.runConfig 18
        (markedTailStartConfigWithBase leftTail
          (true :: true ::
            List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage)
              suffixBits)) =
      config 200
        (List.append [some true, some true, none, some false]
          leftTail)
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).map some)
          (suffixBits.map some)) := by
  cases stage <;>
    simp [AP, AssemblyPrefixDescription, markedTailStartConfigWithBase,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits,
      encodeNat, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
      config, tapeAtCells,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keep,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.writeMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelRestart,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelHalt,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem assemblyPrefixDescription_run_marked_tail_done_stageNat_to_state200_withBase_cells
    (stage : Nat) (suffixCells : List (Option Bool))
    (leftTail : List (Option Bool)) :
    AP.runConfig 18
        (markedTailStartConfigWithBaseCells leftTail
          (List.append
            ((true :: true ::
              DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage).map some)
            suffixCells)) =
      config 200
        (List.append [some true, some true, none, some false]
          leftTail)
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).map some)
          suffixCells) := by
  cases stage <;>
    cases suffixCells <;>
    simp [AP, AssemblyPrefixDescription, markedTailStartConfigWithBaseCells,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits,
      encodeNat, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
      config, tapeAtCells,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keep,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.writeMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelRestart,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelHalt,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem assemblySkeletonDescription_run_marked_tail_tick_to_state120_withBase
    (bits : Word Bool) (leftTail : List (Option Bool)) :
    ASM.runConfig 6
        (markedTailStartConfigWithBase leftTail
          (true :: false :: bits)) =
      config 120
        (List.append [none, some true, none, some false] leftTail)
        (bits.map some) := by
  rw [assemblySkeletonDescription_runConfig_eq_scanner]
  · simp [markedTailStartConfigWithBase,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription,
      config, tapeAtCells,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keep,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.writeMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelRestart,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelHalt,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
    generalize bits.map some = cells
    cases cells <;> rfl
  · simp [markedTailStartConfigWithBase,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription]

theorem assemblySkeletonDescription_run_marked_tail_tick_to_state120_withBase_cells
    (tailCells : List (Option Bool)) (leftTail : List (Option Bool)) :
    ASM.runConfig 6
        (markedTailStartConfigWithBaseCells leftTail
          (some true :: some false :: tailCells)) =
      config 120
        (List.append [none, some true, none, some false] leftTail)
        tailCells := by
  cases tailCells <;>
    simp [ASM, AssemblySkeletonDescription, markedTailStartConfigWithBaseCells,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription,
      config, tapeAtCells,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keep,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.writeMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelRestart,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelHalt,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem assemblyPrefixDescription_run_marked_tail_tick_to_state120_withBase_cells
    (tailCells : List (Option Bool)) (leftTail : List (Option Bool)) :
    AP.runConfig 6
        (markedTailStartConfigWithBaseCells leftTail
          (some true :: some false :: tailCells)) =
      config 120
        (List.append [none, some true, none, some false] leftTail)
        tailCells := by
  cases tailCells <;>
    simp [AP, AssemblyPrefixDescription, markedTailStartConfigWithBaseCells,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription,
      config, tapeAtCells,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keep,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.writeMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelRestart,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelHalt,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem assemblySkeletonDescription_run_state200_tick
    (left right : List (Option Bool)) :
    ASM.runConfig 4
        (config 200 left
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits.map
              some)
            right)) =
      config 200
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits.reverse.map
            some)
          left)
        right := by
  cases right <;>
    simp [ASM, AssemblySkeletonDescription,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits,
      encodeCodeSymbolAsInput, config, tapeAtCells,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keep,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.writeMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelRestart,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelHalt,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem assemblySkeletonDescription_run_state200_done_to_state210
    (left right : List (Option Bool)) :
    ASM.runConfig 4
        (config 200 left
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.doneBits.map
              some)
            right)) =
      config 210
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.doneBits.reverse.map
            some)
          left)
        right := by
  cases right <;>
    simp [ASM, AssemblySkeletonDescription,
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

theorem assemblySkeletonDescription_run_state200_stageNat_to_state210
    (stage : Nat) (left right : List (Option Bool)) :
    ASM.runConfig (4 * stage + 4)
        (config 200 left
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage).map some)
            right)) =
      config 210
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).reverse.map some)
          left)
        right := by
  induction stage generalizing left with
  | zero =>
      simpa [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_zero] using
        assemblySkeletonDescription_run_state200_done_to_state210
          left right
  | succ stage ih =>
      rw [show 4 * (stage + 1) + 4 = 4 + (4 * stage + 4) by
        omega]
      rw [runConfig_add]
      rw [show
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              (stage + 1)).map some =
            List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits.map
                some)
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage).map some) by
          simp [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_succ,
            DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits,
            encodeCodeSymbolAsInput]]
      change
        ASM.runConfig (4 * stage + 4)
          (ASM.runConfig 4
            (config 200 left
              (List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits.map
                  some)
                (List.append
                  ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                    stage).map some)
                  right)))) =
          config 210
            (List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                (stage + 1)).reverse.map some)
              left)
            right
      rw [assemblySkeletonDescription_run_state200_tick]
      have h := ih
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits.reverse.map
            some)
          left)
      simpa [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_succ,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits,
        encodeCodeSymbolAsInput, List.reverse_append, List.map_append,
        List.append_assoc] using h

theorem assemblyPrefixDescription_run_state200_tick
    (left right : List (Option Bool)) :
    AP.runConfig 4
        (config 200 left
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits.map
              some)
            right)) =
      config 200
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits.reverse.map
            some)
          left)
        right := by
  cases right <;>
    simp [AP, AssemblyPrefixDescription,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits,
      encodeCodeSymbolAsInput, config, tapeAtCells,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keep,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.writeMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelRestart,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelHalt,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem assemblyPrefixDescription_run_state200_done_to_state210
    (left right : List (Option Bool)) :
    AP.runConfig 4
        (config 200 left
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.doneBits.map
              some)
            right)) =
      config 210
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.doneBits.reverse.map
            some)
          left)
        right := by
  cases right <;>
    simp [AP, AssemblyPrefixDescription,
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

theorem assemblyPrefixDescription_run_state200_stageNat_to_state210
    (stage : Nat) (left right : List (Option Bool)) :
    AP.runConfig (4 * stage + 4)
        (config 200 left
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage).map some)
            right)) =
      config 210
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).reverse.map some)
          left)
        right := by
  induction stage generalizing left with
  | zero =>
      simpa [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_zero] using
        assemblyPrefixDescription_run_state200_done_to_state210
          left right
  | succ stage ih =>
      rw [show 4 * (stage + 1) + 4 = 4 + (4 * stage + 4) by
        omega]
      rw [runConfig_add]
      rw [show
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              (stage + 1)).map some =
            List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits.map
                some)
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage).map some) by
          simp [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_succ,
            DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits,
            encodeCodeSymbolAsInput]]
      change
        AP.runConfig (4 * stage + 4)
          (AP.runConfig 4
            (config 200 left
              (List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits.map
                  some)
                (List.append
                  ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                    stage).map some)
                  right)))) =
          config 210
            (List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                (stage + 1)).reverse.map some)
              left)
            right
      rw [assemblyPrefixDescription_run_state200_tick]
      have h := ih
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits.reverse.map
            some)
          left)
      simpa [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_succ,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits,
        encodeCodeSymbolAsInput, List.reverse_append, List.map_append,
        List.append_assoc] using h

def finishStartConfigWithTailBitsAndBase
    (w tailBits : Word Bool) (leftTail : List (Option Bool)) :
    Configuration :=
  config 150
    (List.append
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishStartLeft
        w)
      leftTail)
    (List.append
      ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellsBits
        w).map some)
      (tailBits.map some))

def markingState120WithTailBitsAndBase
    (processed : Word Bool) (b : Bool) (rest tailBits : Word Bool)
    (leftTail : List (Option Bool)) :
    Configuration :=
  config 120
    (List.append
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.activeLengthPrefixRev
        processed.length)
      leftTail)
    (List.append
      ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        rest.length).map some)
      (List.append
        ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellsBits
          processed).map some)
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellBits
            b).map some)
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits
              rest).map some)
            (tailBits.map some)))))

def state100AfterMarkedWithTailBitsAndBase
    (processed : Word Bool) (b : Bool) (rest tailBits : Word Bool)
    (leftTail : List (Option Bool)) :
    Configuration :=
  config 100
    (List.append
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishLengthPrefixRev
        processed.length)
      leftTail)
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
              rest).map some)
            (tailBits.map some)))))

def finishStartConfigWithTailCellsAndBase
    (w : Word Bool) (tailCells leftTail : List (Option Bool)) :
    Configuration :=
  config 150
    (List.append
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishStartLeft
        w)
      leftTail)
    (List.append
      ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellsBits
        w).map some)
      tailCells)

def markingState120WithTailCellsAndBase
    (processed : Word Bool) (b : Bool) (rest : Word Bool)
    (tailCells leftTail : List (Option Bool)) :
    Configuration :=
  config 120
    (List.append
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.activeLengthPrefixRev
        processed.length)
      leftTail)
    (List.append
      ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        rest.length).map some)
      (List.append
        ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellsBits
          processed).map some)
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellBits
            b).map some)
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits
              rest).map some)
            tailCells))))

def state100AfterMarkedWithTailCellsAndBase
    (processed : Word Bool) (b : Bool) (rest : Word Bool)
    (tailCells leftTail : List (Option Bool)) :
    Configuration :=
  config 100
    (List.append
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishLengthPrefixRev
        processed.length)
      leftTail)
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
              rest).map some)
            tailCells))))


end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC

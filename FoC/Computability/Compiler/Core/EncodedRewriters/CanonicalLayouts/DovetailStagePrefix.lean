import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.StageInputMarkedScanner.ClosedBasic

set_option doc.verso true

/-!
# Dovetail stage-prefix scanner

The complete stage-input validator halts only when the input ends immediately
after the stage number.  A complete
{name (full := FoC.Computability.MachineDescription.DovetailLayout)}`MachineDescription.DovetailLayout`
has more fields after that
same prefix, so the bounded-layout parser needs a suffix-aware variant.  This
module starts that split by reusing the existing marked stage-input scanner and
changing only its final boundary behavior: after the stage natural has been
validated, a nonblank suffix is accepted as the handoff point for the next
layout-field scanner.
-/

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters
namespace CanonicalLayouts
namespace DovetailStagePrefix

open FoC.Computability.DovetailInitialLayoutInitializer
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner

def MarkedPrefixScannerDescription : MachineDescription where
  stateCount :=
    FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription.stateCount
  start :=
    FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription.start
  halt :=
    FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription.halt
  transitions :=
    FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription.transitions ++
      [ FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove
          210 (some false) Direction.left
          FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription.halt
      , FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove
          210 (some true) Direction.left
          FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription.halt
      ]

theorem markedPrefixScannerDescription_wellFormed :
    MarkedPrefixScannerDescription.WellFormed := by
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · intro t ht
    exact transition_wellFormed_of_all
      (l := MarkedPrefixScannerDescription.transitions)
      (stateCount := MarkedPrefixScannerDescription.stateCount)
      (by
        native_decide) t ht
  · intro t u ht hu hkey
    exact transition_deterministic_of_all
      (l := MarkedPrefixScannerDescription.transitions)
      (by
        native_decide) t u ht hu hkey

theorem markedPrefixScannerDescription_haltTransitionFree :
    MarkedPrefixScannerDescription.HaltTransitionFree := by
  intro t ht
  exact transition_notFrom_of_all
    (l := MarkedPrefixScannerDescription.transitions)
    (state := MarkedPrefixScannerDescription.halt)
    (by
      native_decide) t ht

theorem markedPrefixScannerDescription_subroutineReady :
    MarkedPrefixScannerDescription.SubroutineReady :=
  ⟨markedPrefixScannerDescription_wellFormed,
    markedPrefixScannerDescription_haltTransitionFree⟩

theorem markedPrefix_lookup_210_false :
    MarkedPrefixScannerDescription.lookupTransition 210 (some false) =
      some
        (keepMove 210 (some false) Direction.left
          MarkedPrefixScannerDescription.halt) := by
  native_decide

theorem markedPrefix_lookup_210_true :
    MarkedPrefixScannerDescription.lookupTransition 210 (some true) =
      some
        (keepMove 210 (some true) Direction.left
          MarkedPrefixScannerDescription.halt) := by
  native_decide

theorem markedPrefix_run_state200_stageNat_to_state210
    (stage : Nat) (left right : List (Option Bool)) :
    MarkedPrefixScannerDescription.runConfig (4 * stage + 4)
        (config 200 left
          (List.append ((stageNatBits stage).map some) right)) =
      config
        210
        (List.append ((stageNatBits stage).reverse.map some) left)
        right := by
  induction stage generalizing left with
  | zero =>
      simpa [MarkedPrefixScannerDescription,
        stageNatBits_zero]
        using
          run_state200_done_to_state210 left right
  | succ stage ih =>
      rw [show 4 * (stage + 1) + 4 = 4 + (4 * stage + 4) by
        omega]
      rw [MachineDescription.runConfig_add]
      rw [show
          (stageNatBits (stage + 1)).map some =
            List.append (tickBits.map some)
              ((stageNatBits stage).map some) by
          simp [stageNatBits_succ, tickBits,
            MachineDescription.encodeCodeSymbolAsInput]]
      change
        MarkedPrefixScannerDescription.runConfig
            (4 * stage + 4)
            (MarkedPrefixScannerDescription.runConfig 4
              (config 200 left
                (List.append (tickBits.map some)
                  (List.append ((stageNatBits stage).map some) right)))) =
          config 210
            (List.append ((stageNatBits (stage + 1)).reverse.map some) left)
            right
      have htick :
          MarkedPrefixScannerDescription.runConfig 4
              (config 200 left
                (List.append (tickBits.map some)
                  (List.append ((stageNatBits stage).map some) right))) =
            config 200
              (List.append (tickBits.reverse.map some) left)
              (List.append ((stageNatBits stage).map some) right) := by
        simpa [MarkedPrefixScannerDescription] using
          run_state200_tick left
            (List.append ((stageNatBits stage).map some) right)
      rw [htick]
      have h := ih (List.append (tickBits.reverse.map some) left)
      simpa [stageNatBits_succ, tickBits,
        MachineDescription.encodeCodeSymbolAsInput,
        List.reverse_append, List.map_append, List.append_assoc] using h

theorem markedPrefix_run_state210_handoff
    (b : Bool) (cell : Option Bool)
    (left right : List (Option Bool)) :
    MarkedPrefixScannerDescription.runConfig 1
        (config 210 (cell :: left) (some b :: right)) =
      config MarkedPrefixScannerDescription.halt left
        (cell :: some b :: right) := by
  cases b <;> cases cell <;> cases right <;>
    simp [config, tapeAtCells, keepMove,
      markedPrefix_lookup_210_false, markedPrefix_lookup_210_true,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft]

theorem stageNatBits_reverse_map_some_cons
    (stage : Nat) :
    exists tail : List (Option Bool),
      (stageNatBits stage).reverse.map some = some true :: tail := by
  induction stage with
  | zero =>
      exact ⟨[some true, some false, some false], rfl⟩
  | succ stage ih =>
      rcases ih with ⟨tail, htail⟩
      refine
        ⟨List.append tail
          ((tickBits.reverse).map some), ?_⟩
      simp [stageNatBits_succ, tickBits,
        MachineDescription.encodeCodeSymbolAsInput,
        List.map_append, htail, List.append_assoc]

theorem markedPrefix_run_state200_stageNat_handoff
    (stage : Nat) (b : Bool)
    (left right : List (Option Bool)) :
    exists tail : List (Option Bool),
      MarkedPrefixScannerDescription.runConfig (4 * stage + 5)
          (config 200 left
            (List.append ((stageNatBits stage).map some)
              (some b :: right))) =
        config MarkedPrefixScannerDescription.halt
          (List.append tail left)
          (some true :: some b :: right) := by
  rcases stageNatBits_reverse_map_some_cons stage with
    ⟨tail, htail⟩
  refine ⟨tail, ?_⟩
  rw [show 4 * stage + 5 = (4 * stage + 4) + 1 by omega]
  rw [MachineDescription.runConfig_add]
  rw [markedPrefix_run_state200_stageNat_to_state210]
  rw [htail]
  simpa [List.append_assoc] using
    markedPrefix_run_state210_handoff b (some true)
      (List.append tail left) right

end DovetailStagePrefix
end CanonicalLayouts
end EncodedRewriters

end Computability
end FoC

import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.TapeLemmas
import FoC.Computability.Compiler.Core.CommonGround.SeqComposition
import FoC.Computability.Compiler.Core.DovetailInitLayout.StageInputMarkedScanner.ClosedBasic

set_option doc.verso true

/-!
# Dovetail stage-prefix scanner

The complete stage-input validator halts only when the input ends immediately
after the stage number.  A complete
{name (full := FoC.Computability.MachineDescription.DovetailLayout)}`DovetailLayout`
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
open MachineDescription

namespace EncRewriters
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
  · decide
  constructor
  · decide
  constructor
  · decide
  constructor
  · exact transition_wellFormed_of_all
      (l := MarkedPrefixScannerDescription.transitions)
      (stateCount := MarkedPrefixScannerDescription.stateCount)
      (by
        decide)
  · exact transition_deterministic_of_all
      (l := MarkedPrefixScannerDescription.transitions)
      (by
        decide)

theorem markedPrefixScannerDescription_haltTransitionFree :
    MarkedPrefixScannerDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := MarkedPrefixScannerDescription.transitions)
    (state := MarkedPrefixScannerDescription.halt)
    (by
      decide)

theorem markedPrefixScannerDescription_subroutineReady :
    MarkedPrefixScannerDescription.SubroutineReady :=
  ⟨markedPrefixScannerDescription_wellFormed,
    markedPrefixScannerDescription_haltTransitionFree⟩

def NatSuffixScannerDescription : MachineDescription where
  stateCount := MarkedPrefixScannerDescription.stateCount
  start := 200
  halt := MarkedPrefixScannerDescription.halt
  transitions := MarkedPrefixScannerDescription.transitions

theorem natSuffixScannerDescription_wellFormed :
    NatSuffixScannerDescription.WellFormed := by
  constructor
  · decide
  constructor
  · decide
  constructor
  · decide
  constructor
  · exact transition_wellFormed_of_all
      (l := NatSuffixScannerDescription.transitions)
      (stateCount := NatSuffixScannerDescription.stateCount)
      (by
        decide)
  · exact transition_deterministic_of_all
      (l := NatSuffixScannerDescription.transitions)
      (by
        decide)

theorem natSuffixScannerDescription_haltTransitionFree :
    NatSuffixScannerDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := NatSuffixScannerDescription.transitions)
    (state := NatSuffixScannerDescription.halt)
    (by
      decide)

theorem natSuffixScannerDescription_subroutineReady :
    NatSuffixScannerDescription.SubroutineReady :=
  ⟨natSuffixScannerDescription_wellFormed,
    natSuffixScannerDescription_haltTransitionFree⟩

def nonemptyNatSuffixTransitions : List TransitionDescription :=
  StageInputMarkedScannerDescription.transitions.filter
      (fun t => !((t.source == 210) && (t.read == none))) ++
    [ keepMove 210 (some false) Direction.left
        StageInputMarkedScannerDescription.halt
    , keepMove 210 (some true) Direction.left
        StageInputMarkedScannerDescription.halt
    ]

def NonemptyNatSuffixScannerDescription : MachineDescription where
  stateCount := StageInputMarkedScannerDescription.stateCount
  start := 200
  halt := StageInputMarkedScannerDescription.halt
  transitions := nonemptyNatSuffixTransitions

theorem nonemptyNatSuffixScannerDescription_wellFormed :
    NonemptyNatSuffixScannerDescription.WellFormed := by
  constructor
  · decide
  constructor
  · decide
  constructor
  · decide
  constructor
  · exact transition_wellFormed_of_all
      (l := NonemptyNatSuffixScannerDescription.transitions)
      (stateCount := NonemptyNatSuffixScannerDescription.stateCount)
      (by
        decide)
  · exact transition_deterministic_of_all
      (l := NonemptyNatSuffixScannerDescription.transitions)
      (by
        decide)

theorem nonemptyNatSuffixScannerDescription_haltTransitionFree :
    NonemptyNatSuffixScannerDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := NonemptyNatSuffixScannerDescription.transitions)
    (state := NonemptyNatSuffixScannerDescription.halt)
    (by
      decide)

theorem nonemptyNatSuffixScannerDescription_subroutineReady :
    NonemptyNatSuffixScannerDescription.SubroutineReady :=
  ⟨nonemptyNatSuffixScannerDescription_wellFormed,
    nonemptyNatSuffixScannerDescription_haltTransitionFree⟩

theorem natBits_eq_encodeNatAppend
    (n : Nat) (suffix : Word MachineCodeSymbol) :
    encodeCodeWordAsInput
        (encodeNatAppend n suffix) =
      List.append (stageNatBits n)
        (encodeCodeWordAsInput suffix) := by
  rw [encodeNatAppend]
  rw [encodeCodeWordAsInput_append]
  rfl

private theorem runConfig_eq_of_transitions_eq
    (D E : MachineDescription)
    (htrans : D.transitions = E.transitions)
    (n : Nat) (c : Configuration) :
    D.runConfig n c = E.runConfig n c := by
  induction n generalizing c with
  | zero =>
      rfl
  | succ n ih =>
      change
        (match D.stepConfig c with
        | none => c
        | some next => D.runConfig n next) =
          match E.stepConfig c with
          | none => c
          | some next => E.runConfig n next
      have hstep : D.stepConfig c = E.stepConfig c := by
        unfold stepConfig
        unfold lookupTransition
        rw [htrans]
      rw [hstep]
      cases E.stepConfig c with
      | none =>
          rfl
      | some next =>
          exact ih next

private theorem markedPrefix_lookup_210_false :
    MarkedPrefixScannerDescription.lookupTransition 210 (some false) =
      some
        (keepMove 210 (some false) Direction.left
          MarkedPrefixScannerDescription.halt) := by
  decide

private theorem markedPrefix_lookup_210_true :
    MarkedPrefixScannerDescription.lookupTransition 210 (some true) =
      some
        (keepMove 210 (some true) Direction.left
          MarkedPrefixScannerDescription.halt) := by
  decide

private theorem nonemptyNatSuffix_lookup_210_false :
    NonemptyNatSuffixScannerDescription.lookupTransition 210 (some false) =
      some
        (keepMove 210 (some false) Direction.left
          NonemptyNatSuffixScannerDescription.halt) := by
  decide

private theorem nonemptyNatSuffix_lookup_210_true :
    NonemptyNatSuffixScannerDescription.lookupTransition 210 (some true) =
      some
        (keepMove 210 (some true) Direction.left
          NonemptyNatSuffixScannerDescription.halt) := by
  decide

private theorem nonemptyNatSuffix_lookup_210_none :
    NonemptyNatSuffixScannerDescription.lookupTransition 210 none = none := by
  decide

private theorem markedPrefix_run_state200_stageNat_to_state210
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
        using!
          run_state200_done_to_state210 left right
  | succ stage ih =>
      rw [show 4 * (stage + 1) + 4 = 4 + (4 * stage + 4) by
        lia]
      rw [runConfig_add]
      rw [show
          (stageNatBits (stage + 1)).map some =
            List.append (tickBits.map some)
              ((stageNatBits stage).map some) by
          simp [stageNatBits_succ, tickBits,
            encodeCodeSymbolAsInput]]
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
        simpa [MarkedPrefixScannerDescription] using!
          run_state200_tick left
            (List.append ((stageNatBits stage).map some) right)
      rw [htick]
      have h := ih (List.append (tickBits.reverse.map some) left)
      simpa [stageNatBits_succ, tickBits,
        encodeCodeSymbolAsInput,
        List.reverse_append, List.map_append, List.append_assoc] using h

private theorem markedPrefix_run_state210_handoff
    (b : Bool) (cell : Option Bool)
    (left right : List (Option Bool)) :
    MarkedPrefixScannerDescription.runConfig 1
        (config 210 (cell :: left) (some b :: right)) =
      config MarkedPrefixScannerDescription.halt left
        (cell :: some b :: right) := by
  cases b <;> cases cell <;> cases right <;>
    simp [config, tapeAtCells, keepMove,
      markedPrefix_lookup_210_false, markedPrefix_lookup_210_true,
      runConfig, stepConfig,
      transition, Tape.read, Tape.write, Tape.move,
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
        encodeCodeSymbolAsInput,
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
  rw [show 4 * stage + 5 = (4 * stage + 4) + 1 by lia]
  rw [runConfig_add]
  rw [markedPrefix_run_state200_stageNat_to_state210]
  rw [htail]
  simpa [List.append_assoc] using
    markedPrefix_run_state210_handoff b (some true)
      (List.append tail left) right

private theorem markedPrefix_run_state100_tick
    (left tail : List (Option Bool)) :
    MarkedPrefixScannerDescription.runConfig 4
        (config 100 left
          (List.append (tickBits.map some) tail)) =
      config 120 (List.append markedTickRev left) tail := by
  cases tail <;>
  simp [MarkedPrefixScannerDescription, StageInputMarkedScannerDescription,
    tickBits, markedTickRev, encodeCodeSymbolAsInput,
    config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart, scanLeftToSentinelHalt,
    runConfig, stepConfig, lookupTransition, Matches, transition,
    Tape.read, Tape.write, Tape.move, Tape.moveRight]

private theorem markedPrefix_run_state100_done
    (left tail : List (Option Bool)) :
    MarkedPrefixScannerDescription.runConfig 4
        (config 100 left
          (List.append (doneBits.map some) tail)) =
      config 150
        (List.append (doneBits.reverse.map some) left) tail := by
  cases tail <;>
  simp [MarkedPrefixScannerDescription, StageInputMarkedScannerDescription,
    doneBits, encodeCodeSymbolAsInput, config, tapeAtCells,
    keep, keepMove, writeMove,
    scanLeftToSentinelRestart, scanLeftToSentinelHalt,
    runConfig, stepConfig, lookupTransition, Matches, transition,
    Tape.read, Tape.write, Tape.move, Tape.moveRight]

private theorem markedPrefix_run_state120_tick
    (left right : List (Option Bool)) :
    MarkedPrefixScannerDescription.runConfig 4
        (config 120 left
          (List.append (tickBits.map some) right)) =
      config 120
        (List.append (tickBits.reverse.map some) left) right := by
  cases right <;>
  simp [MarkedPrefixScannerDescription, StageInputMarkedScannerDescription,
    tickBits, config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart, scanLeftToSentinelHalt,
    runConfig, stepConfig, lookupTransition, Matches, transition,
    encodeCodeSymbolAsInput, Tape.read, Tape.write, Tape.move, Tape.moveRight]

private theorem markedPrefix_run_state120_done
    (left right : List (Option Bool)) :
    MarkedPrefixScannerDescription.runConfig 4
        (config 120 left
          (List.append (doneBits.map some) right)) =
      config 130
        (List.append (doneBits.reverse.map some) left) right := by
  cases right <;>
  simp [MarkedPrefixScannerDescription, StageInputMarkedScannerDescription,
    doneBits, config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart, scanLeftToSentinelHalt,
    runConfig, stepConfig, lookupTransition, Matches, transition,
    encodeCodeSymbolAsInput, Tape.read, Tape.write, Tape.move, Tape.moveRight]

private theorem markedPrefix_run_state120_stageNat
    (n : Nat) (left right : List (Option Bool)) :
    MarkedPrefixScannerDescription.runConfig (4 * n + 4)
        (config 120 left
          (List.append ((stageNatBits n).map some) right)) =
      config 130
        (List.append ((stageNatBits n).reverse.map some) left)
        right := by
  induction n generalizing left with
  | zero =>
      simpa [stageNatBits_zero] using!
        markedPrefix_run_state120_done left right
  | succ n ih =>
      rw [show 4 * (n + 1) + 4 = 4 + (4 * n + 4) by
        lia]
      rw [runConfig_add]
      rw [show
          List.append ((stageNatBits (n + 1)).map some) right =
            List.append (tickBits.map some)
              (List.append ((stageNatBits n).map some) right) by
        simp [stageNatBits_succ, tickBits, encodeCodeSymbolAsInput]]
      rw [markedPrefix_run_state120_tick]
      rw [ih]
      simp [stageNatBits_succ, tickBits, encodeCodeSymbolAsInput,
        List.map_append, List.append_assoc]

private theorem markedPrefix_run_state130_markedCell
    (b : Bool) (left right : List (Option Bool)) :
    MarkedPrefixScannerDescription.runConfig 4
        (config 130 left
          (List.append ((markedCellBits b).map some) right)) =
      config 130
        (List.append ((markedCellBits b).reverse.map some) left)
        right := by
  cases b <;> cases right <;>
  simp [MarkedPrefixScannerDescription, StageInputMarkedScannerDescription,
    markedCellBits, config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart, scanLeftToSentinelHalt,
    runConfig, stepConfig, lookupTransition, Matches, transition,
    Tape.read, Tape.write, Tape.move, Tape.moveRight]

private theorem markedPrefix_run_state130_markedCells
    (processed : Word Bool) (left right : List (Option Bool)) :
    MarkedPrefixScannerDescription.runConfig
        (4 * processed.length)
        (config 130 left
          (List.append ((markedCellsBits processed).map some)
            right)) =
      config 130
        (List.append ((markedCellsBits processed).reverse.map some)
          left)
        right := by
  induction processed generalizing left with
  | nil =>
      rfl
  | cons b rest ih =>
      rw [show 4 * (b :: rest).length =
          4 + 4 * rest.length by simp; lia]
      rw [runConfig_add]
      rw [show
          List.append ((markedCellsBits (b :: rest)).map some)
              right =
            List.append ((markedCellBits b).map some)
              (List.append ((markedCellsBits rest).map some)
                right) by
          simp [markedCellsBits, List.map_append, List.append_assoc]]
      rw [markedPrefix_run_state130_markedCell]
      rw [ih]
      simp [markedCellsBits, List.reverse_append, List.map_append,
        List.append_assoc]

private theorem markedPrefix_run_state130_currentCell
    (b : Bool) (left right : List (Option Bool)) :
    MarkedPrefixScannerDescription.runConfig 6
        (config 130 left
          (List.append ((cellBits b).map some) right)) =
      config 140 (some true :: some true :: left)
        (some b :: some (!b) :: right) := by
  cases b <;> cases right <;>
  simp [MarkedPrefixScannerDescription, StageInputMarkedScannerDescription,
    cellBits, config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart, scanLeftToSentinelHalt,
    runConfig, stepConfig, lookupTransition, Matches, transition,
    encodeCodeSymbolAsInput, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    Tape.moveRight]

private theorem markedPrefix_run_state140_returnToLengthMarker
    (scanRev : Word Bool) (headBit : Bool)
    (leftTail right : List (Option Bool)) :
    MarkedPrefixScannerDescription.runConfig
        (scanRev.length + 4)
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
      simp [MarkedPrefixScannerDescription, StageInputMarkedScannerDescription,
        config, tapeAtCells, keep, keepMove, writeMove,
        scanLeftToSentinelRestart, scanLeftToSentinelHalt,
        runConfig, stepConfig, lookupTransition, Matches, transition,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons b rest ih =>
      rw [show (b :: rest).length + 4 =
          1 + (rest.length + 4) by
        simp
        lia]
      rw [runConfig_add]
      change
        MarkedPrefixScannerDescription.runConfig (rest.length + 4)
          (MarkedPrefixScannerDescription.runConfig 1
            (config 140
              (some b :: List.append (List.map some rest)
                (none :: some true :: leftTail))
              (some headBit :: right))) =
          config 100 (some false :: some true :: leftTail)
            (List.append (List.map some (b :: rest).reverse)
              (some headBit :: right))
      rw [show
          MarkedPrefixScannerDescription.runConfig 1
            (config 140
              (some b :: List.append (List.map some rest)
                (none :: some true :: leftTail))
              (some headBit :: right)) =
          config 140
            (List.append (List.map some rest)
              (none :: some true :: leftTail))
            (some b :: some headBit :: right) by
        cases headBit <;> cases b <;> cases right <;>
        simp [MarkedPrefixScannerDescription, StageInputMarkedScannerDescription,
          config, tapeAtCells, keep, keepMove, writeMove,
          scanLeftToSentinelRestart, scanLeftToSentinelHalt,
          runConfig, stepConfig, lookupTransition, Matches, transition,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft]]
      rw [ih]
      simp [List.map_append, List.append_assoc]

private def markedPrefixFinishStartConfigWithTailCells
    (w : Word Bool) (tailCells : List (Option Bool)) :
    Configuration :=
  config 150 (finishStartLeft w)
    (List.append ((markedCellsBits w).map some) tailCells)

private def markedPrefixMarkingState120WithTailCells
    (processed : Word Bool) (b : Bool) (rest : Word Bool)
    (tailCells : List (Option Bool)) :
    Configuration :=
  config 120 (activeLengthPrefixRev processed.length)
    (List.append ((stageNatBits rest.length).map some)
      (List.append ((markedCellsBits processed).map some)
        (List.append ((cellBits b).map some)
          (List.append ((cellsBits rest).map some) tailCells))))

private def markedPrefixState100AfterMarkedWithTailCells
    (processed : Word Bool) (b : Bool) (rest : Word Bool)
    (tailCells : List (Option Bool)) :
    Configuration :=
  config 100 (finishLengthPrefixRev processed.length)
    (List.append ((stageNatBits rest.length).map some)
      (List.append ((markedCellsBits processed).map some)
        (List.append ((markedCellBits b).map some)
          (List.append ((cellsBits rest).map some) tailCells))))

private theorem markedPrefix_run_mark_current_to_state100_withTailCells
    (processed : Word Bool) (b : Bool) (rest : Word Bool)
    (tailCells : List (Option Bool)) :
    exists steps : Nat,
      MarkedPrefixScannerDescription.runConfig steps
          (markedPrefixMarkingState120WithTailCells
            processed b rest tailCells) =
        markedPrefixState100AfterMarkedWithTailCells
          processed b rest tailCells := by
  let scanRev := markingReturnScanRev processed rest
  refine
    ⟨(4 * rest.length + 4) +
        (4 * processed.length + (6 + (scanRev.length + 4))), ?_⟩
  rw [runConfig_add]
  unfold markedPrefixMarkingState120WithTailCells
  rw [markedPrefix_run_state120_stageNat]
  rw [runConfig_add]
  rw [markedPrefix_run_state130_markedCells]
  rw [runConfig_add]
  rw [markedPrefix_run_state130_currentCell]
  have hreturn :=
    markedPrefix_run_state140_returnToLengthMarker scanRev b
      (activeLengthPrefixTail processed.length)
      (some (!b) ::
        List.append ((cellsBits rest).map some) tailCells)
  cases b <;>
  simpa [markedPrefixState100AfterMarkedWithTailCells, scanRev,
    markingReturnScanRev, activeLengthPrefixRev,
    activeLengthPrefixRestored, markedCellBits,
    List.map_append, List.reverse_append, List.append_assoc]
    using hreturn

private theorem markedPrefix_run_marking_loop_from_state120_withTailCells
    (processed : Word Bool) (b : Bool) (rest : Word Bool)
    (tailCells : List (Option Bool)) :
    exists steps : Nat,
      MarkedPrefixScannerDescription.runConfig steps
          (markedPrefixMarkingState120WithTailCells
            processed b rest tailCells) =
        markedPrefixFinishStartConfigWithTailCells
          (List.append processed (b :: rest)) tailCells := by
  induction rest generalizing processed b with
  | nil =>
      rcases markedPrefix_run_mark_current_to_state100_withTailCells
          processed b [] tailCells with
        ⟨markSteps, hmark⟩
      refine ⟨markSteps + 4, ?_⟩
      rw [runConfig_add]
      rw [hmark]
      unfold markedPrefixState100AfterMarkedWithTailCells
      change
        MarkedPrefixScannerDescription.runConfig 4
            (config 100 (finishLengthPrefixRev processed.length)
              (List.append (doneBits.map some)
                (List.append ((markedCellsBits processed).map some)
                  (List.append ((markedCellBits b).map some)
                    tailCells)))) =
          markedPrefixFinishStartConfigWithTailCells
            (List.append processed [b]) tailCells
      rw [markedPrefix_run_state100_done]
      unfold markedPrefixFinishStartConfigWithTailCells finishStartLeft
      rw [markedCellsBits_append_single_map]
      simp [List.length_append, List.append_assoc]
  | cons next rest ih =>
      rcases markedPrefix_run_mark_current_to_state100_withTailCells
          processed b (next :: rest) tailCells with
        ⟨markSteps, hmark⟩
      rcases ih (List.append processed [b]) next with
        ⟨recSteps, hrec⟩
      refine ⟨markSteps + 4 + recSteps, ?_⟩
      rw [show markSteps + 4 + recSteps =
          markSteps + (4 + recSteps) by lia]
      rw [runConfig_add]
      rw [hmark]
      rw [runConfig_add]
      unfold markedPrefixState100AfterMarkedWithTailCells
      rw [show
          (stageNatBits (next :: rest).length).map some =
            List.append (tickBits.map some)
              ((stageNatBits rest.length).map some) by
        simp [stageNatBits_succ, tickBits,
          encodeCodeSymbolAsInput]]
      change
        MarkedPrefixScannerDescription.runConfig recSteps
            (MarkedPrefixScannerDescription.runConfig 4
              (config 100 (finishLengthPrefixRev processed.length)
                (List.append (tickBits.map some)
                  (List.append ((stageNatBits rest.length).map some)
                    (List.append ((markedCellsBits processed).map some)
                      (List.append ((markedCellBits b).map some)
                        (List.append
                          ((cellsBits (next :: rest)).map some)
                          tailCells))))))) =
          markedPrefixFinishStartConfigWithTailCells
            (List.append processed (b :: next :: rest)) tailCells
      rw [markedPrefix_run_state100_tick]
      unfold markedPrefixMarkingState120WithTailCells at hrec
      rw [markedCellsBits_append_single_map] at hrec
      simpa [activeLengthPrefixRev_succ, cellsBits_cons,
        List.length_append, List.map_append, List.append_assoc] using hrec

private theorem markedPrefix_run_state120_bool_tail_to_finish_cells
    (b : Bool) (rest : Word Bool) (tailCells : List (Option Bool)) :
    exists steps : Nat,
      MarkedPrefixScannerDescription.runConfig steps
          (config 120 [none, some true, none, some false]
            (List.append ((stageNatBits rest.length).map some)
              (List.append ((cellBits b).map some)
                (List.append ((cellsBits rest).map some) tailCells)))) =
        markedPrefixFinishStartConfigWithTailCells
          (b :: rest) tailCells := by
  rcases markedPrefix_run_marking_loop_from_state120_withTailCells
      ([] : Word Bool) b rest tailCells with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  simpa [markedPrefixMarkingState120WithTailCells,
    activeLengthPrefixRev_zero] using hsteps

private def markedPrefixState160AfterRestoreWithTailCells
    (w : Word Bool) (tailCells : List (Option Bool)) :
    Configuration :=
  config 160
    (List.append ((cellsBits w).reverse.map some)
      (finishStartLeft w))
    (some false :: none :: tailCells)

private def markedPrefixAppendBlankStartConfigWithTailCells
    (w : Word Bool) (tailCells : List (Option Bool)) :
    Configuration :=
  config 180 [none, some false]
    (List.append ((stageInputSecondBitTailPrefix w).map some)
      (some false :: none :: tailCells))

private theorem markedPrefix_run_state150_markedCell
    (b : Bool) (left right : List (Option Bool)) :
    MarkedPrefixScannerDescription.runConfig 4
        (config 150 left
          (List.append ((markedCellBits b).map some) right)) =
      config 150
        (List.append ((cellBits b).reverse.map some) left)
        right := by
  cases b <;> cases right <;>
  simp [MarkedPrefixScannerDescription, StageInputMarkedScannerDescription,
    markedCellBits, cellBits,
    config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart, scanLeftToSentinelHalt,
    runConfig, stepConfig, lookupTransition, Matches,
    transition, encodeCodeSymbolAsInput,
    Tape.read, Tape.write, Tape.move, Tape.moveRight]

private theorem markedPrefix_run_state150_markedCells
    (processed : Word Bool)
    (left right : List (Option Bool)) :
    MarkedPrefixScannerDescription.runConfig
        (4 * processed.length)
        (config 150 left
          (List.append ((markedCellsBits processed).map some)
            right)) =
      config 150
        (List.append ((cellsBits processed).reverse.map some)
          left)
        right := by
  induction processed generalizing left with
  | nil =>
      rfl
  | cons b rest ih =>
      rw [show 4 * (b :: rest).length =
          4 + 4 * rest.length by simp; lia]
      rw [runConfig_add]
      rw [show
          List.append ((markedCellsBits (b :: rest)).map some)
              right =
            List.append ((markedCellBits b).map some)
              (List.append ((markedCellsBits rest).map some)
                right) by
          simp [markedCellsBits, List.map_append, List.append_assoc]]
      rw [markedPrefix_run_state150_markedCell]
      rw [ih]
      simp [List.reverse_append, List.map_append,
        List.append_assoc]

private theorem markedPrefix_run_state150_to_state160
    (left tail : List (Option Bool)) :
    MarkedPrefixScannerDescription.runConfig 2
        (config 150 left (some false :: some false :: tail)) =
      config 160 left (some false :: none :: tail) := by
  cases tail <;>
  simp [MarkedPrefixScannerDescription, StageInputMarkedScannerDescription,
    config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart, scanLeftToSentinelHalt,
    runConfig, stepConfig, lookupTransition, Matches,
    transition, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    Tape.moveRight]

private theorem markedPrefix_run_finish_restore_cells_tailCells
    (w : Word Bool) (tailCells : List (Option Bool)) :
    MarkedPrefixScannerDescription.runConfig
        (4 * w.length + 2)
        (markedPrefixFinishStartConfigWithTailCells w
          (some false :: some false :: tailCells)) =
      markedPrefixState160AfterRestoreWithTailCells w tailCells := by
  rw [runConfig_add]
  change
    MarkedPrefixScannerDescription.runConfig 2
        (MarkedPrefixScannerDescription.runConfig (4 * w.length)
          (config 150 (finishStartLeft w)
            (List.append ((markedCellsBits w).map some)
              (some false :: some false :: tailCells)))) =
      markedPrefixState160AfterRestoreWithTailCells w tailCells
  rw [markedPrefix_run_state150_markedCells]
  rw [markedPrefix_run_state150_to_state160]
  simp [markedPrefixState160AfterRestoreWithTailCells]

private theorem markedPrefix_run_state160_some_cons
    (b : Bool) (cell : Option Bool)
    (left right : List (Option Bool)) :
    MarkedPrefixScannerDescription.runConfig 1
        (config 160 (cell :: left) (some b :: right)) =
      config 160 left (cell :: some b :: right) := by
  cases b <;> cases cell <;> cases right <;>
  simp [MarkedPrefixScannerDescription, StageInputMarkedScannerDescription,
    config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart, scanLeftToSentinelHalt,
    runConfig, stepConfig, lookupTransition, Matches, transition,
    Tape.read, Tape.write, Tape.move, Tape.moveLeft]

private theorem markedPrefix_run_state160_bits_to_boundary
    (bitsToRight : Word Bool) (boundary : Option Bool)
    (leftTail right : List (Option Bool)) :
    MarkedPrefixScannerDescription.runConfig bitsToRight.length
        (state160ScanConfig bitsToRight boundary leftTail right) =
      config 160 leftTail
        (boundary ::
          List.append (bitsToRight.reverse.map some) right) := by
  induction bitsToRight generalizing boundary leftTail right with
  | nil =>
      rfl
  | cons b rest ih =>
      rw [show (b :: rest).length = rest.length + 1 by simp]
      rw [show rest.length + 1 = 1 + rest.length by lia]
      rw [runConfig_add]
      cases rest with
      | nil =>
          change
            MarkedPrefixScannerDescription.runConfig 0
                (MarkedPrefixScannerDescription.runConfig 1
                  (config 160 (boundary :: leftTail)
                    (some b :: right))) =
              config 160 leftTail (boundary :: some b :: right)
          rw [markedPrefix_run_state160_some_cons]
          rfl
      | cons b' rest =>
          change
            MarkedPrefixScannerDescription.runConfig
                (b' :: rest).length
                (MarkedPrefixScannerDescription.runConfig 1
                  (config 160
                    (some b' ::
                      List.append (rest.map some)
                        (boundary :: leftTail))
                    (some b :: right))) =
              config 160 leftTail
                (boundary ::
                  List.append
                    ((b :: b' :: rest).reverse.map some)
                    right)
          rw [markedPrefix_run_state160_some_cons]
          have h := ih boundary leftTail (some b :: right)
          simp [state160ScanConfig] at h
          simpa [List.map_append, List.append_assoc] using h

private theorem markedPrefix_run_state160_none_to_state161
    (cell : Option Bool) (left right : List (Option Bool)) :
    MarkedPrefixScannerDescription.runConfig 1
        (config 160 (cell :: left) (none :: right)) =
      config 161 left (cell :: none :: right) := by
  cases cell <;> cases right <;>
  simp [MarkedPrefixScannerDescription, StageInputMarkedScannerDescription,
    config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart, scanLeftToSentinelHalt,
    runConfig, stepConfig, lookupTransition, Matches, transition,
    Tape.read, Tape.write, Tape.move, Tape.moveLeft]

private theorem markedPrefix_run_state161_false_to_state170
    (left right : List (Option Bool)) :
    MarkedPrefixScannerDescription.runConfig 1
        (config 161 left (some false :: right)) =
      config 170 (some false :: left) right := by
  cases right <;>
  simp [MarkedPrefixScannerDescription, StageInputMarkedScannerDescription,
    config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart, scanLeftToSentinelHalt,
    runConfig, stepConfig, lookupTransition, Matches, transition,
    Tape.read, Tape.write, Tape.move, Tape.moveRight]

private theorem markedPrefix_run_state170_none_to_state180
    (left right : List (Option Bool)) :
    MarkedPrefixScannerDescription.runConfig 1
        (config 170 (some false :: left) (none :: right)) =
      config 180 (none :: some false :: left) right := by
  cases right <;>
  simp [MarkedPrefixScannerDescription, StageInputMarkedScannerDescription,
    config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart, scanLeftToSentinelHalt,
    runConfig, stepConfig, lookupTransition, Matches, transition,
    Tape.read, Tape.write, Tape.move, Tape.moveRight]

private theorem markedPrefix_run_finish_scan_left_to_append_tailCells
    (b : Bool) (rest : Word Bool) (tailCells : List (Option Bool)) :
    exists steps : Nat,
      MarkedPrefixScannerDescription.runConfig steps
          (markedPrefixState160AfterRestoreWithTailCells
            (b :: rest) tailCells) =
        markedPrefixAppendBlankStartConfigWithTailCells
          (b :: rest) tailCells := by
  let bits := finishScanBits (b :: rest)
  let scanRight := none :: tailCells
  have hstart :
      markedPrefixState160AfterRestoreWithTailCells
          (b :: rest) tailCells =
        state160ScanConfig bits none [some false] scanRight := by
    cases b <;>
    simp [bits, scanRight, finishScanBits,
      markedPrefixState160AfterRestoreWithTailCells, finishStartLeft,
      finishLengthPrefixRev_eq_scanBits, state160ScanConfig,
      cellsBits_cons, cellBits,
      List.map_append, List.reverse_append, List.append_assoc]
  refine ⟨bits.length + 3, ?_⟩
  rw [show bits.length + 3 = bits.length + (1 + (1 + 1)) by
    lia]
  rw [runConfig_add]
  rw [hstart]
  rw [markedPrefix_run_state160_bits_to_boundary]
  rw [runConfig_add]
  rw [markedPrefix_run_state160_none_to_state161]
  rw [runConfig_add]
  rw [markedPrefix_run_state161_false_to_state170]
  rw [markedPrefix_run_state170_none_to_state180]
  simp [markedPrefixAppendBlankStartConfigWithTailCells, bits, scanRight,
    finishScanBits_reverse_nonempty, List.map_append, List.append_assoc]

private theorem markedPrefix_run_state180_some
    (b : Bool) (left right : List (Option Bool)) :
    MarkedPrefixScannerDescription.runConfig 1
        (config 180 left (some b :: right)) =
      config 180 (some b :: left) right := by
  cases b <;> cases right <;>
  simp [MarkedPrefixScannerDescription, StageInputMarkedScannerDescription,
    config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart, scanLeftToSentinelHalt,
    runConfig, stepConfig, lookupTransition, Matches, transition,
    Tape.read, Tape.write, Tape.move, Tape.moveRight]

private theorem markedPrefix_run_state180_bits
    (bits : Word Bool) (left right : List (Option Bool)) :
    MarkedPrefixScannerDescription.runConfig bits.length
        (config 180 left (List.append (bits.map some) right)) =
      config 180
        (List.append (bits.reverse.map some) left) right := by
  induction bits generalizing left right with
  | nil =>
      rfl
  | cons b rest ih =>
      change
        MarkedPrefixScannerDescription.runConfig
            (rest.length + 1)
            (config 180 left
              (some b :: List.append (rest.map some) right)) =
          config 180
            (List.append ((b :: rest).reverse.map some) left) right
      rw [show rest.length + 1 = 1 + rest.length by lia]
      rw [runConfig_add]
      rw [markedPrefix_run_state180_some]
      rw [ih]
      simp [List.map_append, List.append_assoc]

private theorem markedPrefix_run_state180_none_cons
    (cell : Option Bool) (left right : List (Option Bool)) :
    MarkedPrefixScannerDescription.runConfig 1
        (config 180 (cell :: left) (none :: right)) =
      config 200 left (cell :: some false :: right) := by
  cases cell <;>
  simp [MarkedPrefixScannerDescription, StageInputMarkedScannerDescription,
    config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart, scanLeftToSentinelHalt,
    runConfig, stepConfig, lookupTransition, Matches, transition,
    Tape.read, Tape.write, Tape.move, Tape.moveLeft]

private theorem markedPrefix_run_append_blank_to_state200_tailCells
    (b : Bool) (rest : Word Bool) (tailCells : List (Option Bool)) :
    exists steps : Nat,
      MarkedPrefixScannerDescription.runConfig steps
          (markedPrefixAppendBlankStartConfigWithTailCells
            (b :: rest) tailCells) =
        config 200
          (List.append
            ((stageInputSecondBitTailPrefix (b :: rest)).reverse.map some)
            (none :: [some false]))
          (some false :: some false :: tailCells) := by
  let tailPrefix := stageInputSecondBitTailPrefix (b :: rest)
  refine ⟨tailPrefix.length + 2, ?_⟩
  rw [show tailPrefix.length + 2 = tailPrefix.length + (1 + 1) by
    lia]
  rw [runConfig_add]
  unfold markedPrefixAppendBlankStartConfigWithTailCells
  change
    MarkedPrefixScannerDescription.runConfig (1 + 1)
        (MarkedPrefixScannerDescription.runConfig tailPrefix.length
          (config 180 [none, some false]
            (List.append (tailPrefix.map some)
              (some false :: none :: tailCells)))) =
      config 200
        (List.append (tailPrefix.reverse.map some)
          (none :: [some false]))
        (some false :: some false :: tailCells)
  rw [markedPrefix_run_state180_bits]
  rw [runConfig_add]
  rw [markedPrefix_run_state180_some]
  rw [markedPrefix_run_state180_none_cons]

private theorem markedPrefix_run_finish_cells_false_false_to_state200
    (b : Bool) (rest : Word Bool) (tailCells : List (Option Bool)) :
    exists steps : Nat,
      MarkedPrefixScannerDescription.runConfig steps
          (markedPrefixFinishStartConfigWithTailCells
            (b :: rest) (some false :: some false :: tailCells)) =
        config 200
          (List.append
            ((stageInputSecondBitTailPrefix (b :: rest)).reverse.map some)
            (none :: [some false]))
          (some false :: some false :: tailCells) := by
  rcases markedPrefix_run_finish_scan_left_to_append_tailCells
      b rest tailCells with
    ⟨scanSteps, hscan⟩
  rcases markedPrefix_run_append_blank_to_state200_tailCells
      b rest tailCells with
    ⟨appendSteps, happend⟩
  refine
    ⟨(4 * (b :: rest).length + 2) + scanSteps + appendSteps, ?_⟩
  rw [show
      (4 * (b :: rest).length + 2) + scanSteps + appendSteps =
        (4 * (b :: rest).length + 2) +
          (scanSteps + appendSteps) by
    lia]
  rw [runConfig_add]
  rw [markedPrefix_run_finish_restore_cells_tailCells]
  rw [runConfig_add]
  rw [hscan]
  exact happend

theorem markedPrefix_run_marked_tail_done_stageNat_to_state200
    (stage : Nat) (suffixBits : Word Bool) :
    MarkedPrefixScannerDescription.runConfig 18
        (markedTailStartConfig
          (true :: true ::
            List.append (stageNatBits stage) suffixBits)) =
      config 200 [some true, some true, none, some false]
        (List.append ((stageNatBits stage).map some)
          (suffixBits.map some)) := by
  cases stage <;>
  simp [MarkedPrefixScannerDescription, StageInputMarkedScannerDescription,
    markedTailStartConfig, stageNatBits, encodeNat,
    encodeCodeWordAsInput, encodeCodeSymbolAsInput, config, tapeAtCells,
    keep, keepMove, writeMove, scanLeftToSentinelRestart,
    scanLeftToSentinelHalt, runConfig, stepConfig,
    lookupTransition, Matches, transition, Tape.read, Tape.write,
    Tape.move, Tape.moveLeft, Tape.moveRight]

theorem markedPrefix_run_state120_nonempty_to_state200
    (b : Bool) (rest : Word Bool) (stage : Nat)
    (suffixBits : Word Bool) :
    exists steps : Nat,
      MarkedPrefixScannerDescription.runConfig steps
          (config 120 [none, some true, none, some false]
            (List.append ((stageNatBits rest.length).map some)
              (List.append ((cellBits b).map some)
                (List.append ((cellsBits rest).map some)
                  (List.append ((stageNatBits stage).map some)
                    (suffixBits.map some)))))) =
        config 200
          (List.append
            ((stageInputSecondBitTailPrefix (b :: rest)).reverse.map some)
            (none :: [some false]))
          (List.append ((stageNatBits stage).map some)
            (suffixBits.map some)) := by
  rcases stageNatBits_false_false_tail stage with
    ⟨stageTail, hstageTail⟩
  rcases markedPrefix_run_state120_bool_tail_to_finish_cells
      b rest
      (List.append ((stageNatBits stage).map some)
        (suffixBits.map some)) with
    ⟨markSteps, hmark⟩
  rcases markedPrefix_run_finish_cells_false_false_to_state200
      b rest
      (List.append (stageTail.map some) (suffixBits.map some)) with
    ⟨finishSteps, hfinish⟩
  refine ⟨markSteps + finishSteps, ?_⟩
  rw [runConfig_add]
  rw [hmark]
  rw [hstageTail]
  have htailCells :
      List.append (List.map some (false :: false :: stageTail))
          (suffixBits.map some) =
        some false :: some false ::
          List.append (stageTail.map some) (suffixBits.map some) := by
    simp
  rw [htailCells]
  rw [hfinish]

theorem markedPrefix_run_marked_tail_tick_to_state120
    (bits : Word Bool) :
    MarkedPrefixScannerDescription.runConfig 6
        (markedTailStartConfig (true :: false :: bits)) =
      config 120 [none, some true, none, some false]
        (bits.map some) := by
  simp [MarkedPrefixScannerDescription, StageInputMarkedScannerDescription,
    markedTailStartConfig, config, tapeAtCells,
    keep, keepMove, writeMove, scanLeftToSentinelRestart,
    scanLeftToSentinelHalt, runConfig, stepConfig,
    lookupTransition, Matches, transition, Tape.read, Tape.write,
    Tape.move, Tape.moveLeft, Tape.moveRight]
  generalize bits.map some = cells
  cases cells <;> rfl

theorem markedPrefix_run_marked_tail_nonempty_to_state200
    (b : Bool) (rest : Word Bool) (stage : Nat)
    (suffixBits : Word Bool) :
    exists steps : Nat,
      MarkedPrefixScannerDescription.runConfig steps
          (markedTailStartConfig
            (true :: false ::
              List.append (stageNatBits rest.length)
                (List.append (cellBits b)
                  (List.append (cellsBits rest)
                    (List.append (stageNatBits stage) suffixBits))))) =
        config 200
          (List.append
            ((stageInputSecondBitTailPrefix (b :: rest)).reverse.map some)
            (none :: [some false]))
          (List.append ((stageNatBits stage).map some)
            (suffixBits.map some)) := by
  rcases markedPrefix_run_state120_nonempty_to_state200
      b rest stage suffixBits with
    ⟨tailSteps, htail⟩
  refine ⟨6 + tailSteps, ?_⟩
  rw [runConfig_add]
  rw [markedPrefix_run_marked_tail_tick_to_state120]
  simpa [List.map_append, List.append_assoc] using htail

def natSuffixHandoffConfigWithBase
    (stage : Nat) (baseLeft : List (Option Bool))
    (suffixBits : Word Bool) : Configuration :=
  { state := NatSuffixScannerDescription.halt
    tape :=
      Tape.move Direction.left
        (tapeAtCells
          (List.append ((stageNatBits stage).reverse.map some)
            baseLeft)
          (suffixBits.map some)) }

theorem run_markedPrefix_raw_to_handoff_withBase
    (stage : Nat) (baseLeft : List (Option Bool))
    (b : Bool) (suffixTail : Word Bool) :
    exists steps : Nat,
      MarkedPrefixScannerDescription.runConfig steps
          (config 200 baseLeft
            (List.append ((stageNatBits stage).map some)
              (some b :: suffixTail.map some))) =
        natSuffixHandoffConfigWithBase stage baseLeft
          (b :: suffixTail) := by
  rcases stageNatBits_reverse_map_some_cons stage with
    ⟨tail, htail⟩
  refine ⟨4 * stage + 5, ?_⟩
  rw [show 4 * stage + 5 = (4 * stage + 4) + 1 by lia]
  rw [runConfig_add]
  rw [markedPrefix_run_state200_stageNat_to_state210]
  rw [htail]
  unfold natSuffixHandoffConfigWithBase
  simpa [config, tapeAtCells, htail, List.append_assoc] using!
    markedPrefix_run_state210_handoff b (some true)
      (List.append tail baseLeft) (suffixTail.map some)

def natSuffixHandoffConfigWithBaseAndRight
    (stage : Nat) (baseLeft : List (Option Bool))
    (suffixBits : Word Bool) (rightPadding : List (Option Bool)) :
    Configuration :=
  { state := NatSuffixScannerDescription.halt
    tape :=
      Tape.move Direction.left
        (tapeAtCells
          (List.append ((stageNatBits stage).reverse.map some)
            baseLeft)
          (List.append (suffixBits.map some) rightPadding)) }

def nonemptyNatSuffixHandoffConfigWithBase
    (stage : Nat) (baseLeft : List (Option Bool))
    (suffixBits : Word Bool) : Configuration :=
  { state := NonemptyNatSuffixScannerDescription.halt
    tape :=
      Tape.move Direction.left
        (tapeAtCells
          (List.append ((stageNatBits stage).reverse.map some)
            baseLeft)
          (suffixBits.map some)) }

def nonemptyNatSuffixHandoffConfigWithBaseAndRight
    (stage : Nat) (baseLeft : List (Option Bool))
    (suffixBits : Word Bool) (rightPadding : List (Option Bool)) :
    Configuration :=
  { state := NonemptyNatSuffixScannerDescription.halt
    tape :=
      Tape.move Direction.left
        (tapeAtCells
          (List.append ((stageNatBits stage).reverse.map some)
            baseLeft)
          (List.append (suffixBits.map some) rightPadding)) }

theorem natSuffix_run_state200_stageNat_to_state210
    (stage : Nat) (left right : List (Option Bool)) :
    NatSuffixScannerDescription.runConfig (4 * stage + 4)
        (config 200 left
          (List.append ((stageNatBits stage).map some) right)) =
      config
        210
        (List.append ((stageNatBits stage).reverse.map some) left)
        right := by
  rw [runConfig_eq_of_transitions_eq NatSuffixScannerDescription
    MarkedPrefixScannerDescription (by rfl)]
  exact markedPrefix_run_state200_stageNat_to_state210 stage left right

theorem natSuffix_run_state210_handoff
    (b : Bool) (cell : Option Bool)
    (left right : List (Option Bool)) :
    NatSuffixScannerDescription.runConfig 1
        (config 210 (cell :: left) (some b :: right)) =
      config NatSuffixScannerDescription.halt left
        (cell :: some b :: right) := by
  rw [runConfig_eq_of_transitions_eq NatSuffixScannerDescription
    MarkedPrefixScannerDescription (by rfl)]
  exact markedPrefix_run_state210_handoff b cell left right

private theorem nonemptyNatSuffix_run_state200_tick
    (left right : List (Option Bool)) :
    NonemptyNatSuffixScannerDescription.runConfig 4
        (config 200 left
          (List.append (tickBits.map some) right)) =
      config 200
        (List.append (tickBits.reverse.map some) left) right := by
  cases right <;>
    simp [NonemptyNatSuffixScannerDescription,
      nonemptyNatSuffixTransitions, StageInputMarkedScannerDescription,
      tickBits, config, tapeAtCells, keep, keepMove, writeMove,
      scanLeftToSentinelRestart,
      scanLeftToSentinelHalt,
      runConfig, stepConfig,
      lookupTransition, Matches,
      transition, encodeCodeSymbolAsInput,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

private theorem nonemptyNatSuffix_run_state200_done_to_state210
    (left right : List (Option Bool)) :
    NonemptyNatSuffixScannerDescription.runConfig 4
        (config 200 left
          (List.append (doneBits.map some) right)) =
      config 210 (List.append (doneBits.reverse.map some) left)
        right := by
  cases right <;>
    simp [NonemptyNatSuffixScannerDescription,
      nonemptyNatSuffixTransitions, StageInputMarkedScannerDescription,
      doneBits, config, tapeAtCells, keep, keepMove, writeMove,
      scanLeftToSentinelRestart,
      scanLeftToSentinelHalt,
      runConfig, stepConfig,
      lookupTransition, Matches,
      transition,
      encodeCodeSymbolAsInput,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem nonemptyNatSuffix_run_state200_stageNat_to_state210
    (stage : Nat) (left right : List (Option Bool)) :
    NonemptyNatSuffixScannerDescription.runConfig (4 * stage + 4)
        (config 200 left
          (List.append ((stageNatBits stage).map some) right)) =
      config
        210
        (List.append ((stageNatBits stage).reverse.map some) left)
        right := by
  induction stage generalizing left with
  | zero =>
      simpa [stageNatBits_zero] using!
        nonemptyNatSuffix_run_state200_done_to_state210 left right
  | succ stage ih =>
      rw [show 4 * (stage + 1) + 4 = 4 + (4 * stage + 4) by
        lia]
      rw [runConfig_add]
      rw [show
          (stageNatBits (stage + 1)).map some =
            List.append (tickBits.map some)
              ((stageNatBits stage).map some) by
          simp [stageNatBits_succ, tickBits,
            encodeCodeSymbolAsInput]]
      change
        NonemptyNatSuffixScannerDescription.runConfig
            (4 * stage + 4)
            (NonemptyNatSuffixScannerDescription.runConfig 4
              (config 200 left
                (List.append (tickBits.map some)
                  (List.append ((stageNatBits stage).map some) right)))) =
          config 210
            (List.append ((stageNatBits (stage + 1)).reverse.map some) left)
            right
      rw [nonemptyNatSuffix_run_state200_tick]
      have h := ih (List.append (tickBits.reverse.map some) left)
      simpa [stageNatBits_succ, tickBits,
        encodeCodeSymbolAsInput,
        List.reverse_append, List.map_append, List.append_assoc] using h

private theorem nonemptyNatSuffix_run_state210_handoff
    (b : Bool) (cell : Option Bool)
    (left right : List (Option Bool)) :
    NonemptyNatSuffixScannerDescription.runConfig 1
        (config 210 (cell :: left) (some b :: right)) =
      config NonemptyNatSuffixScannerDescription.halt left
        (cell :: some b :: right) := by
  cases b <;> cases cell <;> cases right <;>
    simp [config, tapeAtCells, keepMove,
      nonemptyNatSuffix_lookup_210_false,
      nonemptyNatSuffix_lookup_210_true,
      runConfig, stepConfig,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft]

private theorem nonemptyNatSuffix_step_state210_none
    (left : List (Option Bool)) :
    NonemptyNatSuffixScannerDescription.stepConfig
        (config 210 left []) = none := by
  simp [config, tapeAtCells, stepConfig,
    nonemptyNatSuffix_lookup_210_none, Tape.read]

theorem run_nonemptyNatSuffix_raw_to_handoff_withBase
    (stage : Nat) (baseLeft : List (Option Bool))
    (b : Bool) (suffixTail : Word Bool) :
    exists steps : Nat,
      NonemptyNatSuffixScannerDescription.runConfig steps
          (config 200 baseLeft
            (List.append ((stageNatBits stage).map some)
              (some b :: suffixTail.map some))) =
        nonemptyNatSuffixHandoffConfigWithBase stage baseLeft
          (b :: suffixTail) := by
  rcases stageNatBits_reverse_map_some_cons stage with
    ⟨tail, htail⟩
  refine ⟨4 * stage + 5, ?_⟩
  rw [show 4 * stage + 5 = (4 * stage + 4) + 1 by lia]
  rw [runConfig_add]
  rw [nonemptyNatSuffix_run_state200_stageNat_to_state210]
  rw [htail]
  unfold nonemptyNatSuffixHandoffConfigWithBase
  simpa [config, tapeAtCells, htail, List.append_assoc] using!
    nonemptyNatSuffix_run_state210_handoff b (some true)
      (List.append tail baseLeft) (suffixTail.map some)

theorem run_nonemptyNatSuffix_raw_to_handoff_withBaseAndRight
    (stage : Nat) (baseLeft : List (Option Bool))
    (b : Bool) (suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    exists steps : Nat,
      NonemptyNatSuffixScannerDescription.runConfig steps
          (config 200 baseLeft
            (List.append ((stageNatBits stage).map some)
              (some b ::
                List.append (suffixTail.map some) rightPadding))) =
        nonemptyNatSuffixHandoffConfigWithBaseAndRight
          stage baseLeft (b :: suffixTail) rightPadding := by
  rcases stageNatBits_reverse_map_some_cons stage with
    ⟨tail, htail⟩
  refine ⟨4 * stage + 5, ?_⟩
  rw [show 4 * stage + 5 = (4 * stage + 4) + 1 by lia]
  rw [runConfig_add]
  rw [nonemptyNatSuffix_run_state200_stageNat_to_state210]
  rw [htail]
  unfold nonemptyNatSuffixHandoffConfigWithBaseAndRight
  simpa [config, tapeAtCells, htail, List.append_assoc] using!
    nonemptyNatSuffix_run_state210_handoff b (some true)
      (List.append tail baseLeft)
      (List.append (suffixTail.map some) rightPadding)

theorem nonemptyNatSuffixHandoffConfigWithBase_move_right
    (stage : Nat) (baseLeft : List (Option Bool))
    (b : Bool) (suffixTail : Word Bool) :
    Tape.move Direction.right
        (nonemptyNatSuffixHandoffConfigWithBase stage baseLeft
          (b :: suffixTail)).tape =
      tapeAtCells
        (List.append ((stageNatBits stage).reverse.map some) baseLeft)
        ((b :: suffixTail).map some) := by
  rcases stageNatBits_reverse_map_some_cons stage with
    ⟨tail, htail⟩
  unfold nonemptyNatSuffixHandoffConfigWithBase
  rw [htail]
  simpa [List.append_assoc] using!
    FoC.Computability.CommonGround.FiniteTransducers.tapeAtCells_move_right_move_left_cons (some true)
      (List.append tail baseLeft) (some b) (suffixTail.map some)

theorem nonemptyNatSuffixHandoffConfigWithBaseAndRight_move_right
    (stage : Nat) (baseLeft : List (Option Bool))
    (b : Bool) (suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    Tape.move Direction.right
        (nonemptyNatSuffixHandoffConfigWithBaseAndRight
          stage baseLeft (b :: suffixTail) rightPadding).tape =
      tapeAtCells
        (List.append ((stageNatBits stage).reverse.map some) baseLeft)
        (List.append ((b :: suffixTail).map some) rightPadding) := by
  rcases stageNatBits_reverse_map_some_cons stage with
    ⟨tail, htail⟩
  unfold nonemptyNatSuffixHandoffConfigWithBaseAndRight
  rw [htail]
  simpa [List.append_assoc] using!
    FoC.Computability.CommonGround.FiniteTransducers.tapeAtCells_move_right_move_left_cons (some true)
      (List.append tail baseLeft) (some b)
      (List.append (suffixTail.map some) rightPadding)

theorem nonemptyNatSuffixScannerDescription_runConfig_stageNat_handoff
    (baseLeft : List (Option Bool)) (stage : Nat)
    (b : Bool) (suffixTail : Word Bool)
    {Tout : Tape Bool} {n : Nat}
    (h :
      NonemptyNatSuffixScannerDescription.runConfig n
          (config
            NonemptyNatSuffixScannerDescription.start
            baseLeft
            (List.append
              ((stageNatBits stage).map some)
              ((b :: suffixTail).map some))) =
        { state :=
            NonemptyNatSuffixScannerDescription.halt
          tape := Tout }) :
      Tape.move Direction.right Tout =
        tapeAtCells
          (List.append
            ((stageNatBits stage).reverse.map some)
            baseLeft)
          ((b :: suffixTail).map some) := by
  let c0 : Configuration :=
    config
      NonemptyNatSuffixScannerDescription.start
      baseLeft
      (List.append
        ((stageNatBits stage).map some)
        ((b :: suffixTail).map some))
  rcases
      run_nonemptyNatSuffix_raw_to_handoff_withBase
        stage baseLeft b suffixTail with
    ⟨_steps, hforward⟩
  have hTout :
      Tout =
        (nonemptyNatSuffixHandoffConfigWithBase
          stage baseLeft (b :: suffixTail)).tape := by
    exact
      (MachineDescription.runConfig_halt_tape_functional_of_haltTransitionFree
        nonemptyNatSuffixScannerDescription_haltTransitionFree
        (by simpa [c0] using! hforward)
        (by simpa [c0] using! h)).symm
  rw [hTout]
  exact
    nonemptyNatSuffixHandoffConfigWithBase_move_right
      stage baseLeft b suffixTail

theorem nonemptyNatSuffixScannerDescription_runConfig_encodeNatAppend_handoff
    (baseLeft : List (Option Bool)) (stage : Nat)
    (suffix : Word MachineCodeSymbol) (b : Bool) (suffixTail : Word Bool)
    {Tout : Tape Bool} {n : Nat}
    (hsuffix :
      encodeCodeWordAsInput suffix = b :: suffixTail)
    (h :
      NonemptyNatSuffixScannerDescription.runConfig n
          (config
            NonemptyNatSuffixScannerDescription.start
            baseLeft
            ((encodeCodeWordAsInput
              (encodeNatAppend stage suffix)).map
              some)) =
        { state :=
            NonemptyNatSuffixScannerDescription.halt
          tape := Tout }) :
    exists baseAfter : List (Option Bool),
      Tape.move Direction.right Tout =
        tapeAtCells baseAfter
          ((encodeCodeWordAsInput suffix).map some) := by
  refine
    ⟨List.append ((stageNatBits stage).reverse.map some) baseLeft, ?_⟩
  have hrun :
      NonemptyNatSuffixScannerDescription.runConfig n
          (config
            NonemptyNatSuffixScannerDescription.start
            baseLeft
            (List.append ((stageNatBits stage).map some)
              ((b :: suffixTail).map some))) =
        { state :=
            NonemptyNatSuffixScannerDescription.halt
          tape := Tout } := by
    simpa [natBits_eq_encodeNatAppend,
      hsuffix, List.map_append] using h
  simpa [hsuffix] using
    nonemptyNatSuffixScannerDescription_runConfig_stageNat_handoff
      baseLeft stage b suffixTail hrun

theorem nonemptyNatSuffixScannerDescription_ne_halt_of_reaches_ne_halt_region
    {c mid : Configuration} {k n : Nat}
    (hrun :
      NonemptyNatSuffixScannerDescription.runConfig
          k c = mid)
    (hmid :
      forall m : Nat,
        (NonemptyNatSuffixScannerDescription.runConfig
          m mid).state ≠
          NonemptyNatSuffixScannerDescription.halt) :
    (NonemptyNatSuffixScannerDescription.runConfig
      n c).state ≠
      NonemptyNatSuffixScannerDescription.halt := by
  by_cases hle : n ≤ k
  · intro hhalt
    let rem := k - n
    have hk : k = n + rem := by
      lia
    have hcfg :
        NonemptyNatSuffixScannerDescription.runConfig
            n c =
          { state :=
              NonemptyNatSuffixScannerDescription.halt
            tape :=
              (NonemptyNatSuffixScannerDescription.runConfig
                n c).tape } := by
      cases hrunN :
          NonemptyNatSuffixScannerDescription.runConfig
            n c with
      | mk state tape =>
          simp [hrunN] at hhalt
          simp [hhalt]
    have hhaltAtK :
        (NonemptyNatSuffixScannerDescription.runConfig
          k c).state =
          NonemptyNatSuffixScannerDescription.halt := by
      rw [hk, runConfig_add, hcfg,
        runConfig_halt
          nonemptyNatSuffixScannerDescription_haltTransitionFree]
    rw [hrun] at hhaltAtK
    exact hmid 0 hhaltAtK
  · have hn : n = k + (n - k) := by
      lia
    rw [hn, runConfig_add, hrun]
    exact hmid (n - k)

theorem nonemptyNatSuffixScannerDescription_runConfig_encodeNat_empty_ne_halt
    (stage : Nat) (leftRev : List (Option Bool)) (n : Nat) :
    (NonemptyNatSuffixScannerDescription.runConfig
      n
      (config 200 leftRev
        ((encodeCodeWordAsInput
          (encodeNatAppend stage [])).map some))).state ≠
      NonemptyNatSuffixScannerDescription.halt := by
  exact
    CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
      nonemptyNatSuffixScannerDescription_haltTransitionFree
      (D := NonemptyNatSuffixScannerDescription)
      (c :=
        config 200 leftRev
          ((encodeCodeWordAsInput
            (encodeNatAppend stage [])).map some))
      (stuck :=
        config 210
          (List.append ((stageNatBits stage).reverse.map some) leftRev)
          [])
      (k := 4 * stage + 4) (n := n)
      (by
        simpa [natBits_eq_encodeNatAppend,
          encodeCodeWordAsInput, List.map_append] using
          nonemptyNatSuffix_run_state200_stageNat_to_state210
            stage leftRev ([] : List (Option Bool)))
      (nonemptyNatSuffix_step_state210_none
        (List.append ((stageNatBits stage).reverse.map some) leftRev))
      (by
        change (210 : Nat) ≠ 999
        lia)

theorem nonemptyNatSuffixScannerDescription_runConfig_decodeNat_none_ne_halt
    (tokens : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (hdecode : decodeNat tokens = none) (n : Nat) :
    (NonemptyNatSuffixScannerDescription.runConfig
      n
      (config 200 leftRev
        ((encodeCodeWordAsInput tokens).map some))).state ≠
      NonemptyNatSuffixScannerDescription.halt := by
  induction tokens generalizing leftRev n with
  | nil =>
      exact
        CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
          nonemptyNatSuffixScannerDescription_haltTransitionFree
          (D := NonemptyNatSuffixScannerDescription)
          (c :=
            config 200 leftRev
              ((encodeCodeWordAsInput
                ([] : Word MachineCodeSymbol)).map some))
          (stuck :=
            config 200 leftRev
              ((encodeCodeWordAsInput
                ([] : Word MachineCodeSymbol)).map some))
          (k := 0) (n := n)
          rfl
          (by rfl)
          (by
            change (200 : Nat) ≠ 999
            lia)
  | cons symbol rest ih =>
      cases symbol with
      | header =>
          exact
            CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
              nonemptyNatSuffixScannerDescription_haltTransitionFree
              (D := NonemptyNatSuffixScannerDescription)
              (c :=
                config 200 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.header :: rest)).map some))
              (stuck :=
                NonemptyNatSuffixScannerDescription.runConfig
                  2
                  (config 200 leftRev
                    ((encodeCodeWordAsInput
                      (MachineCodeSymbol.header :: rest)).map some)))
              (k := 2) (n := n)
              rfl
              (by
                cases rest <;>
                simp [NonemptyNatSuffixScannerDescription,
                  nonemptyNatSuffixTransitions,
                  StageInputMarkedScannerDescription,
                  config, tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (202 : Nat) ≠ 999
                lia)
      | transition =>
          exact
            CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
              nonemptyNatSuffixScannerDescription_haltTransitionFree
              (D := NonemptyNatSuffixScannerDescription)
              (c :=
                config 200 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.transition :: rest)).map some))
              (stuck :=
                NonemptyNatSuffixScannerDescription.runConfig
                  2
                  (config 200 leftRev
                    ((encodeCodeWordAsInput
                      (MachineCodeSymbol.transition :: rest)).map some)))
              (k := 2) (n := n)
              rfl
              (by
                cases rest <;>
                simp [NonemptyNatSuffixScannerDescription,
                  nonemptyNatSuffixTransitions,
                  StageInputMarkedScannerDescription,
                  config, tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (202 : Nat) ≠ 999
                lia)
      | tick =>
          simp [decodeNat] at hdecode
          cases hrest : decodeNat rest with
          | none =>
              simp [hrest] at hdecode
              apply
                nonemptyNatSuffixScannerDescription_ne_halt_of_reaches_ne_halt_region
                  (k := 4)
                  (mid :=
                    config 200
                      (List.append (tickBits.reverse.map some) leftRev)
                      ((encodeCodeWordAsInput rest).map
                        some))
              · simpa [tickBits, encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  NonemptyNatSuffixScannerDescription] using
                  nonemptyNatSuffix_run_state200_tick leftRev
                    ((encodeCodeWordAsInput rest).map some)
              · intro m
                exact ih
                  (List.append (tickBits.reverse.map some) leftRev)
                  hrest m
          | some parsed =>
              simp [hrest] at hdecode
      | done =>
          simp [decodeNat] at hdecode
      | blank =>
          exact
            CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
              nonemptyNatSuffixScannerDescription_haltTransitionFree
              (D := NonemptyNatSuffixScannerDescription)
              (c :=
                config 200 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.blank :: rest)).map some))
              (stuck :=
                NonemptyNatSuffixScannerDescription.runConfig
                  1
                  (config 200 leftRev
                    ((encodeCodeWordAsInput
                      (MachineCodeSymbol.blank :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [NonemptyNatSuffixScannerDescription,
                  nonemptyNatSuffixTransitions,
                  StageInputMarkedScannerDescription,
                  config, tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (201 : Nat) ≠ 999
                lia)
      | zero =>
          exact
            CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
              nonemptyNatSuffixScannerDescription_haltTransitionFree
              (D := NonemptyNatSuffixScannerDescription)
              (c :=
                config 200 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.zero :: rest)).map some))
              (stuck :=
                NonemptyNatSuffixScannerDescription.runConfig
                  1
                  (config 200 leftRev
                    ((encodeCodeWordAsInput
                      (MachineCodeSymbol.zero :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [NonemptyNatSuffixScannerDescription,
                  nonemptyNatSuffixTransitions,
                  StageInputMarkedScannerDescription,
                  config, tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (201 : Nat) ≠ 999
                lia)
      | one =>
          exact
            CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
              nonemptyNatSuffixScannerDescription_haltTransitionFree
              (D := NonemptyNatSuffixScannerDescription)
              (c :=
                config 200 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.one :: rest)).map some))
              (stuck :=
                NonemptyNatSuffixScannerDescription.runConfig
                  1
                  (config 200 leftRev
                    ((encodeCodeWordAsInput
                      (MachineCodeSymbol.one :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [NonemptyNatSuffixScannerDescription,
                  nonemptyNatSuffixTransitions,
                  StageInputMarkedScannerDescription,
                  config, tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (201 : Nat) ≠ 999
                lia)
      | moveLeft =>
          exact
            CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
              nonemptyNatSuffixScannerDescription_haltTransitionFree
              (D := NonemptyNatSuffixScannerDescription)
              (c :=
                config 200 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.moveLeft :: rest)).map some))
              (stuck :=
                NonemptyNatSuffixScannerDescription.runConfig
                  1
                  (config 200 leftRev
                    ((encodeCodeWordAsInput
                      (MachineCodeSymbol.moveLeft :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [NonemptyNatSuffixScannerDescription,
                  nonemptyNatSuffixTransitions,
                  StageInputMarkedScannerDescription,
                  config, tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (201 : Nat) ≠ 999
                lia)
      | moveRight =>
          exact
            CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
              nonemptyNatSuffixScannerDescription_haltTransitionFree
              (D := NonemptyNatSuffixScannerDescription)
              (c :=
                config 200 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.moveRight :: rest)).map some))
              (stuck :=
                config 200 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.moveRight :: rest)).map some))
              (k := 0) (n := n)
              rfl
              (by
                cases rest <;>
                simp [NonemptyNatSuffixScannerDescription,
                  nonemptyNatSuffixTransitions,
                  StageInputMarkedScannerDescription,
                  config, tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read])
              (by
                change (200 : Nat) ≠ 999
                lia)

theorem nonemptyNatSuffixScannerDescription_runConfig_code_inv
    (baseLeft : List (Option Bool)) (code : Word MachineCodeSymbol)
    {Tout : Tape Bool} {n : Nat}
    (h :
      NonemptyNatSuffixScannerDescription.runConfig
          n
          (config
            NonemptyNatSuffixScannerDescription.start
            baseLeft
            ((encodeCodeWordAsInput code).map some)) =
        { state :=
            NonemptyNatSuffixScannerDescription.halt
          tape := Tout }) :
    exists stage : Nat,
    exists symbol : MachineCodeSymbol,
    exists suffix : Word MachineCodeSymbol,
      code = encodeNatAppend stage (symbol :: suffix) := by
  cases hdecode : decodeNat code with
  | none =>
      have hne :=
        nonemptyNatSuffixScannerDescription_runConfig_decodeNat_none_ne_halt
          code baseLeft hdecode n
      have hstate :
          (NonemptyNatSuffixScannerDescription.runConfig
            n
            (config
              NonemptyNatSuffixScannerDescription.start
              baseLeft
              ((encodeCodeWordAsInput code).map some))).state =
            NonemptyNatSuffixScannerDescription.halt := by
        simpa using congrArg Configuration.state h
      exact False.elim (hne (by
        simpa [NonemptyNatSuffixScannerDescription] using hstate))
  | some parsed =>
      rcases parsed with ⟨stage, suffix⟩
      have hcode :
          code = encodeNatAppend stage suffix :=
        decodeNat_eq_some_encodeNatAppend hdecode
      cases suffix with
      | nil =>
          have hrun :
              NonemptyNatSuffixScannerDescription.runConfig
                  n
                  (config 200 baseLeft
                    ((encodeCodeWordAsInput
                      (encodeNatAppend stage [])).map
                      some)) =
                { state :=
                    NonemptyNatSuffixScannerDescription.halt
                  tape := Tout } := by
            simpa [NonemptyNatSuffixScannerDescription, hcode] using h
          have hne :=
            nonemptyNatSuffixScannerDescription_runConfig_encodeNat_empty_ne_halt
              stage baseLeft n
          have hstate :
              (NonemptyNatSuffixScannerDescription.runConfig
                n
                (config 200 baseLeft
                  ((encodeCodeWordAsInput
                    (encodeNatAppend stage [])).map
                    some))).state =
                NonemptyNatSuffixScannerDescription.halt := by
            simpa using congrArg Configuration.state hrun
          exact False.elim (hne hstate)
      | cons symbol suffixTail =>
          exact ⟨stage, symbol, suffixTail, hcode⟩

theorem run_natSuffix_raw_to_handoff_withBase
    (stage : Nat) (baseLeft : List (Option Bool))
    (b : Bool) (suffixTail : Word Bool) :
    exists steps : Nat,
      NatSuffixScannerDescription.runConfig steps
          (config 200 baseLeft
            (List.append ((stageNatBits stage).map some)
              (some b :: suffixTail.map some))) =
        natSuffixHandoffConfigWithBase stage baseLeft
          (b :: suffixTail) := by
  rcases stageNatBits_reverse_map_some_cons stage with
    ⟨tail, htail⟩
  refine ⟨4 * stage + 5, ?_⟩
  rw [show 4 * stage + 5 = (4 * stage + 4) + 1 by lia]
  rw [runConfig_add]
  rw [natSuffix_run_state200_stageNat_to_state210]
  rw [htail]
  unfold natSuffixHandoffConfigWithBase
  simpa [config, tapeAtCells, htail, List.append_assoc] using!
    natSuffix_run_state210_handoff b (some true)
      (List.append tail baseLeft) (suffixTail.map some)

theorem run_natSuffix_raw_to_handoff_withBaseAndRight
    (stage : Nat) (baseLeft : List (Option Bool))
    (b : Bool) (suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    exists steps : Nat,
      NatSuffixScannerDescription.runConfig steps
          (config 200 baseLeft
            (List.append ((stageNatBits stage).map some)
              (some b ::
                List.append (suffixTail.map some) rightPadding))) =
        natSuffixHandoffConfigWithBaseAndRight
          stage baseLeft (b :: suffixTail) rightPadding := by
  rcases stageNatBits_reverse_map_some_cons stage with
    ⟨tail, htail⟩
  refine ⟨4 * stage + 5, ?_⟩
  rw [show 4 * stage + 5 = (4 * stage + 4) + 1 by lia]
  rw [runConfig_add]
  rw [natSuffix_run_state200_stageNat_to_state210]
  rw [htail]
  unfold natSuffixHandoffConfigWithBaseAndRight
  simpa [config, tapeAtCells, htail, List.append_assoc] using!
    natSuffix_run_state210_handoff b (some true)
      (List.append tail baseLeft)
      (List.append (suffixTail.map some) rightPadding)

theorem natSuffixHandoffConfigWithBase_move_right
    (stage : Nat) (baseLeft : List (Option Bool))
    (b : Bool) (suffixTail : Word Bool) :
    Tape.move Direction.right
        (natSuffixHandoffConfigWithBase stage baseLeft
          (b :: suffixTail)).tape =
      tapeAtCells
        (List.append ((stageNatBits stage).reverse.map some) baseLeft)
        ((b :: suffixTail).map some) := by
  rcases stageNatBits_reverse_map_some_cons stage with
    ⟨tail, htail⟩
  unfold natSuffixHandoffConfigWithBase
  rw [htail]
  simpa [List.append_assoc] using!
    FoC.Computability.CommonGround.FiniteTransducers.tapeAtCells_move_right_move_left_cons (some true)
      (List.append tail baseLeft) (some b) (suffixTail.map some)

theorem natSuffixHandoffConfigWithBaseAndRight_move_right
    (stage : Nat) (baseLeft : List (Option Bool))
    (b : Bool) (suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    Tape.move Direction.right
        (natSuffixHandoffConfigWithBaseAndRight
          stage baseLeft (b :: suffixTail) rightPadding).tape =
      tapeAtCells
        (List.append ((stageNatBits stage).reverse.map some) baseLeft)
        (List.append ((b :: suffixTail).map some) rightPadding) := by
  rcases stageNatBits_reverse_map_some_cons stage with
    ⟨tail, htail⟩
  unfold natSuffixHandoffConfigWithBaseAndRight
  rw [htail]
  simpa [List.append_assoc] using!
    FoC.Computability.CommonGround.FiniteTransducers.tapeAtCells_move_right_move_left_cons (some true)
      (List.append tail baseLeft) (some b)
      (List.append (suffixTail.map some) rightPadding)


theorem natSuffixScannerDescription_ne_halt_of_reaches_ne_halt_region
    {c mid : Configuration} {k n : Nat}
    (hrun :
      NatSuffixScannerDescription.runConfig
          k c = mid)
    (hmid :
      forall m : Nat,
        (NatSuffixScannerDescription.runConfig
          m mid).state ≠
          NatSuffixScannerDescription.halt) :
    (NatSuffixScannerDescription.runConfig
      n c).state ≠
      NatSuffixScannerDescription.halt := by
  by_cases hle : n ≤ k
  · intro hhalt
    let rem := k - n
    have hk : k = n + rem := by
      lia
    have hcfg :
        NatSuffixScannerDescription.runConfig
            n c =
          { state :=
              NatSuffixScannerDescription.halt
            tape :=
              (NatSuffixScannerDescription.runConfig
                n c).tape } := by
      cases hrunN :
          NatSuffixScannerDescription.runConfig
            n c with
      | mk state tape =>
          simp [hrunN] at hhalt
          simp [hhalt]
    have hhaltAtK :
        (NatSuffixScannerDescription.runConfig
          k c).state =
          NatSuffixScannerDescription.halt := by
      rw [hk, runConfig_add, hcfg,
        runConfig_halt
          natSuffixScannerDescription_haltTransitionFree]
    rw [hrun] at hhaltAtK
    exact hmid 0 hhaltAtK
  · have hn : n = k + (n - k) := by
      lia
    rw [hn, runConfig_add, hrun]
    exact hmid (n - k)

theorem natSuffixScannerDescription_runConfig_decodeNat_none_ne_halt
    (tokens : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (hdecode : decodeNat tokens = none) (n : Nat) :
    (NatSuffixScannerDescription.runConfig
      n
      (config 200 leftRev
        ((encodeCodeWordAsInput tokens).map some))).state ≠
      NatSuffixScannerDescription.halt := by
  induction tokens generalizing leftRev n with
  | nil =>
      exact
        CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
          natSuffixScannerDescription_haltTransitionFree
          (D := NatSuffixScannerDescription)
          (c :=
            config 200 leftRev
              ((encodeCodeWordAsInput
                ([] : Word MachineCodeSymbol)).map some))
          (stuck :=
            config 200 leftRev
              ((encodeCodeWordAsInput
                ([] : Word MachineCodeSymbol)).map some))
          (k := 0) (n := n)
          rfl
          (by rfl)
          (by
            change (200 : Nat) ≠ 999
            lia)
  | cons symbol rest ih =>
      cases symbol with
      | header =>
          exact
            CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
              natSuffixScannerDescription_haltTransitionFree
              (D := NatSuffixScannerDescription)
              (c :=
                config 200 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.header :: rest)).map some))
              (stuck :=
                NatSuffixScannerDescription.runConfig
                  2
                  (config 200 leftRev
                    ((encodeCodeWordAsInput
                      (MachineCodeSymbol.header :: rest)).map some)))
              (k := 2) (n := n)
              rfl
              (by
                cases rest <;>
                simp [NatSuffixScannerDescription,
                  MarkedPrefixScannerDescription,
                  StageInputMarkedScannerDescription,
                  config, tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (202 : Nat) ≠ 999
                lia)
      | transition =>
          exact
            CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
              natSuffixScannerDescription_haltTransitionFree
              (D := NatSuffixScannerDescription)
              (c :=
                config 200 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.transition :: rest)).map some))
              (stuck :=
                NatSuffixScannerDescription.runConfig
                  2
                  (config 200 leftRev
                    ((encodeCodeWordAsInput
                      (MachineCodeSymbol.transition :: rest)).map some)))
              (k := 2) (n := n)
              rfl
              (by
                cases rest <;>
                simp [NatSuffixScannerDescription,
                  MarkedPrefixScannerDescription,
                  StageInputMarkedScannerDescription,
                  config, tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (202 : Nat) ≠ 999
                lia)
      | tick =>
          simp [decodeNat] at hdecode
          cases hrest : decodeNat rest with
          | none =>
              simp [hrest] at hdecode
              apply
                natSuffixScannerDescription_ne_halt_of_reaches_ne_halt_region
                  (k := 4)
                  (mid :=
                    config 200
                      (List.append (tickBits.reverse.map some) leftRev)
                      ((encodeCodeWordAsInput rest).map
                        some))
              · simpa [tickBits, encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  NatSuffixScannerDescription] using!
                  run_state200_tick leftRev
                    ((encodeCodeWordAsInput rest).map some)
              · intro m
                exact ih
                  (List.append (tickBits.reverse.map some) leftRev)
                  hrest m
          | some parsed =>
              simp [hrest] at hdecode
      | done =>
          simp [decodeNat] at hdecode
      | blank =>
          exact
            CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
              natSuffixScannerDescription_haltTransitionFree
              (D := NatSuffixScannerDescription)
              (c :=
                config 200 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.blank :: rest)).map some))
              (stuck :=
                NatSuffixScannerDescription.runConfig
                  1
                  (config 200 leftRev
                    ((encodeCodeWordAsInput
                      (MachineCodeSymbol.blank :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [NatSuffixScannerDescription,
                  MarkedPrefixScannerDescription,
                  StageInputMarkedScannerDescription,
                  config, tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (201 : Nat) ≠ 999
                lia)
      | zero =>
          exact
            CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
              natSuffixScannerDescription_haltTransitionFree
              (D := NatSuffixScannerDescription)
              (c :=
                config 200 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.zero :: rest)).map some))
              (stuck :=
                NatSuffixScannerDescription.runConfig
                  1
                  (config 200 leftRev
                    ((encodeCodeWordAsInput
                      (MachineCodeSymbol.zero :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [NatSuffixScannerDescription,
                  MarkedPrefixScannerDescription,
                  StageInputMarkedScannerDescription,
                  config, tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (201 : Nat) ≠ 999
                lia)
      | one =>
          exact
            CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
              natSuffixScannerDescription_haltTransitionFree
              (D := NatSuffixScannerDescription)
              (c :=
                config 200 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.one :: rest)).map some))
              (stuck :=
                NatSuffixScannerDescription.runConfig
                  1
                  (config 200 leftRev
                    ((encodeCodeWordAsInput
                      (MachineCodeSymbol.one :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [NatSuffixScannerDescription,
                  MarkedPrefixScannerDescription,
                  StageInputMarkedScannerDescription,
                  config, tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (201 : Nat) ≠ 999
                lia)
      | moveLeft =>
          exact
            CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
              natSuffixScannerDescription_haltTransitionFree
              (D := NatSuffixScannerDescription)
              (c :=
                config 200 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.moveLeft :: rest)).map some))
              (stuck :=
                NatSuffixScannerDescription.runConfig
                  1
                  (config 200 leftRev
                    ((encodeCodeWordAsInput
                      (MachineCodeSymbol.moveLeft :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [NatSuffixScannerDescription,
                  MarkedPrefixScannerDescription,
                  StageInputMarkedScannerDescription,
                  config, tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (201 : Nat) ≠ 999
                lia)
      | moveRight =>
          exact
            CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
              natSuffixScannerDescription_haltTransitionFree
              (D := NatSuffixScannerDescription)
              (c :=
                config 200 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.moveRight :: rest)).map some))
              (stuck :=
                config 200 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.moveRight :: rest)).map some))
              (k := 0) (n := n)
              rfl
              (by
                cases rest <;>
                simp [NatSuffixScannerDescription,
                  MarkedPrefixScannerDescription,
                  StageInputMarkedScannerDescription,
                  config, tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read])
              (by
                change (200 : Nat) ≠ 999
                lia)

theorem natSuffixScannerDescription_runConfig_code_inv
    (baseLeft : List (Option Bool)) (code : Word MachineCodeSymbol)
    {Tout : Tape Bool} {n : Nat}
    (h :
      NatSuffixScannerDescription.runConfig
          n
          (config
            NatSuffixScannerDescription.start
            baseLeft
            ((encodeCodeWordAsInput code).map some)) =
        { state :=
            NatSuffixScannerDescription.halt
          tape := Tout }) :
    exists stage : Nat,
    exists suffix : Word MachineCodeSymbol,
      code = encodeNatAppend stage suffix := by
  cases hdecode : decodeNat code with
  | none =>
      have hne :=
        natSuffixScannerDescription_runConfig_decodeNat_none_ne_halt
          code baseLeft hdecode n
      have hstate :
          (NatSuffixScannerDescription.runConfig
            n
            (config
              NatSuffixScannerDescription.start
              baseLeft
              ((encodeCodeWordAsInput code).map some))).state =
            NatSuffixScannerDescription.halt := by
        simpa using congrArg Configuration.state h
      exact False.elim (hne hstate)
  | some parsed =>
      rcases parsed with ⟨stage, suffix⟩
      exact
        ⟨stage, suffix,
          decodeNat_eq_some_encodeNatAppend hdecode⟩

end DovetailStagePrefix
end CanonicalLayouts
end EncRewriters

end Computability
end FoC

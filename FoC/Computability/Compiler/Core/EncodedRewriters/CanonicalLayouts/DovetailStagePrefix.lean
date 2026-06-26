import FoC.Computability.Compiler.Core.CommonGround.SeqComposition
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
  · exact transition_wellFormed_of_all
      (l := MarkedPrefixScannerDescription.transitions)
      (stateCount := MarkedPrefixScannerDescription.stateCount)
      (by
        native_decide)
  · exact transition_deterministic_of_all
      (l := MarkedPrefixScannerDescription.transitions)
      (by
        native_decide)

theorem markedPrefixScannerDescription_haltTransitionFree :
    MarkedPrefixScannerDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := MarkedPrefixScannerDescription.transitions)
    (state := MarkedPrefixScannerDescription.halt)
    (by
      native_decide)

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
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · exact transition_wellFormed_of_all
      (l := NatSuffixScannerDescription.transitions)
      (stateCount := NatSuffixScannerDescription.stateCount)
      (by
        native_decide)
  · exact transition_deterministic_of_all
      (l := NatSuffixScannerDescription.transitions)
      (by
        native_decide)

theorem natSuffixScannerDescription_haltTransitionFree :
    NatSuffixScannerDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := NatSuffixScannerDescription.transitions)
    (state := NatSuffixScannerDescription.halt)
    (by
      native_decide)

theorem natSuffixScannerDescription_subroutineReady :
    NatSuffixScannerDescription.SubroutineReady :=
  ⟨natSuffixScannerDescription_wellFormed,
    natSuffixScannerDescription_haltTransitionFree⟩

theorem natBits_eq_encodeNatAppend
    (n : Nat) (suffix : Word MachineCodeSymbol) :
    MachineDescription.encodeCodeWordAsInput
        (MachineDescription.encodeNatAppend n suffix) =
      List.append (stageNatBits n)
        (MachineDescription.encodeCodeWordAsInput suffix) := by
  rw [MachineDescription.encodeNatAppend]
  rw [MachineDescription.encodeCodeWordAsInput_append]
  rfl

theorem tapeAtCells_move_right_move_left_cons
    (cell : Option Bool) (left : List (Option Bool))
    (head : Option Bool) (right : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (tapeAtCells (cell :: left) (head :: right))) =
      tapeAtCells (cell :: left) (head :: right) := by
  rfl

theorem runConfig_eq_of_transitions_eq
    (D E : MachineDescription)
    (htrans : D.transitions = E.transitions)
    (n : Nat) (c : MachineDescription.Configuration) :
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
        unfold MachineDescription.stepConfig
        unfold MachineDescription.lookupTransition
        rw [htrans]
      rw [hstep]
      cases E.stepConfig c with
      | none =>
          rfl
      | some next =>
          exact ih next

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

def natSuffixHandoffConfigWithBase
    (stage : Nat) (baseLeft : List (Option Bool))
    (suffixBits : Word Bool) : MachineDescription.Configuration :=
  { state := NatSuffixScannerDescription.halt
    tape :=
      Tape.move Direction.left
        (tapeAtCells
          (List.append ((stageNatBits stage).reverse.map some)
            baseLeft)
          (suffixBits.map some)) }

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
  rw [show 4 * stage + 5 = (4 * stage + 4) + 1 by omega]
  rw [MachineDescription.runConfig_add]
  rw [natSuffix_run_state200_stageNat_to_state210]
  rw [htail]
  unfold natSuffixHandoffConfigWithBase
  simpa [config, tapeAtCells, htail, List.append_assoc] using
    natSuffix_run_state210_handoff b (some true)
      (List.append tail baseLeft) (suffixTail.map some)

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
  simpa [List.append_assoc] using
    tapeAtCells_move_right_move_left_cons (some true)
      (List.append tail baseLeft) (some b) (suffixTail.map some)


theorem natSuffixScannerDescription_ne_halt_of_reaches_ne_halt_region
    {c mid : MachineDescription.Configuration} {k n : Nat}
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
      omega
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
      rw [hk, MachineDescription.runConfig_add, hcfg,
        MachineDescription.runConfig_halt
          natSuffixScannerDescription_haltTransitionFree]
    rw [hrun] at hhaltAtK
    exact hmid 0 hhaltAtK
  · have hn : n = k + (n - k) := by
      omega
    rw [hn, MachineDescription.runConfig_add, hrun]
    exact hmid (n - k)

theorem natSuffixScannerDescription_runConfig_decodeNat_none_ne_halt
    (tokens : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (hdecode : MachineDescription.decodeNat tokens = none) (n : Nat) :
    (NatSuffixScannerDescription.runConfig
      n
      (config 200 leftRev
        ((MachineDescription.encodeCodeWordAsInput tokens).map some))).state ≠
      NatSuffixScannerDescription.halt := by
  induction tokens generalizing leftRev n with
  | nil =>
      exact
        CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
          natSuffixScannerDescription_haltTransitionFree
          (D := NatSuffixScannerDescription)
          (c :=
            config 200 leftRev
              ((MachineDescription.encodeCodeWordAsInput
                ([] : Word MachineCodeSymbol)).map some))
          (stuck :=
            config 200 leftRev
              ((MachineDescription.encodeCodeWordAsInput
                ([] : Word MachineCodeSymbol)).map some))
          (k := 0) (n := n)
          rfl
          (by rfl)
          (by
            change (200 : Nat) ≠ 999
            omega)
  | cons symbol rest ih =>
      cases symbol with
      | header =>
          exact
            CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
              natSuffixScannerDescription_haltTransitionFree
              (D := NatSuffixScannerDescription)
              (c :=
                config 200 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.header :: rest)).map some))
              (stuck :=
                NatSuffixScannerDescription.runConfig
                  2
                  (config 200 leftRev
                    ((MachineDescription.encodeCodeWordAsInput
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
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (202 : Nat) ≠ 999
                omega)
      | transition =>
          exact
            CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
              natSuffixScannerDescription_haltTransitionFree
              (D := NatSuffixScannerDescription)
              (c :=
                config 200 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.transition :: rest)).map some))
              (stuck :=
                NatSuffixScannerDescription.runConfig
                  2
                  (config 200 leftRev
                    ((MachineDescription.encodeCodeWordAsInput
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
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (202 : Nat) ≠ 999
                omega)
      | tick =>
          simp [MachineDescription.decodeNat] at hdecode
          cases hrest : MachineDescription.decodeNat rest with
          | none =>
              simp [hrest] at hdecode
              apply
                natSuffixScannerDescription_ne_halt_of_reaches_ne_halt_region
                  (k := 4)
                  (mid :=
                    config 200
                      (List.append (tickBits.reverse.map some) leftRev)
                      ((MachineDescription.encodeCodeWordAsInput rest).map
                        some))
              · simpa [tickBits, MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  NatSuffixScannerDescription] using
                  run_state200_tick leftRev
                    ((MachineDescription.encodeCodeWordAsInput rest).map some)
              · intro m
                exact ih
                  (List.append (tickBits.reverse.map some) leftRev)
                  hrest m
          | some parsed =>
              simp [hrest] at hdecode
      | done =>
          simp [MachineDescription.decodeNat] at hdecode
      | blank =>
          exact
            CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
              natSuffixScannerDescription_haltTransitionFree
              (D := NatSuffixScannerDescription)
              (c :=
                config 200 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.blank :: rest)).map some))
              (stuck :=
                NatSuffixScannerDescription.runConfig
                  1
                  (config 200 leftRev
                    ((MachineDescription.encodeCodeWordAsInput
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
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (201 : Nat) ≠ 999
                omega)
      | zero =>
          exact
            CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
              natSuffixScannerDescription_haltTransitionFree
              (D := NatSuffixScannerDescription)
              (c :=
                config 200 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.zero :: rest)).map some))
              (stuck :=
                NatSuffixScannerDescription.runConfig
                  1
                  (config 200 leftRev
                    ((MachineDescription.encodeCodeWordAsInput
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
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (201 : Nat) ≠ 999
                omega)
      | one =>
          exact
            CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
              natSuffixScannerDescription_haltTransitionFree
              (D := NatSuffixScannerDescription)
              (c :=
                config 200 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.one :: rest)).map some))
              (stuck :=
                NatSuffixScannerDescription.runConfig
                  1
                  (config 200 leftRev
                    ((MachineDescription.encodeCodeWordAsInput
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
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (201 : Nat) ≠ 999
                omega)
      | moveLeft =>
          exact
            CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
              natSuffixScannerDescription_haltTransitionFree
              (D := NatSuffixScannerDescription)
              (c :=
                config 200 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.moveLeft :: rest)).map some))
              (stuck :=
                NatSuffixScannerDescription.runConfig
                  1
                  (config 200 leftRev
                    ((MachineDescription.encodeCodeWordAsInput
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
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (201 : Nat) ≠ 999
                omega)
      | moveRight =>
          exact
            CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
              natSuffixScannerDescription_haltTransitionFree
              (D := NatSuffixScannerDescription)
              (c :=
                config 200 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.moveRight :: rest)).map some))
              (stuck :=
                config 200 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
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
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read])
              (by
                change (200 : Nat) ≠ 999
                omega)

theorem natSuffixScannerDescription_runConfig_code_inv
    (baseLeft : List (Option Bool)) (code : Word MachineCodeSymbol)
    {Tout : Tape Bool} {n : Nat}
    (h :
      NatSuffixScannerDescription.runConfig
          n
          (config
            NatSuffixScannerDescription.start
            baseLeft
            ((MachineDescription.encodeCodeWordAsInput code).map some)) =
        { state :=
            NatSuffixScannerDescription.halt
          tape := Tout }) :
    exists stage : Nat,
    exists suffix : Word MachineCodeSymbol,
      code = MachineDescription.encodeNatAppend stage suffix := by
  cases hdecode : MachineDescription.decodeNat code with
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
              ((MachineDescription.encodeCodeWordAsInput code).map some))).state =
            NatSuffixScannerDescription.halt := by
        simpa using congrArg MachineDescription.Configuration.state h
      exact False.elim (hne hstate)
  | some parsed =>
      rcases parsed with ⟨stage, suffix⟩
      exact
        ⟨stage, suffix,
          MachineDescription.decodeNat_eq_some_encodeNatAppend hdecode⟩

end DovetailStagePrefix
end CanonicalLayouts
end EncodedRewriters

end Computability
end FoC

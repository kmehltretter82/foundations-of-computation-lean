import FoC.Computability.Compiler.Core.CommonGround.SeqComposition
import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.StageInputMarkedScanner.ClosedBasic

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
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · exact transition_wellFormed_of_all
      (l := NonemptyNatSuffixScannerDescription.transitions)
      (stateCount := NonemptyNatSuffixScannerDescription.stateCount)
      (by
        native_decide)
  · exact transition_deterministic_of_all
      (l := NonemptyNatSuffixScannerDescription.transitions)
      (by
        native_decide)

theorem nonemptyNatSuffixScannerDescription_haltTransitionFree :
    NonemptyNatSuffixScannerDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := NonemptyNatSuffixScannerDescription.transitions)
    (state := NonemptyNatSuffixScannerDescription.halt)
    (by
      native_decide)

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

theorem nonemptyNatSuffix_lookup_210_false :
    NonemptyNatSuffixScannerDescription.lookupTransition 210 (some false) =
      some
        (keepMove 210 (some false) Direction.left
          NonemptyNatSuffixScannerDescription.halt) := by
  native_decide

theorem nonemptyNatSuffix_lookup_210_true :
    NonemptyNatSuffixScannerDescription.lookupTransition 210 (some true) =
      some
        (keepMove 210 (some true) Direction.left
          NonemptyNatSuffixScannerDescription.halt) := by
  native_decide

theorem nonemptyNatSuffix_lookup_210_none :
    NonemptyNatSuffixScannerDescription.lookupTransition 210 none = none := by
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
        simpa [MarkedPrefixScannerDescription] using
          run_state200_tick left
            (List.append ((stageNatBits stage).map some) right)
      rw [htick]
      have h := ih (List.append (tickBits.reverse.map some) left)
      simpa [stageNatBits_succ, tickBits,
        encodeCodeSymbolAsInput,
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
  rw [show 4 * stage + 5 = (4 * stage + 4) + 1 by omega]
  rw [runConfig_add]
  rw [markedPrefix_run_state200_stageNat_to_state210]
  rw [htail]
  simpa [List.append_assoc] using
    markedPrefix_run_state210_handoff b (some true)
      (List.append tail left) right

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

theorem nonemptyNatSuffix_run_state200_tick
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

theorem nonemptyNatSuffix_run_state200_done_to_state210
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
      simpa [stageNatBits_zero] using
        nonemptyNatSuffix_run_state200_done_to_state210 left right
  | succ stage ih =>
      rw [show 4 * (stage + 1) + 4 = 4 + (4 * stage + 4) by
        omega]
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

theorem nonemptyNatSuffix_run_state210_handoff
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

theorem nonemptyNatSuffix_step_state210_none
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
  rw [show 4 * stage + 5 = (4 * stage + 4) + 1 by omega]
  rw [runConfig_add]
  rw [nonemptyNatSuffix_run_state200_stageNat_to_state210]
  rw [htail]
  unfold nonemptyNatSuffixHandoffConfigWithBase
  simpa [config, tapeAtCells, htail, List.append_assoc] using
    nonemptyNatSuffix_run_state210_handoff b (some true)
      (List.append tail baseLeft) (suffixTail.map some)

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
  simpa [List.append_assoc] using
    tapeAtCells_move_right_move_left_cons (some true)
      (List.append tail baseLeft) (some b) (suffixTail.map some)

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
        (by simpa [c0] using hforward)
        (by simpa [c0] using h)).symm
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
      omega
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
      omega
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
        omega)

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
            omega)
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
                omega)
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
                omega)
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
                omega)
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
                omega)
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
                omega)
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
                omega)
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
                omega)

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
  rw [show 4 * stage + 5 = (4 * stage + 4) + 1 by omega]
  rw [runConfig_add]
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
      rw [hk, runConfig_add, hcfg,
        runConfig_halt
          natSuffixScannerDescription_haltTransitionFree]
    rw [hrun] at hhaltAtK
    exact hmid 0 hhaltAtK
  · have hn : n = k + (n - k) := by
      omega
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
                omega)
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
                omega)
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
                  NatSuffixScannerDescription] using
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
                omega)
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
                omega)
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
                omega)
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
                omega)
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
end EncodedRewriters

end Computability
end FoC

import FoC.Computability.Compiler.SeqSubroutineSemantics
import FoC.Computability.Compiler.Core.EncodingLemmas
import FoC.Computability.Compiler.Core.TransitionTableChecks

set_option doc.verso true

/-!
# Dovetail initial-layout initializer

This module isolates the finite-source obligation for the
{name}`FoC.Computability.PairedRecognizerDovetailInitialLayoutCode`
initializer.  The exported
right-shifted-output contract is the natural machine-level target: the
initializer emits the canonical encoded dovetail layout and halts one cell to
the right, so the standard code-word handoff move restores the canonical input
tape for the next subroutine.
-/

namespace FoC
namespace Computability

open Languages

private theorem tape_normalizedOutput_move_right_input
    (w : Word Bool) :
    Tape.normalizedOutput
        (Tape.move Direction.right (Tape.input w)) = w := by
  cases w with
  | nil =>
      rfl
  | cons b rest =>
      cases rest with
      | nil =>
          cases b <;> rfl
      | cons c tail =>
          have htail :
              List.filterMap ((fun cell : Option Bool => cell) ∘ some)
                  tail = tail := by
            simpa [Function.comp] using Tape.filterMap_id_map_some tail
          cases b <;> cases c <;>
            simp [Tape.input, Tape.move, Tape.moveRight,
              Tape.normalizedOutput, Tape.cells, htail]

private theorem tape_move_left_move_right_input_encodeCodeWordAsInput_cons
    (symbol : MachineCodeSymbol) (code : Word MachineCodeSymbol) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (Tape.input
            (MachineDescription.encodeCodeWordAsInput (symbol :: code)))) =
      Tape.input
        (MachineDescription.encodeCodeWordAsInput (symbol :: code)) := by
  cases symbol <;> rfl

private theorem tapeCodePrimitiveCodeWord_handoff_tape
    (symbol : MachineCodeSymbol) (code : Word MachineCodeSymbol) :
    Tape.normalizedOutput
        (Tape.move Direction.right
          (Tape.input
            (MachineDescription.encodeCodeWordAsInput (symbol :: code)))) =
        MachineDescription.encodeCodeWordAsInput (symbol :: code) ∧
      Tape.move tapeCodePrimitiveCodeWordHandoffMove
        (Tape.move Direction.right
          (Tape.input
            (MachineDescription.encodeCodeWordAsInput (symbol :: code)))) =
        Tape.input
          (MachineDescription.encodeCodeWordAsInput (symbol :: code)) := by
  constructor
  · exact
      tape_normalizedOutput_move_right_input
        (MachineDescription.encodeCodeWordAsInput (symbol :: code))
  · simpa [tapeCodePrimitiveCodeWordHandoffMove] using
      tape_move_left_move_right_input_encodeCodeWordAsInput_cons
        symbol code

private theorem encodeConfigurationAppend_initial
    (D : MachineDescription) (w : Word Bool)
    (suffix : Word MachineCodeSymbol) :
    MachineDescription.encodeConfigurationAppend (D.initial w) suffix =
      MachineDescription.encodeNatAppend D.start
        (MachineDescription.encodeTapeAppend (Tape.input w) suffix) := by
  rfl

private theorem dovetailInitialLayoutCode_output_eq_transition_cons
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    MachineDescription.DovetailLayout.encode
        (MachineDescription.DovetailLayout.initial
          accept reject w stage) =
      MachineCodeSymbol.transition ::
        MachineDescription.encodeBoolWordAppend w
          (MachineDescription.encodeNatAppend stage
            (MachineDescription.encodeConfigurationAppend
              (accept.initial w)
              (MachineDescription.encodeConfigurationAppend
                (reject.initial w)
                (MachineDescription.encodeBoolAppend false
                  (MachineDescription.encodeBoolAppend false []))))) := by
  rfl

theorem dovetailInitialLayoutCode_output_eq_expanded
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    MachineDescription.DovetailLayout.encode
        (MachineDescription.DovetailLayout.initial
          accept reject w stage) =
      MachineCodeSymbol.transition ::
        MachineDescription.encodeBoolWordAppend w
          (MachineDescription.encodeNatAppend stage
            (MachineDescription.encodeNatAppend accept.start
              (MachineDescription.encodeTapeAppend (Tape.input w)
                (MachineDescription.encodeNatAppend reject.start
                  (MachineDescription.encodeTapeAppend (Tape.input w)
                    (MachineDescription.encodeBoolAppend false
                      (MachineDescription.encodeBoolAppend false []))))))) := by
  rw [dovetailInitialLayoutCode_output_eq_transition_cons,
    encodeConfigurationAppend_initial,
    encodeConfigurationAppend_initial]

theorem pairedRecognizerDovetailInitialLayoutCode_transform_eq_some_cons
    {accept reject : MachineDescription}
    {code out : Word MachineCodeSymbol}
    (h :
      (PairedRecognizerDovetailInitialLayoutCode accept reject).transform
          code = some out) :
    exists tail : Word MachineCodeSymbol,
      out = MachineCodeSymbol.transition :: tail := by
  rcases
      (pairedRecognizerDovetailInitialLayoutCode_transform_eq_some_iff
        accept reject code out).mp h with
    ⟨w, stage, _hcode, hout⟩
  refine
    ⟨MachineDescription.encodeBoolWordAppend w
      (MachineDescription.encodeNatAppend stage
        (MachineDescription.encodeConfigurationAppend
          (accept.initial w)
          (MachineDescription.encodeConfigurationAppend
            (reject.initial w)
            (MachineDescription.encodeBoolAppend false
              (MachineDescription.encodeBoolAppend false []))))), ?_⟩
  rw [hout, dovetailInitialLayoutCode_output_eq_transition_cons]

private theorem tapeCodePrimitiveClosedHandoffCompiled_of_halt_tape_move_right
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (hwell : D.WellFormed)
    (hhaltFree : D.HaltTransitionFree)
    (houtput :
      forall code out : Word MachineCodeSymbol,
        D.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput code)
            (MachineDescription.encodeCodeWordAsInput out) <->
          P.transform code = some out)
    (houtCons :
      forall {code out : Word MachineCodeSymbol},
        P.transform code = some out ->
          exists symbol : MachineCodeSymbol,
          exists tail : Word MachineCodeSymbol,
            out = symbol :: tail)
    (htape :
      forall code : Word MachineCodeSymbol,
      forall T : Tape Bool,
        D.HaltsWithTape
            (MachineDescription.encodeCodeWordAsInput code) T ->
          exists out : Word MachineCodeSymbol,
            P.transform code = some out ∧
              T =
                Tape.move Direction.right
                  (Tape.input
                    (MachineDescription.encodeCodeWordAsInput out))) :
    TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      P D tapeCodePrimitiveCodeWordHandoffMove := by
  constructor
  · exact ⟨⟨hwell, houtput⟩, hhaltFree⟩
  · intro code T hD
    rcases htape code T hD with ⟨out, hp, hT⟩
    rcases houtCons hp with ⟨symbol, tail, hout⟩
    subst out
    subst T
    rcases tapeCodePrimitiveCodeWord_handoff_tape symbol tail with
      ⟨hnorm, hmove⟩
    exact ⟨symbol :: tail, hp, hnorm, hmove⟩

def TapeCodePrimitiveRightShiftedOutputCompiledSubroutineByDescription
    (P : MachineDescription.TapeCodePrimitive)
    (D : MachineDescription) : Prop :=
  D.WellFormed ∧
    D.HaltTransitionFree ∧
      (forall code out : Word MachineCodeSymbol,
        D.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput code)
            (MachineDescription.encodeCodeWordAsInput out) <->
          P.transform code = some out) ∧
        forall code : Word MachineCodeSymbol,
        forall T : Tape Bool,
          D.HaltsWithTape
              (MachineDescription.encodeCodeWordAsInput code) T ->
            exists out : Word MachineCodeSymbol,
              P.transform code = some out ∧
                T =
                  Tape.move Direction.right
                    (Tape.input
                      (MachineDescription.encodeCodeWordAsInput out))

def DovetailInitialLayoutInitializerOutputCode
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) : Word MachineCodeSymbol :=
  MachineDescription.DovetailLayout.encode
    (MachineDescription.DovetailLayout.initial accept reject w stage)

def DovetailInitialLayoutInitializerSuffixCode
    (accept reject : MachineDescription)
    (w : Word Bool) : Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend accept.start
    (MachineDescription.encodeTapeAppend (Tape.input w)
      (MachineDescription.encodeNatAppend reject.start
        (MachineDescription.encodeTapeAppend (Tape.input w)
          (MachineDescription.encodeBoolAppend false
            (MachineDescription.encodeBoolAppend false [])))))

def DovetailInitialLayoutInitializerOutputTape
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) : Tape Bool :=
  Tape.move Direction.right
    (Tape.input
      (MachineDescription.encodeCodeWordAsInput
        (DovetailInitialLayoutInitializerOutputCode
          accept reject w stage)))

def DovetailInitialLayoutInitializerReadySpec
    (initializer : MachineDescription) : Prop :=
  initializer.WellFormed ∧ initializer.HaltTransitionFree

def DovetailInitialLayoutInitializerForwardSpec
    (accept reject initializer : MachineDescription) : Prop :=
  forall w : Word Bool,
  forall stage : Nat,
    initializer.HaltsWithTape
      (MachineDescription.encodeCodeWordAsInput
        (PairedRecognizerDovetailStageInputCode w stage))
      (DovetailInitialLayoutInitializerOutputTape
        accept reject w stage)

def DovetailInitialLayoutInitializerClosedSpec
    (accept reject initializer : MachineDescription) : Prop :=
  forall code : Word MachineCodeSymbol,
  forall T : Tape Bool,
    initializer.HaltsWithTape
        (MachineDescription.encodeCodeWordAsInput code) T ->
      exists w : Word Bool,
      exists stage : Nat,
        code = PairedRecognizerDovetailStageInputCode w stage ∧
          T =
            DovetailInitialLayoutInitializerOutputTape
              accept reject w stage

def DovetailInitialLayoutInitializerRightShiftedSpec
    (accept reject initializer : MachineDescription) : Prop :=
  DovetailInitialLayoutInitializerReadySpec initializer ∧
    DovetailInitialLayoutInitializerForwardSpec
      accept reject initializer ∧
      DovetailInitialLayoutInitializerClosedSpec
        accept reject initializer

def DovetailInitialLayoutInitializerMachineConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists initializer : MachineDescription,
      DovetailInitialLayoutInitializerReadySpec initializer ∧
        DovetailInitialLayoutInitializerForwardSpec
          accept reject initializer ∧
          DovetailInitialLayoutInitializerClosedSpec
            accept reject initializer

def PairedRecognizerDovetailInitialLayoutCodeRightShiftedSpecConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists initializer : MachineDescription,
      DovetailInitialLayoutInitializerRightShiftedSpec
        accept reject initializer

def DovetailInitialLayoutInitializerConcreteMachineConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists initializer : MachineDescription,
      DovetailInitialLayoutInitializerReadySpec initializer ∧
        DovetailInitialLayoutInitializerForwardSpec
          accept reject initializer ∧
          DovetailInitialLayoutInitializerClosedSpec
            accept reject initializer

def DovetailInitialLayoutInitializerRightShiftedOutputCompiledConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists initializer : MachineDescription,
      TapeCodePrimitiveRightShiftedOutputCompiledSubroutineByDescription
        (PairedRecognizerDovetailInitialLayoutCode accept reject)
        initializer

def DovetailInitialLayoutInitializerFiniteDescriptionConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists initializer : MachineDescription,
      DovetailInitialLayoutInitializerRightShiftedSpec
        accept reject initializer

theorem dovetailInitialLayoutInitializerOutputCode_eq_expanded
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    DovetailInitialLayoutInitializerOutputCode accept reject w stage =
      MachineCodeSymbol.transition ::
        MachineDescription.encodeBoolWordAppend w
          (MachineDescription.encodeNatAppend stage
            (MachineDescription.encodeNatAppend accept.start
              (MachineDescription.encodeTapeAppend (Tape.input w)
                (MachineDescription.encodeNatAppend reject.start
                  (MachineDescription.encodeTapeAppend (Tape.input w)
                    (MachineDescription.encodeBoolAppend false
                      (MachineDescription.encodeBoolAppend false []))))))) := by
  exact dovetailInitialLayoutCode_output_eq_expanded accept reject w stage

theorem dovetailInitialLayoutInitializerOutputTape_eq_expanded
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    DovetailInitialLayoutInitializerOutputTape accept reject w stage =
      Tape.move Direction.right
        (Tape.input
          (MachineDescription.encodeCodeWordAsInput
            (MachineCodeSymbol.transition ::
              MachineDescription.encodeBoolWordAppend w
                (MachineDescription.encodeNatAppend stage
                  (MachineDescription.encodeNatAppend accept.start
                    (MachineDescription.encodeTapeAppend (Tape.input w)
                      (MachineDescription.encodeNatAppend reject.start
                        (MachineDescription.encodeTapeAppend (Tape.input w)
                          (MachineDescription.encodeBoolAppend false
                            (MachineDescription.encodeBoolAppend false [])))))))))) := by
  rw [DovetailInitialLayoutInitializerOutputTape,
    dovetailInitialLayoutInitializerOutputCode_eq_expanded]

theorem dovetailInitialLayoutInitializerSuffixCode_eq_configurations
    (accept reject : MachineDescription)
    (w : Word Bool) :
    DovetailInitialLayoutInitializerSuffixCode accept reject w =
      MachineDescription.encodeConfigurationAppend
        (accept.initial w)
        (MachineDescription.encodeConfigurationAppend
          (reject.initial w)
          (MachineDescription.encodeBoolAppend false
            (MachineDescription.encodeBoolAppend false []))) := by
  rw [DovetailInitialLayoutInitializerSuffixCode,
    encodeConfigurationAppend_initial,
    encodeConfigurationAppend_initial]

theorem dovetailInitialLayoutInitializerOutputCode_eq_stageInput_append_suffix
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    DovetailInitialLayoutInitializerOutputCode accept reject w stage =
      MachineCodeSymbol.transition ::
        List.append
          (MachineDescription.DovetailLayout.stageInputCode w stage)
          (DovetailInitialLayoutInitializerSuffixCode accept reject w) := by
  rw [dovetailInitialLayoutInitializerOutputCode_eq_expanded]
  change
    MachineCodeSymbol.transition ::
        MachineDescription.encodeBoolWordAppend w
          (MachineDescription.encodeNatAppend stage
            (DovetailInitialLayoutInitializerSuffixCode accept reject w)) =
      MachineCodeSymbol.transition ::
        List.append
          (MachineDescription.DovetailLayout.stageInputCode w stage)
          (DovetailInitialLayoutInitializerSuffixCode accept reject w)
  congr 1
  have hnat :
      MachineDescription.encodeNatAppend stage
          (DovetailInitialLayoutInitializerSuffixCode accept reject w) =
        List.append (MachineDescription.encodeNatAppend stage [])
          (DovetailInitialLayoutInitializerSuffixCode accept reject w) := by
    simpa using
      encodeNatAppend_append stage ([] : Word MachineCodeSymbol)
        (DovetailInitialLayoutInitializerSuffixCode accept reject w)
  have hbool :=
    encodeBoolWordAppend_append w
      (MachineDescription.encodeNatAppend stage [])
      (DovetailInitialLayoutInitializerSuffixCode accept reject w)
  rw [← hnat] at hbool
  simpa [MachineDescription.DovetailLayout.stageInputCode,
    MachineDescription.DovetailLayout.stageInputCodeAppend] using hbool

theorem encodeTapeAppend_input_nil
    (suffix : Word MachineCodeSymbol) :
    MachineDescription.encodeTapeAppend (Tape.input ([] : Word Bool)) suffix =
      MachineDescription.encodeCellListAppend []
        (MachineDescription.encodeCellAppend none
          (MachineDescription.encodeCellListAppend [] suffix)) := by
  rfl

theorem encodeTapeAppend_input_cons
    (b : Bool) (rest : Word Bool)
    (suffix : Word MachineCodeSymbol) :
    MachineDescription.encodeTapeAppend (Tape.input (b :: rest)) suffix =
      MachineDescription.encodeCellListAppend []
        (MachineDescription.encodeCellAppend (some b)
          (MachineDescription.encodeCellListAppend (rest.map some)
            suffix)) := by
  rfl

theorem dovetailInitialLayoutInitializerOutputBits_eq_stageInput_append_suffix
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    MachineDescription.encodeCodeWordAsInput
        (DovetailInitialLayoutInitializerOutputCode
          accept reject w stage) =
      List.append
        (MachineDescription.encodeCodeSymbolAsInput
          MachineCodeSymbol.transition)
        (List.append
          (MachineDescription.encodeCodeWordAsInput
            (PairedRecognizerDovetailStageInputCode w stage))
          (MachineDescription.encodeCodeWordAsInput
            (DovetailInitialLayoutInitializerSuffixCode
              accept reject w))) := by
  rw [dovetailInitialLayoutInitializerOutputCode_eq_stageInput_append_suffix,
    MachineDescription.encodeCodeWordAsInput]
  rw [MachineDescription.encodeCodeWordAsInput_append]
  rfl

theorem dovetailInitialLayoutInitializerOutputTape_eq_stageInput_append_suffix
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    DovetailInitialLayoutInitializerOutputTape accept reject w stage =
      Tape.move Direction.right
        (Tape.input
          (List.append
            (MachineDescription.encodeCodeSymbolAsInput
              MachineCodeSymbol.transition)
            (List.append
              (MachineDescription.encodeCodeWordAsInput
                (PairedRecognizerDovetailStageInputCode w stage))
              (MachineDescription.encodeCodeWordAsInput
                (DovetailInitialLayoutInitializerSuffixCode
                  accept reject w))))) := by
  rw [DovetailInitialLayoutInitializerOutputTape,
    dovetailInitialLayoutInitializerOutputBits_eq_stageInput_append_suffix]

private def initializerTapeAtCells
    (leftRev cells : List (Option Bool)) : Tape Bool :=
  match cells with
  | [] => { left := leftRev, head := none, right := [] }
  | cell :: rest => { left := leftRev, head := cell, right := rest }

private def initializerConfig
    (state : Nat) (leftRev cells : List (Option Bool)) :
    MachineDescription.Configuration :=
  { state := state, tape := initializerTapeAtCells leftRev cells }

private def initializerCodeCells
    (code : Word MachineCodeSymbol) : List (Option Bool) :=
  (MachineDescription.encodeCodeWordAsInput code).map some

private def initializerStageInputCells
    (w : Word Bool) (stage : Nat) : List (Option Bool) :=
  initializerCodeCells (PairedRecognizerDovetailStageInputCode w stage)

private def initializerSuffixCells
    (accept reject : MachineDescription)
    (w : Word Bool) : List (Option Bool) :=
  initializerCodeCells
    (DovetailInitialLayoutInitializerSuffixCode accept reject w)

private def initializerOutputCells
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) : List (Option Bool) :=
  initializerCodeCells
    (DovetailInitialLayoutInitializerOutputCode accept reject w stage)

private theorem initializer_map_some_append
    (xs ys : Word Bool) :
    List.map some (List.append xs ys) =
      List.append (List.map some xs) (List.map some ys) := by
  induction xs with
  | nil =>
      rfl
  | cons x rest ih =>
      change
        some x :: List.map some (List.append rest ys) =
          some x :: List.append (List.map some rest) (List.map some ys)
      rw [ih]

private theorem initializerCodeCells_append
    (pre suffix : Word MachineCodeSymbol) :
    initializerCodeCells (List.append pre suffix) =
      List.append (initializerCodeCells pre) (initializerCodeCells suffix) := by
  unfold initializerCodeCells
  rw [MachineDescription.encodeCodeWordAsInput_append]
  exact initializer_map_some_append
    (MachineDescription.encodeCodeWordAsInput pre)
    (MachineDescription.encodeCodeWordAsInput suffix)

private def initializerCodeSymbolCells
    (symbol : MachineCodeSymbol) : List (Option Bool) :=
  (MachineDescription.encodeCodeSymbolAsInput symbol).map some

private def initializerNatCodeCells : Nat -> List (Option Bool)
  | 0 => initializerCodeSymbolCells MachineCodeSymbol.done
  | n + 1 =>
      List.append
        (initializerCodeSymbolCells MachineCodeSymbol.tick)
        (initializerNatCodeCells n)

private def initializerCellCodeCells :
    Option Bool -> List (Option Bool)
  | none => initializerCodeSymbolCells MachineCodeSymbol.blank
  | some false => initializerCodeSymbolCells MachineCodeSymbol.zero
  | some true => initializerCodeSymbolCells MachineCodeSymbol.one

private def initializerCellsCodeCells :
    List (Option Bool) -> List (Option Bool)
  | [] => []
  | cell :: rest =>
      List.append (initializerCellCodeCells cell)
        (initializerCellsCodeCells rest)

private def initializerBoolPayloadCells
    (w : Word Bool) : List (Option Bool) :=
  initializerCellsCodeCells (w.map some)

private def initializerBoolWordCells
    (w : Word Bool) : List (Option Bool) :=
  List.append (initializerNatCodeCells w.length)
    (initializerBoolPayloadCells w)

private def initializerMarkedLengthTickCells : List (Option Bool) :=
  [none, some false, some true, some false]

private def initializerConsumedLengthTickCells : List (Option Bool) :=
  [some false, none, some true, some false]

private def initializerMarkedCellCodeCells :
    Option Bool -> List (Option Bool)
  | none => initializerCellCodeCells none
  | some false => [none, some true, some false, some true]
  | some true => [none, some true, some true, some false]

private def initializerRepeatedCells
    (chunk : List (Option Bool)) : Nat -> List (Option Bool)
  | 0 => []
  | n + 1 => List.append chunk (initializerRepeatedCells chunk n)

private def initializerMarkedLengthTickPrefix (n : Nat) :
    List (Option Bool) :=
  initializerRepeatedCells initializerMarkedLengthTickCells n

private def initializerConsumedLengthTickPrefix (n : Nat) :
    List (Option Bool) :=
  initializerRepeatedCells initializerConsumedLengthTickCells n

private def initializerMarkedCellsCodeCells :
    List (Option Bool) -> List (Option Bool)
  | [] => []
  | cell :: rest =>
      List.append (initializerMarkedCellCodeCells cell)
        (initializerMarkedCellsCodeCells rest)

private def initializerMarkedBoolPayloadCells
    (w : Word Bool) : List (Option Bool) :=
  initializerMarkedCellsCodeCells (w.map some)

private def initializerMarkedBoolWordCells
    (w : Word Bool) : List (Option Bool) :=
  List.append (initializerMarkedLengthTickPrefix w.length)
    (List.append (initializerCodeSymbolCells MachineCodeSymbol.done)
      (initializerMarkedBoolPayloadCells w))

private def initializerConsumedBoolWordCells
    (w : Word Bool) : List (Option Bool) :=
  List.append (initializerConsumedLengthTickPrefix w.length)
    (List.append (initializerCodeSymbolCells MachineCodeSymbol.done)
      (initializerMarkedBoolPayloadCells w))

private theorem initializerRepeatedCells_append
    (chunk : List (Option Bool)) (n : Nat)
    (tail : List (Option Bool)) :
    List.append (initializerRepeatedCells chunk n) tail =
      match n with
      | 0 => tail
      | k + 1 =>
          List.append chunk
            (List.append (initializerRepeatedCells chunk k) tail) := by
  cases n <;> simp [initializerRepeatedCells, List.append_assoc]

private theorem initializerNatCodeCells_eq_tick_prefix_done
    (n : Nat) :
    initializerNatCodeCells n =
      List.append
        (initializerRepeatedCells
          (initializerCodeSymbolCells MachineCodeSymbol.tick) n)
        (initializerCodeSymbolCells MachineCodeSymbol.done) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        List.append
            (initializerCodeSymbolCells MachineCodeSymbol.tick)
            (initializerNatCodeCells n) =
          List.append
            (initializerCodeSymbolCells MachineCodeSymbol.tick)
            (List.append
              (initializerRepeatedCells
                (initializerCodeSymbolCells MachineCodeSymbol.tick) n)
              (initializerCodeSymbolCells MachineCodeSymbol.done))
      rw [ih]

private theorem initializerMarkedCellCodeCells_restore
    (cell : Option Bool) :
    initializerMarkedCellCodeCells cell =
      match cell with
      | none => initializerCellCodeCells none
      | some false => [none, some true, some false, some true]
      | some true => [none, some true, some true, some false] := by
  cases cell with
  | none =>
      rfl
  | some b =>
      cases b <;> rfl

private def InitializerWriteTransitionPrefixDescription :
    MachineDescription where
  stateCount := 6
  start := 0
  halt := 5
  transitions :=
    [ MachineDescription.transition
        0 (some false) (some false) Direction.left 1
    , MachineDescription.transition
        0 (some true) (some true) Direction.left 1
    , MachineDescription.transition
        1 none (some true) Direction.left 2
    , MachineDescription.transition
        2 none (some false) Direction.left 3
    , MachineDescription.transition
        3 none (some false) Direction.left 4
    , MachineDescription.transition
        4 none (some false) Direction.right 5
    ]

private theorem initializerWriteTransitionPrefixDescription_wellFormed :
    InitializerWriteTransitionPrefixDescription.WellFormed := by
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · intro t ht
    exact transition_wellFormed_of_all
      (l := InitializerWriteTransitionPrefixDescription.transitions)
      (stateCount :=
        InitializerWriteTransitionPrefixDescription.stateCount)
      (by
        native_decide) t ht
  · intro t u ht hu hkey
    exact transition_deterministic_of_all
      (l := InitializerWriteTransitionPrefixDescription.transitions)
      (by
        native_decide) t u ht hu hkey

private theorem initializerWriteTransitionPrefixDescription_haltTransitionFree :
    InitializerWriteTransitionPrefixDescription.HaltTransitionFree := by
  intro t ht
  exact transition_notFrom_of_all
    (l := InitializerWriteTransitionPrefixDescription.transitions)
    (state := InitializerWriteTransitionPrefixDescription.halt)
    (by
      native_decide) t ht

private theorem initializerWriteTransitionPrefixDescription_subroutineReady :
    InitializerWriteTransitionPrefixDescription.SubroutineReady :=
  ⟨initializerWriteTransitionPrefixDescription_wellFormed,
    initializerWriteTransitionPrefixDescription_haltTransitionFree⟩

private theorem initializerWriteTransitionPrefixDescription_run
    (b : Bool) (rest : List (Option Bool)) :
    InitializerWriteTransitionPrefixDescription.runConfig 5
        (initializerConfig 0 [] (some b :: rest)) =
      initializerConfig 5 [some false]
        (List.append [some false, some false, some true]
          (some b :: rest)) := by
  cases b <;>
    simp [InitializerWriteTransitionPrefixDescription,
      initializerConfig, initializerTapeAtCells,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft, Tape.moveRight]

private def InitializerWriteMarkedTransitionPrefixDescription :
    MachineDescription where
  stateCount := 6
  start := 0
  halt := 5
  transitions :=
    [ MachineDescription.transition
        0 (some false) (some false) Direction.left 1
    , MachineDescription.transition
        0 (some true) (some true) Direction.left 1
    , MachineDescription.transition
        1 none (some true) Direction.left 2
    , MachineDescription.transition
        2 none (some false) Direction.left 3
    , MachineDescription.transition
        3 none none Direction.left 4
    , MachineDescription.transition
        4 none (some false) Direction.right 5
    ]

private theorem initializerWriteMarkedTransitionPrefixDescription_wellFormed :
    InitializerWriteMarkedTransitionPrefixDescription.WellFormed := by
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · intro t ht
    exact transition_wellFormed_of_all
      (l := InitializerWriteMarkedTransitionPrefixDescription.transitions)
      (stateCount :=
        InitializerWriteMarkedTransitionPrefixDescription.stateCount)
      (by
        native_decide) t ht
  · intro t u ht hu hkey
    exact transition_deterministic_of_all
      (l := InitializerWriteMarkedTransitionPrefixDescription.transitions)
      (by
        native_decide) t u ht hu hkey

private theorem initializerWriteMarkedTransitionPrefixDescription_haltTransitionFree :
    InitializerWriteMarkedTransitionPrefixDescription.HaltTransitionFree := by
  intro t ht
  exact transition_notFrom_of_all
    (l := InitializerWriteMarkedTransitionPrefixDescription.transitions)
    (state := InitializerWriteMarkedTransitionPrefixDescription.halt)
    (by
      native_decide) t ht

private theorem initializerWriteMarkedTransitionPrefixDescription_subroutineReady :
    InitializerWriteMarkedTransitionPrefixDescription.SubroutineReady :=
  ⟨initializerWriteMarkedTransitionPrefixDescription_wellFormed,
    initializerWriteMarkedTransitionPrefixDescription_haltTransitionFree⟩

private theorem initializerWriteMarkedTransitionPrefixDescription_run
    (b : Bool) (rest : List (Option Bool)) :
    InitializerWriteMarkedTransitionPrefixDescription.runConfig 5
        (initializerConfig 0 [] (some b :: rest)) =
      initializerConfig 5 [some false]
        (List.append [none, some false, some true]
          (some b :: rest)) := by
  cases b <;>
    simp [InitializerWriteMarkedTransitionPrefixDescription,
      initializerConfig, initializerTapeAtCells,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft, Tape.moveRight]

private def initializerAppendRightLastTape
    (leftRev : Word Bool) (b0 b1 b2 b3 : Bool) : Tape Bool :=
  { left := (List.append [b2, b1, b0] leftRev).map some
    head := some b3
    right := [] }

private def InitializerAppendFixedFourBitsLastDescription
    (b0 b1 b2 b3 : Bool) : MachineDescription where
  stateCount := 6
  start := 0
  halt := 5
  transitions :=
    [ MachineDescription.transition
        0 (some false) (some false) Direction.right 0
    , MachineDescription.transition
        0 (some true) (some true) Direction.right 0
    , MachineDescription.transition
        0 none (some b0) Direction.right 1
    , MachineDescription.transition
        1 none (some b1) Direction.right 2
    , MachineDescription.transition
        2 none (some b2) Direction.right 3
    , MachineDescription.transition
        3 none (some b3) Direction.left 4
    , MachineDescription.transition
        4 (some false) (some false) Direction.right 5
    , MachineDescription.transition
        4 (some true) (some true) Direction.right 5
    ]

private theorem initializerAppendFixedFourBitsLastDescription_wellFormed
    (b0 b1 b2 b3 : Bool) :
    (InitializerAppendFixedFourBitsLastDescription b0 b1 b2 b3).WellFormed := by
  constructor
  · cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
      native_decide
  constructor
  · cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
      native_decide
  constructor
  · cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
      native_decide
  constructor
  · intro t ht
    exact transition_wellFormed_of_all
      (l :=
        (InitializerAppendFixedFourBitsLastDescription
          b0 b1 b2 b3).transitions)
      (stateCount :=
        (InitializerAppendFixedFourBitsLastDescription
          b0 b1 b2 b3).stateCount)
      (by
        cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
          native_decide) t ht
  · intro t u ht hu hkey
    exact transition_deterministic_of_all
      (l :=
        (InitializerAppendFixedFourBitsLastDescription
          b0 b1 b2 b3).transitions)
      (by
        cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
          native_decide) t u ht hu hkey

private theorem initializerAppendFixedFourBitsLastDescription_haltTransitionFree
    (b0 b1 b2 b3 : Bool) :
    (InitializerAppendFixedFourBitsLastDescription
      b0 b1 b2 b3).HaltTransitionFree := by
  intro t ht
  exact transition_notFrom_of_all
    (l :=
      (InitializerAppendFixedFourBitsLastDescription
        b0 b1 b2 b3).transitions)
    (state :=
      (InitializerAppendFixedFourBitsLastDescription
        b0 b1 b2 b3).halt)
    (by
      cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
        native_decide) t ht

private theorem initializerAppendFixedFourBitsLastDescription_step_scan_nonempty
    (b0 b1 b2 b3 : Bool)
    (leftRev : Word Bool) (b : Bool) (rest : Word Bool) :
    (InitializerAppendFixedFourBitsLastDescription b0 b1 b2 b3).stepConfig
        { state := 0
          tape := MachineDescription.appendRightScanTape leftRev (b :: rest) } =
      some
        { state := 0
          tape := MachineDescription.appendRightScanTape
            (b :: leftRev) rest } := by
  cases b <;>
    cases rest <;>
      simp [InitializerAppendFixedFourBitsLastDescription,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition, MachineDescription.Matches,
        MachineDescription.transition,
        MachineDescription.appendRightScanTape, Tape.read, Tape.write,
        Tape.move, Tape.moveRight]

private theorem initializerAppendFixedFourBitsLastDescription_run_scan
    (b0 b1 b2 b3 : Bool)
    (leftRev remaining : Word Bool) :
    (InitializerAppendFixedFourBitsLastDescription b0 b1 b2 b3).runConfig
        remaining.length
        { state := 0
          tape := MachineDescription.appendRightScanTape leftRev remaining } =
      { state := 0
        tape :=
          MachineDescription.appendRightScanTape
            (List.append remaining.reverse leftRev) [] } := by
  induction remaining generalizing leftRev with
  | nil =>
      simp [MachineDescription.runConfig]
  | cons b rest ih =>
      simp [MachineDescription.runConfig,
        initializerAppendFixedFourBitsLastDescription_step_scan_nonempty,
        ih, List.append_assoc]

private theorem initializerAppendFixedFourBitsLastDescription_run_write
    (b0 b1 b2 b3 : Bool) (leftRev : Word Bool) :
    (InitializerAppendFixedFourBitsLastDescription b0 b1 b2 b3).runConfig 5
        { state := 0
          tape := MachineDescription.appendRightScanTape leftRev [] } =
      { state := 5
        tape := initializerAppendRightLastTape leftRev b0 b1 b2 b3 } := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    simp [InitializerAppendFixedFourBitsLastDescription,
      initializerAppendRightLastTape,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition,
      MachineDescription.appendRightScanTape, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft, Tape.moveRight]

private theorem initializerAppendFixedFourBitsLastDescription_run_halt
    (b0 b1 b2 b3 : Bool) (w : Word Bool) :
    (InitializerAppendFixedFourBitsLastDescription b0 b1 b2 b3).runConfig
        (w.length + 5)
        ((InitializerAppendFixedFourBitsLastDescription b0 b1 b2 b3).initial w) =
      { state := 5
        tape := initializerAppendRightLastTape w.reverse b0 b1 b2 b3 } := by
  rw [MachineDescription.runConfig_add]
  have hscan :
      (InitializerAppendFixedFourBitsLastDescription b0 b1 b2 b3).runConfig
          w.length
          ((InitializerAppendFixedFourBitsLastDescription
            b0 b1 b2 b3).initial w) =
        { state := 0
          tape := MachineDescription.appendRightScanTape w.reverse [] } := by
    simpa [MachineDescription.initial,
      InitializerAppendFixedFourBitsLastDescription,
      MachineDescription.appendRightScanTape_nil_eq_input] using
      initializerAppendFixedFourBitsLastDescription_run_scan
        b0 b1 b2 b3 [] w
  rw [hscan]
  exact initializerAppendFixedFourBitsLastDescription_run_write
    b0 b1 b2 b3 w.reverse

private def initializerAppendScanTapeAtCells
    (leftRev : List (Option Bool)) (remaining : Word Bool) :
    Tape Bool :=
  match remaining with
  | [] => { left := leftRev, head := none, right := [] }
  | b :: rest => { left := leftRev, head := some b, right := rest.map some }

private def initializerAppendRightLastTapeAtCells
    (leftRev : List (Option Bool)) (b0 b1 b2 b3 : Bool) :
    Tape Bool :=
  { left :=
      List.append [some b2, some b1, some b0] leftRev
    head := some b3
    right := [] }

private theorem initializerAppendScanTapeAtCells_of_bits
    (leftRev remaining : Word Bool) :
    initializerAppendScanTapeAtCells (leftRev.map some) remaining =
      MachineDescription.appendRightScanTape leftRev remaining := by
  cases remaining <;> rfl

private theorem initializerAppendRightLastTapeAtCells_of_bits
    (leftRev : Word Bool) (b0 b1 b2 b3 : Bool) :
    initializerAppendRightLastTapeAtCells
        (leftRev.map some) b0 b1 b2 b3 =
      initializerAppendRightLastTape leftRev b0 b1 b2 b3 := by
  simp [initializerAppendRightLastTapeAtCells,
    initializerAppendRightLastTape]

private theorem initializerAppendFixedFourBitsLastDescription_step_scan_nonempty_atCells
    (b0 b1 b2 b3 : Bool)
    (leftRev : List (Option Bool)) (b : Bool) (rest : Word Bool) :
    (InitializerAppendFixedFourBitsLastDescription b0 b1 b2 b3).stepConfig
        { state := 0
          tape := initializerAppendScanTapeAtCells leftRev (b :: rest) } =
      some
        { state := 0
          tape := initializerAppendScanTapeAtCells
            (some b :: leftRev) rest } := by
  cases b <;>
    cases rest <;>
      simp [InitializerAppendFixedFourBitsLastDescription,
        initializerAppendScanTapeAtCells,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition, MachineDescription.Matches,
        MachineDescription.transition, Tape.read, Tape.write,
        Tape.move, Tape.moveRight]

private theorem initializerAppendFixedFourBitsLastDescription_run_scan_atCells
    (b0 b1 b2 b3 : Bool)
    (leftRev : List (Option Bool)) (remaining : Word Bool) :
    (InitializerAppendFixedFourBitsLastDescription b0 b1 b2 b3).runConfig
        remaining.length
        { state := 0
          tape := initializerAppendScanTapeAtCells leftRev remaining } =
      { state := 0
        tape :=
          initializerAppendScanTapeAtCells
            (List.append (remaining.reverse.map some) leftRev) [] } := by
  induction remaining generalizing leftRev with
  | nil =>
      simp [MachineDescription.runConfig]
  | cons b rest ih =>
      simp [MachineDescription.runConfig,
        initializerAppendFixedFourBitsLastDescription_step_scan_nonempty_atCells,
        ih, List.append_assoc]

private theorem initializerAppendFixedFourBitsLastDescription_run_write_atCells
    (b0 b1 b2 b3 : Bool) (leftRev : List (Option Bool)) :
    (InitializerAppendFixedFourBitsLastDescription b0 b1 b2 b3).runConfig 5
        { state := 0
          tape := initializerAppendScanTapeAtCells leftRev [] } =
      { state := 5
        tape :=
          initializerAppendRightLastTapeAtCells
            leftRev b0 b1 b2 b3 } := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    simp [InitializerAppendFixedFourBitsLastDescription,
      initializerAppendScanTapeAtCells,
      initializerAppendRightLastTapeAtCells,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft, Tape.moveRight]

private theorem initializerAppendFixedFourBitsLastDescription_run_from_scan_atCells
    (b0 b1 b2 b3 : Bool)
    (leftRev : List (Option Bool)) (remaining : Word Bool) :
    (InitializerAppendFixedFourBitsLastDescription b0 b1 b2 b3).runConfig
        (remaining.length + 5)
        { state := 0
          tape := initializerAppendScanTapeAtCells leftRev remaining } =
      { state := 5
        tape :=
          initializerAppendRightLastTapeAtCells
            (List.append (remaining.reverse.map some) leftRev)
            b0 b1 b2 b3 } := by
  rw [MachineDescription.runConfig_add]
  rw [initializerAppendFixedFourBitsLastDescription_run_scan_atCells]
  exact initializerAppendFixedFourBitsLastDescription_run_write_atCells
    b0 b1 b2 b3 _

private theorem initializerWriteMarkedTransitionPrefixDescription_handoff_to_append
    (b : Bool) (rest : Word Bool) :
    Tape.move Direction.right
        (initializerTapeAtCells [some false]
          (List.append [none, some false, some true]
            (some b :: rest.map some))) =
      initializerAppendScanTapeAtCells
        [none, some false] (false :: true :: b :: rest) := by
  cases b <;>
    cases rest <;>
      simp [initializerTapeAtCells, initializerAppendScanTapeAtCells,
        Tape.move, Tape.moveRight]

private def InitializerAppendCodeSymbolLastDescription
    (symbol : MachineCodeSymbol) : MachineDescription :=
  match MachineDescription.encodeCodeSymbolAsInput symbol with
  | [b0, b1, b2, b3] =>
      InitializerAppendFixedFourBitsLastDescription b0 b1 b2 b3
  | _ => MachineDescription.ExactIdentityDescription

private def initializerAppendCodeSymbolLastTape
    (leftRev : Word Bool) (symbol : MachineCodeSymbol) : Tape Bool :=
  match MachineDescription.encodeCodeSymbolAsInput symbol with
  | [b0, b1, b2, b3] =>
      initializerAppendRightLastTape leftRev b0 b1 b2 b3
  | _ => Tape.input leftRev.reverse

private theorem initializerAppendCodeSymbolLastDescription_start
    (symbol : MachineCodeSymbol) :
    (InitializerAppendCodeSymbolLastDescription symbol).start = 0 := by
  cases symbol <;> rfl

private theorem initializerAppendCodeSymbolLastDescription_halt
    (symbol : MachineCodeSymbol) :
    (InitializerAppendCodeSymbolLastDescription symbol).halt = 5 := by
  cases symbol <;> rfl

private theorem initializerAppendCodeSymbolLastDescription_wellFormed
    (symbol : MachineCodeSymbol) :
    (InitializerAppendCodeSymbolLastDescription symbol).WellFormed := by
  cases symbol <;>
    exact initializerAppendFixedFourBitsLastDescription_wellFormed _ _ _ _

private theorem initializerAppendCodeSymbolLastDescription_haltTransitionFree
    (symbol : MachineCodeSymbol) :
    (InitializerAppendCodeSymbolLastDescription
      symbol).HaltTransitionFree := by
  cases symbol <;>
    exact
      initializerAppendFixedFourBitsLastDescription_haltTransitionFree
        _ _ _ _

private theorem initializerAppendCodeSymbolLastDescription_run_from_scan
    (symbol : MachineCodeSymbol)
    (leftRev remaining : Word Bool) :
    (InitializerAppendCodeSymbolLastDescription symbol).runConfig
        (remaining.length + 5)
        { state := 0
          tape := MachineDescription.appendRightScanTape leftRev remaining } =
      { state := 5
        tape :=
          initializerAppendCodeSymbolLastTape
            (List.append remaining.reverse leftRev) symbol } := by
  cases symbol <;>
    rw [MachineDescription.runConfig_add] <;>
    simp [InitializerAppendCodeSymbolLastDescription,
      initializerAppendCodeSymbolLastTape,
      MachineDescription.encodeCodeSymbolAsInput,
      initializerAppendFixedFourBitsLastDescription_run_scan,
      initializerAppendFixedFourBitsLastDescription_run_write]

private theorem initializerAppendCodeSymbolLastDescription_run_halt
    (symbol : MachineCodeSymbol) (w : Word Bool) :
    (InitializerAppendCodeSymbolLastDescription symbol).runConfig
        (w.length + 5)
        ((InitializerAppendCodeSymbolLastDescription symbol).initial w) =
      { state := 5
        tape := initializerAppendCodeSymbolLastTape w.reverse symbol } := by
  cases symbol <;>
    simpa [InitializerAppendCodeSymbolLastDescription,
      initializerAppendCodeSymbolLastTape,
      MachineDescription.encodeCodeSymbolAsInput] using
      initializerAppendFixedFourBitsLastDescription_run_halt
        _ _ _ _ w

private theorem initializerAppendCodeSymbolLastTape_move_right
    (leftRev : Word Bool) (symbol : MachineCodeSymbol) :
    Tape.move Direction.right
        (initializerAppendCodeSymbolLastTape leftRev symbol) =
      MachineDescription.appendRightScanTape
        (List.append
          (MachineDescription.encodeCodeSymbolAsInput symbol).reverse
          leftRev) [] := by
  cases symbol <;>
    simp [initializerAppendCodeSymbolLastTape,
      initializerAppendRightLastTape,
      MachineDescription.encodeCodeSymbolAsInput,
      MachineDescription.appendRightScanTape, Tape.move, Tape.moveRight]

private theorem initializerAppendCodeSymbolLastDescription_haltsWithTape
    (symbol : MachineCodeSymbol) (w : Word Bool) :
    (InitializerAppendCodeSymbolLastDescription symbol).HaltsWithTape
        w (initializerAppendCodeSymbolLastTape w.reverse symbol) := by
  exists w.length + 5
  constructor
  · rw [initializerAppendCodeSymbolLastDescription_run_halt]
    cases symbol <;> rfl
  · rw [initializerAppendCodeSymbolLastDescription_run_halt]

private def InitializerAppendCodeWordLastDescription :
    Word MachineCodeSymbol -> MachineDescription
  | [] => MachineDescription.ExactIdentityDescription
  | symbol :: [] => InitializerAppendCodeSymbolLastDescription symbol
  | symbol :: next :: rest =>
      MachineDescription.seqSubroutine
        (InitializerAppendCodeSymbolLastDescription symbol)
        (InitializerAppendCodeWordLastDescription (next :: rest))
        Direction.right

private def initializerAppendCodeWordLastTape
    (leftRev : Word Bool) :
    Word MachineCodeSymbol -> Tape Bool
  | [] => MachineDescription.appendRightScanTape leftRev []
  | symbol :: [] => initializerAppendCodeSymbolLastTape leftRev symbol
  | symbol :: next :: rest =>
      initializerAppendCodeWordLastTape
        (List.append
          (MachineDescription.encodeCodeSymbolAsInput symbol).reverse
          leftRev)
        (next :: rest)

private theorem initializerAppendCodeSymbolLastDescription_subroutineReady
    (symbol : MachineCodeSymbol) :
    (InitializerAppendCodeSymbolLastDescription symbol).SubroutineReady :=
  ⟨initializerAppendCodeSymbolLastDescription_wellFormed symbol,
    initializerAppendCodeSymbolLastDescription_haltTransitionFree symbol⟩

private theorem initializerAppendCodeWordLastDescription_subroutineReady :
    forall code : Word MachineCodeSymbol,
      code ≠ [] ->
        (InitializerAppendCodeWordLastDescription code).SubroutineReady
  | [], h => False.elim (h rfl)
  | symbol :: [], _ =>
      initializerAppendCodeSymbolLastDescription_subroutineReady symbol
  | symbol :: next :: rest, _ =>
      MachineDescription.seqSubroutine_subroutineReady
        (initializerAppendCodeSymbolLastDescription_subroutineReady symbol)
        (initializerAppendCodeWordLastDescription_subroutineReady
          (next :: rest) (by intro h; cases h))

private theorem initializerAppendCodeWordLastDescription_run_from_scan :
    forall code : Word MachineCodeSymbol,
      code ≠ [] ->
        forall leftRev remaining : Word Bool,
          exists n : Nat,
            (InitializerAppendCodeWordLastDescription code).runConfig n
                { state := (InitializerAppendCodeWordLastDescription code).start
                  tape :=
                    MachineDescription.appendRightScanTape
                      leftRev remaining } =
              { state := (InitializerAppendCodeWordLastDescription code).halt
                tape :=
                  initializerAppendCodeWordLastTape
                    (List.append remaining.reverse leftRev) code }
  | [], h => False.elim (h rfl)
  | symbol :: [], _ => by
      intro leftRev remaining
      refine ⟨remaining.length + 5, ?_⟩
      simpa [InitializerAppendCodeWordLastDescription,
        initializerAppendCodeWordLastTape,
        initializerAppendCodeSymbolLastDescription_start,
        initializerAppendCodeSymbolLastDescription_halt] using
        initializerAppendCodeSymbolLastDescription_run_from_scan
          symbol leftRev remaining
  | symbol :: next :: rest, _ => by
      intro leftRev remaining
      let A := InitializerAppendCodeSymbolLastDescription symbol
      let B := InitializerAppendCodeWordLastDescription (next :: rest)
      let Tmid :=
        initializerAppendCodeSymbolLastTape
          (List.append remaining.reverse leftRev) symbol
      let leftAfterSymbol :=
        List.append
          (MachineDescription.encodeCodeSymbolAsInput symbol).reverse
          (List.append remaining.reverse leftRev)
      have hAready : A.SubroutineReady := by
        exact initializerAppendCodeSymbolLastDescription_subroutineReady symbol
      have hBready : B.SubroutineReady := by
        exact
          initializerAppendCodeWordLastDescription_subroutineReady
            (next :: rest) (by intro h; cases h)
      have hArun :
          A.runConfig (remaining.length + 5)
              { state := A.start
                tape :=
                  MachineDescription.appendRightScanTape leftRev remaining } =
            { state := A.halt, tape := Tmid } := by
        simpa [A, Tmid,
          initializerAppendCodeSymbolLastDescription_start,
          initializerAppendCodeSymbolLastDescription_halt] using
          initializerAppendCodeSymbolLastDescription_run_from_scan
            symbol leftRev remaining
      have hBReach :
          exists nB : Nat,
            B.runConfig nB
                { state := B.start
                  tape := Tape.move Direction.right Tmid } =
              { state := B.halt
                tape :=
                  initializerAppendCodeWordLastTape
                    leftAfterSymbol (next :: rest) } := by
        rcases
            initializerAppendCodeWordLastDescription_run_from_scan
              (next :: rest) (by intro h; cases h)
              leftAfterSymbol ([] : Word Bool) with
          ⟨nB, hB⟩
        refine ⟨nB, ?_⟩
        simpa [B, Tmid, leftAfterSymbol,
          initializerAppendCodeSymbolLastTape_move_right] using hB
      rcases
          MachineDescription.seqSubroutine_reaches_of_runConfig_eq
            (A := A) (B := B) (handoffMove := Direction.right)
            hAready hBready hArun hBReach with
        ⟨n, hn⟩
      refine ⟨n, ?_⟩
      simpa [InitializerAppendCodeWordLastDescription,
        initializerAppendCodeWordLastTape, A, B, Tmid, leftAfterSymbol] using hn

private theorem initializerAppendCodeWordLastDescription_run_halt
    (code : Word MachineCodeSymbol) (hcode : code ≠ [])
    (w : Word Bool) :
    exists n : Nat,
      (InitializerAppendCodeWordLastDescription code).runConfig n
          ((InitializerAppendCodeWordLastDescription code).initial w) =
        { state := (InitializerAppendCodeWordLastDescription code).halt
          tape := initializerAppendCodeWordLastTape w.reverse code } := by
  rcases
      initializerAppendCodeWordLastDescription_run_from_scan
        code hcode ([] : Word Bool) w with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [MachineDescription.initial,
    MachineDescription.appendRightScanTape_nil_eq_input] using hn

private theorem initializerAppendCodeWordLastDescription_haltsWithTape
    (code : Word MachineCodeSymbol) (hcode : code ≠ [])
    (w : Word Bool) :
    (InitializerAppendCodeWordLastDescription code).HaltsWithTape
      w (initializerAppendCodeWordLastTape w.reverse code) := by
  rcases initializerAppendCodeWordLastDescription_run_halt
      code hcode w with
    ⟨n, hn⟩
  exact ⟨n, by
    constructor
    · simpa [MachineDescription.HaltsWithTapeIn] using
        congrArg MachineDescription.Configuration.state hn
    · simpa [MachineDescription.HaltsWithTapeIn] using
        congrArg MachineDescription.Configuration.tape hn⟩

private def initializerAppendCodeSymbolLastTapeAtCells
    (leftRev : List (Option Bool))
    (symbol : MachineCodeSymbol) : Tape Bool :=
  match MachineDescription.encodeCodeSymbolAsInput symbol with
  | [b0, b1, b2, b3] =>
      initializerAppendRightLastTapeAtCells leftRev b0 b1 b2 b3
  | _ => initializerAppendScanTapeAtCells leftRev []

private theorem initializerAppendCodeSymbolLastTapeAtCells_of_bits
    (leftRev : Word Bool) (symbol : MachineCodeSymbol) :
    initializerAppendCodeSymbolLastTapeAtCells
        (leftRev.map some) symbol =
      initializerAppendCodeSymbolLastTape leftRev symbol := by
  cases symbol <;>
    simp [initializerAppendCodeSymbolLastTapeAtCells,
      initializerAppendCodeSymbolLastTape,
      initializerAppendRightLastTapeAtCells_of_bits,
      MachineDescription.encodeCodeSymbolAsInput]

private theorem initializerAppendCodeSymbolLastDescription_run_from_scan_atCells
    (symbol : MachineCodeSymbol)
    (leftRev : List (Option Bool)) (remaining : Word Bool) :
    (InitializerAppendCodeSymbolLastDescription symbol).runConfig
        (remaining.length + 5)
        { state := 0
          tape := initializerAppendScanTapeAtCells leftRev remaining } =
      { state := 5
        tape :=
          initializerAppendCodeSymbolLastTapeAtCells
            (List.append (remaining.reverse.map some) leftRev) symbol } := by
  cases symbol <;>
    simpa [InitializerAppendCodeSymbolLastDescription,
      initializerAppendCodeSymbolLastTapeAtCells,
      MachineDescription.encodeCodeSymbolAsInput] using
      initializerAppendFixedFourBitsLastDescription_run_from_scan_atCells
        _ _ _ _ leftRev remaining

private theorem initializerAppendCodeSymbolLastTapeAtCells_move_right
    (leftRev : List (Option Bool)) (symbol : MachineCodeSymbol) :
    Tape.move Direction.right
        (initializerAppendCodeSymbolLastTapeAtCells leftRev symbol) =
      initializerAppendScanTapeAtCells
        (List.append
          ((MachineDescription.encodeCodeSymbolAsInput symbol).reverse.map some)
          leftRev) [] := by
  cases symbol <;>
    simp [initializerAppendCodeSymbolLastTapeAtCells,
      initializerAppendRightLastTapeAtCells,
      initializerAppendScanTapeAtCells,
      MachineDescription.encodeCodeSymbolAsInput,
      Tape.move, Tape.moveRight]

private def initializerAppendCodeWordLastTapeAtCells
    (leftRev : List (Option Bool)) :
    Word MachineCodeSymbol -> Tape Bool
  | [] => initializerAppendScanTapeAtCells leftRev []
  | symbol :: [] => initializerAppendCodeSymbolLastTapeAtCells leftRev symbol
  | symbol :: next :: rest =>
      initializerAppendCodeWordLastTapeAtCells
        (List.append
          ((MachineDescription.encodeCodeSymbolAsInput symbol).reverse.map some)
          leftRev)
        (next :: rest)

private theorem initializerAppendCodeWordLastTapeAtCells_of_bits :
    forall code : Word MachineCodeSymbol,
    forall leftRev : Word Bool,
      initializerAppendCodeWordLastTapeAtCells
          (leftRev.map some) code =
        initializerAppendCodeWordLastTape leftRev code
  | [], leftRev => by
      simp [initializerAppendCodeWordLastTapeAtCells,
        initializerAppendCodeWordLastTape,
        initializerAppendScanTapeAtCells_of_bits]
  | symbol :: [], leftRev => by
      simp [initializerAppendCodeWordLastTapeAtCells,
        initializerAppendCodeWordLastTape,
        initializerAppendCodeSymbolLastTapeAtCells_of_bits]
  | symbol :: next :: rest, leftRev => by
      change
        initializerAppendCodeWordLastTapeAtCells
            (List.append
              ((MachineDescription.encodeCodeSymbolAsInput symbol).reverse.map some)
              (leftRev.map some))
            (next :: rest) =
          initializerAppendCodeWordLastTape
            (List.append
              (MachineDescription.encodeCodeSymbolAsInput symbol).reverse
              leftRev)
            (next :: rest)
      have hmap :
          List.append
              ((MachineDescription.encodeCodeSymbolAsInput symbol).reverse.map some)
              (leftRev.map some) =
            (List.append
              (MachineDescription.encodeCodeSymbolAsInput symbol).reverse
              leftRev).map some := by
        simp
      rw [hmap]
      exact
        initializerAppendCodeWordLastTapeAtCells_of_bits
          (next :: rest)
          (List.append
            (MachineDescription.encodeCodeSymbolAsInput symbol).reverse
            leftRev)

private theorem initializerAppendCodeWordLastDescription_run_from_scan_atCells :
    forall code : Word MachineCodeSymbol,
      code ≠ [] ->
        forall leftRev : List (Option Bool),
        forall remaining : Word Bool,
          exists n : Nat,
            (InitializerAppendCodeWordLastDescription code).runConfig n
                { state := (InitializerAppendCodeWordLastDescription code).start
                  tape :=
                    initializerAppendScanTapeAtCells
                      leftRev remaining } =
              { state := (InitializerAppendCodeWordLastDescription code).halt
                tape :=
                  initializerAppendCodeWordLastTapeAtCells
                    (List.append (remaining.reverse.map some) leftRev) code }
  | [], h => False.elim (h rfl)
  | symbol :: [], _ => by
      intro leftRev remaining
      refine ⟨remaining.length + 5, ?_⟩
      simpa [InitializerAppendCodeWordLastDescription,
        initializerAppendCodeWordLastTapeAtCells,
        initializerAppendCodeSymbolLastDescription_start,
        initializerAppendCodeSymbolLastDescription_halt] using
        initializerAppendCodeSymbolLastDescription_run_from_scan_atCells
          symbol leftRev remaining
  | symbol :: next :: rest, _ => by
      intro leftRev remaining
      let A := InitializerAppendCodeSymbolLastDescription symbol
      let B := InitializerAppendCodeWordLastDescription (next :: rest)
      let Tmid :=
        initializerAppendCodeSymbolLastTapeAtCells
          (List.append (remaining.reverse.map some) leftRev) symbol
      let leftAfterSymbol :=
        List.append
          ((MachineDescription.encodeCodeSymbolAsInput symbol).reverse.map some)
          (List.append (remaining.reverse.map some) leftRev)
      have hAready : A.SubroutineReady := by
        exact initializerAppendCodeSymbolLastDescription_subroutineReady symbol
      have hBready : B.SubroutineReady := by
        exact
          initializerAppendCodeWordLastDescription_subroutineReady
            (next :: rest) (by intro h; cases h)
      have hArun :
          A.runConfig (remaining.length + 5)
              { state := A.start
                tape :=
                  initializerAppendScanTapeAtCells leftRev remaining } =
            { state := A.halt, tape := Tmid } := by
        simpa [A, Tmid,
          initializerAppendCodeSymbolLastDescription_start,
          initializerAppendCodeSymbolLastDescription_halt] using
          initializerAppendCodeSymbolLastDescription_run_from_scan_atCells
            symbol leftRev remaining
      have hBReach :
          exists nB : Nat,
            B.runConfig nB
                { state := B.start
                  tape := Tape.move Direction.right Tmid } =
              { state := B.halt
                tape :=
                  initializerAppendCodeWordLastTapeAtCells
                    leftAfterSymbol (next :: rest) } := by
        rcases
            initializerAppendCodeWordLastDescription_run_from_scan_atCells
              (next :: rest) (by intro h; cases h)
              leftAfterSymbol ([] : Word Bool) with
          ⟨nB, hB⟩
        refine ⟨nB, ?_⟩
        simpa [B, Tmid, leftAfterSymbol,
          initializerAppendCodeSymbolLastTapeAtCells_move_right] using hB
      rcases
          MachineDescription.seqSubroutine_reaches_of_runConfig_eq
            (A := A) (B := B) (handoffMove := Direction.right)
            hAready hBready hArun hBReach with
        ⟨n, hn⟩
      refine ⟨n, ?_⟩
      simpa [InitializerAppendCodeWordLastDescription,
        initializerAppendCodeWordLastTapeAtCells, A, B, Tmid,
        leftAfterSymbol] using hn

private def InitializerMarkedPrefixThenAppendCodeWordLastDescription
    (code : Word MachineCodeSymbol) : MachineDescription :=
  MachineDescription.seqSubroutine
    InitializerWriteMarkedTransitionPrefixDescription
    (InitializerAppendCodeWordLastDescription code)
    Direction.right

private theorem
    initializerMarkedPrefixThenAppendCodeWordLastDescription_subroutineReady
    (code : Word MachineCodeSymbol) (hcode : code ≠ []) :
    (InitializerMarkedPrefixThenAppendCodeWordLastDescription
      code).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    initializerWriteMarkedTransitionPrefixDescription_subroutineReady
    (initializerAppendCodeWordLastDescription_subroutineReady code hcode)

private theorem initializerMarkedPrefixThenAppendCodeWordLastDescription_run
    (code : Word MachineCodeSymbol) (hcode : code ≠ [])
    (b : Bool) (rest : Word Bool) :
    exists n : Nat,
      (InitializerMarkedPrefixThenAppendCodeWordLastDescription code).runConfig n
          ((InitializerMarkedPrefixThenAppendCodeWordLastDescription
            code).initial (b :: rest)) =
        { state :=
            (InitializerMarkedPrefixThenAppendCodeWordLastDescription code).halt
          tape :=
            initializerAppendCodeWordLastTapeAtCells
              (List.append
                ((false :: true :: b :: rest).reverse.map some)
                [none, some false])
              code } := by
  let A := InitializerWriteMarkedTransitionPrefixDescription
  let B := InitializerAppendCodeWordLastDescription code
  let Tmid :=
    initializerTapeAtCells [some false]
      (List.append [none, some false, some true]
        (some b :: rest.map some))
  have hAready : A.SubroutineReady := by
    exact initializerWriteMarkedTransitionPrefixDescription_subroutineReady
  have hBready : B.SubroutineReady := by
    exact initializerAppendCodeWordLastDescription_subroutineReady code hcode
  have hArun :
      A.runConfig 5
          { state := A.start
            tape := Tape.input (b :: rest) } =
        { state := A.halt, tape := Tmid } := by
    simpa [A, Tmid, MachineDescription.initial,
      initializerConfig, initializerTapeAtCells, Tape.input] using
      initializerWriteMarkedTransitionPrefixDescription_run
        b (rest.map some)
  have hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start
              tape := Tape.move Direction.right Tmid } =
          { state := B.halt
            tape :=
              initializerAppendCodeWordLastTapeAtCells
                (List.append
                  ((false :: true :: b :: rest).reverse.map some)
                  [none, some false])
                code } := by
    rcases
        initializerAppendCodeWordLastDescription_run_from_scan_atCells
          code hcode [none, some false] (false :: true :: b :: rest) with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    simpa [B, Tmid,
      initializerWriteMarkedTransitionPrefixDescription_handoff_to_append] using hB
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.right)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [InitializerMarkedPrefixThenAppendCodeWordLastDescription,
    MachineDescription.initial, A, B] using hn

private theorem initializer_encodeNat_ne_nil (n : Nat) :
    MachineDescription.encodeNat n ≠ [] := by
  cases n <;> simp [MachineDescription.encodeNat]

private def InitializerAppendNatLastDescription
    (n : Nat) : MachineDescription :=
  InitializerAppendCodeWordLastDescription
    (MachineDescription.encodeNat n)

private def initializerAppendNatLastTape
    (leftRev : Word Bool) (n : Nat) : Tape Bool :=
  initializerAppendCodeWordLastTape leftRev
    (MachineDescription.encodeNat n)

private theorem initializerAppendNatLastDescription_subroutineReady
    (n : Nat) :
    (InitializerAppendNatLastDescription n).SubroutineReady :=
  initializerAppendCodeWordLastDescription_subroutineReady
    (MachineDescription.encodeNat n)
    (initializer_encodeNat_ne_nil n)

private theorem initializerAppendNatLastDescription_run_from_scan
    (n : Nat) (leftRev remaining : Word Bool) :
    exists steps : Nat,
      (InitializerAppendNatLastDescription n).runConfig steps
          { state := (InitializerAppendNatLastDescription n).start
            tape := MachineDescription.appendRightScanTape leftRev remaining } =
        { state := (InitializerAppendNatLastDescription n).halt
          tape :=
            initializerAppendNatLastTape
              (List.append remaining.reverse leftRev) n } := by
  simpa [InitializerAppendNatLastDescription,
    initializerAppendNatLastTape] using
    initializerAppendCodeWordLastDescription_run_from_scan
      (MachineDescription.encodeNat n)
      (initializer_encodeNat_ne_nil n)
      leftRev remaining

private theorem initializerAppendNatLastDescription_haltsWithTape
    (n : Nat) (w : Word Bool) :
    (InitializerAppendNatLastDescription n).HaltsWithTape
      w (initializerAppendNatLastTape w.reverse n) := by
  simpa [InitializerAppendNatLastDescription,
    initializerAppendNatLastTape] using
    initializerAppendCodeWordLastDescription_haltsWithTape
      (MachineDescription.encodeNat n)
      (initializer_encodeNat_ne_nil n)
      w

private def InitializerMarkedPrefixThenAppendNatLastDescription
    (n : Nat) : MachineDescription :=
  InitializerMarkedPrefixThenAppendCodeWordLastDescription
    (MachineDescription.encodeNat n)

private theorem
    initializerMarkedPrefixThenAppendNatLastDescription_subroutineReady
    (n : Nat) :
    (InitializerMarkedPrefixThenAppendNatLastDescription
      n).SubroutineReady :=
  initializerMarkedPrefixThenAppendCodeWordLastDescription_subroutineReady
    (MachineDescription.encodeNat n)
    (initializer_encodeNat_ne_nil n)

private theorem initializerMarkedPrefixThenAppendNatLastDescription_run
    (n : Nat) (b : Bool) (rest : Word Bool) :
    exists steps : Nat,
      (InitializerMarkedPrefixThenAppendNatLastDescription n).runConfig steps
          ((InitializerMarkedPrefixThenAppendNatLastDescription
            n).initial (b :: rest)) =
        { state :=
            (InitializerMarkedPrefixThenAppendNatLastDescription n).halt
          tape :=
            initializerAppendCodeWordLastTapeAtCells
              (List.append
                ((false :: true :: b :: rest).reverse.map some)
                [none, some false])
              (MachineDescription.encodeNat n) } := by
  simpa [InitializerMarkedPrefixThenAppendNatLastDescription] using
    initializerMarkedPrefixThenAppendCodeWordLastDescription_run
      (MachineDescription.encodeNat n)
      (initializer_encodeNat_ne_nil n)
      b rest

private def InitializerMarkTransitionSecondBitDescription :
    MachineDescription where
  stateCount := 3
  start := 0
  halt := 2
  transitions :=
    [ MachineDescription.transition
        0 (some false) none Direction.left 1
    , MachineDescription.transition
        1 (some false) (some false) Direction.right 2
    ]

private theorem initializerMarkTransitionSecondBitDescription_wellFormed :
    InitializerMarkTransitionSecondBitDescription.WellFormed := by
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · intro t ht
    exact transition_wellFormed_of_all
      (l := InitializerMarkTransitionSecondBitDescription.transitions)
      (stateCount :=
        InitializerMarkTransitionSecondBitDescription.stateCount)
      (by
        native_decide) t ht
  · intro t u ht hu hkey
    exact transition_deterministic_of_all
      (l := InitializerMarkTransitionSecondBitDescription.transitions)
      (by
        native_decide) t u ht hu hkey

private theorem initializerMarkTransitionSecondBitDescription_haltTransitionFree :
    InitializerMarkTransitionSecondBitDescription.HaltTransitionFree := by
  intro t ht
  exact transition_notFrom_of_all
    (l := InitializerMarkTransitionSecondBitDescription.transitions)
    (state := InitializerMarkTransitionSecondBitDescription.halt)
    (by
      native_decide) t ht

private theorem initializerMarkTransitionSecondBitDescription_subroutineReady :
    InitializerMarkTransitionSecondBitDescription.SubroutineReady :=
  ⟨initializerMarkTransitionSecondBitDescription_wellFormed,
    initializerMarkTransitionSecondBitDescription_haltTransitionFree⟩

private theorem initializerMarkTransitionSecondBitDescription_run
    (payload : Word Bool) :
    InitializerMarkTransitionSecondBitDescription.runConfig 2
        (initializerConfig 0 [some false]
          (some false ::
            ((List.append [false, true] payload).map some))) =
      { state := InitializerMarkTransitionSecondBitDescription.halt
        tape :=
          initializerTapeAtCells [some false]
            (none ::
              ((List.append [false, true] payload).map some)) } := by
  cases payload <;>
    simp [InitializerMarkTransitionSecondBitDescription,
      initializerConfig, initializerTapeAtCells,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft, Tape.moveRight]

private def InitializerTransitionPrefixedThenAppendCodeWordLastDescription
    (code : Word MachineCodeSymbol) : MachineDescription :=
  MachineDescription.seqSubroutine
    InitializerMarkTransitionSecondBitDescription
    (InitializerAppendCodeWordLastDescription code)
    Direction.right

private theorem
    initializerTransitionPrefixedThenAppendCodeWordLastDescription_subroutineReady
    (code : Word MachineCodeSymbol) (hcode : code ≠ []) :
    (InitializerTransitionPrefixedThenAppendCodeWordLastDescription
      code).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    initializerMarkTransitionSecondBitDescription_subroutineReady
    (initializerAppendCodeWordLastDescription_subroutineReady code hcode)

private theorem
    initializerTransitionPrefixedThenAppendCodeWordLastDescription_run
    (code : Word MachineCodeSymbol) (hcode : code ≠ [])
    (payload : Word Bool) :
    exists steps : Nat,
      (InitializerTransitionPrefixedThenAppendCodeWordLastDescription
        code).runConfig steps
          { state :=
              (InitializerTransitionPrefixedThenAppendCodeWordLastDescription
                code).start
            tape :=
              initializerTapeAtCells [some false]
                (some false ::
                  ((List.append [false, true] payload).map some)) } =
        { state :=
            (InitializerTransitionPrefixedThenAppendCodeWordLastDescription
              code).halt
          tape :=
            initializerAppendCodeWordLastTapeAtCells
              (List.append
                ((false :: true :: payload).reverse.map some)
                [none, some false])
              code } := by
  let A := InitializerMarkTransitionSecondBitDescription
  let B := InitializerAppendCodeWordLastDescription code
  let Tmid :=
    initializerTapeAtCells [some false]
      (none ::
        ((List.append [false, true] payload).map some))
  have hAready : A.SubroutineReady := by
    exact initializerMarkTransitionSecondBitDescription_subroutineReady
  have hBready : B.SubroutineReady := by
    exact initializerAppendCodeWordLastDescription_subroutineReady code hcode
  have hArun :
      A.runConfig 2
          { state := A.start
            tape :=
              initializerTapeAtCells [some false]
                (some false ::
                  ((List.append [false, true] payload).map some)) } =
        { state := A.halt, tape := Tmid } := by
    simpa [A, Tmid, initializerConfig] using
      initializerMarkTransitionSecondBitDescription_run payload
  have hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start
              tape := Tape.move Direction.right Tmid } =
          { state := B.halt
            tape :=
              initializerAppendCodeWordLastTapeAtCells
                (List.append
                  ((false :: true :: payload).reverse.map some)
                  [none, some false])
                code } := by
    rcases
        initializerAppendCodeWordLastDescription_run_from_scan_atCells
          code hcode [none, some false] (false :: true :: payload) with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    simpa [B, Tmid, initializerTapeAtCells,
      initializerAppendScanTapeAtCells, Tape.move, Tape.moveRight] using hB
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.right)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [InitializerTransitionPrefixedThenAppendCodeWordLastDescription,
    A, B] using hn

private def InitializerReturnToTransitionMarkerDescription :
    MachineDescription where
  stateCount := 3
  start := 0
  halt := 2
  transitions :=
    [ MachineDescription.transition
        0 (some false) (some false) Direction.left 0
    , MachineDescription.transition
        0 (some true) (some true) Direction.left 0
    , MachineDescription.transition
        0 none (some false) Direction.left 1
    , MachineDescription.transition
        1 (some false) (some false) Direction.right 2
    , MachineDescription.transition
        1 (some true) (some true) Direction.right 2
    ]

private theorem initializerReturnToTransitionMarkerDescription_wellFormed :
    InitializerReturnToTransitionMarkerDescription.WellFormed := by
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · intro t ht
    exact transition_wellFormed_of_all
      (l := InitializerReturnToTransitionMarkerDescription.transitions)
      (stateCount :=
        InitializerReturnToTransitionMarkerDescription.stateCount)
      (by
        native_decide) t ht
  · intro t u ht hu hkey
    exact transition_deterministic_of_all
      (l := InitializerReturnToTransitionMarkerDescription.transitions)
      (by
        native_decide) t u ht hu hkey

private theorem initializerReturnToTransitionMarkerDescription_haltTransitionFree :
    InitializerReturnToTransitionMarkerDescription.HaltTransitionFree := by
  intro t ht
  exact transition_notFrom_of_all
    (l := InitializerReturnToTransitionMarkerDescription.transitions)
    (state := InitializerReturnToTransitionMarkerDescription.halt)
    (by
      native_decide) t ht

private theorem initializerReturnToTransitionMarkerDescription_subroutineReady :
    InitializerReturnToTransitionMarkerDescription.SubroutineReady :=
  ⟨initializerReturnToTransitionMarkerDescription_wellFormed,
    initializerReturnToTransitionMarkerDescription_haltTransitionFree⟩

private theorem initializerReturnToTransitionMarkerDescription_step_scan
    (preRev : Word Bool) (leftBit current : Bool)
    (right : List (Option Bool)) :
    InitializerReturnToTransitionMarkerDescription.stepConfig
        (initializerConfig 0
          (List.append
            (some leftBit :: preRev.map some) [none, some false])
          (some current :: right)) =
      some
        (initializerConfig 0
          (List.append (preRev.map some) [none, some false])
          (some leftBit :: some current :: right)) := by
  cases leftBit <;> cases current <;>
    simp [InitializerReturnToTransitionMarkerDescription,
      initializerConfig, initializerTapeAtCells,
      MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft]

private theorem initializerReturnToTransitionMarkerDescription_run
    (preRev : Word Bool) (current : Bool)
    (right : List (Option Bool)) :
    InitializerReturnToTransitionMarkerDescription.runConfig
        (preRev.length + 3)
        (initializerConfig 0
          (List.append (preRev.map some) [none, some false])
          (some current :: right)) =
      initializerConfig 2 [some false]
        (some false ::
          List.append (preRev.reverse.map some)
            (some current :: right)) := by
  induction preRev generalizing current right with
  | nil =>
      cases current <;>
        simp [InitializerReturnToTransitionMarkerDescription,
          initializerConfig, initializerTapeAtCells,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read, Tape.write,
          Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons b rest ih =>
      simp only [List.map_cons, List.length_cons, List.reverse_cons]
      rw [show Nat.succ rest.length + 3 = (rest.length + 3) + 1 by omega]
      rw [MachineDescription.runConfig]
      rw [initializerReturnToTransitionMarkerDescription_step_scan]
      simpa [List.append_assoc] using ih b (some current :: right)

private theorem
    initializerReturnToTransitionMarkerDescription_run_after_append_four_atCells
    (pre : Word Bool) (b0 b1 b2 b3 : Bool) :
    InitializerReturnToTransitionMarkerDescription.runConfig
        (pre.length + 5)
        { state := InitializerReturnToTransitionMarkerDescription.start
          tape :=
            Tape.move Direction.left
              (initializerAppendRightLastTapeAtCells
                (List.append (pre.reverse.map some)
                  [none, some false]) b0 b1 b2 b3) } =
      { state := InitializerReturnToTransitionMarkerDescription.halt
        tape :=
          initializerTapeAtCells [some false]
            (some false ::
              ((List.append pre [b0, b1, b2, b3]).map some)) } := by
  simpa [initializerAppendRightLastTapeAtCells, initializerTapeAtCells,
    Tape.move, Tape.moveLeft, List.append_assoc] using
    initializerReturnToTransitionMarkerDescription_run
      (List.append [b1, b0] pre.reverse) b2 [some b3]

private theorem
    initializerReturnToTransitionMarkerDescription_run_after_append_atCells :
    forall code : Word MachineCodeSymbol,
      code ≠ [] ->
        forall pre : Word Bool,
          exists steps : Nat,
            InitializerReturnToTransitionMarkerDescription.runConfig steps
                { state := InitializerReturnToTransitionMarkerDescription.start
                  tape :=
                    Tape.move Direction.left
                      (initializerAppendCodeWordLastTapeAtCells
                        (List.append (pre.reverse.map some)
                          [none, some false])
                        code) } =
              { state := InitializerReturnToTransitionMarkerDescription.halt
                tape :=
                  initializerTapeAtCells [some false]
                    (some false ::
                      ((List.append pre
                        (MachineDescription.encodeCodeWordAsInput code)).map
                        some)) }
  | [], h => False.elim (h rfl)
  | symbol :: [], _ => by
      intro pre
      cases symbol <;>
        refine ⟨pre.length + 5, ?_⟩ <;>
        simpa [initializerAppendCodeWordLastTapeAtCells,
          initializerAppendCodeSymbolLastTapeAtCells,
          initializerAppendRightLastTapeAtCells,
          MachineDescription.encodeCodeSymbolAsInput,
          MachineDescription.encodeCodeWordAsInput,
          Tape.move, Tape.moveLeft, List.append_assoc] using
          initializerReturnToTransitionMarkerDescription_run_after_append_four_atCells
            pre _ _ _ _
  | symbol :: next :: rest, _ => by
      intro pre
      let symbolBits := MachineDescription.encodeCodeSymbolAsInput symbol
      rcases
          initializerReturnToTransitionMarkerDescription_run_after_append_atCells
            (next :: rest) (by intro h; cases h)
            (List.append pre symbolBits) with
        ⟨steps, hsteps⟩
      refine ⟨steps, ?_⟩
      have hleft :
          List.append (symbolBits.reverse.map some)
              (List.append (pre.reverse.map some) [none, some false]) =
            List.append
              ((List.append pre symbolBits).reverse.map some)
              [none, some false] := by
        simp [List.reverse_append, List.map_append, List.append_assoc]
      have hbits :
          List.append (List.append pre symbolBits)
              (MachineDescription.encodeCodeWordAsInput (next :: rest)) =
            List.append pre
              (MachineDescription.encodeCodeWordAsInput
                (symbol :: next :: rest)) := by
        simp [symbolBits,
          MachineDescription.encodeCodeWordAsInput, List.append_assoc]
      simpa [initializerAppendCodeWordLastTapeAtCells, symbolBits,
        hleft, hbits, MachineDescription.encodeCodeWordAsInput,
        List.map_append, List.append_assoc] using hsteps

private def InitializerMarkedPrefixAppendCodeWordReturnDescription
    (code : Word MachineCodeSymbol) : MachineDescription :=
  MachineDescription.seqSubroutine
    (InitializerMarkedPrefixThenAppendCodeWordLastDescription code)
    InitializerReturnToTransitionMarkerDescription
    Direction.left

private theorem
    initializerMarkedPrefixAppendCodeWordReturnDescription_subroutineReady
    (code : Word MachineCodeSymbol) (hcode : code ≠ []) :
    (InitializerMarkedPrefixAppendCodeWordReturnDescription
      code).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    (initializerMarkedPrefixThenAppendCodeWordLastDescription_subroutineReady
      code hcode)
    initializerReturnToTransitionMarkerDescription_subroutineReady

private theorem initializerMarkedPrefixAppendCodeWordReturnDescription_run
    (code : Word MachineCodeSymbol) (hcode : code ≠ [])
    (b : Bool) (rest : Word Bool) :
    exists steps : Nat,
      (InitializerMarkedPrefixAppendCodeWordReturnDescription code).runConfig steps
          ((InitializerMarkedPrefixAppendCodeWordReturnDescription
            code).initial (b :: rest)) =
        { state :=
            (InitializerMarkedPrefixAppendCodeWordReturnDescription code).halt
          tape :=
            initializerTapeAtCells [some false]
              (some false ::
                ((List.append (false :: true :: b :: rest)
                  (MachineDescription.encodeCodeWordAsInput code)).map
                  some)) } := by
  let A := InitializerMarkedPrefixThenAppendCodeWordLastDescription code
  let B := InitializerReturnToTransitionMarkerDescription
  let Tmid :=
    initializerAppendCodeWordLastTapeAtCells
      (List.append
        ((false :: true :: b :: rest).reverse.map some)
        [none, some false])
      code
  have hAready : A.SubroutineReady := by
    exact
      initializerMarkedPrefixThenAppendCodeWordLastDescription_subroutineReady
        code hcode
  have hBready : B.SubroutineReady := by
    exact initializerReturnToTransitionMarkerDescription_subroutineReady
  rcases
      initializerMarkedPrefixThenAppendCodeWordLastDescription_run
        code hcode b rest with
    ⟨nA, hArunBase⟩
  have hArun :
      A.runConfig nA
          { state := A.start
            tape := Tape.input (b :: rest) } =
        { state := A.halt, tape := Tmid } := by
    simpa [A, Tmid, MachineDescription.initial] using hArunBase
  have hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start
              tape := Tape.move Direction.left Tmid } =
          { state := B.halt
            tape :=
              initializerTapeAtCells [some false]
                (some false ::
                  ((List.append (false :: true :: b :: rest)
                    (MachineDescription.encodeCodeWordAsInput code)).map
                    some)) } := by
    rcases
        initializerReturnToTransitionMarkerDescription_run_after_append_atCells
          code hcode (false :: true :: b :: rest) with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    simpa [B, Tmid] using hB
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.left)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [InitializerMarkedPrefixAppendCodeWordReturnDescription,
    MachineDescription.initial, A, B] using hn

private def InitializerMarkedPrefixAppendNatReturnDescription
    (n : Nat) : MachineDescription :=
  InitializerMarkedPrefixAppendCodeWordReturnDescription
    (MachineDescription.encodeNat n)

private theorem
    initializerMarkedPrefixAppendNatReturnDescription_subroutineReady
    (n : Nat) :
    (InitializerMarkedPrefixAppendNatReturnDescription
      n).SubroutineReady :=
  initializerMarkedPrefixAppendCodeWordReturnDescription_subroutineReady
    (MachineDescription.encodeNat n)
    (initializer_encodeNat_ne_nil n)

private theorem initializerMarkedPrefixAppendNatReturnDescription_run
    (n : Nat) (b : Bool) (rest : Word Bool) :
    exists steps : Nat,
      (InitializerMarkedPrefixAppendNatReturnDescription n).runConfig steps
          ((InitializerMarkedPrefixAppendNatReturnDescription
            n).initial (b :: rest)) =
        { state :=
            (InitializerMarkedPrefixAppendNatReturnDescription n).halt
          tape :=
            initializerTapeAtCells [some false]
              (some false ::
                ((List.append (false :: true :: b :: rest)
                  (MachineDescription.encodeCodeWordAsInput
                    (MachineDescription.encodeNat n))).map some)) } := by
  simpa [InitializerMarkedPrefixAppendNatReturnDescription] using
    initializerMarkedPrefixAppendCodeWordReturnDescription_run
      (MachineDescription.encodeNat n)
      (initializer_encodeNat_ne_nil n)
      b rest

private theorem initializerStageInputBits_exists_cons
    (w : Word Bool) (stage : Nat) :
    exists b : Bool,
    exists rest : Word Bool,
      MachineDescription.encodeCodeWordAsInput
          (PairedRecognizerDovetailStageInputCode w stage) =
        b :: rest := by
  have hne :
      MachineDescription.encodeCodeWordAsInput
          (PairedRecognizerDovetailStageInputCode w stage) ≠ [] := by
    cases w <;>
      simp [PairedRecognizerDovetailStageInputCode,
        MachineDescription.DovetailLayout.stageInputCode,
        MachineDescription.DovetailLayout.stageInputCodeAppend,
        MachineDescription.encodeBoolWordAppend,
        MachineDescription.encodeCellListAppend,
        MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat,
        MachineDescription.encodeCodeWordAsInput,
        MachineDescription.encodeCodeSymbolAsInput]
  cases hbits :
      MachineDescription.encodeCodeWordAsInput
        (PairedRecognizerDovetailStageInputCode w stage) with
  | nil =>
      exact False.elim (hne hbits)
  | cons b rest =>
      exact ⟨b, rest, rfl⟩

private theorem
    initializerMarkedPrefixAppendCodeWordReturnDescription_run_stageInput
    (code : Word MachineCodeSymbol) (hcode : code ≠ [])
    (w : Word Bool) (stage : Nat) :
    exists steps : Nat,
      (InitializerMarkedPrefixAppendCodeWordReturnDescription code).runConfig steps
          ((InitializerMarkedPrefixAppendCodeWordReturnDescription
            code).initial
            (MachineDescription.encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w stage))) =
        { state :=
            (InitializerMarkedPrefixAppendCodeWordReturnDescription code).halt
          tape :=
            initializerTapeAtCells [some false]
              (some false ::
                ((List.append [false, true]
                  (List.append
                    (MachineDescription.encodeCodeWordAsInput
                      (PairedRecognizerDovetailStageInputCode w stage))
                    (MachineDescription.encodeCodeWordAsInput code))).map
                  some)) } := by
  rcases initializerStageInputBits_exists_cons w stage with
    ⟨b, rest, hbits⟩
  rcases
      initializerMarkedPrefixAppendCodeWordReturnDescription_run
        code hcode b rest with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  simpa [hbits, MachineDescription.initial, List.append_assoc] using hsteps

private theorem initializerMarkedPrefixAppendNatReturnDescription_run_stageInput
    (n : Nat) (w : Word Bool) (stage : Nat) :
    exists steps : Nat,
      (InitializerMarkedPrefixAppendNatReturnDescription n).runConfig steps
          ((InitializerMarkedPrefixAppendNatReturnDescription
            n).initial
            (MachineDescription.encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w stage))) =
        { state :=
            (InitializerMarkedPrefixAppendNatReturnDescription n).halt
          tape :=
            initializerTapeAtCells [some false]
              (some false ::
                ((List.append [false, true]
                  (List.append
                    (MachineDescription.encodeCodeWordAsInput
                      (PairedRecognizerDovetailStageInputCode w stage))
                    (MachineDescription.encodeCodeWordAsInput
                      (MachineDescription.encodeNat n)))).map some)) } := by
  simpa [InitializerMarkedPrefixAppendNatReturnDescription] using
    initializerMarkedPrefixAppendCodeWordReturnDescription_run_stageInput
      (MachineDescription.encodeNat n)
      (initializer_encodeNat_ne_nil n)
      w stage

private def InitializerTransitionPrefixedAppendCodeWordReturnDescription
    (code : Word MachineCodeSymbol) : MachineDescription :=
  MachineDescription.seqSubroutine
    (InitializerTransitionPrefixedThenAppendCodeWordLastDescription code)
    InitializerReturnToTransitionMarkerDescription
    Direction.left

private theorem
    initializerTransitionPrefixedAppendCodeWordReturnDescription_subroutineReady
    (code : Word MachineCodeSymbol) (hcode : code ≠ []) :
    (InitializerTransitionPrefixedAppendCodeWordReturnDescription
      code).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    (initializerTransitionPrefixedThenAppendCodeWordLastDescription_subroutineReady
      code hcode)
    initializerReturnToTransitionMarkerDescription_subroutineReady

private theorem initializerTransitionPrefixedAppendCodeWordReturnDescription_run
    (code : Word MachineCodeSymbol) (hcode : code ≠ [])
    (payload : Word Bool) :
    exists steps : Nat,
      (InitializerTransitionPrefixedAppendCodeWordReturnDescription
        code).runConfig steps
          { state :=
              (InitializerTransitionPrefixedAppendCodeWordReturnDescription
                code).start
            tape :=
              initializerTapeAtCells [some false]
                (some false ::
                  ((List.append [false, true] payload).map some)) } =
        { state :=
            (InitializerTransitionPrefixedAppendCodeWordReturnDescription
              code).halt
          tape :=
            initializerTapeAtCells [some false]
              (some false ::
                ((List.append (false :: true :: payload)
                  (MachineDescription.encodeCodeWordAsInput code)).map
                  some)) } := by
  let A := InitializerTransitionPrefixedThenAppendCodeWordLastDescription code
  let B := InitializerReturnToTransitionMarkerDescription
  let Tmid :=
    initializerAppendCodeWordLastTapeAtCells
      (List.append
        ((false :: true :: payload).reverse.map some)
        [none, some false])
      code
  have hAready : A.SubroutineReady := by
    exact
      initializerTransitionPrefixedThenAppendCodeWordLastDescription_subroutineReady
        code hcode
  have hBready : B.SubroutineReady := by
    exact initializerReturnToTransitionMarkerDescription_subroutineReady
  rcases
      initializerTransitionPrefixedThenAppendCodeWordLastDescription_run
        code hcode payload with
    ⟨nA, hArunBase⟩
  have hArun :
      A.runConfig nA
          { state := A.start
            tape :=
              initializerTapeAtCells [some false]
                (some false ::
                  ((List.append [false, true] payload).map some)) } =
        { state := A.halt, tape := Tmid } := by
    simpa [A, Tmid] using hArunBase
  have hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start
              tape := Tape.move Direction.left Tmid } =
          { state := B.halt
            tape :=
              initializerTapeAtCells [some false]
                (some false ::
                  ((List.append (false :: true :: payload)
                    (MachineDescription.encodeCodeWordAsInput code)).map
                    some)) } := by
    rcases
        initializerReturnToTransitionMarkerDescription_run_after_append_atCells
          code hcode (false :: true :: payload) with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    simpa [B, Tmid] using hB
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.left)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [InitializerTransitionPrefixedAppendCodeWordReturnDescription,
    A, B] using hn

private def InitializerTransitionPrefixedAppendNatReturnDescription
    (n : Nat) : MachineDescription :=
  InitializerTransitionPrefixedAppendCodeWordReturnDescription
    (MachineDescription.encodeNat n)

private theorem
    initializerTransitionPrefixedAppendNatReturnDescription_subroutineReady
    (n : Nat) :
    (InitializerTransitionPrefixedAppendNatReturnDescription
      n).SubroutineReady :=
  initializerTransitionPrefixedAppendCodeWordReturnDescription_subroutineReady
    (MachineDescription.encodeNat n)
    (initializer_encodeNat_ne_nil n)

private theorem initializerTransitionPrefixedAppendNatReturnDescription_run
    (n : Nat) (payload : Word Bool) :
    exists steps : Nat,
      (InitializerTransitionPrefixedAppendNatReturnDescription
        n).runConfig steps
          { state :=
              (InitializerTransitionPrefixedAppendNatReturnDescription
                n).start
            tape :=
              initializerTapeAtCells [some false]
                (some false ::
                  ((List.append [false, true] payload).map some)) } =
        { state :=
            (InitializerTransitionPrefixedAppendNatReturnDescription n).halt
          tape :=
            initializerTapeAtCells [some false]
              (some false ::
                ((List.append (false :: true :: payload)
                  (MachineDescription.encodeCodeWordAsInput
                    (MachineDescription.encodeNat n))).map some)) } := by
  simpa [InitializerTransitionPrefixedAppendNatReturnDescription] using
    initializerTransitionPrefixedAppendCodeWordReturnDescription_run
      (MachineDescription.encodeNat n)
      (initializer_encodeNat_ne_nil n)
      payload

private theorem initializerExactIdentityDescription_subroutineReady :
    MachineDescription.ExactIdentityDescription.SubroutineReady :=
  ⟨MachineDescription.exactIdentityDescription_wellFormed,
    MachineDescription.exactIdentityDescription_haltTransitionFree⟩

private def InitializerTransitionPrefixedFirstBitAppendCodeWordReturnDescription
    (code : Word MachineCodeSymbol) : MachineDescription :=
  MachineDescription.seqSubroutine
    MachineDescription.ExactIdentityDescription
    (InitializerTransitionPrefixedAppendCodeWordReturnDescription code)
    Direction.right

private theorem
    initializerTransitionPrefixedFirstBitAppendCodeWordReturnDescription_subroutineReady
    (code : Word MachineCodeSymbol) (hcode : code ≠ []) :
    (InitializerTransitionPrefixedFirstBitAppendCodeWordReturnDescription
      code).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    initializerExactIdentityDescription_subroutineReady
    (initializerTransitionPrefixedAppendCodeWordReturnDescription_subroutineReady
      code hcode)

private theorem
    initializerTransitionPrefixedFirstBitAppendCodeWordReturnDescription_run
    (code : Word MachineCodeSymbol) (hcode : code ≠ [])
    (payload : Word Bool) :
    exists steps : Nat,
      (InitializerTransitionPrefixedFirstBitAppendCodeWordReturnDescription
        code).runConfig steps
          { state :=
              (InitializerTransitionPrefixedFirstBitAppendCodeWordReturnDescription
                code).start
            tape :=
              initializerTapeAtCells []
                (some false :: some false ::
                  ((List.append [false, true] payload).map some)) } =
        { state :=
            (InitializerTransitionPrefixedFirstBitAppendCodeWordReturnDescription
              code).halt
          tape :=
            initializerTapeAtCells [some false]
              (some false ::
                ((List.append (false :: true :: payload)
                  (MachineDescription.encodeCodeWordAsInput code)).map
                  some)) } := by
  let A := MachineDescription.ExactIdentityDescription
  let B := InitializerTransitionPrefixedAppendCodeWordReturnDescription code
  let Tin :=
    initializerTapeAtCells []
      (some false :: some false ::
        ((List.append [false, true] payload).map some))
  have hAready : A.SubroutineReady := by
    exact initializerExactIdentityDescription_subroutineReady
  have hBready : B.SubroutineReady := by
    exact
      initializerTransitionPrefixedAppendCodeWordReturnDescription_subroutineReady
        code hcode
  have hArun :
      A.runConfig 0
          { state := A.start, tape := Tin } =
        { state := A.halt, tape := Tin } := by
    rfl
  have hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start
              tape := Tape.move Direction.right Tin } =
          { state := B.halt
            tape :=
              initializerTapeAtCells [some false]
                (some false ::
                  ((List.append (false :: true :: payload)
                    (MachineDescription.encodeCodeWordAsInput code)).map
                    some)) } := by
    rcases
        initializerTransitionPrefixedAppendCodeWordReturnDescription_run
          code hcode payload with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    simpa [B, Tin, initializerTapeAtCells, Tape.move, Tape.moveRight] using hB
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.right)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [
    InitializerTransitionPrefixedFirstBitAppendCodeWordReturnDescription,
    A, B, Tin] using hn

private def InitializerTransitionPrefixedFirstBitAppendNatReturnDescription
    (n : Nat) : MachineDescription :=
  InitializerTransitionPrefixedFirstBitAppendCodeWordReturnDescription
    (MachineDescription.encodeNat n)

private theorem
    initializerTransitionPrefixedFirstBitAppendNatReturnDescription_subroutineReady
    (n : Nat) :
    (InitializerTransitionPrefixedFirstBitAppendNatReturnDescription
      n).SubroutineReady :=
  initializerTransitionPrefixedFirstBitAppendCodeWordReturnDescription_subroutineReady
    (MachineDescription.encodeNat n)
    (initializer_encodeNat_ne_nil n)

private theorem
    initializerTransitionPrefixedFirstBitAppendNatReturnDescription_run
    (n : Nat) (payload : Word Bool) :
    exists steps : Nat,
      (InitializerTransitionPrefixedFirstBitAppendNatReturnDescription
        n).runConfig steps
          { state :=
              (InitializerTransitionPrefixedFirstBitAppendNatReturnDescription
                n).start
            tape :=
              initializerTapeAtCells []
                (some false :: some false ::
                  ((List.append [false, true] payload).map some)) } =
        { state :=
            (InitializerTransitionPrefixedFirstBitAppendNatReturnDescription
              n).halt
          tape :=
            initializerTapeAtCells [some false]
              (some false ::
                ((List.append (false :: true :: payload)
                  (MachineDescription.encodeCodeWordAsInput
                    (MachineDescription.encodeNat n))).map some)) } := by
  simpa [
    InitializerTransitionPrefixedFirstBitAppendNatReturnDescription] using
    initializerTransitionPrefixedFirstBitAppendCodeWordReturnDescription_run
      (MachineDescription.encodeNat n)
      (initializer_encodeNat_ne_nil n)
      payload

private def InitializerAppendTwoCodeWordsReturnDescription
    (first second : Word MachineCodeSymbol) : MachineDescription :=
  MachineDescription.seqSubroutine
    (InitializerMarkedPrefixAppendCodeWordReturnDescription first)
    (InitializerTransitionPrefixedFirstBitAppendCodeWordReturnDescription
      second)
    Direction.left

private theorem initializerAppendTwoCodeWordsReturnDescription_subroutineReady
    (first second : Word MachineCodeSymbol)
    (hfirst : first ≠ []) (hsecond : second ≠ []) :
    (InitializerAppendTwoCodeWordsReturnDescription
      first second).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    (initializerMarkedPrefixAppendCodeWordReturnDescription_subroutineReady
      first hfirst)
    (initializerTransitionPrefixedFirstBitAppendCodeWordReturnDescription_subroutineReady
      second hsecond)

private theorem initializerAppendTwoCodeWordsReturnDescription_run
    (first second : Word MachineCodeSymbol)
    (hfirst : first ≠ []) (hsecond : second ≠ [])
    (b : Bool) (rest : Word Bool) :
    exists steps : Nat,
      (InitializerAppendTwoCodeWordsReturnDescription
        first second).runConfig steps
          ((InitializerAppendTwoCodeWordsReturnDescription
            first second).initial (b :: rest)) =
        { state :=
            (InitializerAppendTwoCodeWordsReturnDescription
              first second).halt
          tape :=
            initializerTapeAtCells [some false]
              (some false ::
                ((List.append (false :: true :: b :: rest)
                  (List.append
                    (MachineDescription.encodeCodeWordAsInput first)
                    (MachineDescription.encodeCodeWordAsInput second))).map
                  some)) } := by
  let A := InitializerMarkedPrefixAppendCodeWordReturnDescription first
  let B :=
    InitializerTransitionPrefixedFirstBitAppendCodeWordReturnDescription
      second
  let firstBits := MachineDescription.encodeCodeWordAsInput first
  let secondBits := MachineDescription.encodeCodeWordAsInput second
  let Tmid :=
    initializerTapeAtCells [some false]
      (some false ::
        ((List.append (false :: true :: b :: rest) firstBits).map some))
  have hAready : A.SubroutineReady := by
    exact
      initializerMarkedPrefixAppendCodeWordReturnDescription_subroutineReady
        first hfirst
  have hBready : B.SubroutineReady := by
    exact
      initializerTransitionPrefixedFirstBitAppendCodeWordReturnDescription_subroutineReady
        second hsecond
  rcases
      initializerMarkedPrefixAppendCodeWordReturnDescription_run
        first hfirst b rest with
    ⟨nA, hArunBase⟩
  have hArun :
      A.runConfig nA
          { state := A.start
            tape := Tape.input (b :: rest) } =
        { state := A.halt, tape := Tmid } := by
    simpa [A, Tmid, firstBits, MachineDescription.initial] using hArunBase
  have hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start
              tape := Tape.move Direction.left Tmid } =
          { state := B.halt
            tape :=
              initializerTapeAtCells [some false]
                (some false ::
                  ((List.append (false :: true :: b :: rest)
                    (List.append firstBits secondBits)).map some)) } := by
    rcases
        initializerTransitionPrefixedFirstBitAppendCodeWordReturnDescription_run
          second hsecond (List.append (b :: rest) firstBits) with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    simpa [B, Tmid, firstBits, secondBits, initializerTapeAtCells,
      Tape.move, Tape.moveLeft, List.append_assoc] using hB
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.left)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [InitializerAppendTwoCodeWordsReturnDescription,
    MachineDescription.initial, A, B, firstBits, secondBits] using hn

private theorem initializerAppendTwoCodeWordsReturnDescription_run_stageInput
    (first second : Word MachineCodeSymbol)
    (hfirst : first ≠ []) (hsecond : second ≠ [])
    (w : Word Bool) (stage : Nat) :
    exists steps : Nat,
      (InitializerAppendTwoCodeWordsReturnDescription
        first second).runConfig steps
          ((InitializerAppendTwoCodeWordsReturnDescription
            first second).initial
            (MachineDescription.encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w stage))) =
        { state :=
            (InitializerAppendTwoCodeWordsReturnDescription
              first second).halt
          tape :=
            initializerTapeAtCells [some false]
              (some false ::
                ((List.append [false, true]
                  (List.append
                    (MachineDescription.encodeCodeWordAsInput
                      (PairedRecognizerDovetailStageInputCode w stage))
                    (List.append
                      (MachineDescription.encodeCodeWordAsInput first)
                      (MachineDescription.encodeCodeWordAsInput second)))).map
                  some)) } := by
  rcases initializerStageInputBits_exists_cons w stage with
    ⟨b, rest, hbits⟩
  rcases
      initializerAppendTwoCodeWordsReturnDescription_run
        first second hfirst hsecond b rest with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  simpa [hbits, MachineDescription.initial, List.append_assoc] using hsteps

private theorem initializerCodeCells_encodeNat
    (n : Nat) :
    initializerCodeCells (MachineDescription.encodeNat n) =
      initializerNatCodeCells n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        List.append
            (initializerCodeSymbolCells MachineCodeSymbol.tick)
            (initializerCodeCells (MachineDescription.encodeNat n)) =
          List.append
            (initializerCodeSymbolCells MachineCodeSymbol.tick)
            (initializerNatCodeCells n)
      rw [ih]

private theorem initializerCodeCells_encodeNatAppend
    (n : Nat) (suffix : Word MachineCodeSymbol) :
    initializerCodeCells
        (MachineDescription.encodeNatAppend n suffix) =
      List.append (initializerNatCodeCells n)
        (initializerCodeCells suffix) := by
  rw [MachineDescription.encodeNatAppend, initializerCodeCells_append,
    initializerCodeCells_encodeNat]

private theorem initializerCodeCells_encodeCell
    (cell : Option Bool) :
    initializerCodeCells (MachineDescription.encodeCell cell) =
      initializerCellCodeCells cell := by
  cases cell with
  | none =>
      rfl
  | some b =>
      cases b <;> rfl

private theorem initializerCodeCells_encodeCellAppend
    (cell : Option Bool) (suffix : Word MachineCodeSymbol) :
    initializerCodeCells
        (MachineDescription.encodeCellAppend cell suffix) =
      List.append (initializerCellCodeCells cell)
        (initializerCodeCells suffix) := by
  rw [MachineDescription.encodeCellAppend, initializerCodeCells_append,
    initializerCodeCells_encodeCell]

private theorem initializerCodeCells_encodeCellsAppend
    (cells : List (Option Bool)) (suffix : Word MachineCodeSymbol) :
    initializerCodeCells
        (MachineDescription.encodeCellsAppend cells suffix) =
      List.append (initializerCellsCodeCells cells)
        (initializerCodeCells suffix) := by
  induction cells with
  | nil =>
      rfl
  | cons cell rest ih =>
      rw [MachineDescription.encodeCellsAppend,
        initializerCodeCells_encodeCellAppend, ih]
      simp [initializerCellsCodeCells, List.append_assoc]

private theorem initializerCodeCells_encodeCellListAppend
    (cells : List (Option Bool)) (suffix : Word MachineCodeSymbol) :
    initializerCodeCells
        (MachineDescription.encodeCellListAppend cells suffix) =
      List.append (initializerNatCodeCells cells.length)
        (List.append (initializerCellsCodeCells cells)
          (initializerCodeCells suffix)) := by
  rw [MachineDescription.encodeCellListAppend,
    initializerCodeCells_encodeNatAppend,
    initializerCodeCells_encodeCellsAppend]

private def initializerInputTapeCodeCells :
    Word Bool -> List (Option Bool)
  | [] =>
      List.append (initializerNatCodeCells 0)
        (List.append (initializerCellCodeCells none)
          (initializerNatCodeCells 0))
  | b :: rest =>
      List.append (initializerNatCodeCells 0)
        (List.append (initializerCellCodeCells (some b))
          (List.append (initializerNatCodeCells rest.length)
            (initializerCellsCodeCells (rest.map some))))

private theorem initializerCodeCells_encodeTapeAppend_input
    (w : Word Bool) (suffix : Word MachineCodeSymbol) :
    initializerCodeCells
        (MachineDescription.encodeTapeAppend (Tape.input w) suffix) =
      List.append (initializerInputTapeCodeCells w)
        (initializerCodeCells suffix) := by
  cases w with
  | nil =>
      rw [encodeTapeAppend_input_nil,
        initializerCodeCells_encodeCellListAppend,
        initializerCodeCells_encodeCellAppend,
        initializerCodeCells_encodeCellListAppend]
      simp [initializerInputTapeCodeCells, initializerCellsCodeCells,
        List.append_assoc]
  | cons b rest =>
      rw [encodeTapeAppend_input_cons,
        initializerCodeCells_encodeCellListAppend,
        initializerCodeCells_encodeCellAppend,
        initializerCodeCells_encodeCellListAppend]
      simp [initializerInputTapeCodeCells, initializerCellsCodeCells,
        List.append_assoc]

private def initializerBoolCodeCells (b : Bool) :
    List (Option Bool) :=
  initializerCellCodeCells (some b)

private theorem initializerCodeCells_encodeBoolAppend
    (b : Bool) (suffix : Word MachineCodeSymbol) :
    initializerCodeCells
        (MachineDescription.encodeBoolAppend b suffix) =
      List.append (initializerBoolCodeCells b)
        (initializerCodeCells suffix) := by
  rw [MachineDescription.encodeBoolAppend,
    initializerCodeCells_encodeCellAppend]
  rfl

private theorem initializerCodeCells_encodeBoolWordAppend
    (w : Word Bool) (suffix : Word MachineCodeSymbol) :
    initializerCodeCells
        (MachineDescription.encodeBoolWordAppend w suffix) =
      List.append (initializerBoolWordCells w)
        (initializerCodeCells suffix) := by
  rw [MachineDescription.encodeBoolWordAppend,
    initializerCodeCells_encodeCellListAppend]
  simp [initializerBoolWordCells, initializerBoolPayloadCells,
    List.append_assoc]

private theorem initializerStageInputCells_eq_bool_word_nat
    (w : Word Bool) (stage : Nat) :
    initializerStageInputCells w stage =
      List.append (initializerBoolWordCells w)
        (initializerNatCodeCells stage) := by
  rw [initializerStageInputCells, PairedRecognizerDovetailStageInputCode,
    MachineDescription.DovetailLayout.stageInputCode,
    MachineDescription.DovetailLayout.stageInputCodeAppend,
    initializerCodeCells_encodeBoolWordAppend,
    initializerCodeCells_encodeNatAppend]
  simp [initializerCodeCells, MachineDescription.encodeCodeWordAsInput]

private theorem initializerSuffixCells_eq_field_blocks
    (accept reject : MachineDescription)
    (w : Word Bool) :
    initializerSuffixCells accept reject w =
      List.append (initializerNatCodeCells accept.start)
        (List.append (initializerInputTapeCodeCells w)
          (List.append (initializerNatCodeCells reject.start)
            (List.append (initializerInputTapeCodeCells w)
              (List.append (initializerBoolCodeCells false)
                (initializerBoolCodeCells false))))) := by
  rw [initializerSuffixCells, DovetailInitialLayoutInitializerSuffixCode,
    initializerCodeCells_encodeNatAppend,
    initializerCodeCells_encodeTapeAppend_input,
    initializerCodeCells_encodeNatAppend,
    initializerCodeCells_encodeTapeAppend_input,
    initializerCodeCells_encodeBoolAppend,
    initializerCodeCells_encodeBoolAppend]
  simp [initializerCodeCells, MachineDescription.encodeCodeWordAsInput]

private theorem initializerOutputCells_eq_stageInput_append_suffix
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    initializerOutputCells accept reject w stage =
      List.append [some false, some false, some false, some true]
        (List.append
          (initializerStageInputCells w stage)
          (initializerSuffixCells accept reject w)) := by
  rw [initializerOutputCells, initializerStageInputCells,
    initializerSuffixCells,
    dovetailInitialLayoutInitializerOutputCode_eq_stageInput_append_suffix]
  unfold initializerCodeCells
  simp [MachineDescription.encodeCodeWordAsInput,
    MachineDescription.encodeCodeSymbolAsInput]
  change
    List.map some
        (MachineDescription.encodeCodeWordAsInput
          (List.append
            (PairedRecognizerDovetailStageInputCode w stage)
            (DovetailInitialLayoutInitializerSuffixCode accept reject w))) =
      List.append
        (List.map some
          (MachineDescription.encodeCodeWordAsInput
            (PairedRecognizerDovetailStageInputCode w stage)))
        (List.map some
          (MachineDescription.encodeCodeWordAsInput
            (DovetailInitialLayoutInitializerSuffixCode accept reject w)))
  rw [MachineDescription.encodeCodeWordAsInput_append]
  exact initializer_map_some_append
    (MachineDescription.encodeCodeWordAsInput
      (PairedRecognizerDovetailStageInputCode w stage))
    (MachineDescription.encodeCodeWordAsInput
      (DovetailInitialLayoutInitializerSuffixCode accept reject w))

private theorem initializerOutputCells_eq_phase_blocks
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    initializerOutputCells accept reject w stage =
      List.append [some false, some false, some false, some true]
        (List.append (initializerBoolWordCells w)
          (List.append (initializerNatCodeCells stage)
            (initializerSuffixCells accept reject w))) := by
  rw [initializerOutputCells_eq_stageInput_append_suffix,
    initializerStageInputCells_eq_bool_word_nat]
  simp [List.append_assoc]

private theorem initializerOutputCells_eq_full_field_blocks
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    initializerOutputCells accept reject w stage =
      List.append [some false, some false, some false, some true]
        (List.append (initializerBoolWordCells w)
          (List.append (initializerNatCodeCells stage)
            (List.append (initializerNatCodeCells accept.start)
              (List.append (initializerInputTapeCodeCells w)
                (List.append (initializerNatCodeCells reject.start)
                  (List.append (initializerInputTapeCodeCells w)
                    (List.append (initializerBoolCodeCells false)
                      (initializerBoolCodeCells false)))))))) := by
  rw [initializerOutputCells_eq_phase_blocks,
    initializerSuffixCells_eq_field_blocks]

private theorem initializerTapeAtCells_eq_input_transition_prefixed
    (tail : Word Bool) :
    initializerTapeAtCells []
        ((List.append
          (MachineDescription.encodeCodeSymbolAsInput
            MachineCodeSymbol.transition) tail).map some) =
      Tape.input
        (List.append
          (MachineDescription.encodeCodeSymbolAsInput
            MachineCodeSymbol.transition) tail) := by
  simp [initializerTapeAtCells,
    MachineDescription.encodeCodeSymbolAsInput, Tape.input]

private theorem initializerTapeAtCells_right_eq_move_right_input_transition_prefixed
    (tail : Word Bool) :
    initializerTapeAtCells
        [some false]
        (List.append [some false, some false, some true]
          (tail.map some)) =
      Tape.move Direction.right
        (Tape.input
          (List.append
            (MachineDescription.encodeCodeSymbolAsInput
              MachineCodeSymbol.transition) tail)) := by
  simp [initializerTapeAtCells,
    MachineDescription.encodeCodeSymbolAsInput, Tape.input,
    Tape.move, Tape.moveRight]

private theorem dovetailInitialLayoutInitializerOutputTape_eq_cells
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    DovetailInitialLayoutInitializerOutputTape accept reject w stage =
      initializerTapeAtCells
        [some false]
        (List.append [some false, some false, some true]
          (List.append
            ((MachineDescription.encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w stage)).map some)
            ((MachineDescription.encodeCodeWordAsInput
              (DovetailInitialLayoutInitializerSuffixCode
                accept reject w)).map some))) := by
  rw [dovetailInitialLayoutInitializerOutputTape_eq_stageInput_append_suffix]
  rw [← initializerTapeAtCells_right_eq_move_right_input_transition_prefixed
    (tail :=
      List.append
        (MachineDescription.encodeCodeWordAsInput
          (PairedRecognizerDovetailStageInputCode w stage))
        (MachineDescription.encodeCodeWordAsInput
          (DovetailInitialLayoutInitializerSuffixCode
            accept reject w)))]
  rw [initializer_map_some_append]

theorem dovetailInitialLayoutInitializerRightShiftedSpec_of_rightShiftedOutputCompiled
    {accept reject initializer : MachineDescription}
    (hinit :
      TapeCodePrimitiveRightShiftedOutputCompiledSubroutineByDescription
        (PairedRecognizerDovetailInitialLayoutCode accept reject)
        initializer) :
    DovetailInitialLayoutInitializerRightShiftedSpec
      accept reject initializer := by
  constructor
  · exact ⟨hinit.left, hinit.right.left⟩
  constructor
  · intro w stage
    let code := PairedRecognizerDovetailStageInputCode w stage
    let out := DovetailInitialLayoutInitializerOutputCode
      accept reject w stage
    have htransform :
        (PairedRecognizerDovetailInitialLayoutCode accept reject).transform
            code = some out := by
      simpa [code, out, DovetailInitialLayoutInitializerOutputCode] using
        pairedRecognizerDovetailInitialLayoutCode_encode
          accept reject w stage
    have houtput :
        initializer.HaltsWithOutput
          (MachineDescription.encodeCodeWordAsInput code)
          (MachineDescription.encodeCodeWordAsInput out) :=
      (hinit.right.right.left code out).mpr htransform
    rcases houtput with ⟨n, hn⟩
    let T :=
      (initializer.runConfig n
        (initializer.initial
          (MachineDescription.encodeCodeWordAsInput code))).tape
    have hTape :
        initializer.HaltsWithTape
          (MachineDescription.encodeCodeWordAsInput code) T := by
      exact ⟨n, ⟨hn.left, rfl⟩⟩
    rcases hinit.right.right.right code T hTape with
      ⟨actualOut, hactual, hT⟩
    have hactualEq : actualOut = out := by
      rw [htransform] at hactual
      cases hactual
      rfl
    subst actualOut
    refine ⟨n, ?_⟩
    constructor
    · exact hn.left
    · change T =
        DovetailInitialLayoutInitializerOutputTape accept reject w stage
      rw [hT]
      simp [out, DovetailInitialLayoutInitializerOutputTape]
  · intro code T hhalt
    rcases hinit.right.right.right code T hhalt with
      ⟨out, htransform, hT⟩
    rcases
        (pairedRecognizerDovetailInitialLayoutCode_transform_eq_some_iff
          accept reject code out).mp htransform with
      ⟨w, stage, hcode, hout⟩
    refine ⟨w, stage, hcode, ?_⟩
    rw [hT, hout]
    rfl

theorem dovetailInitialLayoutInitializerConcreteMachineConstruction_of_rightShiftedOutputCompiled
    (hcompile :
      DovetailInitialLayoutInitializerRightShiftedOutputCompiledConstruction) :
    DovetailInitialLayoutInitializerConcreteMachineConstruction := by
  intro accept reject
  rcases hcompile accept reject with ⟨initializer, hinit⟩
  exact
    ⟨initializer,
      dovetailInitialLayoutInitializerRightShiftedSpec_of_rightShiftedOutputCompiled
        hinit⟩

private theorem dovetailInitialLayoutInitializerRightShiftedSpec_haltsWithOutput_iff
    {accept reject initializer : MachineDescription}
    (hinit :
      DovetailInitialLayoutInitializerRightShiftedSpec
        accept reject initializer)
    (code out : Word MachineCodeSymbol) :
    initializer.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out) <->
      (PairedRecognizerDovetailInitialLayoutCode accept reject).transform
        code = some out := by
  constructor
  · intro hhalt
    rcases hhalt with ⟨n, hn⟩
    let T :=
      (initializer.runConfig n
        (initializer.initial
          (MachineDescription.encodeCodeWordAsInput code))).tape
    have hTape :
        initializer.HaltsWithTape
          (MachineDescription.encodeCodeWordAsInput code) T := by
      exact ⟨n, ⟨hn.left, rfl⟩⟩
    rcases hinit.right.right code T hTape with
      ⟨w, stage, hcode, hT⟩
    let expected :=
      MachineDescription.DovetailLayout.encode
        (MachineDescription.DovetailLayout.initial accept reject w stage)
    have hactual :
        Tape.normalizedOutput T =
          MachineDescription.encodeCodeWordAsInput out := by
      simpa [T] using hn.right
    have hexpected :
        Tape.normalizedOutput T =
          MachineDescription.encodeCodeWordAsInput expected := by
      rw [hT]
      exact
        tape_normalizedOutput_move_right_input
          (MachineDescription.encodeCodeWordAsInput expected)
    have houtBits :
        MachineDescription.encodeCodeWordAsInput out =
          MachineDescription.encodeCodeWordAsInput expected := by
      rw [← hactual]
      exact hexpected
    have hout : out = expected :=
      MachineDescription.encodeCodeWordAsInput_injective houtBits
    exact
      (pairedRecognizerDovetailInitialLayoutCode_transform_eq_some_iff
        accept reject code out).mpr
        ⟨w, stage, hcode, hout⟩
  · intro htransform
    rcases
        (pairedRecognizerDovetailInitialLayoutCode_transform_eq_some_iff
          accept reject code out).mp htransform with
      ⟨w, stage, hcode, hout⟩
    subst code
    subst out
    simpa [DovetailInitialLayoutInitializerOutputTape,
      DovetailInitialLayoutInitializerOutputCode,
      tape_normalizedOutput_move_right_input] using
      MachineDescription.haltsWithOutput_of_haltsWithTape
        (hinit.right.left w stage)

private theorem tapeCodePrimitiveRightShiftedOutputCompiled_of_dovetailInitialLayoutSpec
    {accept reject initializer : MachineDescription}
    (hinit :
      DovetailInitialLayoutInitializerRightShiftedSpec
        accept reject initializer) :
    TapeCodePrimitiveRightShiftedOutputCompiledSubroutineByDescription
      (PairedRecognizerDovetailInitialLayoutCode accept reject)
      initializer := by
  constructor
  · exact hinit.left.left
  · constructor
    · exact hinit.left.right
    · constructor
      · exact
          dovetailInitialLayoutInitializerRightShiftedSpec_haltsWithOutput_iff
            hinit
      · intro code T hhalt
        rcases hinit.right.right code T hhalt with
          ⟨w, stage, hcode, hT⟩
        refine
          ⟨MachineDescription.DovetailLayout.encode
            (MachineDescription.DovetailLayout.initial
              accept reject w stage), ?_, hT⟩
        exact
          (pairedRecognizerDovetailInitialLayoutCode_transform_eq_some_iff
            accept reject code
              (MachineDescription.DovetailLayout.encode
                (MachineDescription.DovetailLayout.initial
                  accept reject w stage))).mpr
            ⟨w, stage, hcode, rfl⟩

theorem tapeCodePrimitiveClosedHandoffCompiled_of_rightShiftedOutputCompiled
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (hD :
      TapeCodePrimitiveRightShiftedOutputCompiledSubroutineByDescription
        P D)
    (houtCons :
      forall {code out : Word MachineCodeSymbol},
        P.transform code = some out ->
          exists symbol : MachineCodeSymbol,
          exists tail : Word MachineCodeSymbol,
            out = symbol :: tail) :
    TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      P D tapeCodePrimitiveCodeWordHandoffMove :=
  tapeCodePrimitiveClosedHandoffCompiled_of_halt_tape_move_right
    hD.left hD.right.left hD.right.right.left houtCons
    hD.right.right.right

private theorem dovetailInitialLayoutInitializerFiniteDescription_realizer
    (accept reject : MachineDescription) :
    exists initializer : MachineDescription,
      DovetailInitialLayoutInitializerRightShiftedSpec
        accept reject initializer := by
  sorry

theorem dovetailInitialLayoutInitializerFiniteDescriptionConstruction_scaffold :
    DovetailInitialLayoutInitializerFiniteDescriptionConstruction := by
  intro accept reject
  exact
    dovetailInitialLayoutInitializerFiniteDescription_realizer
      accept reject

theorem dovetailInitialLayoutInitializerRightShiftedOutputCompiledConstruction :
    DovetailInitialLayoutInitializerRightShiftedOutputCompiledConstruction := by
  intro accept reject
  rcases
      dovetailInitialLayoutInitializerFiniteDescriptionConstruction_scaffold
        accept reject with
    ⟨initializer, hinit⟩
  exact
    ⟨initializer,
      tapeCodePrimitiveRightShiftedOutputCompiled_of_dovetailInitialLayoutSpec
        hinit⟩

theorem dovetailInitialLayoutInitializerConcreteMachineConstruction :
    DovetailInitialLayoutInitializerConcreteMachineConstruction :=
  dovetailInitialLayoutInitializerConcreteMachineConstruction_of_rightShiftedOutputCompiled
    dovetailInitialLayoutInitializerRightShiftedOutputCompiledConstruction

theorem dovetailInitialLayoutInitializerMachineConstruction :
    DovetailInitialLayoutInitializerMachineConstruction := by
  intro accept reject
  exact
    dovetailInitialLayoutInitializerConcreteMachineConstruction
      accept reject

theorem pairedRecognizerDovetailInitialLayoutCode_rightShiftedSpecConstruction :
    PairedRecognizerDovetailInitialLayoutCodeRightShiftedSpecConstruction := by
  intro accept reject
  exact
    dovetailInitialLayoutInitializerFiniteDescriptionConstruction_scaffold
      accept reject

theorem pairedRecognizerDovetailInitialLayoutCode_rightShiftedOutputCompiledSubroutine
    (accept reject : MachineDescription) :
    exists initializer : MachineDescription,
      TapeCodePrimitiveRightShiftedOutputCompiledSubroutineByDescription
        (PairedRecognizerDovetailInitialLayoutCode accept reject)
        initializer :=
  dovetailInitialLayoutInitializerRightShiftedOutputCompiledConstruction
    accept reject

theorem pairedRecognizerDovetailInitialLayoutCode_closedHandoffCompiledSubroutine
    (accept reject : MachineDescription) :
    exists initializer : MachineDescription,
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        (PairedRecognizerDovetailInitialLayoutCode accept reject)
        initializer tapeCodePrimitiveCodeWordHandoffMove := by
  rcases
      pairedRecognizerDovetailInitialLayoutCode_rightShiftedOutputCompiledSubroutine
        accept reject with
    ⟨initializer, hinitializer⟩
  refine ⟨initializer, ?_⟩
  have houtCons :
      forall {code out : Word MachineCodeSymbol},
        (PairedRecognizerDovetailInitialLayoutCode accept reject).transform
            code = some out ->
          exists symbol : MachineCodeSymbol,
          exists tail : Word MachineCodeSymbol,
            out = symbol :: tail := by
    intro code out hp
    rcases
        pairedRecognizerDovetailInitialLayoutCode_transform_eq_some_cons hp with
      ⟨tail, hout⟩
    exact ⟨MachineCodeSymbol.transition, tail, hout⟩
  exact
    tapeCodePrimitiveClosedHandoffCompiled_of_rightShiftedOutputCompiled
      hinitializer houtCons

end Computability
end FoC

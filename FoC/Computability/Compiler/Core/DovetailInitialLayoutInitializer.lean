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

namespace DovetailInitialLayoutInitializer

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

private theorem haltsWithTape_functional_of_haltTransitionFree
    {D : MachineDescription} {w : Word Bool} {T₁ T₂ : Tape Bool}
    (hD : D.HaltTransitionFree)
    (h₁ : D.HaltsWithTape w T₁)
    (h₂ : D.HaltsWithTape w T₂) :
    T₁ = T₂ := by
  rcases h₁ with ⟨n₁, h₁⟩
  rcases h₂ with ⟨n₂, h₂⟩
  let c₀ := D.initial w
  have hordered :
      forall {n m : Nat} {Tn Tm : Tape Bool},
        n ≤ m ->
        D.HaltsWithTapeIn n w Tn ->
        D.HaltsWithTapeIn m w Tm ->
          Tn = Tm := by
    intro n m Tn Tm hle hn hm
    let d := m - n
    have hm_eq : m = n + d := by
      omega
    have hconfig_n :
        D.runConfig n c₀ =
          { state := D.halt, tape := Tn } := by
      cases hfinal : D.runConfig n c₀ with
      | mk state tape =>
          have hstate : state = D.halt := by
            simpa [MachineDescription.HaltsWithTapeIn, c₀, hfinal] using
              hn.left
          have htape : tape = Tn := by
            simpa [MachineDescription.HaltsWithTapeIn, c₀, hfinal] using
              hn.right
          simp [hstate, htape]
    have hrunm :
        D.runConfig m c₀ = D.runConfig d (D.runConfig n c₀) := by
      rw [hm_eq, MachineDescription.runConfig_add]
    have hstay :
        D.runConfig d (D.runConfig n c₀) =
          D.runConfig n c₀ := by
      rw [hconfig_n]
      exact MachineDescription.runConfig_halt hD Tn d
    have htape_m :
        (D.runConfig m c₀).tape = Tn := by
      rw [hrunm, hstay, hconfig_n]
    have htm : (D.runConfig m c₀).tape = Tm := by
      simpa [MachineDescription.HaltsWithTapeIn, c₀] using hm.right
    rw [htm] at htape_m
    exact htape_m.symm
  by_cases hle : n₁ ≤ n₂
  · exact hordered hle h₁ h₂
  · have hle' : n₂ ≤ n₁ := by omega
    exact (hordered hle' h₂ h₁).symm

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

def OutputCode
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) : Word MachineCodeSymbol :=
  MachineDescription.DovetailLayout.encode
    (MachineDescription.DovetailLayout.initial accept reject w stage)

def SuffixCode
    (accept reject : MachineDescription)
    (w : Word Bool) : Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend accept.start
    (MachineDescription.encodeTapeAppend (Tape.input w)
      (MachineDescription.encodeNatAppend reject.start
        (MachineDescription.encodeTapeAppend (Tape.input w)
          (MachineDescription.encodeBoolAppend false
            (MachineDescription.encodeBoolAppend false [])))))

def OutputTape
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) : Tape Bool :=
  Tape.move Direction.right
    (Tape.input
      (MachineDescription.encodeCodeWordAsInput
        (OutputCode
          accept reject w stage)))

def ReadySpec
    (initializer : MachineDescription) : Prop :=
  initializer.WellFormed ∧ initializer.HaltTransitionFree

def ForwardSpec
    (accept reject initializer : MachineDescription) : Prop :=
  forall w : Word Bool,
  forall stage : Nat,
    initializer.HaltsWithTape
      (MachineDescription.encodeCodeWordAsInput
        (PairedRecognizerDovetailStageInputCode w stage))
      (OutputTape
        accept reject w stage)

def ClosedSpec
    (accept reject initializer : MachineDescription) : Prop :=
  forall code : Word MachineCodeSymbol,
  forall T : Tape Bool,
    initializer.HaltsWithTape
        (MachineDescription.encodeCodeWordAsInput code) T ->
      exists w : Word Bool,
      exists stage : Nat,
        code = PairedRecognizerDovetailStageInputCode w stage ∧
          T =
            OutputTape
              accept reject w stage

def RightShiftedSpec
    (accept reject initializer : MachineDescription) : Prop :=
  ReadySpec initializer ∧
    ForwardSpec
      accept reject initializer ∧
      ClosedSpec
        accept reject initializer

def MachineConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists initializer : MachineDescription,
      ReadySpec initializer ∧
        ForwardSpec
          accept reject initializer ∧
          ClosedSpec
            accept reject initializer

def PairedRecognizerDovetailInitialLayoutCodeRightShiftedSpecConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists initializer : MachineDescription,
      RightShiftedSpec
        accept reject initializer

def ConcreteMachineConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists initializer : MachineDescription,
      ReadySpec initializer ∧
        ForwardSpec
          accept reject initializer ∧
          ClosedSpec
            accept reject initializer

def RightShiftedOutputCompiledConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists initializer : MachineDescription,
      TapeCodePrimitiveRightShiftedOutputCompiledSubroutineByDescription
        (PairedRecognizerDovetailInitialLayoutCode accept reject)
        initializer

def FiniteDescriptionConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists initializer : MachineDescription,
      RightShiftedSpec
        accept reject initializer

theorem outputCode_eq_expanded
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    OutputCode accept reject w stage =
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

theorem outputTape_eq_expanded
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    OutputTape accept reject w stage =
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
  rw [OutputTape,
    outputCode_eq_expanded]

theorem suffixCode_eq_configurations
    (accept reject : MachineDescription)
    (w : Word Bool) :
    SuffixCode accept reject w =
      MachineDescription.encodeConfigurationAppend
        (accept.initial w)
        (MachineDescription.encodeConfigurationAppend
          (reject.initial w)
          (MachineDescription.encodeBoolAppend false
            (MachineDescription.encodeBoolAppend false []))) := by
  rw [SuffixCode,
    encodeConfigurationAppend_initial,
    encodeConfigurationAppend_initial]

theorem outputCode_eq_stageInput_append_suffix
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    OutputCode accept reject w stage =
      MachineCodeSymbol.transition ::
        List.append
          (MachineDescription.DovetailLayout.stageInputCode w stage)
          (SuffixCode accept reject w) := by
  rw [outputCode_eq_expanded]
  change
    MachineCodeSymbol.transition ::
        MachineDescription.encodeBoolWordAppend w
          (MachineDescription.encodeNatAppend stage
            (SuffixCode accept reject w)) =
      MachineCodeSymbol.transition ::
        List.append
          (MachineDescription.DovetailLayout.stageInputCode w stage)
          (SuffixCode accept reject w)
  congr 1
  have hnat :
      MachineDescription.encodeNatAppend stage
          (SuffixCode accept reject w) =
        List.append (MachineDescription.encodeNatAppend stage [])
          (SuffixCode accept reject w) := by
    simpa using
      encodeNatAppend_append stage ([] : Word MachineCodeSymbol)
        (SuffixCode accept reject w)
  have hbool :=
    encodeBoolWordAppend_append w
      (MachineDescription.encodeNatAppend stage [])
      (SuffixCode accept reject w)
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

theorem outputBits_eq_stageInput_append_suffix
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    MachineDescription.encodeCodeWordAsInput
        (OutputCode
          accept reject w stage) =
      List.append
        (MachineDescription.encodeCodeSymbolAsInput
          MachineCodeSymbol.transition)
        (List.append
          (MachineDescription.encodeCodeWordAsInput
            (PairedRecognizerDovetailStageInputCode w stage))
          (MachineDescription.encodeCodeWordAsInput
            (SuffixCode
              accept reject w))) := by
  rw [outputCode_eq_stageInput_append_suffix,
    MachineDescription.encodeCodeWordAsInput]
  rw [MachineDescription.encodeCodeWordAsInput_append]
  rfl

theorem outputTape_eq_stageInput_append_suffix
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    OutputTape accept reject w stage =
      Tape.move Direction.right
        (Tape.input
          (List.append
            (MachineDescription.encodeCodeSymbolAsInput
              MachineCodeSymbol.transition)
            (List.append
              (MachineDescription.encodeCodeWordAsInput
                (PairedRecognizerDovetailStageInputCode w stage))
              (MachineDescription.encodeCodeWordAsInput
                (SuffixCode
                  accept reject w))))) := by
  rw [OutputTape,
    outputBits_eq_stageInput_append_suffix]

private def tapeAtCells
    (leftRev cells : List (Option Bool)) : Tape Bool :=
  match cells with
  | [] => { left := leftRev, head := none, right := [] }
  | cell :: rest => { left := leftRev, head := cell, right := rest }

private def config
    (state : Nat) (leftRev cells : List (Option Bool)) :
    MachineDescription.Configuration :=
  { state := state, tape := tapeAtCells leftRev cells }

private def codeCells
    (code : Word MachineCodeSymbol) : List (Option Bool) :=
  (MachineDescription.encodeCodeWordAsInput code).map some

private def stageInputCells
    (w : Word Bool) (stage : Nat) : List (Option Bool) :=
  codeCells (PairedRecognizerDovetailStageInputCode w stage)

private def suffixCells
    (accept reject : MachineDescription)
    (w : Word Bool) : List (Option Bool) :=
  codeCells
    (SuffixCode accept reject w)

private def outputCells
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) : List (Option Bool) :=
  codeCells
    (OutputCode accept reject w stage)

private theorem map_some_append
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

private theorem codeCells_append
    (pre suffix : Word MachineCodeSymbol) :
    codeCells (List.append pre suffix) =
      List.append (codeCells pre) (codeCells suffix) := by
  unfold codeCells
  rw [MachineDescription.encodeCodeWordAsInput_append]
  exact map_some_append
    (MachineDescription.encodeCodeWordAsInput pre)
    (MachineDescription.encodeCodeWordAsInput suffix)

private def codeSymbolCells
    (symbol : MachineCodeSymbol) : List (Option Bool) :=
  (MachineDescription.encodeCodeSymbolAsInput symbol).map some

private def natCodeCells : Nat -> List (Option Bool)
  | 0 => codeSymbolCells MachineCodeSymbol.done
  | n + 1 =>
      List.append
        (codeSymbolCells MachineCodeSymbol.tick)
        (natCodeCells n)

private def cellCodeCells :
    Option Bool -> List (Option Bool)
  | none => codeSymbolCells MachineCodeSymbol.blank
  | some false => codeSymbolCells MachineCodeSymbol.zero
  | some true => codeSymbolCells MachineCodeSymbol.one

private def cellsCodeCells :
    List (Option Bool) -> List (Option Bool)
  | [] => []
  | cell :: rest =>
      List.append (cellCodeCells cell)
        (cellsCodeCells rest)

private def boolPayloadCells
    (w : Word Bool) : List (Option Bool) :=
  cellsCodeCells (w.map some)

private def boolWordCells
    (w : Word Bool) : List (Option Bool) :=
  List.append (natCodeCells w.length)
    (boolPayloadCells w)

private def markedLengthTickCells : List (Option Bool) :=
  [none, some false, some true, some false]

private def consumedLengthTickCells : List (Option Bool) :=
  [some false, none, some true, some false]

private def markedCellCodeCells :
    Option Bool -> List (Option Bool)
  | none => cellCodeCells none
  | some false => [none, some true, some false, some true]
  | some true => [none, some true, some true, some false]

private def repeatedCells
    (chunk : List (Option Bool)) : Nat -> List (Option Bool)
  | 0 => []
  | n + 1 => List.append chunk (repeatedCells chunk n)

private def markedLengthTickPrefix (n : Nat) :
    List (Option Bool) :=
  repeatedCells markedLengthTickCells n

private def consumedLengthTickPrefix (n : Nat) :
    List (Option Bool) :=
  repeatedCells consumedLengthTickCells n

private def markedCellsCodeCells :
    List (Option Bool) -> List (Option Bool)
  | [] => []
  | cell :: rest =>
      List.append (markedCellCodeCells cell)
        (markedCellsCodeCells rest)

private def markedBoolPayloadCells
    (w : Word Bool) : List (Option Bool) :=
  markedCellsCodeCells (w.map some)

private def markedBoolWordCells
    (w : Word Bool) : List (Option Bool) :=
  List.append (markedLengthTickPrefix w.length)
    (List.append (codeSymbolCells MachineCodeSymbol.done)
      (markedBoolPayloadCells w))

private def consumedBoolWordCells
    (w : Word Bool) : List (Option Bool) :=
  List.append (consumedLengthTickPrefix w.length)
    (List.append (codeSymbolCells MachineCodeSymbol.done)
      (markedBoolPayloadCells w))

private theorem repeatedCells_append
    (chunk : List (Option Bool)) (n : Nat)
    (tail : List (Option Bool)) :
    List.append (repeatedCells chunk n) tail =
      match n with
      | 0 => tail
      | k + 1 =>
          List.append chunk
            (List.append (repeatedCells chunk k) tail) := by
  cases n <;> simp [repeatedCells, List.append_assoc]

private theorem repeatedCells_succ_right
    (chunk : List (Option Bool)) (n : Nat) :
    repeatedCells chunk (n + 1) =
      List.append (repeatedCells chunk n) chunk := by
  induction n with
  | zero =>
      simp [repeatedCells]
  | succ n ih =>
      change
        List.append chunk (repeatedCells chunk (n + 1)) =
          List.append (List.append chunk (repeatedCells chunk n))
            chunk
      rw [ih]
      simp [List.append_assoc]

private theorem repeatedCells_length
    (chunk : List (Option Bool)) (n : Nat) :
    (repeatedCells chunk n).length = chunk.length * n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change (List.append chunk (repeatedCells chunk n)).length =
        chunk.length * (n + 1)
      simp [List.length_append, ih]
      rw [Nat.mul_succ]
      omega

private theorem repeatedCells_reverse
    (chunk : List (Option Bool)) (n : Nat) :
    (repeatedCells chunk n).reverse =
      repeatedCells chunk.reverse n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        (List.append chunk (repeatedCells chunk n)).reverse =
          repeatedCells chunk.reverse (n + 1)
      simp [List.reverse_append, ih, repeatedCells_succ_right]

private theorem natCodeCells_eq_tick_prefix_done
    (n : Nat) :
    natCodeCells n =
      List.append
        (repeatedCells
          (codeSymbolCells MachineCodeSymbol.tick) n)
        (codeSymbolCells MachineCodeSymbol.done) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        List.append
            (codeSymbolCells MachineCodeSymbol.tick)
            (natCodeCells n) =
          List.append
            (codeSymbolCells MachineCodeSymbol.tick)
            (List.append
              (repeatedCells
                (codeSymbolCells MachineCodeSymbol.tick) n)
              (codeSymbolCells MachineCodeSymbol.done))
      rw [ih]

private theorem markedCellCodeCells_restore
    (cell : Option Bool) :
    markedCellCodeCells cell =
      match cell with
      | none => cellCodeCells none
      | some false => [none, some true, some false, some true]
      | some true => [none, some true, some true, some false] := by
  cases cell with
  | none =>
      rfl
  | some b =>
      cases b <;> rfl

private theorem codeCells_replicate_tick
    (n : Nat) :
    codeCells (List.replicate n MachineCodeSymbol.tick) =
      repeatedCells
        (codeSymbolCells MachineCodeSymbol.tick) n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        List.append (codeSymbolCells MachineCodeSymbol.tick)
            (codeCells (List.replicate n MachineCodeSymbol.tick)) =
          List.append (codeSymbolCells MachineCodeSymbol.tick)
            (repeatedCells
              (codeSymbolCells MachineCodeSymbol.tick) n)
      rw [ih]

private theorem cellsCodeCells_append
    (left right : List (Option Bool)) :
    cellsCodeCells (List.append left right) =
      List.append (cellsCodeCells left)
        (cellsCodeCells right) := by
  induction left with
  | nil =>
      rfl
  | cons cell rest ih =>
      change
        List.append (cellCodeCells cell)
            (cellsCodeCells (List.append rest right)) =
          List.append
            (List.append (cellCodeCells cell)
              (cellsCodeCells rest))
            (cellsCodeCells right)
      rw [ih]
      simp [List.append_assoc]

@[simp] private theorem boolPayloadCells_append
    (left right : Word Bool) :
    boolPayloadCells (List.append left right) =
      List.append (boolPayloadCells left)
        (boolPayloadCells right) := by
  unfold boolPayloadCells
  have hmap :
      List.map some (List.append left right) =
        List.append (List.map some left) (List.map some right) := by
    simp
  rw [hmap]
  exact cellsCodeCells_append (left.map some) (right.map some)

private theorem markedCellsCodeCells_append
    (left right : List (Option Bool)) :
    markedCellsCodeCells (List.append left right) =
      List.append (markedCellsCodeCells left)
        (markedCellsCodeCells right) := by
  induction left with
  | nil =>
      rfl
  | cons cell rest ih =>
      change
        List.append (markedCellCodeCells cell)
            (markedCellsCodeCells (List.append rest right)) =
          List.append
            (List.append (markedCellCodeCells cell)
              (markedCellsCodeCells rest))
            (markedCellsCodeCells right)
      rw [ih]
      simp [List.append_assoc]

@[simp] private theorem markedBoolPayloadCells_append
    (left right : Word Bool) :
    markedBoolPayloadCells (List.append left right) =
      List.append (markedBoolPayloadCells left)
        (markedBoolPayloadCells right) := by
  unfold markedBoolPayloadCells
  have hmap :
      List.map some (List.append left right) =
        List.append (List.map some left) (List.map some right) := by
    simp
  rw [hmap]
  exact
    markedCellsCodeCells_append
      (left.map some) (right.map some)

@[simp] private theorem markedBoolPayloadCells_append_false
    (marked : Word Bool) :
    markedBoolPayloadCells (List.append marked [false]) =
      List.append (markedBoolPayloadCells marked)
        (markedCellCodeCells (some false)) := by
  simpa [markedBoolPayloadCells,
    markedCellsCodeCells] using
    markedBoolPayloadCells_append marked ([false] : Word Bool)

@[simp] private theorem markedBoolPayloadCells_append_true
    (marked : Word Bool) :
    markedBoolPayloadCells (List.append marked [true]) =
      List.append (markedBoolPayloadCells marked)
        (markedCellCodeCells (some true)) := by
  simpa [markedBoolPayloadCells,
    markedCellsCodeCells] using
    markedBoolPayloadCells_append marked ([true] : Word Bool)

private def WriteTransitionPrefixDescription :
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

private theorem writeTransitionPrefixDescription_wellFormed :
    WriteTransitionPrefixDescription.WellFormed := by
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · intro t ht
    exact transition_wellFormed_of_all
      (l := WriteTransitionPrefixDescription.transitions)
      (stateCount :=
        WriteTransitionPrefixDescription.stateCount)
      (by
        native_decide) t ht
  · intro t u ht hu hkey
    exact transition_deterministic_of_all
      (l := WriteTransitionPrefixDescription.transitions)
      (by
        native_decide) t u ht hu hkey

private theorem writeTransitionPrefixDescription_haltTransitionFree :
    WriteTransitionPrefixDescription.HaltTransitionFree := by
  intro t ht
  exact transition_notFrom_of_all
    (l := WriteTransitionPrefixDescription.transitions)
    (state := WriteTransitionPrefixDescription.halt)
    (by
      native_decide) t ht

private theorem writeTransitionPrefixDescription_subroutineReady :
    WriteTransitionPrefixDescription.SubroutineReady :=
  ⟨writeTransitionPrefixDescription_wellFormed,
    writeTransitionPrefixDescription_haltTransitionFree⟩

private theorem writeTransitionPrefixDescription_run
    (b : Bool) (rest : List (Option Bool)) :
    WriteTransitionPrefixDescription.runConfig 5
        (config 0 [] (some b :: rest)) =
      config 5 [some false]
        (List.append [some false, some false, some true]
          (some b :: rest)) := by
  cases b <;>
    simp [WriteTransitionPrefixDescription,
      config, tapeAtCells,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft, Tape.moveRight]

private def WriteMarkedTransitionPrefixDescription :
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

private theorem writeMarkedTransitionPrefixDescription_wellFormed :
    WriteMarkedTransitionPrefixDescription.WellFormed := by
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · intro t ht
    exact transition_wellFormed_of_all
      (l := WriteMarkedTransitionPrefixDescription.transitions)
      (stateCount :=
        WriteMarkedTransitionPrefixDescription.stateCount)
      (by
        native_decide) t ht
  · intro t u ht hu hkey
    exact transition_deterministic_of_all
      (l := WriteMarkedTransitionPrefixDescription.transitions)
      (by
        native_decide) t u ht hu hkey

private theorem writeMarkedTransitionPrefixDescription_haltTransitionFree :
    WriteMarkedTransitionPrefixDescription.HaltTransitionFree := by
  intro t ht
  exact transition_notFrom_of_all
    (l := WriteMarkedTransitionPrefixDescription.transitions)
    (state := WriteMarkedTransitionPrefixDescription.halt)
    (by
      native_decide) t ht

private theorem writeMarkedTransitionPrefixDescription_subroutineReady :
    WriteMarkedTransitionPrefixDescription.SubroutineReady :=
  ⟨writeMarkedTransitionPrefixDescription_wellFormed,
    writeMarkedTransitionPrefixDescription_haltTransitionFree⟩

private theorem writeMarkedTransitionPrefixDescription_run
    (b : Bool) (rest : List (Option Bool)) :
    WriteMarkedTransitionPrefixDescription.runConfig 5
        (config 0 [] (some b :: rest)) =
      config 5 [some false]
        (List.append [none, some false, some true]
          (some b :: rest)) := by
  cases b <;>
    simp [WriteMarkedTransitionPrefixDescription,
      config, tapeAtCells,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft, Tape.moveRight]

private def appendRightLastTape
    (leftRev : Word Bool) (b0 b1 b2 b3 : Bool) : Tape Bool :=
  { left := (List.append [b2, b1, b0] leftRev).map some
    head := some b3
    right := [] }

private def AppendFixedFourBitsLastDescription
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

private theorem appendFixedFourBitsLastDescription_wellFormed
    (b0 b1 b2 b3 : Bool) :
    (AppendFixedFourBitsLastDescription b0 b1 b2 b3).WellFormed := by
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
        (AppendFixedFourBitsLastDescription
          b0 b1 b2 b3).transitions)
      (stateCount :=
        (AppendFixedFourBitsLastDescription
          b0 b1 b2 b3).stateCount)
      (by
        cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
          native_decide) t ht
  · intro t u ht hu hkey
    exact transition_deterministic_of_all
      (l :=
        (AppendFixedFourBitsLastDescription
          b0 b1 b2 b3).transitions)
      (by
        cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
          native_decide) t u ht hu hkey

private theorem appendFixedFourBitsLastDescription_haltTransitionFree
    (b0 b1 b2 b3 : Bool) :
    (AppendFixedFourBitsLastDescription
      b0 b1 b2 b3).HaltTransitionFree := by
  intro t ht
  exact transition_notFrom_of_all
    (l :=
      (AppendFixedFourBitsLastDescription
        b0 b1 b2 b3).transitions)
    (state :=
      (AppendFixedFourBitsLastDescription
        b0 b1 b2 b3).halt)
    (by
      cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
        native_decide) t ht

private theorem appendFixedFourBitsLastDescription_step_scan_nonempty
    (b0 b1 b2 b3 : Bool)
    (leftRev : Word Bool) (b : Bool) (rest : Word Bool) :
    (AppendFixedFourBitsLastDescription b0 b1 b2 b3).stepConfig
        { state := 0
          tape := MachineDescription.appendRightScanTape leftRev (b :: rest) } =
      some
        { state := 0
          tape := MachineDescription.appendRightScanTape
            (b :: leftRev) rest } := by
  cases b <;>
    cases rest <;>
      simp [AppendFixedFourBitsLastDescription,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition, MachineDescription.Matches,
        MachineDescription.transition,
        MachineDescription.appendRightScanTape, Tape.read, Tape.write,
        Tape.move, Tape.moveRight]

private theorem appendFixedFourBitsLastDescription_run_scan
    (b0 b1 b2 b3 : Bool)
    (leftRev remaining : Word Bool) :
    (AppendFixedFourBitsLastDescription b0 b1 b2 b3).runConfig
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
        appendFixedFourBitsLastDescription_step_scan_nonempty,
        ih, List.append_assoc]

private theorem appendFixedFourBitsLastDescription_run_write
    (b0 b1 b2 b3 : Bool) (leftRev : Word Bool) :
    (AppendFixedFourBitsLastDescription b0 b1 b2 b3).runConfig 5
        { state := 0
          tape := MachineDescription.appendRightScanTape leftRev [] } =
      { state := 5
        tape := appendRightLastTape leftRev b0 b1 b2 b3 } := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    simp [AppendFixedFourBitsLastDescription,
      appendRightLastTape,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition,
      MachineDescription.appendRightScanTape, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft, Tape.moveRight]

private theorem appendFixedFourBitsLastDescription_run_halt
    (b0 b1 b2 b3 : Bool) (w : Word Bool) :
    (AppendFixedFourBitsLastDescription b0 b1 b2 b3).runConfig
        (w.length + 5)
        ((AppendFixedFourBitsLastDescription b0 b1 b2 b3).initial w) =
      { state := 5
        tape := appendRightLastTape w.reverse b0 b1 b2 b3 } := by
  rw [MachineDescription.runConfig_add]
  have hscan :
      (AppendFixedFourBitsLastDescription b0 b1 b2 b3).runConfig
          w.length
          ((AppendFixedFourBitsLastDescription
            b0 b1 b2 b3).initial w) =
        { state := 0
          tape := MachineDescription.appendRightScanTape w.reverse [] } := by
    simpa [MachineDescription.initial,
      AppendFixedFourBitsLastDescription,
      MachineDescription.appendRightScanTape_nil_eq_input] using
      appendFixedFourBitsLastDescription_run_scan
        b0 b1 b2 b3 [] w
  rw [hscan]
  exact appendFixedFourBitsLastDescription_run_write
    b0 b1 b2 b3 w.reverse

private def appendScanTapeAtCells
    (leftRev : List (Option Bool)) (remaining : Word Bool) :
    Tape Bool :=
  match remaining with
  | [] => { left := leftRev, head := none, right := [] }
  | b :: rest => { left := leftRev, head := some b, right := rest.map some }

private def appendRightLastTapeAtCells
    (leftRev : List (Option Bool)) (b0 b1 b2 b3 : Bool) :
    Tape Bool :=
  { left :=
      List.append [some b2, some b1, some b0] leftRev
    head := some b3
    right := [] }

private theorem appendScanTapeAtCells_of_bits
    (leftRev remaining : Word Bool) :
    appendScanTapeAtCells (leftRev.map some) remaining =
      MachineDescription.appendRightScanTape leftRev remaining := by
  cases remaining <;> rfl

private theorem appendRightLastTapeAtCells_of_bits
    (leftRev : Word Bool) (b0 b1 b2 b3 : Bool) :
    appendRightLastTapeAtCells
        (leftRev.map some) b0 b1 b2 b3 =
      appendRightLastTape leftRev b0 b1 b2 b3 := by
  simp [appendRightLastTapeAtCells,
    appendRightLastTape]

private theorem appendFixedFourBitsLastDescription_step_scan_nonempty_atCells
    (b0 b1 b2 b3 : Bool)
    (leftRev : List (Option Bool)) (b : Bool) (rest : Word Bool) :
    (AppendFixedFourBitsLastDescription b0 b1 b2 b3).stepConfig
        { state := 0
          tape := appendScanTapeAtCells leftRev (b :: rest) } =
      some
        { state := 0
          tape := appendScanTapeAtCells
            (some b :: leftRev) rest } := by
  cases b <;>
    cases rest <;>
      simp [AppendFixedFourBitsLastDescription,
        appendScanTapeAtCells,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition, MachineDescription.Matches,
        MachineDescription.transition, Tape.read, Tape.write,
        Tape.move, Tape.moveRight]

private theorem appendFixedFourBitsLastDescription_run_scan_atCells
    (b0 b1 b2 b3 : Bool)
    (leftRev : List (Option Bool)) (remaining : Word Bool) :
    (AppendFixedFourBitsLastDescription b0 b1 b2 b3).runConfig
        remaining.length
        { state := 0
          tape := appendScanTapeAtCells leftRev remaining } =
      { state := 0
        tape :=
          appendScanTapeAtCells
            (List.append (remaining.reverse.map some) leftRev) [] } := by
  induction remaining generalizing leftRev with
  | nil =>
      simp [MachineDescription.runConfig]
  | cons b rest ih =>
      simp [MachineDescription.runConfig,
        appendFixedFourBitsLastDescription_step_scan_nonempty_atCells,
        ih, List.append_assoc]

private theorem appendFixedFourBitsLastDescription_run_write_atCells
    (b0 b1 b2 b3 : Bool) (leftRev : List (Option Bool)) :
    (AppendFixedFourBitsLastDescription b0 b1 b2 b3).runConfig 5
        { state := 0
          tape := appendScanTapeAtCells leftRev [] } =
      { state := 5
        tape :=
          appendRightLastTapeAtCells
            leftRev b0 b1 b2 b3 } := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    simp [AppendFixedFourBitsLastDescription,
      appendScanTapeAtCells,
      appendRightLastTapeAtCells,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft, Tape.moveRight]

private theorem appendFixedFourBitsLastDescription_run_from_scan_atCells
    (b0 b1 b2 b3 : Bool)
    (leftRev : List (Option Bool)) (remaining : Word Bool) :
    (AppendFixedFourBitsLastDescription b0 b1 b2 b3).runConfig
        (remaining.length + 5)
        { state := 0
          tape := appendScanTapeAtCells leftRev remaining } =
      { state := 5
        tape :=
          appendRightLastTapeAtCells
            (List.append (remaining.reverse.map some) leftRev)
            b0 b1 b2 b3 } := by
  rw [MachineDescription.runConfig_add]
  rw [appendFixedFourBitsLastDescription_run_scan_atCells]
  exact appendFixedFourBitsLastDescription_run_write_atCells
    b0 b1 b2 b3 _

private theorem writeMarkedTransitionPrefixDescription_handoff_to_append
    (b : Bool) (rest : Word Bool) :
    Tape.move Direction.right
        (tapeAtCells [some false]
          (List.append [none, some false, some true]
            (some b :: rest.map some))) =
      appendScanTapeAtCells
        [none, some false] (false :: true :: b :: rest) := by
  cases b <;>
    cases rest <;>
      simp [tapeAtCells, appendScanTapeAtCells,
        Tape.move, Tape.moveRight]

private def AppendCodeSymbolLastDescription
    (symbol : MachineCodeSymbol) : MachineDescription :=
  match MachineDescription.encodeCodeSymbolAsInput symbol with
  | [b0, b1, b2, b3] =>
      AppendFixedFourBitsLastDescription b0 b1 b2 b3
  | _ => MachineDescription.ExactIdentityDescription

private def appendCodeSymbolLastTape
    (leftRev : Word Bool) (symbol : MachineCodeSymbol) : Tape Bool :=
  match MachineDescription.encodeCodeSymbolAsInput symbol with
  | [b0, b1, b2, b3] =>
      appendRightLastTape leftRev b0 b1 b2 b3
  | _ => Tape.input leftRev.reverse

private theorem appendCodeSymbolLastDescription_start
    (symbol : MachineCodeSymbol) :
    (AppendCodeSymbolLastDescription symbol).start = 0 := by
  cases symbol <;> rfl

private theorem appendCodeSymbolLastDescription_halt
    (symbol : MachineCodeSymbol) :
    (AppendCodeSymbolLastDescription symbol).halt = 5 := by
  cases symbol <;> rfl

private theorem appendCodeSymbolLastDescription_wellFormed
    (symbol : MachineCodeSymbol) :
    (AppendCodeSymbolLastDescription symbol).WellFormed := by
  cases symbol <;>
    exact appendFixedFourBitsLastDescription_wellFormed _ _ _ _

private theorem appendCodeSymbolLastDescription_haltTransitionFree
    (symbol : MachineCodeSymbol) :
    (AppendCodeSymbolLastDescription
      symbol).HaltTransitionFree := by
  cases symbol <;>
    exact
      appendFixedFourBitsLastDescription_haltTransitionFree
        _ _ _ _

private theorem appendCodeSymbolLastDescription_run_from_scan
    (symbol : MachineCodeSymbol)
    (leftRev remaining : Word Bool) :
    (AppendCodeSymbolLastDescription symbol).runConfig
        (remaining.length + 5)
        { state := 0
          tape := MachineDescription.appendRightScanTape leftRev remaining } =
      { state := 5
        tape :=
          appendCodeSymbolLastTape
            (List.append remaining.reverse leftRev) symbol } := by
  cases symbol <;>
    rw [MachineDescription.runConfig_add] <;>
    simp [AppendCodeSymbolLastDescription,
      appendCodeSymbolLastTape,
      MachineDescription.encodeCodeSymbolAsInput,
      appendFixedFourBitsLastDescription_run_scan,
      appendFixedFourBitsLastDescription_run_write]

private theorem appendCodeSymbolLastDescription_run_halt
    (symbol : MachineCodeSymbol) (w : Word Bool) :
    (AppendCodeSymbolLastDescription symbol).runConfig
        (w.length + 5)
        ((AppendCodeSymbolLastDescription symbol).initial w) =
      { state := 5
        tape := appendCodeSymbolLastTape w.reverse symbol } := by
  cases symbol <;>
    simpa [AppendCodeSymbolLastDescription,
      appendCodeSymbolLastTape,
      MachineDescription.encodeCodeSymbolAsInput] using
      appendFixedFourBitsLastDescription_run_halt
        _ _ _ _ w

private theorem appendCodeSymbolLastTape_move_right
    (leftRev : Word Bool) (symbol : MachineCodeSymbol) :
    Tape.move Direction.right
        (appendCodeSymbolLastTape leftRev symbol) =
      MachineDescription.appendRightScanTape
        (List.append
          (MachineDescription.encodeCodeSymbolAsInput symbol).reverse
          leftRev) [] := by
  cases symbol <;>
    simp [appendCodeSymbolLastTape,
      appendRightLastTape,
      MachineDescription.encodeCodeSymbolAsInput,
      MachineDescription.appendRightScanTape, Tape.move, Tape.moveRight]

private theorem appendCodeSymbolLastDescription_haltsWithTape
    (symbol : MachineCodeSymbol) (w : Word Bool) :
    (AppendCodeSymbolLastDescription symbol).HaltsWithTape
        w (appendCodeSymbolLastTape w.reverse symbol) := by
  exists w.length + 5
  constructor
  · rw [appendCodeSymbolLastDescription_run_halt]
    cases symbol <;> rfl
  · rw [appendCodeSymbolLastDescription_run_halt]

private def AppendCodeWordLastDescription :
    Word MachineCodeSymbol -> MachineDescription
  | [] => MachineDescription.ExactIdentityDescription
  | symbol :: [] => AppendCodeSymbolLastDescription symbol
  | symbol :: next :: rest =>
      MachineDescription.seqSubroutine
        (AppendCodeSymbolLastDescription symbol)
        (AppendCodeWordLastDescription (next :: rest))
        Direction.right

private def appendCodeWordLastTape
    (leftRev : Word Bool) :
    Word MachineCodeSymbol -> Tape Bool
  | [] => MachineDescription.appendRightScanTape leftRev []
  | symbol :: [] => appendCodeSymbolLastTape leftRev symbol
  | symbol :: next :: rest =>
      appendCodeWordLastTape
        (List.append
          (MachineDescription.encodeCodeSymbolAsInput symbol).reverse
          leftRev)
        (next :: rest)

private theorem appendCodeSymbolLastDescription_subroutineReady
    (symbol : MachineCodeSymbol) :
    (AppendCodeSymbolLastDescription symbol).SubroutineReady :=
  ⟨appendCodeSymbolLastDescription_wellFormed symbol,
    appendCodeSymbolLastDescription_haltTransitionFree symbol⟩

private theorem appendCodeWordLastDescription_subroutineReady :
    forall code : Word MachineCodeSymbol,
      code ≠ [] ->
        (AppendCodeWordLastDescription code).SubroutineReady
  | [], h => False.elim (h rfl)
  | symbol :: [], _ =>
      appendCodeSymbolLastDescription_subroutineReady symbol
  | symbol :: next :: rest, _ =>
      MachineDescription.seqSubroutine_subroutineReady
        (appendCodeSymbolLastDescription_subroutineReady symbol)
        (appendCodeWordLastDescription_subroutineReady
          (next :: rest) (by intro h; cases h))

private theorem appendCodeWordLastDescription_run_from_scan :
    forall code : Word MachineCodeSymbol,
      code ≠ [] ->
        forall leftRev remaining : Word Bool,
          exists n : Nat,
            (AppendCodeWordLastDescription code).runConfig n
                { state := (AppendCodeWordLastDescription code).start
                  tape :=
                    MachineDescription.appendRightScanTape
                      leftRev remaining } =
              { state := (AppendCodeWordLastDescription code).halt
                tape :=
                  appendCodeWordLastTape
                    (List.append remaining.reverse leftRev) code }
  | [], h => False.elim (h rfl)
  | symbol :: [], _ => by
      intro leftRev remaining
      refine ⟨remaining.length + 5, ?_⟩
      simpa [AppendCodeWordLastDescription,
        appendCodeWordLastTape,
        appendCodeSymbolLastDescription_start,
        appendCodeSymbolLastDescription_halt] using
        appendCodeSymbolLastDescription_run_from_scan
          symbol leftRev remaining
  | symbol :: next :: rest, _ => by
      intro leftRev remaining
      let A := AppendCodeSymbolLastDescription symbol
      let B := AppendCodeWordLastDescription (next :: rest)
      let Tmid :=
        appendCodeSymbolLastTape
          (List.append remaining.reverse leftRev) symbol
      let leftAfterSymbol :=
        List.append
          (MachineDescription.encodeCodeSymbolAsInput symbol).reverse
          (List.append remaining.reverse leftRev)
      have hAready : A.SubroutineReady := by
        exact appendCodeSymbolLastDescription_subroutineReady symbol
      have hBready : B.SubroutineReady := by
        exact
          appendCodeWordLastDescription_subroutineReady
            (next :: rest) (by intro h; cases h)
      have hArun :
          A.runConfig (remaining.length + 5)
              { state := A.start
                tape :=
                  MachineDescription.appendRightScanTape leftRev remaining } =
            { state := A.halt, tape := Tmid } := by
        simpa [A, Tmid,
          appendCodeSymbolLastDescription_start,
          appendCodeSymbolLastDescription_halt] using
          appendCodeSymbolLastDescription_run_from_scan
            symbol leftRev remaining
      have hBReach :
          exists nB : Nat,
            B.runConfig nB
                { state := B.start
                  tape := Tape.move Direction.right Tmid } =
              { state := B.halt
                tape :=
                  appendCodeWordLastTape
                    leftAfterSymbol (next :: rest) } := by
        rcases
            appendCodeWordLastDescription_run_from_scan
              (next :: rest) (by intro h; cases h)
              leftAfterSymbol ([] : Word Bool) with
          ⟨nB, hB⟩
        refine ⟨nB, ?_⟩
        simpa [B, Tmid, leftAfterSymbol,
          appendCodeSymbolLastTape_move_right] using hB
      rcases
          MachineDescription.seqSubroutine_reaches_of_runConfig_eq
            (A := A) (B := B) (handoffMove := Direction.right)
            hAready hBready hArun hBReach with
        ⟨n, hn⟩
      refine ⟨n, ?_⟩
      simpa [AppendCodeWordLastDescription,
        appendCodeWordLastTape, A, B, Tmid, leftAfterSymbol] using hn

private theorem appendCodeWordLastDescription_run_halt
    (code : Word MachineCodeSymbol) (hcode : code ≠ [])
    (w : Word Bool) :
    exists n : Nat,
      (AppendCodeWordLastDescription code).runConfig n
          ((AppendCodeWordLastDescription code).initial w) =
        { state := (AppendCodeWordLastDescription code).halt
          tape := appendCodeWordLastTape w.reverse code } := by
  rcases
      appendCodeWordLastDescription_run_from_scan
        code hcode ([] : Word Bool) w with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [MachineDescription.initial,
    MachineDescription.appendRightScanTape_nil_eq_input] using hn

private theorem appendCodeWordLastDescription_haltsWithTape
    (code : Word MachineCodeSymbol) (hcode : code ≠ [])
    (w : Word Bool) :
    (AppendCodeWordLastDescription code).HaltsWithTape
      w (appendCodeWordLastTape w.reverse code) := by
  rcases appendCodeWordLastDescription_run_halt
      code hcode w with
    ⟨n, hn⟩
  exact ⟨n, by
    constructor
    · simpa [MachineDescription.HaltsWithTapeIn] using
        congrArg MachineDescription.Configuration.state hn
    · simpa [MachineDescription.HaltsWithTapeIn] using
        congrArg MachineDescription.Configuration.tape hn⟩

private def appendCodeSymbolLastTapeAtCells
    (leftRev : List (Option Bool))
    (symbol : MachineCodeSymbol) : Tape Bool :=
  match MachineDescription.encodeCodeSymbolAsInput symbol with
  | [b0, b1, b2, b3] =>
      appendRightLastTapeAtCells leftRev b0 b1 b2 b3
  | _ => appendScanTapeAtCells leftRev []

private theorem appendCodeSymbolLastTapeAtCells_of_bits
    (leftRev : Word Bool) (symbol : MachineCodeSymbol) :
    appendCodeSymbolLastTapeAtCells
        (leftRev.map some) symbol =
      appendCodeSymbolLastTape leftRev symbol := by
  cases symbol <;>
    simp [appendCodeSymbolLastTapeAtCells,
      appendCodeSymbolLastTape,
      appendRightLastTapeAtCells_of_bits,
      MachineDescription.encodeCodeSymbolAsInput]

private theorem appendCodeSymbolLastDescription_run_from_scan_atCells
    (symbol : MachineCodeSymbol)
    (leftRev : List (Option Bool)) (remaining : Word Bool) :
    (AppendCodeSymbolLastDescription symbol).runConfig
        (remaining.length + 5)
        { state := 0
          tape := appendScanTapeAtCells leftRev remaining } =
      { state := 5
        tape :=
          appendCodeSymbolLastTapeAtCells
            (List.append (remaining.reverse.map some) leftRev) symbol } := by
  cases symbol <;>
    simpa [AppendCodeSymbolLastDescription,
      appendCodeSymbolLastTapeAtCells,
      MachineDescription.encodeCodeSymbolAsInput] using
      appendFixedFourBitsLastDescription_run_from_scan_atCells
        _ _ _ _ leftRev remaining

private theorem appendCodeSymbolLastTapeAtCells_move_right
    (leftRev : List (Option Bool)) (symbol : MachineCodeSymbol) :
    Tape.move Direction.right
        (appendCodeSymbolLastTapeAtCells leftRev symbol) =
      appendScanTapeAtCells
        (List.append
          ((MachineDescription.encodeCodeSymbolAsInput symbol).reverse.map some)
          leftRev) [] := by
  cases symbol <;>
    simp [appendCodeSymbolLastTapeAtCells,
      appendRightLastTapeAtCells,
      appendScanTapeAtCells,
      MachineDescription.encodeCodeSymbolAsInput,
      Tape.move, Tape.moveRight]

private def appendCodeWordLastTapeAtCells
    (leftRev : List (Option Bool)) :
    Word MachineCodeSymbol -> Tape Bool
  | [] => appendScanTapeAtCells leftRev []
  | symbol :: [] => appendCodeSymbolLastTapeAtCells leftRev symbol
  | symbol :: next :: rest =>
      appendCodeWordLastTapeAtCells
        (List.append
          ((MachineDescription.encodeCodeSymbolAsInput symbol).reverse.map some)
          leftRev)
        (next :: rest)

private theorem appendCodeWordLastTapeAtCells_of_bits :
    forall code : Word MachineCodeSymbol,
    forall leftRev : Word Bool,
      appendCodeWordLastTapeAtCells
          (leftRev.map some) code =
        appendCodeWordLastTape leftRev code
  | [], leftRev => by
      simp [appendCodeWordLastTapeAtCells,
        appendCodeWordLastTape,
        appendScanTapeAtCells_of_bits]
  | symbol :: [], leftRev => by
      simp [appendCodeWordLastTapeAtCells,
        appendCodeWordLastTape,
        appendCodeSymbolLastTapeAtCells_of_bits]
  | symbol :: next :: rest, leftRev => by
      change
        appendCodeWordLastTapeAtCells
            (List.append
              ((MachineDescription.encodeCodeSymbolAsInput symbol).reverse.map some)
              (leftRev.map some))
            (next :: rest) =
          appendCodeWordLastTape
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
        appendCodeWordLastTapeAtCells_of_bits
          (next :: rest)
          (List.append
            (MachineDescription.encodeCodeSymbolAsInput symbol).reverse
            leftRev)

private theorem appendCodeWordLastDescription_run_from_scan_atCells :
    forall code : Word MachineCodeSymbol,
      code ≠ [] ->
        forall leftRev : List (Option Bool),
        forall remaining : Word Bool,
          exists n : Nat,
            (AppendCodeWordLastDescription code).runConfig n
                { state := (AppendCodeWordLastDescription code).start
                  tape :=
                    appendScanTapeAtCells
                      leftRev remaining } =
              { state := (AppendCodeWordLastDescription code).halt
                tape :=
                  appendCodeWordLastTapeAtCells
                    (List.append (remaining.reverse.map some) leftRev) code }
  | [], h => False.elim (h rfl)
  | symbol :: [], _ => by
      intro leftRev remaining
      refine ⟨remaining.length + 5, ?_⟩
      simpa [AppendCodeWordLastDescription,
        appendCodeWordLastTapeAtCells,
        appendCodeSymbolLastDescription_start,
        appendCodeSymbolLastDescription_halt] using
        appendCodeSymbolLastDescription_run_from_scan_atCells
          symbol leftRev remaining
  | symbol :: next :: rest, _ => by
      intro leftRev remaining
      let A := AppendCodeSymbolLastDescription symbol
      let B := AppendCodeWordLastDescription (next :: rest)
      let Tmid :=
        appendCodeSymbolLastTapeAtCells
          (List.append (remaining.reverse.map some) leftRev) symbol
      let leftAfterSymbol :=
        List.append
          ((MachineDescription.encodeCodeSymbolAsInput symbol).reverse.map some)
          (List.append (remaining.reverse.map some) leftRev)
      have hAready : A.SubroutineReady := by
        exact appendCodeSymbolLastDescription_subroutineReady symbol
      have hBready : B.SubroutineReady := by
        exact
          appendCodeWordLastDescription_subroutineReady
            (next :: rest) (by intro h; cases h)
      have hArun :
          A.runConfig (remaining.length + 5)
              { state := A.start
                tape :=
                  appendScanTapeAtCells leftRev remaining } =
            { state := A.halt, tape := Tmid } := by
        simpa [A, Tmid,
          appendCodeSymbolLastDescription_start,
          appendCodeSymbolLastDescription_halt] using
          appendCodeSymbolLastDescription_run_from_scan_atCells
            symbol leftRev remaining
      have hBReach :
          exists nB : Nat,
            B.runConfig nB
                { state := B.start
                  tape := Tape.move Direction.right Tmid } =
              { state := B.halt
                tape :=
                  appendCodeWordLastTapeAtCells
                    leftAfterSymbol (next :: rest) } := by
        rcases
            appendCodeWordLastDescription_run_from_scan_atCells
              (next :: rest) (by intro h; cases h)
              leftAfterSymbol ([] : Word Bool) with
          ⟨nB, hB⟩
        refine ⟨nB, ?_⟩
        simpa [B, Tmid, leftAfterSymbol,
          appendCodeSymbolLastTapeAtCells_move_right] using hB
      rcases
          MachineDescription.seqSubroutine_reaches_of_runConfig_eq
            (A := A) (B := B) (handoffMove := Direction.right)
            hAready hBready hArun hBReach with
        ⟨n, hn⟩
      refine ⟨n, ?_⟩
      simpa [AppendCodeWordLastDescription,
        appendCodeWordLastTapeAtCells, A, B, Tmid,
        leftAfterSymbol] using hn

private def MarkedPrefixThenAppendCodeWordLastDescription
    (code : Word MachineCodeSymbol) : MachineDescription :=
  MachineDescription.seqSubroutine
    WriteMarkedTransitionPrefixDescription
    (AppendCodeWordLastDescription code)
    Direction.right

private theorem
    markedPrefixThenAppendCodeWordLastDescription_subroutineReady
    (code : Word MachineCodeSymbol) (hcode : code ≠ []) :
    (MarkedPrefixThenAppendCodeWordLastDescription
      code).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    writeMarkedTransitionPrefixDescription_subroutineReady
    (appendCodeWordLastDescription_subroutineReady code hcode)

private theorem markedPrefixThenAppendCodeWordLastDescription_run
    (code : Word MachineCodeSymbol) (hcode : code ≠ [])
    (b : Bool) (rest : Word Bool) :
    exists n : Nat,
      (MarkedPrefixThenAppendCodeWordLastDescription code).runConfig n
          ((MarkedPrefixThenAppendCodeWordLastDescription
            code).initial (b :: rest)) =
        { state :=
            (MarkedPrefixThenAppendCodeWordLastDescription code).halt
          tape :=
            appendCodeWordLastTapeAtCells
              (List.append
                ((false :: true :: b :: rest).reverse.map some)
                [none, some false])
              code } := by
  let A := WriteMarkedTransitionPrefixDescription
  let B := AppendCodeWordLastDescription code
  let Tmid :=
    tapeAtCells [some false]
      (List.append [none, some false, some true]
        (some b :: rest.map some))
  have hAready : A.SubroutineReady := by
    exact writeMarkedTransitionPrefixDescription_subroutineReady
  have hBready : B.SubroutineReady := by
    exact appendCodeWordLastDescription_subroutineReady code hcode
  have hArun :
      A.runConfig 5
          { state := A.start
            tape := Tape.input (b :: rest) } =
        { state := A.halt, tape := Tmid } := by
    simpa [A, Tmid, MachineDescription.initial,
      config, tapeAtCells, Tape.input] using
      writeMarkedTransitionPrefixDescription_run
        b (rest.map some)
  have hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start
              tape := Tape.move Direction.right Tmid } =
          { state := B.halt
            tape :=
              appendCodeWordLastTapeAtCells
                (List.append
                  ((false :: true :: b :: rest).reverse.map some)
                  [none, some false])
                code } := by
    rcases
        appendCodeWordLastDescription_run_from_scan_atCells
          code hcode [none, some false] (false :: true :: b :: rest) with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    simpa [B, Tmid,
      writeMarkedTransitionPrefixDescription_handoff_to_append] using hB
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.right)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [MarkedPrefixThenAppendCodeWordLastDescription,
    MachineDescription.initial, A, B] using hn

private theorem encodeNat_ne_nil (n : Nat) :
    MachineDescription.encodeNat n ≠ [] := by
  cases n <;> simp [MachineDescription.encodeNat]

private def AppendNatLastDescription
    (n : Nat) : MachineDescription :=
  AppendCodeWordLastDescription
    (MachineDescription.encodeNat n)

private def appendNatLastTape
    (leftRev : Word Bool) (n : Nat) : Tape Bool :=
  appendCodeWordLastTape leftRev
    (MachineDescription.encodeNat n)

private theorem appendNatLastDescription_subroutineReady
    (n : Nat) :
    (AppendNatLastDescription n).SubroutineReady :=
  appendCodeWordLastDescription_subroutineReady
    (MachineDescription.encodeNat n)
    (encodeNat_ne_nil n)

private theorem appendNatLastDescription_run_from_scan
    (n : Nat) (leftRev remaining : Word Bool) :
    exists steps : Nat,
      (AppendNatLastDescription n).runConfig steps
          { state := (AppendNatLastDescription n).start
            tape := MachineDescription.appendRightScanTape leftRev remaining } =
        { state := (AppendNatLastDescription n).halt
          tape :=
            appendNatLastTape
              (List.append remaining.reverse leftRev) n } := by
  simpa [AppendNatLastDescription,
    appendNatLastTape] using
    appendCodeWordLastDescription_run_from_scan
      (MachineDescription.encodeNat n)
      (encodeNat_ne_nil n)
      leftRev remaining

private theorem appendNatLastDescription_haltsWithTape
    (n : Nat) (w : Word Bool) :
    (AppendNatLastDescription n).HaltsWithTape
      w (appendNatLastTape w.reverse n) := by
  simpa [AppendNatLastDescription,
    appendNatLastTape] using
    appendCodeWordLastDescription_haltsWithTape
      (MachineDescription.encodeNat n)
      (encodeNat_ne_nil n)
      w

private def MarkedPrefixThenAppendNatLastDescription
    (n : Nat) : MachineDescription :=
  MarkedPrefixThenAppendCodeWordLastDescription
    (MachineDescription.encodeNat n)

private theorem
    markedPrefixThenAppendNatLastDescription_subroutineReady
    (n : Nat) :
    (MarkedPrefixThenAppendNatLastDescription
      n).SubroutineReady :=
  markedPrefixThenAppendCodeWordLastDescription_subroutineReady
    (MachineDescription.encodeNat n)
    (encodeNat_ne_nil n)

private theorem markedPrefixThenAppendNatLastDescription_run
    (n : Nat) (b : Bool) (rest : Word Bool) :
    exists steps : Nat,
      (MarkedPrefixThenAppendNatLastDescription n).runConfig steps
          ((MarkedPrefixThenAppendNatLastDescription
            n).initial (b :: rest)) =
        { state :=
            (MarkedPrefixThenAppendNatLastDescription n).halt
          tape :=
            appendCodeWordLastTapeAtCells
              (List.append
                ((false :: true :: b :: rest).reverse.map some)
                [none, some false])
              (MachineDescription.encodeNat n) } := by
  simpa [MarkedPrefixThenAppendNatLastDescription] using
    markedPrefixThenAppendCodeWordLastDescription_run
      (MachineDescription.encodeNat n)
      (encodeNat_ne_nil n)
      b rest

private def MarkTransitionSecondBitDescription :
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

private theorem markTransitionSecondBitDescription_wellFormed :
    MarkTransitionSecondBitDescription.WellFormed := by
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · intro t ht
    exact transition_wellFormed_of_all
      (l := MarkTransitionSecondBitDescription.transitions)
      (stateCount :=
        MarkTransitionSecondBitDescription.stateCount)
      (by
        native_decide) t ht
  · intro t u ht hu hkey
    exact transition_deterministic_of_all
      (l := MarkTransitionSecondBitDescription.transitions)
      (by
        native_decide) t u ht hu hkey

private theorem markTransitionSecondBitDescription_haltTransitionFree :
    MarkTransitionSecondBitDescription.HaltTransitionFree := by
  intro t ht
  exact transition_notFrom_of_all
    (l := MarkTransitionSecondBitDescription.transitions)
    (state := MarkTransitionSecondBitDescription.halt)
    (by
      native_decide) t ht

private theorem markTransitionSecondBitDescription_subroutineReady :
    MarkTransitionSecondBitDescription.SubroutineReady :=
  ⟨markTransitionSecondBitDescription_wellFormed,
    markTransitionSecondBitDescription_haltTransitionFree⟩

private theorem markTransitionSecondBitDescription_run
    (payload : Word Bool) :
    MarkTransitionSecondBitDescription.runConfig 2
        (config 0 [some false]
          (some false ::
            ((List.append [false, true] payload).map some))) =
      { state := MarkTransitionSecondBitDescription.halt
        tape :=
          tapeAtCells [some false]
            (none ::
              ((List.append [false, true] payload).map some)) } := by
  cases payload <;>
    simp [MarkTransitionSecondBitDescription,
      config, tapeAtCells,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft, Tape.moveRight]

private def TransitionPrefixedThenAppendCodeWordLastDescription
    (code : Word MachineCodeSymbol) : MachineDescription :=
  MachineDescription.seqSubroutine
    MarkTransitionSecondBitDescription
    (AppendCodeWordLastDescription code)
    Direction.right

private theorem
    transitionPrefixedThenAppendCodeWordLastDescription_subroutineReady
    (code : Word MachineCodeSymbol) (hcode : code ≠ []) :
    (TransitionPrefixedThenAppendCodeWordLastDescription
      code).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    markTransitionSecondBitDescription_subroutineReady
    (appendCodeWordLastDescription_subroutineReady code hcode)

private theorem
    transitionPrefixedThenAppendCodeWordLastDescription_run
    (code : Word MachineCodeSymbol) (hcode : code ≠ [])
    (payload : Word Bool) :
    exists steps : Nat,
      (TransitionPrefixedThenAppendCodeWordLastDescription
        code).runConfig steps
          { state :=
              (TransitionPrefixedThenAppendCodeWordLastDescription
                code).start
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append [false, true] payload).map some)) } =
        { state :=
            (TransitionPrefixedThenAppendCodeWordLastDescription
              code).halt
          tape :=
            appendCodeWordLastTapeAtCells
              (List.append
                ((false :: true :: payload).reverse.map some)
                [none, some false])
              code } := by
  let A := MarkTransitionSecondBitDescription
  let B := AppendCodeWordLastDescription code
  let Tmid :=
    tapeAtCells [some false]
      (none ::
        ((List.append [false, true] payload).map some))
  have hAready : A.SubroutineReady := by
    exact markTransitionSecondBitDescription_subroutineReady
  have hBready : B.SubroutineReady := by
    exact appendCodeWordLastDescription_subroutineReady code hcode
  have hArun :
      A.runConfig 2
          { state := A.start
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append [false, true] payload).map some)) } =
        { state := A.halt, tape := Tmid } := by
    simpa [A, Tmid, config] using
      markTransitionSecondBitDescription_run payload
  have hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start
              tape := Tape.move Direction.right Tmid } =
          { state := B.halt
            tape :=
              appendCodeWordLastTapeAtCells
                (List.append
                  ((false :: true :: payload).reverse.map some)
                  [none, some false])
                code } := by
    rcases
        appendCodeWordLastDescription_run_from_scan_atCells
          code hcode [none, some false] (false :: true :: payload) with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    simpa [B, Tmid, tapeAtCells,
      appendScanTapeAtCells, Tape.move, Tape.moveRight] using hB
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.right)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [TransitionPrefixedThenAppendCodeWordLastDescription,
    A, B] using hn

private def ReturnToCurrentMarkerDescription :
    MachineDescription where
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [ MachineDescription.transition
        0 (some false) (some false) Direction.left 0
    , MachineDescription.transition
        0 (some true) (some true) Direction.left 0
    , MachineDescription.transition
        0 none (some false) Direction.right 1
    ]

private theorem returnToCurrentMarkerDescription_wellFormed :
    ReturnToCurrentMarkerDescription.WellFormed := by
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · intro t ht
    exact transition_wellFormed_of_all
      (l := ReturnToCurrentMarkerDescription.transitions)
      (stateCount :=
        ReturnToCurrentMarkerDescription.stateCount)
      (by
        native_decide) t ht
  · intro t u ht hu hkey
    exact transition_deterministic_of_all
      (l := ReturnToCurrentMarkerDescription.transitions)
      (by
        native_decide) t u ht hu hkey

private theorem
    returnToCurrentMarkerDescription_haltTransitionFree :
    ReturnToCurrentMarkerDescription.HaltTransitionFree := by
  intro t ht
  exact transition_notFrom_of_all
    (l := ReturnToCurrentMarkerDescription.transitions)
    (state := ReturnToCurrentMarkerDescription.halt)
    (by
      native_decide) t ht

private theorem
    returnToCurrentMarkerDescription_subroutineReady :
    ReturnToCurrentMarkerDescription.SubroutineReady :=
  ⟨returnToCurrentMarkerDescription_wellFormed,
    returnToCurrentMarkerDescription_haltTransitionFree⟩

private theorem returnToCurrentMarkerDescription_step_scan
    (preRev : Word Bool) (leftBit current : Bool)
    (leftOfMarker right : List (Option Bool)) :
    ReturnToCurrentMarkerDescription.stepConfig
        (config 0
          (List.append
            (some leftBit :: preRev.map some)
            (none :: leftOfMarker))
          (some current :: right)) =
      some
        (config 0
          (List.append
            (preRev.map some)
            (none :: leftOfMarker))
          (some leftBit :: some current :: right)) := by
  cases leftBit <;> cases current <;>
    simp [ReturnToCurrentMarkerDescription,
      config, tapeAtCells,
      MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft]

private theorem returnToCurrentMarkerDescription_run
    (preRev : Word Bool) (current : Bool)
    (leftOfMarker right : List (Option Bool)) :
    ReturnToCurrentMarkerDescription.runConfig
        (preRev.length + 2)
        (config 0
          (List.append (preRev.map some) (none :: leftOfMarker))
          (some current :: right)) =
      config 1
        (some false :: leftOfMarker)
        (List.append (preRev.reverse.map some)
          (some current :: right)) := by
  induction preRev generalizing current right with
  | nil =>
      cases current <;>
        simp [ReturnToCurrentMarkerDescription,
          config, tapeAtCells,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read, Tape.write,
          Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons b rest ih =>
      simp only [List.map_cons, List.length_cons, List.reverse_cons]
      rw [show Nat.succ rest.length + 2 = (rest.length + 2) + 1 by omega]
      rw [MachineDescription.runConfig]
      rw [returnToCurrentMarkerDescription_step_scan]
      simpa [List.append_assoc] using ih b (some current :: right)

private theorem
    returnToCurrentMarkerDescription_run_after_append_four_atCells
    (pre : Word Bool) (leftOfMarker : List (Option Bool))
    (b0 b1 b2 b3 : Bool) :
    ReturnToCurrentMarkerDescription.runConfig
        (pre.length + 4)
        { state := ReturnToCurrentMarkerDescription.start
          tape :=
            Tape.move Direction.left
              (appendRightLastTapeAtCells
                (List.append (pre.reverse.map some)
                  (none :: leftOfMarker)) b0 b1 b2 b3) } =
      config
        ReturnToCurrentMarkerDescription.halt
        (some false :: leftOfMarker)
        ((List.append pre [b0, b1, b2, b3]).map some) := by
  simpa [appendRightLastTapeAtCells, config,
    Tape.move, Tape.moveLeft, List.append_assoc] using
    returnToCurrentMarkerDescription_run
      (List.append [b1, b0] pre.reverse) b2
      leftOfMarker [some b3]

private theorem
    returnToCurrentMarkerDescription_run_after_append_atCells :
    forall code : Word MachineCodeSymbol,
      code ≠ [] ->
        forall pre : Word Bool,
        forall leftOfMarker : List (Option Bool),
          exists steps : Nat,
            ReturnToCurrentMarkerDescription.runConfig steps
                { state := ReturnToCurrentMarkerDescription.start
                  tape :=
                    Tape.move Direction.left
                      (appendCodeWordLastTapeAtCells
                        (List.append (pre.reverse.map some)
                          (none :: leftOfMarker))
                        code) } =
              config
                ReturnToCurrentMarkerDescription.halt
                (some false :: leftOfMarker)
                ((List.append pre
                  (MachineDescription.encodeCodeWordAsInput code)).map some)
  | [], h => False.elim (h rfl)
  | symbol :: [], _ => by
      intro pre leftOfMarker
      cases symbol <;>
        refine ⟨pre.length + 4, ?_⟩ <;>
        simpa [appendCodeWordLastTapeAtCells,
          appendCodeSymbolLastTapeAtCells,
          appendRightLastTapeAtCells,
          MachineDescription.encodeCodeSymbolAsInput,
          MachineDescription.encodeCodeWordAsInput,
          Tape.move, Tape.moveLeft, List.append_assoc] using
          returnToCurrentMarkerDescription_run_after_append_four_atCells
            pre leftOfMarker _ _ _ _
  | symbol :: next :: rest, _ => by
      intro pre leftOfMarker
      let symbolBits := MachineDescription.encodeCodeSymbolAsInput symbol
      rcases
          returnToCurrentMarkerDescription_run_after_append_atCells
            (next :: rest) (by intro h; cases h)
            (List.append pre symbolBits) leftOfMarker with
        ⟨steps, hsteps⟩
      refine ⟨steps, ?_⟩
      have hleft :
          List.append (symbolBits.reverse.map some)
              (List.append (pre.reverse.map some)
                (none :: leftOfMarker)) =
            List.append
              ((List.append pre symbolBits).reverse.map some)
              (none :: leftOfMarker) := by
        simp [List.reverse_append, List.map_append, List.append_assoc]
      have hbits :
          List.append (List.append pre symbolBits)
              (MachineDescription.encodeCodeWordAsInput (next :: rest)) =
            List.append pre
              (MachineDescription.encodeCodeWordAsInput
                (symbol :: next :: rest)) := by
        simp [symbolBits,
          MachineDescription.encodeCodeWordAsInput, List.append_assoc]
      simpa [appendCodeWordLastTapeAtCells, symbolBits,
        hleft, hbits, MachineDescription.encodeCodeWordAsInput,
        List.map_append, List.append_assoc] using hsteps

private def AppendCodeWordReturnToCurrentMarkerDescription
    (code : Word MachineCodeSymbol) : MachineDescription :=
  MachineDescription.seqSubroutine
    (AppendCodeWordLastDescription code)
    ReturnToCurrentMarkerDescription
    Direction.left

private theorem
    appendCodeWordReturnToCurrentMarkerDescription_subroutineReady
    (code : Word MachineCodeSymbol) (hcode : code ≠ []) :
    (AppendCodeWordReturnToCurrentMarkerDescription
      code).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    (appendCodeWordLastDescription_subroutineReady code hcode)
    returnToCurrentMarkerDescription_subroutineReady

private theorem
    appendCodeWordReturnToCurrentMarkerDescription_run_from_scan
    (code : Word MachineCodeSymbol) (hcode : code ≠ [])
    (pre remaining : Word Bool)
    (leftOfMarker : List (Option Bool)) :
    exists steps : Nat,
      (AppendCodeWordReturnToCurrentMarkerDescription
        code).runConfig steps
          { state :=
              (AppendCodeWordReturnToCurrentMarkerDescription
                code).start
            tape :=
              appendScanTapeAtCells
                (List.append (pre.reverse.map some)
                  (none :: leftOfMarker))
                remaining } =
        config
          (AppendCodeWordReturnToCurrentMarkerDescription
            code).halt
          (some false :: leftOfMarker)
          ((List.append (List.append pre remaining)
            (MachineDescription.encodeCodeWordAsInput code)).map some) := by
  let A := AppendCodeWordLastDescription code
  let B := ReturnToCurrentMarkerDescription
  let preAll := List.append pre remaining
  let Tmid :=
    appendCodeWordLastTapeAtCells
      (List.append (remaining.reverse.map some)
        (List.append (pre.reverse.map some)
          (none :: leftOfMarker)))
      code
  have hAready : A.SubroutineReady := by
    exact appendCodeWordLastDescription_subroutineReady code hcode
  have hBready : B.SubroutineReady := by
    exact returnToCurrentMarkerDescription_subroutineReady
  rcases
      appendCodeWordLastDescription_run_from_scan_atCells
        code hcode
        (List.append (pre.reverse.map some) (none :: leftOfMarker))
        remaining with
    ⟨nA, hA⟩
  have hArun :
      A.runConfig nA
          { state := A.start
            tape :=
              appendScanTapeAtCells
                (List.append (pre.reverse.map some)
                  (none :: leftOfMarker))
                remaining } =
        { state := A.halt, tape := Tmid } := by
    simpa [A, Tmid] using hA
  have hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start
              tape := Tape.move Direction.left Tmid } =
          config B.halt
            (some false :: leftOfMarker)
            ((List.append preAll
              (MachineDescription.encodeCodeWordAsInput code)).map some) := by
    have hleft :
        List.append ((List.map some remaining).reverse)
            (List.append ((List.map some pre).reverse)
              (none :: leftOfMarker)) =
          List.append ((List.map some preAll).reverse)
            (none :: leftOfMarker) := by
      simp [preAll, List.reverse_append, List.map_append,
        List.append_assoc]
    rcases
        returnToCurrentMarkerDescription_run_after_append_atCells
          code hcode preAll leftOfMarker with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    have hstart :
        ({ state := B.start
           tape := Tape.move Direction.left Tmid } :
            MachineDescription.Configuration) =
          { state := B.start
            tape :=
              Tape.move Direction.left
                (appendCodeWordLastTapeAtCells
                  (List.append ((List.map some preAll).reverse)
                    (none :: leftOfMarker))
                  code) } := by
      simp [B, Tmid]
      exact
        congrArg
          (fun left =>
            Tape.move Direction.left
              (appendCodeWordLastTapeAtCells left code))
          hleft
    rw [hstart]
    simpa [B] using hB
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.left)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [AppendCodeWordReturnToCurrentMarkerDescription,
    A, B, preAll] using hn

private def RightCellsCopierStartDescription :
    MachineDescription where
  stateCount := 9
  start := 0
  halt := 8
  transitions :=
    [ MachineDescription.transition
        0 (some false) (some false) Direction.right 1
    , MachineDescription.transition
        1 (some false) none Direction.right 2
    , MachineDescription.transition
        2 (some false) (some false) Direction.right 3
    , MachineDescription.transition
        3 (some true) (some true) Direction.right 4
    , MachineDescription.transition
        4 (some false) (some false) Direction.right 5
    , MachineDescription.transition
        5 (some false) (some false) Direction.right 6
    , MachineDescription.transition
        6 (some true) (some true) Direction.right 7
    , MachineDescription.transition
        7 (some false) (some false) Direction.right 8
    ]

private theorem rightCellsCopierStartDescription_wellFormed :
    RightCellsCopierStartDescription.WellFormed := by
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · intro t ht
    exact transition_wellFormed_of_all
      (l := RightCellsCopierStartDescription.transitions)
      (stateCount :=
        RightCellsCopierStartDescription.stateCount)
      (by
        native_decide) t ht
  · intro t u ht hu hkey
    exact transition_deterministic_of_all
      (l := RightCellsCopierStartDescription.transitions)
      (by
        native_decide) t u ht hu hkey

private theorem
    rightCellsCopierStartDescription_haltTransitionFree :
    RightCellsCopierStartDescription.HaltTransitionFree := by
  intro t ht
  exact transition_notFrom_of_all
    (l := RightCellsCopierStartDescription.transitions)
    (state := RightCellsCopierStartDescription.halt)
    (by
      native_decide) t ht

private theorem
    rightCellsCopierStartDescription_subroutineReady :
    RightCellsCopierStartDescription.SubroutineReady :=
  ⟨rightCellsCopierStartDescription_wellFormed,
    rightCellsCopierStartDescription_haltTransitionFree⟩

private theorem rightCellsCopierStartDescription_run
    (tail : List (Option Bool)) :
    RightCellsCopierStartDescription.runConfig 8
        (config 0 []
          (List.append
            [some false, some false, some false, some true,
              some false, some false, some true, some false]
            tail)) =
      config 8
        [some false, some true, some false, some false,
          some true, some false, none, some false]
        tail := by
  cases tail <;>
    simp [RightCellsCopierStartDescription,
      config, tapeAtCells,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

private def InputTapeRightCellsDirectCopierDescription :
    MachineDescription where
  stateCount := 100
  start := 0
  halt := 99
  transitions :=
    [ -- Copy the residual unary length prefix.
      MachineDescription.transition
        0 (some false) none Direction.right 1
    , MachineDescription.transition
        1 (some false) (some false) Direction.right 2
    , MachineDescription.transition
        2 (some true) (some true) Direction.right 3
    , MachineDescription.transition
        3 (some false) (some false) Direction.right 20
    , MachineDescription.transition
        3 (some true) (some true) Direction.right 30

      -- In cell mode, stop when the next source symbol is a nat symbol.
    , MachineDescription.transition
        10 (some false) (some false) Direction.right 11
    , MachineDescription.transition
        11 (some false) (some false) Direction.left 80
    , MachineDescription.transition
        11 (some true) (some true) Direction.left 12
    , MachineDescription.transition
        12 (some false) none Direction.right 13
    , MachineDescription.transition
        13 (some true) (some true) Direction.right 14
    , MachineDescription.transition
        14 (some false) (some false) Direction.right 15
    , MachineDescription.transition
        14 (some true) (some true) Direction.right 18
    , MachineDescription.transition
        15 (some false) (some false) Direction.right 50
    , MachineDescription.transition
        15 (some true) (some true) Direction.right 60
    , MachineDescription.transition
        18 (some false) (some false) Direction.right 70

      -- Append a tick symbol, return to its temporary marker, and advance.
    , MachineDescription.transition
        20 (some false) (some false) Direction.right 20
    , MachineDescription.transition
        20 (some true) (some true) Direction.right 20
    , MachineDescription.transition
        20 none (some false) Direction.right 21
    , MachineDescription.transition
        21 none (some false) Direction.right 22
    , MachineDescription.transition
        22 none (some true) Direction.right 23
    , MachineDescription.transition
        23 none (some false) Direction.left 24
    , MachineDescription.transition
        24 (some false) (some false) Direction.left 24
    , MachineDescription.transition
        24 (some true) (some true) Direction.left 24
    , MachineDescription.transition
        24 none (some false) Direction.right 25
    , MachineDescription.transition
        25 (some false) (some false) Direction.right 26
    , MachineDescription.transition
        25 (some true) (some true) Direction.right 26
    , MachineDescription.transition
        26 (some false) (some false) Direction.right 27
    , MachineDescription.transition
        26 (some true) (some true) Direction.right 27
    , MachineDescription.transition
        27 (some false) (some false) Direction.right 0
    , MachineDescription.transition
        27 (some true) (some true) Direction.right 0

      -- Append the done symbol, return, then skip done plus the head cell.
    , MachineDescription.transition
        30 (some false) (some false) Direction.right 30
    , MachineDescription.transition
        30 (some true) (some true) Direction.right 30
    , MachineDescription.transition
        30 none (some false) Direction.right 31
    , MachineDescription.transition
        31 none (some false) Direction.right 32
    , MachineDescription.transition
        32 none (some true) Direction.right 33
    , MachineDescription.transition
        33 none (some true) Direction.left 34
    , MachineDescription.transition
        34 (some false) (some false) Direction.left 34
    , MachineDescription.transition
        34 (some true) (some true) Direction.left 34
    , MachineDescription.transition
        34 none (some false) Direction.right 35
    , MachineDescription.transition
        35 (some false) (some false) Direction.right 36
    , MachineDescription.transition
        35 (some true) (some true) Direction.right 36
    , MachineDescription.transition
        36 (some false) (some false) Direction.right 37
    , MachineDescription.transition
        36 (some true) (some true) Direction.right 37
    , MachineDescription.transition
        37 (some false) (some false) Direction.right 38
    , MachineDescription.transition
        37 (some true) (some true) Direction.right 38
    , MachineDescription.transition
        38 (some false) (some false) Direction.right 39
    , MachineDescription.transition
        38 (some true) (some true) Direction.right 39
    , MachineDescription.transition
        39 (some false) (some false) Direction.right 40
    , MachineDescription.transition
        39 (some true) (some true) Direction.right 40
    , MachineDescription.transition
        40 (some false) (some false) Direction.right 41
    , MachineDescription.transition
        40 (some true) (some true) Direction.right 41
    , MachineDescription.transition
        41 (some false) (some false) Direction.right 10
    , MachineDescription.transition
        41 (some true) (some true) Direction.right 10

      -- Append blank, zero, and one cell symbols from the remaining cells.
    , MachineDescription.transition
        50 (some false) (some false) Direction.right 50
    , MachineDescription.transition
        50 (some true) (some true) Direction.right 50
    , MachineDescription.transition
        50 none (some false) Direction.right 51
    , MachineDescription.transition
        51 none (some true) Direction.right 52
    , MachineDescription.transition
        52 none (some false) Direction.right 53
    , MachineDescription.transition
        53 none (some false) Direction.left 54
    , MachineDescription.transition
        54 (some false) (some false) Direction.left 54
    , MachineDescription.transition
        54 (some true) (some true) Direction.left 54
    , MachineDescription.transition
        54 none (some false) Direction.right 55
    , MachineDescription.transition
        55 (some false) (some false) Direction.right 56
    , MachineDescription.transition
        55 (some true) (some true) Direction.right 56
    , MachineDescription.transition
        56 (some false) (some false) Direction.right 57
    , MachineDescription.transition
        56 (some true) (some true) Direction.right 57
    , MachineDescription.transition
        57 (some false) (some false) Direction.right 10
    , MachineDescription.transition
        57 (some true) (some true) Direction.right 10

    , MachineDescription.transition
        60 (some false) (some false) Direction.right 60
    , MachineDescription.transition
        60 (some true) (some true) Direction.right 60
    , MachineDescription.transition
        60 none (some false) Direction.right 61
    , MachineDescription.transition
        61 none (some true) Direction.right 62
    , MachineDescription.transition
        62 none (some false) Direction.right 63
    , MachineDescription.transition
        63 none (some true) Direction.left 64
    , MachineDescription.transition
        64 (some false) (some false) Direction.left 64
    , MachineDescription.transition
        64 (some true) (some true) Direction.left 64
    , MachineDescription.transition
        64 none (some false) Direction.right 65
    , MachineDescription.transition
        65 (some false) (some false) Direction.right 66
    , MachineDescription.transition
        65 (some true) (some true) Direction.right 66
    , MachineDescription.transition
        66 (some false) (some false) Direction.right 67
    , MachineDescription.transition
        66 (some true) (some true) Direction.right 67
    , MachineDescription.transition
        67 (some false) (some false) Direction.right 10
    , MachineDescription.transition
        67 (some true) (some true) Direction.right 10

    , MachineDescription.transition
        70 (some false) (some false) Direction.right 70
    , MachineDescription.transition
        70 (some true) (some true) Direction.right 70
    , MachineDescription.transition
        70 none (some false) Direction.right 71
    , MachineDescription.transition
        71 none (some true) Direction.right 72
    , MachineDescription.transition
        72 none (some true) Direction.right 73
    , MachineDescription.transition
        73 none (some false) Direction.left 74
    , MachineDescription.transition
        74 (some false) (some false) Direction.left 74
    , MachineDescription.transition
        74 (some true) (some true) Direction.left 74
    , MachineDescription.transition
        74 none (some false) Direction.right 75
    , MachineDescription.transition
        75 (some false) (some false) Direction.right 76
    , MachineDescription.transition
        75 (some true) (some true) Direction.right 76
    , MachineDescription.transition
        76 (some false) (some false) Direction.right 77
    , MachineDescription.transition
        76 (some true) (some true) Direction.right 77
    , MachineDescription.transition
        77 (some false) (some false) Direction.right 10
    , MachineDescription.transition
        77 (some true) (some true) Direction.right 10

      -- Return to the transition marker and halt on the restored marker.
    , MachineDescription.transition
        80 (some false) (some false) Direction.left 80
    , MachineDescription.transition
        80 (some true) (some true) Direction.left 80
    , MachineDescription.transition
        80 none (some false) Direction.left 81
    , MachineDescription.transition
        81 (some false) (some false) Direction.right 99
    , MachineDescription.transition
        81 (some true) (some true) Direction.right 99
    ]

private theorem inputTapeRightCellsDirectCopierDescription_wellFormed :
    InputTapeRightCellsDirectCopierDescription.WellFormed := by
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · intro t ht
    exact transition_wellFormed_of_all
      (l := InputTapeRightCellsDirectCopierDescription.transitions)
      (stateCount :=
        InputTapeRightCellsDirectCopierDescription.stateCount)
      (by
        native_decide) t ht
  · intro t u ht hu hkey
    exact transition_deterministic_of_all
      (l := InputTapeRightCellsDirectCopierDescription.transitions)
      (by
        native_decide) t u ht hu hkey

private theorem
    inputTapeRightCellsDirectCopierDescription_haltTransitionFree :
    InputTapeRightCellsDirectCopierDescription.HaltTransitionFree := by
  intro t ht
  exact transition_notFrom_of_all
    (l := InputTapeRightCellsDirectCopierDescription.transitions)
    (state := InputTapeRightCellsDirectCopierDescription.halt)
    (by
      native_decide) t ht

private theorem
    inputTapeRightCellsDirectCopierDescription_subroutineReady :
    InputTapeRightCellsDirectCopierDescription.SubroutineReady :=
  ⟨inputTapeRightCellsDirectCopierDescription_wellFormed,
    inputTapeRightCellsDirectCopierDescription_haltTransitionFree⟩

private theorem
    inputTapeRightCellsDirectCopierDescription_step_scan20
    (leftRev : List (Option Bool)) (bit : Bool) (rest : Word Bool) :
    InputTapeRightCellsDirectCopierDescription.stepConfig
        (config 20 leftRev (some bit :: rest.map some)) =
      some (config 20 (some bit :: leftRev)
        (rest.map some)) := by
  cases bit <;> cases rest <;>
    simp [InputTapeRightCellsDirectCopierDescription,
      config, tapeAtCells,
      MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

private theorem
    inputTapeRightCellsDirectCopierDescription_run_scan20
    (leftRev : List (Option Bool)) (remaining : Word Bool) :
    InputTapeRightCellsDirectCopierDescription.runConfig
        remaining.length
        (config 20 leftRev (remaining.map some)) =
      config 20
        (List.append (remaining.reverse.map some) leftRev) [] := by
  induction remaining generalizing leftRev with
  | nil =>
      simp [MachineDescription.runConfig, config,
        tapeAtCells]
  | cons bit rest ih =>
      simp [MachineDescription.runConfig,
        inputTapeRightCellsDirectCopierDescription_step_scan20,
        ih, List.append_assoc]

private theorem
    inputTapeRightCellsDirectCopierDescription_run_write_tick
    (leftRev : List (Option Bool)) :
    InputTapeRightCellsDirectCopierDescription.runConfig 4
        (config 20 leftRev []) =
      config 24
        (List.append [some false, some false] leftRev)
        [some true, some false] := by
  simp [InputTapeRightCellsDirectCopierDescription,
    config, tapeAtCells,
    MachineDescription.runConfig, MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition, Tape.read, Tape.write, Tape.move,
    Tape.moveLeft, Tape.moveRight]

private theorem
    inputTapeRightCellsDirectCopierDescription_step_return24
    (preRev : Word Bool) (leftOfMarker : List (Option Bool))
    (leftBit current : Bool) (right : List (Option Bool)) :
    InputTapeRightCellsDirectCopierDescription.stepConfig
        (config 24
          (List.append (some leftBit :: preRev.map some)
            (none :: leftOfMarker))
          (some current :: right)) =
      some (config 24
        (List.append (preRev.map some) (none :: leftOfMarker))
        (some leftBit :: some current :: right)) := by
  cases leftBit <;> cases current <;> cases right <;>
    simp [InputTapeRightCellsDirectCopierDescription,
      config, tapeAtCells,
      MachineDescription.stepConfig, MachineDescription.lookupTransition,
      MachineDescription.Matches, MachineDescription.transition, Tape.read,
      Tape.write, Tape.move, Tape.moveLeft]

private theorem
    inputTapeRightCellsDirectCopierDescription_run_return24
    (preRev : Word Bool) (leftOfMarker : List (Option Bool))
    (current : Bool) (right : List (Option Bool)) :
    InputTapeRightCellsDirectCopierDescription.runConfig
        (preRev.length + 2)
        (config 24
          (List.append (preRev.map some) (none :: leftOfMarker))
          (some current :: right)) =
      config 25 (some false :: leftOfMarker)
        (List.append (preRev.reverse.map some)
          (some current :: right)) := by
  induction preRev generalizing current right with
  | nil =>
      cases current <;> cases right <;>
        simp [InputTapeRightCellsDirectCopierDescription,
          config, tapeAtCells,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, Tape.moveRight]
  | cons bit rest ih =>
      simp only [List.map_cons, List.length_cons, List.reverse_cons]
      rw [show rest.length + 1 + 2 = (rest.length + 2) + 1 by
        omega]
      rw [MachineDescription.runConfig]
      rw [inputTapeRightCellsDirectCopierDescription_step_return24]
      simpa [List.append_assoc] using ih bit (some current :: right)

private theorem
    inputTapeRightCellsDirectCopierDescription_run_advance25_to0
    (leftRev : List (Option Bool)) (b1 b2 b3 : Bool)
    (right : List (Option Bool)) :
    InputTapeRightCellsDirectCopierDescription.runConfig 3
        (config 25 leftRev
          (some b1 :: some b2 :: some b3 :: right)) =
      config 0
        (some b3 :: some b2 :: some b1 :: leftRev) right := by
  cases b1 <;> cases b2 <;> cases b3 <;> cases right <;>
    simp [InputTapeRightCellsDirectCopierDescription,
      config, tapeAtCells,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

private theorem
    inputTapeRightCellsDirectCopierDescription_run_copy_tick
    (leftOfMarker : List (Option Bool))
    (pre remaining : Word Bool) :
    exists steps : Nat,
      InputTapeRightCellsDirectCopierDescription.runConfig steps
          (config 0
            (List.append (pre.reverse.map some)
              (none :: leftOfMarker))
            ((List.append
              (MachineDescription.encodeCodeSymbolAsInput
                MachineCodeSymbol.tick)
              remaining).map some)) =
        config 0
          (List.append
            ((MachineDescription.encodeCodeSymbolAsInput
              MachineCodeSymbol.tick).reverse.map some)
            (List.append (pre.reverse.map some)
              (none :: leftOfMarker)))
          ((List.append remaining
            (MachineDescription.encodeCodeSymbolAsInput
              MachineCodeSymbol.tick)).map some) := by
  let afterPrefixLeft : List (Option Bool) :=
    List.append [some false, some true, some false, none]
      (List.append (pre.reverse.map some) (none :: leftOfMarker))
  let returnPre : Word Bool :=
    List.append [false, false]
      (List.append remaining.reverse [false, true, false])
  let returnLeft : List (Option Bool) :=
    List.append (pre.reverse.map some) (none :: leftOfMarker)
  have hprefix :
      InputTapeRightCellsDirectCopierDescription.runConfig 4
          (config 0
            (List.append (pre.reverse.map some)
              (none :: leftOfMarker))
            ((List.append
              (MachineDescription.encodeCodeSymbolAsInput
                MachineCodeSymbol.tick)
              remaining).map some)) =
        config 20 afterPrefixLeft (remaining.map some) := by
    simp [afterPrefixLeft,
      InputTapeRightCellsDirectCopierDescription,
      MachineDescription.encodeCodeSymbolAsInput,
      config, tapeAtCells,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight, List.map_reverse]
    cases List.map some remaining <;> rfl
  refine
    ⟨4 + (remaining.length + (4 + ((returnPre.length + 2) + 3))), ?_⟩
  rw [MachineDescription.runConfig_add]
  rw [hprefix]
  rw [MachineDescription.runConfig_add]
  rw [inputTapeRightCellsDirectCopierDescription_run_scan20]
  rw [MachineDescription.runConfig_add]
  rw [inputTapeRightCellsDirectCopierDescription_run_write_tick]
  rw [MachineDescription.runConfig_add]
  have hleft :
      List.append [some false, some false]
          (List.append (remaining.reverse.map some) afterPrefixLeft) =
        List.append (returnPre.map some) (none :: returnLeft) := by
    simp [afterPrefixLeft, returnPre, returnLeft,
      List.map_append, List.append_assoc]
  rw [show
      config 24
        (List.append [some false, some false]
          (List.append (remaining.reverse.map some) afterPrefixLeft))
        [some true, some false] =
      config 24
        (List.append (returnPre.map some) (none :: returnLeft))
        (some true :: [some false]) by
        simpa [List.map_reverse] using
          congrArg
            (fun left =>
              config 24 left [some true, some false])
            hleft]
  rw [inputTapeRightCellsDirectCopierDescription_run_return24]
  rw [show
      config 25 (some false :: returnLeft)
        (List.append (returnPre.reverse.map some) [some true, some false]) =
      config 25 (some false :: returnLeft)
        (some false :: some true :: some false ::
          ((List.append remaining
            (MachineDescription.encodeCodeSymbolAsInput
              MachineCodeSymbol.tick)).map some)) by
        simp [returnPre, MachineDescription.encodeCodeSymbolAsInput,
          List.map_append, List.reverse_append, List.append_assoc]]
  rw [inputTapeRightCellsDirectCopierDescription_run_advance25_to0]
  simp [returnLeft, MachineDescription.encodeCodeSymbolAsInput,
    List.map_append]

private def AppendCodeSymbolReturnToCurrentMarkerDescription
    (symbol : MachineCodeSymbol) : MachineDescription :=
  AppendCodeWordReturnToCurrentMarkerDescription [symbol]

private theorem
    appendCodeSymbolReturnToCurrentMarkerDescription_subroutineReady
    (symbol : MachineCodeSymbol) :
    (AppendCodeSymbolReturnToCurrentMarkerDescription
      symbol).SubroutineReady :=
  appendCodeWordReturnToCurrentMarkerDescription_subroutineReady
    [symbol] (by intro h; cases h)

private theorem
    appendCodeSymbolReturnToCurrentMarkerDescription_run_from_scan
    (symbol : MachineCodeSymbol)
    (pre remaining : Word Bool)
    (leftOfMarker : List (Option Bool)) :
    exists steps : Nat,
      (AppendCodeSymbolReturnToCurrentMarkerDescription
        symbol).runConfig steps
          { state :=
              (AppendCodeSymbolReturnToCurrentMarkerDescription
                symbol).start
            tape :=
              appendScanTapeAtCells
                (List.append (pre.reverse.map some)
                  (none :: leftOfMarker))
                remaining } =
        config
          (AppendCodeSymbolReturnToCurrentMarkerDescription
            symbol).halt
          (some false :: leftOfMarker)
          ((List.append (List.append pre remaining)
            (MachineDescription.encodeCodeSymbolAsInput symbol)).map
            some) := by
  rcases
      appendCodeWordReturnToCurrentMarkerDescription_run_from_scan
        [symbol] (by intro h; cases h)
        pre remaining leftOfMarker with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  simpa [AppendCodeSymbolReturnToCurrentMarkerDescription,
    MachineDescription.encodeCodeWordAsInput] using hsteps

private def ReturnToTransitionMarkerDescription :
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

private theorem returnToTransitionMarkerDescription_wellFormed :
    ReturnToTransitionMarkerDescription.WellFormed := by
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · intro t ht
    exact transition_wellFormed_of_all
      (l := ReturnToTransitionMarkerDescription.transitions)
      (stateCount :=
        ReturnToTransitionMarkerDescription.stateCount)
      (by
        native_decide) t ht
  · intro t u ht hu hkey
    exact transition_deterministic_of_all
      (l := ReturnToTransitionMarkerDescription.transitions)
      (by
        native_decide) t u ht hu hkey

private theorem returnToTransitionMarkerDescription_haltTransitionFree :
    ReturnToTransitionMarkerDescription.HaltTransitionFree := by
  intro t ht
  exact transition_notFrom_of_all
    (l := ReturnToTransitionMarkerDescription.transitions)
    (state := ReturnToTransitionMarkerDescription.halt)
    (by
      native_decide) t ht

private theorem returnToTransitionMarkerDescription_subroutineReady :
    ReturnToTransitionMarkerDescription.SubroutineReady :=
  ⟨returnToTransitionMarkerDescription_wellFormed,
    returnToTransitionMarkerDescription_haltTransitionFree⟩

private theorem returnToTransitionMarkerDescription_step_scan
    (preRev : Word Bool) (leftBit current : Bool)
    (right : List (Option Bool)) :
    ReturnToTransitionMarkerDescription.stepConfig
        (config 0
          (List.append
            (some leftBit :: preRev.map some) [none, some false])
          (some current :: right)) =
      some
        (config 0
          (List.append (preRev.map some) [none, some false])
          (some leftBit :: some current :: right)) := by
  cases leftBit <;> cases current <;>
    simp [ReturnToTransitionMarkerDescription,
      config, tapeAtCells,
      MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft]

private theorem returnToTransitionMarkerDescription_run
    (preRev : Word Bool) (current : Bool)
    (right : List (Option Bool)) :
    ReturnToTransitionMarkerDescription.runConfig
        (preRev.length + 3)
        (config 0
          (List.append (preRev.map some) [none, some false])
          (some current :: right)) =
      config 2 [some false]
        (some false ::
          List.append (preRev.reverse.map some)
            (some current :: right)) := by
  induction preRev generalizing current right with
  | nil =>
      cases current <;>
        simp [ReturnToTransitionMarkerDescription,
          config, tapeAtCells,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read, Tape.write,
          Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons b rest ih =>
      simp only [List.map_cons, List.length_cons, List.reverse_cons]
      rw [show Nat.succ rest.length + 3 = (rest.length + 3) + 1 by omega]
      rw [MachineDescription.runConfig]
      rw [returnToTransitionMarkerDescription_step_scan]
      simpa [List.append_assoc] using ih b (some current :: right)

private theorem
    returnToTransitionMarkerDescription_run_after_append_four_atCells
    (pre : Word Bool) (b0 b1 b2 b3 : Bool) :
    ReturnToTransitionMarkerDescription.runConfig
        (pre.length + 5)
        { state := ReturnToTransitionMarkerDescription.start
          tape :=
            Tape.move Direction.left
              (appendRightLastTapeAtCells
                (List.append (pre.reverse.map some)
                  [none, some false]) b0 b1 b2 b3) } =
      { state := ReturnToTransitionMarkerDescription.halt
        tape :=
          tapeAtCells [some false]
            (some false ::
              ((List.append pre [b0, b1, b2, b3]).map some)) } := by
  simpa [appendRightLastTapeAtCells, tapeAtCells,
    Tape.move, Tape.moveLeft, List.append_assoc] using
    returnToTransitionMarkerDescription_run
      (List.append [b1, b0] pre.reverse) b2 [some b3]

private theorem
    returnToTransitionMarkerDescription_run_after_append_atCells :
    forall code : Word MachineCodeSymbol,
      code ≠ [] ->
        forall pre : Word Bool,
          exists steps : Nat,
            ReturnToTransitionMarkerDescription.runConfig steps
                { state := ReturnToTransitionMarkerDescription.start
                  tape :=
                    Tape.move Direction.left
                      (appendCodeWordLastTapeAtCells
                        (List.append (pre.reverse.map some)
                          [none, some false])
                        code) } =
              { state := ReturnToTransitionMarkerDescription.halt
                tape :=
                  tapeAtCells [some false]
                    (some false ::
                      ((List.append pre
                        (MachineDescription.encodeCodeWordAsInput code)).map
                        some)) }
  | [], h => False.elim (h rfl)
  | symbol :: [], _ => by
      intro pre
      cases symbol <;>
        refine ⟨pre.length + 5, ?_⟩ <;>
        simpa [appendCodeWordLastTapeAtCells,
          appendCodeSymbolLastTapeAtCells,
          appendRightLastTapeAtCells,
          MachineDescription.encodeCodeSymbolAsInput,
          MachineDescription.encodeCodeWordAsInput,
          Tape.move, Tape.moveLeft, List.append_assoc] using
          returnToTransitionMarkerDescription_run_after_append_four_atCells
            pre _ _ _ _
  | symbol :: next :: rest, _ => by
      intro pre
      let symbolBits := MachineDescription.encodeCodeSymbolAsInput symbol
      rcases
          returnToTransitionMarkerDescription_run_after_append_atCells
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
      simpa [appendCodeWordLastTapeAtCells, symbolBits,
        hleft, hbits, MachineDescription.encodeCodeWordAsInput,
        List.map_append, List.append_assoc] using hsteps

private def MarkedPrefixAppendCodeWordReturnDescription
    (code : Word MachineCodeSymbol) : MachineDescription :=
  MachineDescription.seqSubroutine
    (MarkedPrefixThenAppendCodeWordLastDescription code)
    ReturnToTransitionMarkerDescription
    Direction.left

private theorem
    markedPrefixAppendCodeWordReturnDescription_subroutineReady
    (code : Word MachineCodeSymbol) (hcode : code ≠ []) :
    (MarkedPrefixAppendCodeWordReturnDescription
      code).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    (markedPrefixThenAppendCodeWordLastDescription_subroutineReady
      code hcode)
    returnToTransitionMarkerDescription_subroutineReady

private theorem markedPrefixAppendCodeWordReturnDescription_run
    (code : Word MachineCodeSymbol) (hcode : code ≠ [])
    (b : Bool) (rest : Word Bool) :
    exists steps : Nat,
      (MarkedPrefixAppendCodeWordReturnDescription code).runConfig steps
          ((MarkedPrefixAppendCodeWordReturnDescription
            code).initial (b :: rest)) =
        { state :=
            (MarkedPrefixAppendCodeWordReturnDescription code).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append (false :: true :: b :: rest)
                  (MachineDescription.encodeCodeWordAsInput code)).map
                  some)) } := by
  let A := MarkedPrefixThenAppendCodeWordLastDescription code
  let B := ReturnToTransitionMarkerDescription
  let Tmid :=
    appendCodeWordLastTapeAtCells
      (List.append
        ((false :: true :: b :: rest).reverse.map some)
        [none, some false])
      code
  have hAready : A.SubroutineReady := by
    exact
      markedPrefixThenAppendCodeWordLastDescription_subroutineReady
        code hcode
  have hBready : B.SubroutineReady := by
    exact returnToTransitionMarkerDescription_subroutineReady
  rcases
      markedPrefixThenAppendCodeWordLastDescription_run
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
              tapeAtCells [some false]
                (some false ::
                  ((List.append (false :: true :: b :: rest)
                    (MachineDescription.encodeCodeWordAsInput code)).map
                    some)) } := by
    rcases
        returnToTransitionMarkerDescription_run_after_append_atCells
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
  simpa [MarkedPrefixAppendCodeWordReturnDescription,
    MachineDescription.initial, A, B] using hn

private def MarkedPrefixAppendNatReturnDescription
    (n : Nat) : MachineDescription :=
  MarkedPrefixAppendCodeWordReturnDescription
    (MachineDescription.encodeNat n)

private theorem
    markedPrefixAppendNatReturnDescription_subroutineReady
    (n : Nat) :
    (MarkedPrefixAppendNatReturnDescription
      n).SubroutineReady :=
  markedPrefixAppendCodeWordReturnDescription_subroutineReady
    (MachineDescription.encodeNat n)
    (encodeNat_ne_nil n)

private theorem markedPrefixAppendNatReturnDescription_run
    (n : Nat) (b : Bool) (rest : Word Bool) :
    exists steps : Nat,
      (MarkedPrefixAppendNatReturnDescription n).runConfig steps
          ((MarkedPrefixAppendNatReturnDescription
            n).initial (b :: rest)) =
        { state :=
            (MarkedPrefixAppendNatReturnDescription n).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append (false :: true :: b :: rest)
                  (MachineDescription.encodeCodeWordAsInput
                    (MachineDescription.encodeNat n))).map some)) } := by
  simpa [MarkedPrefixAppendNatReturnDescription] using
    markedPrefixAppendCodeWordReturnDescription_run
      (MachineDescription.encodeNat n)
      (encodeNat_ne_nil n)
      b rest

private theorem stageInputBits_exists_cons
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
    markedPrefixAppendCodeWordReturnDescription_run_stageInput
    (code : Word MachineCodeSymbol) (hcode : code ≠ [])
    (w : Word Bool) (stage : Nat) :
    exists steps : Nat,
      (MarkedPrefixAppendCodeWordReturnDescription code).runConfig steps
          ((MarkedPrefixAppendCodeWordReturnDescription
            code).initial
            (MachineDescription.encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w stage))) =
        { state :=
            (MarkedPrefixAppendCodeWordReturnDescription code).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append [false, true]
                  (List.append
                    (MachineDescription.encodeCodeWordAsInput
                      (PairedRecognizerDovetailStageInputCode w stage))
                    (MachineDescription.encodeCodeWordAsInput code))).map
                  some)) } := by
  rcases stageInputBits_exists_cons w stage with
    ⟨b, rest, hbits⟩
  rcases
      markedPrefixAppendCodeWordReturnDescription_run
        code hcode b rest with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  simpa [hbits, MachineDescription.initial, List.append_assoc] using hsteps

private theorem markedPrefixAppendNatReturnDescription_run_stageInput
    (n : Nat) (w : Word Bool) (stage : Nat) :
    exists steps : Nat,
      (MarkedPrefixAppendNatReturnDescription n).runConfig steps
          ((MarkedPrefixAppendNatReturnDescription
            n).initial
            (MachineDescription.encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w stage))) =
        { state :=
            (MarkedPrefixAppendNatReturnDescription n).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append [false, true]
                  (List.append
                    (MachineDescription.encodeCodeWordAsInput
                      (PairedRecognizerDovetailStageInputCode w stage))
                    (MachineDescription.encodeCodeWordAsInput
                      (MachineDescription.encodeNat n)))).map some)) } := by
  simpa [MarkedPrefixAppendNatReturnDescription] using
    markedPrefixAppendCodeWordReturnDescription_run_stageInput
      (MachineDescription.encodeNat n)
      (encodeNat_ne_nil n)
      w stage

private def TransitionPrefixedAppendCodeWordReturnDescription
    (code : Word MachineCodeSymbol) : MachineDescription :=
  MachineDescription.seqSubroutine
    (TransitionPrefixedThenAppendCodeWordLastDescription code)
    ReturnToTransitionMarkerDescription
    Direction.left

private theorem
    transitionPrefixedAppendCodeWordReturnDescription_subroutineReady
    (code : Word MachineCodeSymbol) (hcode : code ≠ []) :
    (TransitionPrefixedAppendCodeWordReturnDescription
      code).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    (transitionPrefixedThenAppendCodeWordLastDescription_subroutineReady
      code hcode)
    returnToTransitionMarkerDescription_subroutineReady

private theorem transitionPrefixedAppendCodeWordReturnDescription_run
    (code : Word MachineCodeSymbol) (hcode : code ≠ [])
    (payload : Word Bool) :
    exists steps : Nat,
      (TransitionPrefixedAppendCodeWordReturnDescription
        code).runConfig steps
          { state :=
              (TransitionPrefixedAppendCodeWordReturnDescription
                code).start
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append [false, true] payload).map some)) } =
        { state :=
            (TransitionPrefixedAppendCodeWordReturnDescription
              code).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append (false :: true :: payload)
                  (MachineDescription.encodeCodeWordAsInput code)).map
                  some)) } := by
  let A := TransitionPrefixedThenAppendCodeWordLastDescription code
  let B := ReturnToTransitionMarkerDescription
  let Tmid :=
    appendCodeWordLastTapeAtCells
      (List.append
        ((false :: true :: payload).reverse.map some)
        [none, some false])
      code
  have hAready : A.SubroutineReady := by
    exact
      transitionPrefixedThenAppendCodeWordLastDescription_subroutineReady
        code hcode
  have hBready : B.SubroutineReady := by
    exact returnToTransitionMarkerDescription_subroutineReady
  rcases
      transitionPrefixedThenAppendCodeWordLastDescription_run
        code hcode payload with
    ⟨nA, hArunBase⟩
  have hArun :
      A.runConfig nA
          { state := A.start
            tape :=
              tapeAtCells [some false]
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
              tapeAtCells [some false]
                (some false ::
                  ((List.append (false :: true :: payload)
                    (MachineDescription.encodeCodeWordAsInput code)).map
                    some)) } := by
    rcases
        returnToTransitionMarkerDescription_run_after_append_atCells
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
  simpa [TransitionPrefixedAppendCodeWordReturnDescription,
    A, B] using hn

private def TransitionPrefixedAppendNatReturnDescription
    (n : Nat) : MachineDescription :=
  TransitionPrefixedAppendCodeWordReturnDescription
    (MachineDescription.encodeNat n)

private theorem
    transitionPrefixedAppendNatReturnDescription_subroutineReady
    (n : Nat) :
    (TransitionPrefixedAppendNatReturnDescription
      n).SubroutineReady :=
  transitionPrefixedAppendCodeWordReturnDescription_subroutineReady
    (MachineDescription.encodeNat n)
    (encodeNat_ne_nil n)

private theorem transitionPrefixedAppendNatReturnDescription_run
    (n : Nat) (payload : Word Bool) :
    exists steps : Nat,
      (TransitionPrefixedAppendNatReturnDescription
        n).runConfig steps
          { state :=
              (TransitionPrefixedAppendNatReturnDescription
                n).start
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append [false, true] payload).map some)) } =
        { state :=
            (TransitionPrefixedAppendNatReturnDescription n).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append (false :: true :: payload)
                  (MachineDescription.encodeCodeWordAsInput
                    (MachineDescription.encodeNat n))).map some)) } := by
  simpa [TransitionPrefixedAppendNatReturnDescription] using
    transitionPrefixedAppendCodeWordReturnDescription_run
      (MachineDescription.encodeNat n)
      (encodeNat_ne_nil n)
      payload

private theorem exactIdentityDescription_subroutineReady :
    MachineDescription.ExactIdentityDescription.SubroutineReady :=
  ⟨MachineDescription.exactIdentityDescription_wellFormed,
    MachineDescription.exactIdentityDescription_haltTransitionFree⟩

private def TransitionPrefixedFirstBitAppendCodeWordReturnDescription
    (code : Word MachineCodeSymbol) : MachineDescription :=
  MachineDescription.seqSubroutine
    MachineDescription.ExactIdentityDescription
    (TransitionPrefixedAppendCodeWordReturnDescription code)
    Direction.right

private theorem
    transitionPrefixedFirstBitAppendCodeWordReturnDescription_subroutineReady
    (code : Word MachineCodeSymbol) (hcode : code ≠ []) :
    (TransitionPrefixedFirstBitAppendCodeWordReturnDescription
      code).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    exactIdentityDescription_subroutineReady
    (transitionPrefixedAppendCodeWordReturnDescription_subroutineReady
      code hcode)

private theorem
    transitionPrefixedFirstBitAppendCodeWordReturnDescription_run
    (code : Word MachineCodeSymbol) (hcode : code ≠ [])
    (payload : Word Bool) :
    exists steps : Nat,
      (TransitionPrefixedFirstBitAppendCodeWordReturnDescription
        code).runConfig steps
          { state :=
              (TransitionPrefixedFirstBitAppendCodeWordReturnDescription
                code).start
            tape :=
              tapeAtCells []
                (some false :: some false ::
                  ((List.append [false, true] payload).map some)) } =
        { state :=
            (TransitionPrefixedFirstBitAppendCodeWordReturnDescription
              code).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append (false :: true :: payload)
                  (MachineDescription.encodeCodeWordAsInput code)).map
                  some)) } := by
  let A := MachineDescription.ExactIdentityDescription
  let B := TransitionPrefixedAppendCodeWordReturnDescription code
  let Tin :=
    tapeAtCells []
      (some false :: some false ::
        ((List.append [false, true] payload).map some))
  have hAready : A.SubroutineReady := by
    exact exactIdentityDescription_subroutineReady
  have hBready : B.SubroutineReady := by
    exact
      transitionPrefixedAppendCodeWordReturnDescription_subroutineReady
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
              tapeAtCells [some false]
                (some false ::
                  ((List.append (false :: true :: payload)
                    (MachineDescription.encodeCodeWordAsInput code)).map
                    some)) } := by
    rcases
        transitionPrefixedAppendCodeWordReturnDescription_run
          code hcode payload with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    simpa [B, Tin, tapeAtCells, Tape.move, Tape.moveRight] using hB
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.right)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [
    TransitionPrefixedFirstBitAppendCodeWordReturnDescription,
    A, B, Tin] using hn

private def TransitionPrefixedFirstBitAppendNatReturnDescription
    (n : Nat) : MachineDescription :=
  TransitionPrefixedFirstBitAppendCodeWordReturnDescription
    (MachineDescription.encodeNat n)

private theorem
    transitionPrefixedFirstBitAppendNatReturnDescription_subroutineReady
    (n : Nat) :
    (TransitionPrefixedFirstBitAppendNatReturnDescription
      n).SubroutineReady :=
  transitionPrefixedFirstBitAppendCodeWordReturnDescription_subroutineReady
    (MachineDescription.encodeNat n)
    (encodeNat_ne_nil n)

private theorem
    transitionPrefixedFirstBitAppendNatReturnDescription_run
    (n : Nat) (payload : Word Bool) :
    exists steps : Nat,
      (TransitionPrefixedFirstBitAppendNatReturnDescription
        n).runConfig steps
          { state :=
              (TransitionPrefixedFirstBitAppendNatReturnDescription
                n).start
            tape :=
              tapeAtCells []
                (some false :: some false ::
                  ((List.append [false, true] payload).map some)) } =
        { state :=
            (TransitionPrefixedFirstBitAppendNatReturnDescription
              n).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append (false :: true :: payload)
                  (MachineDescription.encodeCodeWordAsInput
                    (MachineDescription.encodeNat n))).map some)) } := by
  simpa [
    TransitionPrefixedFirstBitAppendNatReturnDescription] using
    transitionPrefixedFirstBitAppendCodeWordReturnDescription_run
      (MachineDescription.encodeNat n)
      (encodeNat_ne_nil n)
      payload

private def AppendTwoCodeWordsReturnDescription
    (first second : Word MachineCodeSymbol) : MachineDescription :=
  MachineDescription.seqSubroutine
    (MarkedPrefixAppendCodeWordReturnDescription first)
    (TransitionPrefixedFirstBitAppendCodeWordReturnDescription
      second)
    Direction.left

private theorem appendTwoCodeWordsReturnDescription_subroutineReady
    (first second : Word MachineCodeSymbol)
    (hfirst : first ≠ []) (hsecond : second ≠ []) :
    (AppendTwoCodeWordsReturnDescription
      first second).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    (markedPrefixAppendCodeWordReturnDescription_subroutineReady
      first hfirst)
    (transitionPrefixedFirstBitAppendCodeWordReturnDescription_subroutineReady
      second hsecond)

private theorem appendTwoCodeWordsReturnDescription_run
    (first second : Word MachineCodeSymbol)
    (hfirst : first ≠ []) (hsecond : second ≠ [])
    (b : Bool) (rest : Word Bool) :
    exists steps : Nat,
      (AppendTwoCodeWordsReturnDescription
        first second).runConfig steps
          ((AppendTwoCodeWordsReturnDescription
            first second).initial (b :: rest)) =
        { state :=
            (AppendTwoCodeWordsReturnDescription
              first second).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append (false :: true :: b :: rest)
                  (List.append
                    (MachineDescription.encodeCodeWordAsInput first)
                    (MachineDescription.encodeCodeWordAsInput second))).map
                  some)) } := by
  let A := MarkedPrefixAppendCodeWordReturnDescription first
  let B :=
    TransitionPrefixedFirstBitAppendCodeWordReturnDescription
      second
  let firstBits := MachineDescription.encodeCodeWordAsInput first
  let secondBits := MachineDescription.encodeCodeWordAsInput second
  let Tmid :=
    tapeAtCells [some false]
      (some false ::
        ((List.append (false :: true :: b :: rest) firstBits).map some))
  have hAready : A.SubroutineReady := by
    exact
      markedPrefixAppendCodeWordReturnDescription_subroutineReady
        first hfirst
  have hBready : B.SubroutineReady := by
    exact
      transitionPrefixedFirstBitAppendCodeWordReturnDescription_subroutineReady
        second hsecond
  rcases
      markedPrefixAppendCodeWordReturnDescription_run
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
              tapeAtCells [some false]
                (some false ::
                  ((List.append (false :: true :: b :: rest)
                    (List.append firstBits secondBits)).map some)) } := by
    rcases
        transitionPrefixedFirstBitAppendCodeWordReturnDescription_run
          second hsecond (List.append (b :: rest) firstBits) with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    simpa [B, Tmid, firstBits, secondBits, tapeAtCells,
      Tape.move, Tape.moveLeft, List.append_assoc] using hB
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.left)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [AppendTwoCodeWordsReturnDescription,
    MachineDescription.initial, A, B, firstBits, secondBits] using hn

private theorem appendTwoCodeWordsReturnDescription_run_stageInput
    (first second : Word MachineCodeSymbol)
    (hfirst : first ≠ []) (hsecond : second ≠ [])
    (w : Word Bool) (stage : Nat) :
    exists steps : Nat,
      (AppendTwoCodeWordsReturnDescription
        first second).runConfig steps
          ((AppendTwoCodeWordsReturnDescription
            first second).initial
            (MachineDescription.encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w stage))) =
        { state :=
            (AppendTwoCodeWordsReturnDescription
              first second).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append [false, true]
                  (List.append
                    (MachineDescription.encodeCodeWordAsInput
                      (PairedRecognizerDovetailStageInputCode w stage))
                    (List.append
                      (MachineDescription.encodeCodeWordAsInput first)
                      (MachineDescription.encodeCodeWordAsInput second)))).map
                  some)) } := by
  rcases stageInputBits_exists_cons w stage with
    ⟨b, rest, hbits⟩
  rcases
      appendTwoCodeWordsReturnDescription_run
        first second hfirst hsecond b rest with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  simpa [hbits, MachineDescription.initial, List.append_assoc] using hsteps

private def stageInputBits
    (w : Word Bool) (stage : Nat) : Word Bool :=
  MachineDescription.encodeCodeWordAsInput
    (PairedRecognizerDovetailStageInputCode w stage)

private theorem stageInputBits_move_left_move_right_input
    (w : Word Bool) (stage : Nat) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (Tape.input (stageInputBits w stage))) =
      Tape.input (stageInputBits w stage) := by
  cases w with
  | nil =>
      cases stage <;>
        simp [stageInputBits,
          PairedRecognizerDovetailStageInputCode,
          MachineDescription.DovetailLayout.stageInputCode,
          MachineDescription.DovetailLayout.stageInputCodeAppend,
          MachineDescription.encodeBoolWordAppend,
          MachineDescription.encodeCellListAppend,
          MachineDescription.encodeNatAppend,
          MachineDescription.encodeNat,
          MachineDescription.encodeCellsAppend,
          MachineDescription.encodeCodeWordAsInput,
          MachineDescription.encodeCodeSymbolAsInput,
          Tape.input, Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons b rest =>
      cases b <;> cases stage <;>
        simp [stageInputBits,
          PairedRecognizerDovetailStageInputCode,
          MachineDescription.DovetailLayout.stageInputCode,
          MachineDescription.DovetailLayout.stageInputCodeAppend,
          MachineDescription.encodeBoolWordAppend,
          MachineDescription.encodeCellListAppend,
          MachineDescription.encodeNatAppend,
          MachineDescription.encodeNat,
          MachineDescription.encodeCellsAppend,
          MachineDescription.encodeCodeWordAsInput,
          MachineDescription.encodeCodeSymbolAsInput,
          Tape.input, Tape.move, Tape.moveLeft, Tape.moveRight]

private theorem tape_eq_move_right_input_of_move_left_eq_input_cons_cons
    {a b : Bool} {rest : Word Bool} {T : Tape Bool}
    (h : Tape.move Direction.left T = Tape.input (a :: b :: rest)) :
    T = Tape.move Direction.right (Tape.input (a :: b :: rest)) := by
  cases T with
  | mk left head right =>
      cases left with
      | nil =>
          simp [Tape.move, Tape.moveLeft, Tape.input] at h
      | cons first leftRest =>
          cases leftRest with
          | nil =>
              simpa [Tape.move, Tape.moveLeft, Tape.moveRight,
                Tape.input] using h
          | cons second more =>
              simp [Tape.move, Tape.moveLeft, Tape.input] at h

private theorem stageInputBits_exists_cons_cons
    (w : Word Bool) (stage : Nat) :
    exists a : Bool,
    exists b : Bool,
    exists rest : Word Bool,
      stageInputBits w stage = a :: b :: rest := by
  cases w with
  | nil =>
      refine ⟨false, false, ?_⟩
      simp [stageInputBits,
        PairedRecognizerDovetailStageInputCode,
        MachineDescription.DovetailLayout.stageInputCode,
        MachineDescription.DovetailLayout.stageInputCodeAppend,
        MachineDescription.encodeBoolWordAppend,
        MachineDescription.encodeCellListAppend,
        MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat,
        MachineDescription.encodeCodeWordAsInput,
        MachineDescription.encodeCodeSymbolAsInput]
      exact ⟨_, rfl⟩
  | cons c restw =>
      refine ⟨false, false, ?_⟩
      simp [stageInputBits,
        PairedRecognizerDovetailStageInputCode,
        MachineDescription.DovetailLayout.stageInputCode,
        MachineDescription.DovetailLayout.stageInputCodeAppend,
        MachineDescription.encodeBoolWordAppend,
        MachineDescription.encodeCellListAppend,
        MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat,
        MachineDescription.encodeCodeWordAsInput,
        MachineDescription.encodeCodeSymbolAsInput]
      exact ⟨_, rfl⟩

private def inputTapeBits
    (w : Word Bool) : Word Bool :=
  MachineDescription.encodeCodeWordAsInput
    (MachineDescription.encodeTapeAppend (Tape.input w) [])

private def natBits (n : Nat) : Word Bool :=
  MachineDescription.encodeCodeWordAsInput
    (MachineDescription.encodeNat n)

@[simp] private theorem natBits_zero :
    natBits 0 = [false, false, true, true] := by
  rfl

@[simp] private theorem natBits_succ (n : Nat) :
    natBits (n + 1) =
      false :: false :: true :: false :: natBits n := by
  rfl

@[simp] private theorem natBits_append_cell_false
    (n : Nat) (tokens : Word MachineCodeSymbol) :
    MachineDescription.encodeCodeWordAsInput
        (List.append (MachineDescription.encodeNat n)
          (MachineCodeSymbol.zero :: tokens)) =
      List.append (natBits n)
        (false :: true :: false :: true ::
          MachineDescription.encodeCodeWordAsInput tokens) := by
  rw [MachineDescription.encodeCodeWordAsInput_append]
  rfl

@[simp] private theorem natBits_append_cell_true
    (n : Nat) (tokens : Word MachineCodeSymbol) :
    MachineDescription.encodeCodeWordAsInput
        (List.append (MachineDescription.encodeNat n)
          (MachineCodeSymbol.one :: tokens)) =
      List.append (natBits n)
        (false :: true :: true :: false ::
          MachineDescription.encodeCodeWordAsInput tokens) := by
  rw [MachineDescription.encodeCodeWordAsInput_append]
  rfl

@[simp] private theorem encodeCodeWordAsInput_tick_cons
    (tokens : Word MachineCodeSymbol) :
    MachineDescription.encodeCodeWordAsInput
        (MachineCodeSymbol.tick :: tokens) =
      false :: false :: true :: false ::
        MachineDescription.encodeCodeWordAsInput tokens := by
  rfl

@[simp] private theorem natBits_map_append_cell_false
    (n : Nat) (tokens : Word MachineCodeSymbol) (suffixBits : Word Bool) :
    List.append
        (List.map some
          (MachineDescription.encodeCodeWordAsInput
            (List.append (MachineDescription.encodeNat n)
              (MachineCodeSymbol.zero :: tokens))))
        (List.map some suffixBits) =
      List.append (List.map some (natBits n))
        (some false :: some true :: some false :: some true ::
          List.append
            (List.map some
              (MachineDescription.encodeCodeWordAsInput tokens))
            (List.map some suffixBits)) := by
  rw [natBits_append_cell_false]
  simp [List.map_append, List.append_assoc]

@[simp] private theorem natBits_map_append_cell_true
    (n : Nat) (tokens : Word MachineCodeSymbol) (suffixBits : Word Bool) :
    List.append
        (List.map some
          (MachineDescription.encodeCodeWordAsInput
            (List.append (MachineDescription.encodeNat n)
              (MachineCodeSymbol.one :: tokens))))
        (List.map some suffixBits) =
      List.append (List.map some (natBits n))
        (some false :: some true :: some true :: some false ::
          List.append
            (List.map some
              (MachineDescription.encodeCodeWordAsInput tokens))
            (List.map some suffixBits)) := by
  rw [natBits_append_cell_true]
  simp [List.map_append, List.append_assoc]

private def emptyInputTapeCode :
    Word MachineCodeSymbol :=
  MachineDescription.encodeTapeAppend
    (Tape.input ([] : Word Bool)) []

private theorem emptyInputTapeCode_ne_nil :
    emptyInputTapeCode ≠ [] := by
  simp [emptyInputTapeCode, encodeTapeAppend_input_nil,
    MachineDescription.encodeCellListAppend,
    MachineDescription.encodeNatAppend,
    MachineDescription.encodeNat]

private def AppendEmptyInputTapeReturnDescription :
    MachineDescription :=
  TransitionPrefixedFirstBitAppendCodeWordReturnDescription
    emptyInputTapeCode

private theorem
    appendEmptyInputTapeReturnDescription_subroutineReady :
    AppendEmptyInputTapeReturnDescription.SubroutineReady :=
  transitionPrefixedFirstBitAppendCodeWordReturnDescription_subroutineReady
    emptyInputTapeCode
    emptyInputTapeCode_ne_nil

private theorem inputTapeBits_nil :
    inputTapeBits ([] : Word Bool) =
      MachineDescription.encodeCodeWordAsInput
        emptyInputTapeCode := by
  rfl

private theorem appendEmptyInputTapeReturnDescription_run
    (stage : Nat) (suffixBits : Word Bool) :
    exists steps : Nat,
      AppendEmptyInputTapeReturnDescription.runConfig steps
          { state := AppendEmptyInputTapeReturnDescription.start
            tape :=
              tapeAtCells []
                (some false :: some false ::
                  ((List.append [false, true]
                    (List.append
                      (stageInputBits ([] : Word Bool) stage)
                      suffixBits)).map some)) } =
        { state := AppendEmptyInputTapeReturnDescription.halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append [false, true]
                  (List.append
                    (stageInputBits ([] : Word Bool) stage)
                    (List.append suffixBits
                      (inputTapeBits ([] : Word Bool))))).map
                    some)) } := by
  rcases
      transitionPrefixedFirstBitAppendCodeWordReturnDescription_run
        emptyInputTapeCode
        emptyInputTapeCode_ne_nil
        (List.append
          (stageInputBits ([] : Word Bool) stage)
          suffixBits) with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  simpa [AppendEmptyInputTapeReturnDescription,
    inputTapeBits_nil, List.append_assoc] using hsteps

private def inputTapeHeadPrefixCode
    (b : Bool) : Word MachineCodeSymbol :=
  MachineDescription.encodeCellListAppend []
    (MachineDescription.encodeCellAppend (some b) [])

private def inputTapeRightCellsCode
    (rest : Word Bool) : Word MachineCodeSymbol :=
  MachineDescription.encodeCellListAppend (rest.map some) []

private theorem inputTapeRightCellsCode_eq_nat_cells
    (rest : Word Bool) :
    inputTapeRightCellsCode rest =
      MachineDescription.encodeNatAppend rest.length
        (MachineDescription.encodeCellsAppend (rest.map some) []) := by
  simp [inputTapeRightCellsCode,
    MachineDescription.encodeCellListAppend]

private theorem inputTapeRightCellsCode_cons_eq_tick_nat_cell_cells
    (b : Bool) (rest : Word Bool) :
    inputTapeRightCellsCode (b :: rest) =
      MachineCodeSymbol.tick ::
        MachineDescription.encodeNatAppend rest.length
          (MachineDescription.encodeCellAppend (some b)
            (MachineDescription.encodeCellsAppend (rest.map some) [])) := by
  cases b <;>
    simp [inputTapeRightCellsCode,
      MachineDescription.encodeCellListAppend,
      MachineDescription.encodeNatAppend,
      MachineDescription.encodeNat,
      MachineDescription.encodeCellsAppend,
      MachineDescription.encodeCellAppend,
      MachineDescription.encodeCell]

private theorem inputTapeRightCellsBits_eq_nat_cells
    (rest : Word Bool) :
    MachineDescription.encodeCodeWordAsInput
        (inputTapeRightCellsCode rest) =
      List.append (natBits rest.length)
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.encodeCellsAppend (rest.map some) [])) := by
  rw [inputTapeRightCellsCode_eq_nat_cells,
    MachineDescription.encodeNatAppend,
    MachineDescription.encodeCodeWordAsInput_append]
  rfl

private theorem inputTapeRightCellsBits_cons_eq_tick_nat_cell_cells
    (b : Bool) (rest : Word Bool) :
    MachineDescription.encodeCodeWordAsInput
        (inputTapeRightCellsCode (b :: rest)) =
      List.append
        (MachineDescription.encodeCodeSymbolAsInput MachineCodeSymbol.tick)
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.encodeNatAppend rest.length
            (MachineDescription.encodeCellAppend (some b)
              (MachineDescription.encodeCellsAppend (rest.map some) [])))) := by
  rw [inputTapeRightCellsCode_cons_eq_tick_nat_cell_cells]
  rfl

private theorem inputTapeHeadPrefixCode_ne_nil
    (b : Bool) :
    inputTapeHeadPrefixCode b ≠ [] := by
  cases b <;>
    simp [inputTapeHeadPrefixCode,
      MachineDescription.encodeCellListAppend,
      MachineDescription.encodeNatAppend,
      MachineDescription.encodeNat,
      MachineDescription.encodeCellAppend,
      MachineDescription.encodeCell]

private theorem inputTapeBits_cons_eq_headPrefix_append
    (b : Bool) (rest : Word Bool) :
    inputTapeBits (b :: rest) =
      List.append
        (MachineDescription.encodeCodeWordAsInput
          (inputTapeHeadPrefixCode b))
        (MachineDescription.encodeCodeWordAsInput
          (inputTapeRightCellsCode rest)) := by
  rw [inputTapeBits, encodeTapeAppend_input_cons]
  change
    MachineDescription.encodeCodeWordAsInput
        (MachineDescription.encodeCellListAppend []
          (MachineDescription.encodeCellAppend (some b)
            (MachineDescription.encodeCellListAppend (rest.map some) []))) =
      List.append
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.encodeCellListAppend []
            (MachineDescription.encodeCellAppend (some b) [])))
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.encodeCellListAppend (rest.map some) []))
  rw [← MachineDescription.encodeCodeWordAsInput_append]
  simp [MachineDescription.encodeCellListAppend,
    MachineDescription.encodeCellsAppend,
    MachineDescription.encodeNatAppend,
    MachineDescription.encodeNat,
    MachineDescription.encodeCellAppend]

private def AppendInputTapeHeadPrefixReturnDescription
    (b : Bool) : MachineDescription :=
  TransitionPrefixedFirstBitAppendCodeWordReturnDescription
    (inputTapeHeadPrefixCode b)

private theorem
    appendInputTapeHeadPrefixReturnDescription_subroutineReady
    (b : Bool) :
    (AppendInputTapeHeadPrefixReturnDescription b).SubroutineReady :=
  transitionPrefixedFirstBitAppendCodeWordReturnDescription_subroutineReady
    (inputTapeHeadPrefixCode b)
    (inputTapeHeadPrefixCode_ne_nil b)

private theorem appendInputTapeHeadPrefixReturnDescription_run
    (b : Bool) (payload suffixBits : Word Bool) :
    exists steps : Nat,
      (AppendInputTapeHeadPrefixReturnDescription b).runConfig steps
          { state := (AppendInputTapeHeadPrefixReturnDescription b).start
            tape :=
              tapeAtCells []
                (some false :: some false ::
                  ((List.append [false, true]
                    (List.append payload suffixBits)).map some)) } =
        { state := (AppendInputTapeHeadPrefixReturnDescription b).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append [false, true]
                  (List.append payload
                    (List.append suffixBits
                      (MachineDescription.encodeCodeWordAsInput
                        (inputTapeHeadPrefixCode b))))).map
                    some)) } := by
  rcases
      transitionPrefixedFirstBitAppendCodeWordReturnDescription_run
        (inputTapeHeadPrefixCode b)
        (inputTapeHeadPrefixCode_ne_nil b)
        (List.append payload suffixBits) with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  simpa [AppendInputTapeHeadPrefixReturnDescription,
    List.append_assoc] using hsteps

private def AppendInputTapeRightCellsReturnSpec
    (rightCopier : MachineDescription) : Prop :=
  rightCopier.SubroutineReady ∧
    forall b : Bool,
    forall rest : Word Bool,
    forall stage : Nat,
    forall suffixBits : Word Bool,
      exists steps : Nat,
        rightCopier.runConfig steps
            { state := rightCopier.start
              tape :=
                tapeAtCells []
                  (some false :: some false ::
                    ((List.append [false, true]
                      (List.append
                        (stageInputBits (b :: rest) stage)
                        suffixBits)).map some)) } =
          { state := rightCopier.halt
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append [false, true]
                    (List.append
                      (stageInputBits (b :: rest) stage)
                      (List.append suffixBits
                        (MachineDescription.encodeCodeWordAsInput
                          (inputTapeRightCellsCode rest))))).map
                    some)) }

private def AppendKnownHeadInputTapeReturnDescription
    (b : Bool) (rightCopier : MachineDescription) :
    MachineDescription :=
  MachineDescription.seqSubroutine
    (AppendInputTapeHeadPrefixReturnDescription b)
    rightCopier
    Direction.left

private theorem
    appendKnownHeadInputTapeReturnDescription_subroutineReady
    {rightCopier : MachineDescription}
    (hright : AppendInputTapeRightCellsReturnSpec rightCopier)
    (b : Bool) :
    (AppendKnownHeadInputTapeReturnDescription
      b rightCopier).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    (appendInputTapeHeadPrefixReturnDescription_subroutineReady b)
    hright.left

private theorem appendKnownHeadInputTapeReturnDescription_run
    {rightCopier : MachineDescription}
    (hright : AppendInputTapeRightCellsReturnSpec rightCopier)
    (b : Bool) (rest : Word Bool) (stage : Nat)
    (suffixBits : Word Bool) :
    exists steps : Nat,
      (AppendKnownHeadInputTapeReturnDescription
        b rightCopier).runConfig steps
          { state :=
              (AppendKnownHeadInputTapeReturnDescription
                b rightCopier).start
            tape :=
              tapeAtCells []
                (some false :: some false ::
                  ((List.append [false, true]
                    (List.append
                      (stageInputBits (b :: rest) stage)
                      suffixBits)).map some)) } =
        { state :=
            (AppendKnownHeadInputTapeReturnDescription
              b rightCopier).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append [false, true]
                  (List.append
                    (stageInputBits (b :: rest) stage)
                    (List.append suffixBits
                      (inputTapeBits (b :: rest))))).map some)) } := by
  let A := AppendInputTapeHeadPrefixReturnDescription b
  let B := rightCopier
  let headBits :=
    MachineDescription.encodeCodeWordAsInput
      (inputTapeHeadPrefixCode b)
  let rightBits :=
    MachineDescription.encodeCodeWordAsInput
      (inputTapeRightCellsCode rest)
  let Tmid :=
    tapeAtCells [some false]
      (some false ::
        ((List.append [false, true]
          (List.append
            (stageInputBits (b :: rest) stage)
            (List.append suffixBits headBits))).map some))
  have hAready : A.SubroutineReady :=
    appendInputTapeHeadPrefixReturnDescription_subroutineReady b
  have hBready : B.SubroutineReady := hright.left
  rcases
      appendInputTapeHeadPrefixReturnDescription_run
        b (stageInputBits (b :: rest) stage) suffixBits with
    ⟨nA, hA⟩
  have hArun :
      A.runConfig nA
          { state := A.start
            tape :=
              tapeAtCells []
                (some false :: some false ::
                  ((List.append [false, true]
                    (List.append
                      (stageInputBits (b :: rest) stage)
                      suffixBits)).map some)) } =
        { state := A.halt, tape := Tmid } := by
    simpa [A, Tmid, headBits, List.append_assoc] using hA
  have hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start
              tape := Tape.move Direction.left Tmid } =
          { state := B.halt
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append [false, true]
                    (List.append
                      (stageInputBits (b :: rest) stage)
                      (List.append suffixBits
                        (inputTapeBits (b :: rest))))).map some)) } := by
    rcases
        hright.right b rest stage (List.append suffixBits headBits) with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    simpa [B, Tmid, headBits, rightBits, tapeAtCells,
      Tape.move, Tape.moveLeft,
      inputTapeBits_cons_eq_headPrefix_append,
      List.map_append, List.append_assoc] using hB
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.left)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [AppendKnownHeadInputTapeReturnDescription,
    A, B] using hn

private def AppendEmptyRightCellsReturnDescription :
    MachineDescription :=
  TransitionPrefixedFirstBitAppendCodeWordReturnDescription
    (inputTapeRightCellsCode ([] : Word Bool))

private theorem inputTapeRightCellsCode_nil_ne_nil :
    inputTapeRightCellsCode ([] : Word Bool) ≠ [] := by
  simp [inputTapeRightCellsCode,
    MachineDescription.encodeCellListAppend,
    MachineDescription.encodeNatAppend,
    MachineDescription.encodeNat]

private theorem
    appendEmptyRightCellsReturnDescription_subroutineReady :
    AppendEmptyRightCellsReturnDescription.SubroutineReady :=
  transitionPrefixedFirstBitAppendCodeWordReturnDescription_subroutineReady
    (inputTapeRightCellsCode ([] : Word Bool))
    inputTapeRightCellsCode_nil_ne_nil

private theorem appendEmptyRightCellsReturnDescription_run
    (b : Bool) (stage : Nat) (suffixBits : Word Bool) :
    exists steps : Nat,
      AppendEmptyRightCellsReturnDescription.runConfig steps
          { state := AppendEmptyRightCellsReturnDescription.start
            tape :=
              tapeAtCells []
                (some false :: some false ::
                  ((List.append [false, true]
                    (List.append
                      (stageInputBits ([b] : Word Bool) stage)
                      suffixBits)).map some)) } =
        { state := AppendEmptyRightCellsReturnDescription.halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append [false, true]
                  (List.append
                    (stageInputBits ([b] : Word Bool) stage)
                    (List.append suffixBits
                      (MachineDescription.encodeCodeWordAsInput
                        (inputTapeRightCellsCode
                          ([] : Word Bool)))))).map some)) } := by
  rcases
      transitionPrefixedFirstBitAppendCodeWordReturnDescription_run
        (inputTapeRightCellsCode ([] : Word Bool))
        inputTapeRightCellsCode_nil_ne_nil
        (List.append
          (stageInputBits ([b] : Word Bool) stage)
          suffixBits) with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  simpa [AppendEmptyRightCellsReturnDescription,
    List.append_assoc] using hsteps

private def AppendSingletonInputTapeReturnDescription
    (b : Bool) : MachineDescription :=
  MachineDescription.seqSubroutine
    (AppendInputTapeHeadPrefixReturnDescription b)
    AppendEmptyRightCellsReturnDescription
    Direction.left

private theorem
    appendSingletonInputTapeReturnDescription_subroutineReady
    (b : Bool) :
    (AppendSingletonInputTapeReturnDescription
      b).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    (appendInputTapeHeadPrefixReturnDescription_subroutineReady b)
    appendEmptyRightCellsReturnDescription_subroutineReady

private theorem appendSingletonInputTapeReturnDescription_run
    (b : Bool) (stage : Nat) (suffixBits : Word Bool) :
    exists steps : Nat,
      (AppendSingletonInputTapeReturnDescription b).runConfig steps
          { state :=
              (AppendSingletonInputTapeReturnDescription b).start
            tape :=
              tapeAtCells []
                (some false :: some false ::
                  ((List.append [false, true]
                    (List.append
                      (stageInputBits ([b] : Word Bool) stage)
                      suffixBits)).map some)) } =
        { state :=
            (AppendSingletonInputTapeReturnDescription b).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append [false, true]
                  (List.append
                    (stageInputBits ([b] : Word Bool) stage)
                    (List.append suffixBits
                      (inputTapeBits ([b] : Word Bool))))).map
                    some)) } := by
  let A := AppendInputTapeHeadPrefixReturnDescription b
  let B := AppendEmptyRightCellsReturnDescription
  let headBits :=
    MachineDescription.encodeCodeWordAsInput
      (inputTapeHeadPrefixCode b)
  let rightBits :=
    MachineDescription.encodeCodeWordAsInput
      (inputTapeRightCellsCode ([] : Word Bool))
  let Tmid :=
    tapeAtCells [some false]
      (some false ::
        ((List.append [false, true]
          (List.append
            (stageInputBits ([b] : Word Bool) stage)
            (List.append suffixBits headBits))).map some))
  have hAready : A.SubroutineReady :=
    appendInputTapeHeadPrefixReturnDescription_subroutineReady b
  have hBready : B.SubroutineReady :=
    appendEmptyRightCellsReturnDescription_subroutineReady
  rcases
      appendInputTapeHeadPrefixReturnDescription_run
        b (stageInputBits ([b] : Word Bool) stage) suffixBits with
    ⟨nA, hA⟩
  have hArun :
      A.runConfig nA
          { state := A.start
            tape :=
              tapeAtCells []
                (some false :: some false ::
                  ((List.append [false, true]
                    (List.append
                      (stageInputBits ([b] : Word Bool) stage)
                      suffixBits)).map some)) } =
        { state := A.halt, tape := Tmid } := by
    simpa [A, Tmid, headBits, List.append_assoc] using hA
  have hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start
              tape := Tape.move Direction.left Tmid } =
          { state := B.halt
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append [false, true]
                    (List.append
                      (stageInputBits ([b] : Word Bool) stage)
                      (List.append suffixBits
                        (inputTapeBits ([b] : Word Bool))))).map
                      some)) } := by
    rcases
        appendEmptyRightCellsReturnDescription_run
          b stage (List.append suffixBits headBits) with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    simpa [B, Tmid, headBits, rightBits, tapeAtCells,
      Tape.move, Tape.moveLeft,
      inputTapeBits_cons_eq_headPrefix_append,
      List.map_append, List.append_assoc] using hB
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.left)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [AppendSingletonInputTapeReturnDescription,
    A, B] using hn

private def AppendEmptyInputTapeSecondBitReturnDescription :
    MachineDescription :=
  TransitionPrefixedAppendCodeWordReturnDescription
    emptyInputTapeCode

private theorem
    appendEmptyInputTapeSecondBitReturnDescription_subroutineReady :
    AppendEmptyInputTapeSecondBitReturnDescription.SubroutineReady :=
  transitionPrefixedAppendCodeWordReturnDescription_subroutineReady
    emptyInputTapeCode
    emptyInputTapeCode_ne_nil

private theorem appendEmptyInputTapeSecondBitReturnDescription_run
    (stage : Nat) (suffixBits : Word Bool) :
    exists steps : Nat,
      AppendEmptyInputTapeSecondBitReturnDescription.runConfig steps
          { state :=
              AppendEmptyInputTapeSecondBitReturnDescription.start
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append [false, true]
                    (List.append
                      (stageInputBits ([] : Word Bool) stage)
                      suffixBits)).map some)) } =
        { state :=
            AppendEmptyInputTapeSecondBitReturnDescription.halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append [false, true]
                  (List.append
                    (stageInputBits ([] : Word Bool) stage)
                    (List.append suffixBits
                      (inputTapeBits ([] : Word Bool))))).map
                  some)) } := by
  rcases
      transitionPrefixedAppendCodeWordReturnDescription_run
        emptyInputTapeCode
        emptyInputTapeCode_ne_nil
        (List.append
          (stageInputBits ([] : Word Bool) stage)
          suffixBits) with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  simpa [AppendEmptyInputTapeSecondBitReturnDescription,
    inputTapeBits_nil, List.append_assoc] using hsteps

private def AppendInputTapeSecondBitHeadPrefixReturnDescription
    (b : Bool) : MachineDescription :=
  TransitionPrefixedAppendCodeWordReturnDescription
    (inputTapeHeadPrefixCode b)

private theorem
    appendInputTapeSecondBitHeadPrefixReturnDescription_subroutineReady
    (b : Bool) :
    (AppendInputTapeSecondBitHeadPrefixReturnDescription
      b).SubroutineReady :=
  transitionPrefixedAppendCodeWordReturnDescription_subroutineReady
    (inputTapeHeadPrefixCode b)
    (inputTapeHeadPrefixCode_ne_nil b)

private theorem
    appendInputTapeSecondBitHeadPrefixReturnDescription_run
    (b : Bool) (payload suffixBits : Word Bool) :
    exists steps : Nat,
      (AppendInputTapeSecondBitHeadPrefixReturnDescription
        b).runConfig steps
          { state :=
              (AppendInputTapeSecondBitHeadPrefixReturnDescription
                b).start
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append [false, true]
                    (List.append payload suffixBits)).map some)) } =
        { state :=
            (AppendInputTapeSecondBitHeadPrefixReturnDescription
              b).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append [false, true]
                  (List.append payload
                    (List.append suffixBits
                      (MachineDescription.encodeCodeWordAsInput
                        (inputTapeHeadPrefixCode b))))).map
                    some)) } := by
  rcases
      transitionPrefixedAppendCodeWordReturnDescription_run
        (inputTapeHeadPrefixCode b)
        (inputTapeHeadPrefixCode_ne_nil b)
        (List.append payload suffixBits) with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  simpa [AppendInputTapeSecondBitHeadPrefixReturnDescription,
    List.append_assoc] using hsteps

private def AppendKnownHeadInputTapeSecondBitReturnDescription
    (b : Bool) (rightCopier : MachineDescription) :
    MachineDescription :=
  MachineDescription.seqSubroutine
    (AppendInputTapeSecondBitHeadPrefixReturnDescription b)
    rightCopier
    Direction.left

private theorem
    appendKnownHeadInputTapeSecondBitReturnDescription_subroutineReady
    {rightCopier : MachineDescription}
    (hright : AppendInputTapeRightCellsReturnSpec rightCopier)
    (b : Bool) :
    (AppendKnownHeadInputTapeSecondBitReturnDescription
      b rightCopier).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    (appendInputTapeSecondBitHeadPrefixReturnDescription_subroutineReady
      b)
    hright.left

private theorem
    appendKnownHeadInputTapeSecondBitReturnDescription_run
    {rightCopier : MachineDescription}
    (hright : AppendInputTapeRightCellsReturnSpec rightCopier)
    (b : Bool) (rest : Word Bool) (stage : Nat)
    (suffixBits : Word Bool) :
    exists steps : Nat,
      (AppendKnownHeadInputTapeSecondBitReturnDescription
        b rightCopier).runConfig steps
          { state :=
              (AppendKnownHeadInputTapeSecondBitReturnDescription
                b rightCopier).start
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append [false, true]
                    (List.append
                      (stageInputBits (b :: rest) stage)
                      suffixBits)).map some)) } =
        { state :=
            (AppendKnownHeadInputTapeSecondBitReturnDescription
              b rightCopier).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append [false, true]
                  (List.append
                    (stageInputBits (b :: rest) stage)
                    (List.append suffixBits
                      (inputTapeBits (b :: rest))))).map some)) } := by
  let A := AppendInputTapeSecondBitHeadPrefixReturnDescription b
  let B := rightCopier
  let headBits :=
    MachineDescription.encodeCodeWordAsInput
      (inputTapeHeadPrefixCode b)
  let rightBits :=
    MachineDescription.encodeCodeWordAsInput
      (inputTapeRightCellsCode rest)
  let Tmid :=
    tapeAtCells [some false]
      (some false ::
        ((List.append [false, true]
          (List.append
            (stageInputBits (b :: rest) stage)
            (List.append suffixBits headBits))).map some))
  have hAready : A.SubroutineReady :=
    appendInputTapeSecondBitHeadPrefixReturnDescription_subroutineReady
      b
  have hBready : B.SubroutineReady := hright.left
  rcases
      appendInputTapeSecondBitHeadPrefixReturnDescription_run
        b (stageInputBits (b :: rest) stage) suffixBits with
    ⟨nA, hA⟩
  have hArun :
      A.runConfig nA
          { state := A.start
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append [false, true]
                    (List.append
                      (stageInputBits (b :: rest) stage)
                      suffixBits)).map some)) } =
        { state := A.halt, tape := Tmid } := by
    simpa [A, Tmid, headBits, List.append_assoc] using hA
  have hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start
              tape := Tape.move Direction.left Tmid } =
          { state := B.halt
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append [false, true]
                    (List.append
                      (stageInputBits (b :: rest) stage)
                      (List.append suffixBits
                        (inputTapeBits (b :: rest))))).map some)) } := by
    rcases
        hright.right b rest stage (List.append suffixBits headBits) with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    simpa [B, Tmid, headBits, rightBits, tapeAtCells,
      Tape.move, Tape.moveLeft,
      inputTapeBits_cons_eq_headPrefix_append,
      List.map_append, List.append_assoc] using hB
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.left)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [AppendKnownHeadInputTapeSecondBitReturnDescription,
    A, B] using hn

private def sharedExitRetargetTransition
    (offset oldHalt commonHalt : Nat)
    (t : TransitionDescription) : TransitionDescription where
  source := offset + t.source
  read := t.read
  write := t.write
  move := t.move
  target := if t.target = oldHalt then commonHalt else offset + t.target

private def taggedBranchBlankOffset : Nat := 2

private def taggedBranchFalseOffset
    (blankBranch : MachineDescription) : Nat :=
  taggedBranchBlankOffset + blankBranch.stateCount

private def taggedBranchTrueOffset
    (blankBranch falseBranch : MachineDescription) : Nat :=
  taggedBranchFalseOffset blankBranch + falseBranch.stateCount

private def taggedBranchStateCount
    (blankBranch falseBranch trueBranch : MachineDescription) : Nat :=
  taggedBranchTrueOffset blankBranch falseBranch +
    trueBranch.stateCount

private def RestoreFirstBitTaggedBrancherDescription
    (blankBranch falseBranch trueBranch : MachineDescription) :
    MachineDescription where
  stateCount :=
    taggedBranchStateCount blankBranch falseBranch trueBranch
  start := 0
  halt := 1
  transitions :=
    [ MachineDescription.transition
        0 none (some false) Direction.right
        (if blankBranch.start = blankBranch.halt then 1
          else taggedBranchBlankOffset + blankBranch.start)
    , MachineDescription.transition
        0 (some false) (some false) Direction.right
        (if falseBranch.start = falseBranch.halt then 1
          else taggedBranchFalseOffset blankBranch +
            falseBranch.start)
    , MachineDescription.transition
        0 (some true) (some false) Direction.right
        (if trueBranch.start = trueBranch.halt then 1
          else taggedBranchTrueOffset blankBranch falseBranch +
            trueBranch.start)
    ] ++
    blankBranch.transitions.map
      (sharedExitRetargetTransition
        taggedBranchBlankOffset blankBranch.halt 1) ++
    falseBranch.transitions.map
      (sharedExitRetargetTransition
        (taggedBranchFalseOffset blankBranch)
        falseBranch.halt 1) ++
    trueBranch.transitions.map
      (sharedExitRetargetTransition
        (taggedBranchTrueOffset blankBranch falseBranch)
        trueBranch.halt 1)

private def sharedExitBranchConfiguration
    (offset oldHalt commonHalt : Nat)
    (c : MachineDescription.Configuration) :
    MachineDescription.Configuration where
  state := if c.state = oldHalt then commonHalt else offset + c.state
  tape := c.tape

private theorem sharedExitRetargetTransition_sameAction
    (offset oldHalt commonHalt : Nat)
    {t u : TransitionDescription}
    (h : TransitionDescription.SameAction t u) :
    TransitionDescription.SameAction
      (sharedExitRetargetTransition
        offset oldHalt commonHalt t)
      (sharedExitRetargetTransition
        offset oldHalt commonHalt u) := by
  rcases h with ⟨hwrite, hmove, htarget⟩
  simp [TransitionDescription.SameAction,
    sharedExitRetargetTransition, hwrite, hmove, htarget]

private theorem sharedExitRetargetTransition_sameKey_source
    {offset oldHalt commonHalt : Nat}
    {t u : TransitionDescription}
    (h :
      TransitionDescription.SameKey
        (sharedExitRetargetTransition
          offset oldHalt commonHalt t)
        (sharedExitRetargetTransition
          offset oldHalt commonHalt u)) :
    TransitionDescription.SameKey t u := by
  constructor
  · exact Nat.add_left_cancel h.left
  · exact h.right

private theorem
    restoreFirstBitTaggedBrancherDescription_subroutineReady
    {blankBranch falseBranch trueBranch : MachineDescription}
    (hblank : blankBranch.SubroutineReady)
    (hfalse : falseBranch.SubroutineReady)
    (htrue : trueBranch.SubroutineReady) :
    (RestoreFirstBitTaggedBrancherDescription
      blankBranch falseBranch trueBranch).SubroutineReady := by
  constructor
  · constructor
    · simp [RestoreFirstBitTaggedBrancherDescription,
        taggedBranchStateCount,
        taggedBranchTrueOffset,
        taggedBranchFalseOffset,
        taggedBranchBlankOffset]
      omega
    constructor
    · simp [RestoreFirstBitTaggedBrancherDescription,
        taggedBranchStateCount,
        taggedBranchTrueOffset,
        taggedBranchFalseOffset,
        taggedBranchBlankOffset]
      omega
    constructor
    · simp [RestoreFirstBitTaggedBrancherDescription,
        taggedBranchStateCount,
        taggedBranchTrueOffset,
        taggedBranchFalseOffset,
        taggedBranchBlankOffset]
      omega
    constructor
    · intro t ht
      simp [RestoreFirstBitTaggedBrancherDescription,
        taggedBranchStateCount,
        taggedBranchTrueOffset,
        taggedBranchFalseOffset,
        taggedBranchBlankOffset,
        sharedExitRetargetTransition,
        MachineDescription.transition,
        TransitionDescription.WellFormed] at ht ⊢
      have hblankStart : blankBranch.start < blankBranch.stateCount :=
        hblank.left.right.left
      have hfalseStart : falseBranch.start < falseBranch.stateCount :=
        hfalse.left.right.left
      have htrueStart : trueBranch.start < trueBranch.stateCount :=
        htrue.left.right.left
      rcases ht with rfl | rfl | rfl |
          ⟨base, hbase, rfl⟩ |
          ⟨base, hbase, rfl⟩ |
          ⟨base, hbase, rfl⟩
      · constructor
        · simp
          omega
        · by_cases hstart : blankBranch.start = blankBranch.halt
          · simp [hstart]
            omega
          · simp [hstart]
            omega
      · constructor
        · simp
          omega
        · by_cases hstart : falseBranch.start = falseBranch.halt
          · simp [hstart]
            omega
          · simp [hstart]
            omega
      · constructor
        · simp
          omega
        · by_cases hstart : trueBranch.start = trueBranch.halt
          · simp [hstart]
            omega
          · simp [hstart]
            omega
      · have hbaseWF :=
          hblank.left.right.right.right.left base hbase
        have hbaseSource : base.source < blankBranch.stateCount :=
          hbaseWF.left
        have hbaseTarget : base.target < blankBranch.stateCount :=
          hbaseWF.right
        constructor
        · change
            2 + base.source <
              2 + blankBranch.stateCount +
                falseBranch.stateCount + trueBranch.stateCount
          omega
        · by_cases htarget : base.target = blankBranch.halt
          · simpa [htarget] using
              (show
                1 <
                  2 + blankBranch.stateCount +
                    falseBranch.stateCount + trueBranch.stateCount by
                omega)
          · change
              (if base.target = blankBranch.halt then 1
                else 2 + base.target) <
                2 + blankBranch.stateCount +
                  falseBranch.stateCount + trueBranch.stateCount
            simp [htarget]
            omega
      · have hbaseWF :=
          hfalse.left.right.right.right.left base hbase
        have hbaseSource : base.source < falseBranch.stateCount :=
          hbaseWF.left
        have hbaseTarget : base.target < falseBranch.stateCount :=
          hbaseWF.right
        constructor
        · change
            2 + blankBranch.stateCount + base.source <
              2 + blankBranch.stateCount +
                falseBranch.stateCount + trueBranch.stateCount
          omega
        · by_cases htarget : base.target = falseBranch.halt
          · simpa [htarget] using
              (show
                1 <
                  2 + blankBranch.stateCount +
                    falseBranch.stateCount + trueBranch.stateCount by
                omega)
          · change
              (if base.target = falseBranch.halt then 1
                else 2 + blankBranch.stateCount + base.target) <
                2 + blankBranch.stateCount +
                  falseBranch.stateCount + trueBranch.stateCount
            simp [htarget]
            omega
      · have hbaseWF :=
          htrue.left.right.right.right.left base hbase
        have hbaseSource : base.source < trueBranch.stateCount :=
          hbaseWF.left
        have hbaseTarget : base.target < trueBranch.stateCount :=
          hbaseWF.right
        constructor
        · change
            2 + blankBranch.stateCount + falseBranch.stateCount +
                base.source <
              2 + blankBranch.stateCount +
                falseBranch.stateCount + trueBranch.stateCount
          omega
        · by_cases htarget : base.target = trueBranch.halt
          · simpa [htarget] using
              (show
                1 <
                  2 + blankBranch.stateCount +
                    falseBranch.stateCount + trueBranch.stateCount by
                omega)
          · change
              (if base.target = trueBranch.halt then 1
                else 2 + blankBranch.stateCount +
                  falseBranch.stateCount + base.target) <
                2 + blankBranch.stateCount +
                  falseBranch.stateCount + trueBranch.stateCount
            simp [htarget]
            omega
    · intro t u ht hu hkey
      simp [RestoreFirstBitTaggedBrancherDescription,
        taggedBranchStateCount,
        taggedBranchTrueOffset,
        taggedBranchFalseOffset,
        taggedBranchBlankOffset,
        sharedExitRetargetTransition,
        MachineDescription.transition] at ht hu ⊢
      rcases ht with rfl | rfl | rfl |
          ⟨baseT, hbaseT, rfl⟩ |
          ⟨baseT, hbaseT, rfl⟩ |
          ⟨baseT, hbaseT, rfl⟩
      · rcases hu with rfl | rfl | rfl |
            ⟨baseU, hbaseU, rfl⟩ |
            ⟨baseU, hbaseU, rfl⟩ |
            ⟨baseU, hbaseU, rfl⟩ <;>
          simp [TransitionDescription.SameKey,
            TransitionDescription.SameAction] at hkey ⊢ <;>
          try omega
      · rcases hu with rfl | rfl | rfl |
            ⟨baseU, hbaseU, rfl⟩ |
            ⟨baseU, hbaseU, rfl⟩ |
            ⟨baseU, hbaseU, rfl⟩ <;>
          simp [TransitionDescription.SameKey,
            TransitionDescription.SameAction] at hkey ⊢ <;>
          try omega
      · rcases hu with rfl | rfl | rfl |
            ⟨baseU, hbaseU, rfl⟩ |
            ⟨baseU, hbaseU, rfl⟩ |
            ⟨baseU, hbaseU, rfl⟩ <;>
          simp [TransitionDescription.SameKey,
            TransitionDescription.SameAction] at hkey ⊢ <;>
          try omega
      · rcases hu with rfl | rfl | rfl |
            ⟨baseU, hbaseU, rfl⟩ |
            ⟨baseU, hbaseU, rfl⟩ |
            ⟨baseU, hbaseU, rfl⟩
        · simp [TransitionDescription.SameKey] at hkey
        · simp [TransitionDescription.SameKey] at hkey
        · simp [TransitionDescription.SameKey] at hkey
        · simp [TransitionDescription.SameKey,
            TransitionDescription.SameAction] at hkey ⊢
          have hsame :=
            hblank.left.right.right.right.right
              baseT baseU hbaseT hbaseU hkey
          rcases hsame with ⟨hwrite, hmove, htarget⟩
          simp [hwrite, hmove, htarget]
        · simp [TransitionDescription.SameKey,
            TransitionDescription.SameAction] at hkey ⊢
          have hbaseTSource :
              baseT.source < blankBranch.stateCount :=
            (hblank.left.right.right.right.left baseT hbaseT).left
          omega
        · simp [TransitionDescription.SameKey,
            TransitionDescription.SameAction] at hkey ⊢
          have hbaseTSource :
              baseT.source < blankBranch.stateCount :=
            (hblank.left.right.right.right.left baseT hbaseT).left
          omega
      · rcases hu with rfl | rfl | rfl |
            ⟨baseU, hbaseU, rfl⟩ |
            ⟨baseU, hbaseU, rfl⟩ |
            ⟨baseU, hbaseU, rfl⟩
        · simp [TransitionDescription.SameKey] at hkey
        · simp [TransitionDescription.SameKey] at hkey
        · simp [TransitionDescription.SameKey] at hkey
        · simp [TransitionDescription.SameKey,
            TransitionDescription.SameAction] at hkey ⊢
          have hbaseUSource :
              baseU.source < blankBranch.stateCount :=
            (hblank.left.right.right.right.left baseU hbaseU).left
          omega
        · simp [TransitionDescription.SameKey,
            TransitionDescription.SameAction] at hkey ⊢
          have hsame :=
            hfalse.left.right.right.right.right
              baseT baseU hbaseT hbaseU hkey
          rcases hsame with ⟨hwrite, hmove, htarget⟩
          simp [hwrite, hmove, htarget]
        · simp [TransitionDescription.SameKey,
            TransitionDescription.SameAction] at hkey ⊢
          have hbaseTSource :
              baseT.source < falseBranch.stateCount :=
            (hfalse.left.right.right.right.left baseT hbaseT).left
          omega
      · rcases hu with rfl | rfl | rfl |
            ⟨baseU, hbaseU, rfl⟩ |
            ⟨baseU, hbaseU, rfl⟩ |
            ⟨baseU, hbaseU, rfl⟩
        · simp [TransitionDescription.SameKey] at hkey
        · simp [TransitionDescription.SameKey] at hkey
        · simp [TransitionDescription.SameKey] at hkey
        · simp [TransitionDescription.SameKey,
            TransitionDescription.SameAction] at hkey ⊢
          have hbaseUSource :
              baseU.source < blankBranch.stateCount :=
            (hblank.left.right.right.right.left baseU hbaseU).left
          omega
        · simp [TransitionDescription.SameKey,
            TransitionDescription.SameAction] at hkey ⊢
          have hbaseUSource :
              baseU.source < falseBranch.stateCount :=
            (hfalse.left.right.right.right.left baseU hbaseU).left
          omega
        · simp [TransitionDescription.SameKey,
            TransitionDescription.SameAction] at hkey ⊢
          have hsame :=
            htrue.left.right.right.right.right
              baseT baseU hbaseT hbaseU hkey
          rcases hsame with ⟨hwrite, hmove, htarget⟩
          simp [hwrite, hmove, htarget]
  · intro t ht
    simp [RestoreFirstBitTaggedBrancherDescription,
      taggedBranchStateCount,
      taggedBranchTrueOffset,
      taggedBranchFalseOffset,
      taggedBranchBlankOffset,
      sharedExitRetargetTransition,
      MachineDescription.transition] at ht ⊢
    rcases ht with rfl | rfl | rfl |
        ⟨base, _hbase, rfl⟩ |
        ⟨base, _hbase, rfl⟩ |
        ⟨base, _hbase, rfl⟩ <;> simp <;> omega

private theorem
    restoreFirstBitTaggedBrancherDescription_lookup_blank
    {blankBranch falseBranch trueBranch : MachineDescription}
    (_hblank : blankBranch.SubroutineReady)
    (hfalse : falseBranch.SubroutineReady)
    (htrue : trueBranch.SubroutineReady)
    {state : Nat} {cell : Option Bool}
    (hstate : state < blankBranch.stateCount) :
    (RestoreFirstBitTaggedBrancherDescription
      blankBranch falseBranch trueBranch).lookupTransition
        (taggedBranchBlankOffset + state) cell =
      Option.map
        (sharedExitRetargetTransition
          taggedBranchBlankOffset blankBranch.halt 1)
        (blankBranch.lookupTransition state cell) := by
  unfold MachineDescription.lookupTransition
  have hfindControl :
      List.find?
          (MachineDescription.Matches
            (taggedBranchBlankOffset + state) cell)
          [ MachineDescription.transition
              0 none (some false) Direction.right
              (if blankBranch.start = blankBranch.halt then 1
                else taggedBranchBlankOffset + blankBranch.start)
          , MachineDescription.transition
              0 (some false) (some false) Direction.right
              (if falseBranch.start = falseBranch.halt then 1
                else taggedBranchFalseOffset blankBranch +
                  falseBranch.start)
          , MachineDescription.transition
              0 (some true) (some false) Direction.right
              (if trueBranch.start = trueBranch.halt then 1
                else taggedBranchTrueOffset blankBranch falseBranch +
                  trueBranch.start)
          ] = none := by
    simp [MachineDescription.Matches, MachineDescription.transition,
      taggedBranchBlankOffset,
      taggedBranchFalseOffset,
      taggedBranchTrueOffset]
    omega
  have hfindFalse :
      List.find?
          (MachineDescription.Matches
            (taggedBranchBlankOffset + state) cell)
          (falseBranch.transitions.map
            (sharedExitRetargetTransition
              (taggedBranchFalseOffset blankBranch)
              falseBranch.halt 1)) = none := by
    apply (List.find?_eq_none).mpr
    intro t ht hmatch
    rcases List.mem_map.mp ht with ⟨base, hbase, rfl⟩
    have hbaseSource : base.source < falseBranch.stateCount :=
      (hfalse.left.right.right.right.left base hbase).left
    have hsource :
        taggedBranchFalseOffset blankBranch + base.source =
          taggedBranchBlankOffset + state := by
      have hpair :
          taggedBranchFalseOffset blankBranch + base.source =
              taggedBranchBlankOffset + state ∧
            base.read = cell := by
        simpa [MachineDescription.Matches,
          sharedExitRetargetTransition] using hmatch
      exact hpair.left
    simp [taggedBranchBlankOffset,
      taggedBranchFalseOffset] at hsource
    omega
  have hfindTrue :
      List.find?
          (MachineDescription.Matches
            (taggedBranchBlankOffset + state) cell)
          (trueBranch.transitions.map
            (sharedExitRetargetTransition
              (taggedBranchTrueOffset blankBranch falseBranch)
              trueBranch.halt 1)) = none := by
    apply (List.find?_eq_none).mpr
    intro t ht hmatch
    rcases List.mem_map.mp ht with ⟨base, hbase, rfl⟩
    have hbaseSource : base.source < trueBranch.stateCount :=
      (htrue.left.right.right.right.left base hbase).left
    have hsource :
        taggedBranchTrueOffset blankBranch falseBranch +
            base.source =
          taggedBranchBlankOffset + state := by
      have hpair :
          taggedBranchTrueOffset blankBranch falseBranch +
                base.source =
              taggedBranchBlankOffset + state ∧
            base.read = cell := by
        simpa [MachineDescription.Matches,
          sharedExitRetargetTransition] using hmatch
      exact hpair.left
    simp [taggedBranchBlankOffset,
      taggedBranchFalseOffset,
      taggedBranchTrueOffset] at hsource
    omega
  have hpredicate :
      (MachineDescription.Matches
          (taggedBranchBlankOffset + state) cell ∘
        sharedExitRetargetTransition
          taggedBranchBlankOffset blankBranch.halt 1) =
        MachineDescription.Matches state cell := by
    funext t
    have hsourceBeq :
        (taggedBranchBlankOffset + t.source ==
            taggedBranchBlankOffset + state) =
          (t.source == state) := by
      by_cases hsource : t.source = state
      · have hoffset :
          taggedBranchBlankOffset + t.source =
            taggedBranchBlankOffset + state := by
          omega
        have hleft :
            (taggedBranchBlankOffset + t.source ==
                taggedBranchBlankOffset + state) = true := by
          rw [beq_iff_eq]
          exact hoffset
        have hright : (t.source == state) = true := by
          rw [beq_iff_eq]
          exact hsource
        rw [hleft, hright]
      · have hoffset :
          taggedBranchBlankOffset + t.source ≠
            taggedBranchBlankOffset + state := by
          omega
        have hleft :
            (taggedBranchBlankOffset + t.source ==
                taggedBranchBlankOffset + state) = false := by
          rw [beq_eq_false_iff_ne]
          exact hoffset
        have hright : (t.source == state) = false := by
          rw [beq_eq_false_iff_ne]
          exact hsource
        rw [hleft, hright]
    simp [Function.comp, MachineDescription.Matches,
      sharedExitRetargetTransition, hsourceBeq]
  have hfindControl' :
      List.find?
          (MachineDescription.Matches (2 + state) cell)
          [ MachineDescription.transition
              0 none (some false) Direction.right
              (if blankBranch.start = blankBranch.halt then 1
                else 2 + blankBranch.start)
          , MachineDescription.transition
              0 (some false) (some false) Direction.right
              (if falseBranch.start = falseBranch.halt then 1
                else 2 + blankBranch.stateCount + falseBranch.start)
          , MachineDescription.transition
              0 (some true) (some false) Direction.right
              (if trueBranch.start = trueBranch.halt then 1
                else 2 + blankBranch.stateCount + falseBranch.stateCount +
                  trueBranch.start)
          ] = none := by
    simpa [taggedBranchBlankOffset,
      taggedBranchFalseOffset,
      taggedBranchTrueOffset] using hfindControl
  have hfindFalse' :
      List.find?
          (MachineDescription.Matches (2 + state) cell)
          (falseBranch.transitions.map
            (sharedExitRetargetTransition
              (2 + blankBranch.stateCount) falseBranch.halt 1)) = none := by
    simpa [taggedBranchBlankOffset,
      taggedBranchFalseOffset] using hfindFalse
  have hfindTrue' :
      List.find?
          (MachineDescription.Matches (2 + state) cell)
          (trueBranch.transitions.map
            (sharedExitRetargetTransition
              (2 + blankBranch.stateCount + falseBranch.stateCount)
              trueBranch.halt 1)) = none := by
    simpa [taggedBranchBlankOffset,
      taggedBranchFalseOffset,
      taggedBranchTrueOffset] using hfindTrue
  change
    List.find?
        (MachineDescription.Matches (2 + state) cell)
        ([ MachineDescription.transition
              0 none (some false) Direction.right
              (if blankBranch.start = blankBranch.halt then 1
                else 2 + blankBranch.start)
          , MachineDescription.transition
              0 (some false) (some false) Direction.right
              (if falseBranch.start = falseBranch.halt then 1
                else 2 + blankBranch.stateCount + falseBranch.start)
          , MachineDescription.transition
              0 (some true) (some false) Direction.right
              (if trueBranch.start = trueBranch.halt then 1
                else 2 + blankBranch.stateCount + falseBranch.stateCount +
                  trueBranch.start)
          ] ++
          (blankBranch.transitions.map
            (sharedExitRetargetTransition 2 blankBranch.halt 1) ++
          falseBranch.transitions.map
            (sharedExitRetargetTransition
              (2 + blankBranch.stateCount) falseBranch.halt 1) ++
          trueBranch.transitions.map
            (sharedExitRetargetTransition
              (2 + blankBranch.stateCount + falseBranch.stateCount)
              trueBranch.halt 1))) =
      Option.map
        (sharedExitRetargetTransition 2 blankBranch.halt 1)
        (List.find? (MachineDescription.Matches state cell)
          blankBranch.transitions)
  have hpredicate' :
      (MachineDescription.Matches (2 + state) cell ∘
        sharedExitRetargetTransition
          2 blankBranch.halt 1) =
        MachineDescription.Matches state cell := by
    simpa [taggedBranchBlankOffset] using hpredicate
  have hfalseMapNone :
      Option.map
          (sharedExitRetargetTransition
            (2 + blankBranch.stateCount) falseBranch.halt 1)
          (List.find?
            (MachineDescription.Matches (2 + state) cell ∘
              sharedExitRetargetTransition
                (2 + blankBranch.stateCount) falseBranch.halt 1)
            falseBranch.transitions) = none := by
    rw [← List.find?_map]
    exact hfindFalse'
  have htrueMapNone :
      Option.map
          (sharedExitRetargetTransition
            (2 + blankBranch.stateCount + falseBranch.stateCount)
            trueBranch.halt 1)
          (List.find?
            (MachineDescription.Matches (2 + state) cell ∘
              sharedExitRetargetTransition
                (2 + blankBranch.stateCount + falseBranch.stateCount)
                trueBranch.halt 1)
            trueBranch.transitions) = none := by
    rw [← List.find?_map]
    exact hfindTrue'
  rw [List.find?_append, hfindControl']
  simp
  rw [hpredicate', hfalseMapNone, htrueMapNone]
  cases hlocal :
      List.find? (MachineDescription.Matches state cell)
        blankBranch.transitions <;>
    simp

private theorem
    restoreFirstBitTaggedBrancherDescription_step_blank
    {blankBranch falseBranch trueBranch : MachineDescription}
    (hblank : blankBranch.SubroutineReady)
    (hfalse : falseBranch.SubroutineReady)
    (htrue : trueBranch.SubroutineReady)
    {c : MachineDescription.Configuration}
    (hstate : c.state < blankBranch.stateCount) :
    (RestoreFirstBitTaggedBrancherDescription
      blankBranch falseBranch trueBranch).stepConfig
        (sharedExitBranchConfiguration
          taggedBranchBlankOffset blankBranch.halt 1 c) =
      Option.map
        (sharedExitBranchConfiguration
          taggedBranchBlankOffset blankBranch.halt 1)
        (blankBranch.stepConfig c) := by
  cases c with
  | mk state tape =>
      by_cases hhalt : state = blankBranch.halt
      · subst state
        have hblankStep :
            blankBranch.stepConfig
                { state := blankBranch.halt, tape := tape } = none :=
          MachineDescription.stepConfig_halt_none hblank.right tape
        have hbrancherStep :
            (RestoreFirstBitTaggedBrancherDescription
              blankBranch falseBranch trueBranch).stepConfig
                { state := 1, tape := tape } = none :=
          MachineDescription.stepConfig_halt_none
            (restoreFirstBitTaggedBrancherDescription_subroutineReady
              hblank hfalse htrue).right tape
        simp [sharedExitBranchConfiguration, hblankStep,
          hbrancherStep]
      · have hlookup :=
          restoreFirstBitTaggedBrancherDescription_lookup_blank
            hblank hfalse htrue (state := state)
            (cell := Tape.read tape) hstate
        simp [MachineDescription.stepConfig,
          sharedExitBranchConfiguration, hhalt, hlookup]
        cases hlocal :
            blankBranch.lookupTransition state (Tape.read tape) with
        | none =>
            simp
        | some t =>
            simp [sharedExitRetargetTransition,
              sharedExitBranchConfiguration]

private theorem restoreFirstBitTaggedBrancherDescription_run_blank
    {blankBranch falseBranch trueBranch : MachineDescription}
    (hblank : blankBranch.SubroutineReady)
    (hfalse : falseBranch.SubroutineReady)
    (htrue : trueBranch.SubroutineReady)
    (n : Nat) (c : MachineDescription.Configuration)
    (hstate : c.state < blankBranch.stateCount) :
    (RestoreFirstBitTaggedBrancherDescription
      blankBranch falseBranch trueBranch).runConfig n
        (sharedExitBranchConfiguration
          taggedBranchBlankOffset blankBranch.halt 1 c) =
      sharedExitBranchConfiguration
        taggedBranchBlankOffset blankBranch.halt 1
        (blankBranch.runConfig n c) := by
  induction n generalizing c with
  | zero =>
      rfl
  | succ n ih =>
      rw [MachineDescription.runConfig]
      rw [restoreFirstBitTaggedBrancherDescription_step_blank
        hblank hfalse htrue hstate]
      cases hstep : blankBranch.stepConfig c with
      | none =>
          simp [MachineDescription.runConfig, hstep]
      | some next =>
          have hnextState : next.state < blankBranch.stateCount :=
            MachineDescription.stepConfig_state_bound hblank.left hstep
          simp [MachineDescription.runConfig, hstep, ih next hnextState]

private theorem restoreFirstBitTaggedBrancherDescription_run_none
    {blankBranch falseBranch trueBranch : MachineDescription}
    (hblank : blankBranch.SubroutineReady)
    (hfalse : falseBranch.SubroutineReady)
    (htrue : trueBranch.SubroutineReady)
    {T Tout : Tape Bool}
    (hread : Tape.read T = none)
    (hbranch :
      exists steps : Nat,
        blankBranch.runConfig steps
            { state := blankBranch.start
              tape := Tape.move Direction.right
                (Tape.write (some false) T) } =
          { state := blankBranch.halt, tape := Tout }) :
    exists steps : Nat,
      (RestoreFirstBitTaggedBrancherDescription
        blankBranch falseBranch trueBranch).runConfig steps
          { state :=
              (RestoreFirstBitTaggedBrancherDescription
                blankBranch falseBranch trueBranch).start
            tape := T } =
        { state :=
            (RestoreFirstBitTaggedBrancherDescription
              blankBranch falseBranch trueBranch).halt
          tape := Tout } := by
  rcases hbranch with ⟨n, hn⟩
  let D :=
    RestoreFirstBitTaggedBrancherDescription
      blankBranch falseBranch trueBranch
  let branchStart : MachineDescription.Configuration :=
    { state := blankBranch.start
      tape := Tape.move Direction.right (Tape.write (some false) T) }
  have hfirst :
      D.runConfig 1 { state := D.start, tape := T } =
        sharedExitBranchConfiguration
          taggedBranchBlankOffset blankBranch.halt 1
          branchStart := by
    cases T with
    | mk left head right =>
        cases head with
        | none =>
            simp [D, branchStart,
              RestoreFirstBitTaggedBrancherDescription,
              sharedExitBranchConfiguration,
              taggedBranchBlankOffset,
              taggedBranchFalseOffset,
              taggedBranchTrueOffset,
              MachineDescription.runConfig, MachineDescription.stepConfig,
              MachineDescription.lookupTransition, MachineDescription.Matches,
              MachineDescription.transition, Tape.read, Tape.write,
              Tape.move, Tape.moveRight]
        | some b =>
            cases b <;> simp [Tape.read] at hread
  refine ⟨1 + n, ?_⟩
  rw [MachineDescription.runConfig_add]
  rw [hfirst]
  have hstartBound : branchStart.state < blankBranch.stateCount := by
    exact hblank.left.right.left
  rw [restoreFirstBitTaggedBrancherDescription_run_blank
    hblank hfalse htrue n branchStart hstartBound]
  rw [hn]
  simp [RestoreFirstBitTaggedBrancherDescription,
    sharedExitBranchConfiguration]

private theorem
    restoreFirstBitTaggedBrancherDescription_lookup_false
    {blankBranch falseBranch trueBranch : MachineDescription}
    (hblank : blankBranch.SubroutineReady)
    (_hfalse : falseBranch.SubroutineReady)
    (htrue : trueBranch.SubroutineReady)
    {state : Nat} {cell : Option Bool}
    (hstate : state < falseBranch.stateCount) :
    (RestoreFirstBitTaggedBrancherDescription
      blankBranch falseBranch trueBranch).lookupTransition
        (taggedBranchFalseOffset blankBranch + state) cell =
      Option.map
        (sharedExitRetargetTransition
          (taggedBranchFalseOffset blankBranch)
          falseBranch.halt 1)
        (falseBranch.lookupTransition state cell) := by
  unfold MachineDescription.lookupTransition
  have hfindControl :
      List.find?
          (MachineDescription.Matches
            (taggedBranchFalseOffset blankBranch + state) cell)
          [ MachineDescription.transition
              0 none (some false) Direction.right
              (if blankBranch.start = blankBranch.halt then 1
                else taggedBranchBlankOffset + blankBranch.start)
          , MachineDescription.transition
              0 (some false) (some false) Direction.right
              (if falseBranch.start = falseBranch.halt then 1
                else taggedBranchFalseOffset blankBranch +
                  falseBranch.start)
          , MachineDescription.transition
              0 (some true) (some false) Direction.right
              (if trueBranch.start = trueBranch.halt then 1
                else taggedBranchTrueOffset blankBranch falseBranch +
                  trueBranch.start)
          ] = none := by
    simp [MachineDescription.Matches, MachineDescription.transition,
      taggedBranchBlankOffset,
      taggedBranchFalseOffset,
      taggedBranchTrueOffset]
    omega
  have hfindBlank :
      List.find?
          (MachineDescription.Matches
            (taggedBranchFalseOffset blankBranch + state) cell)
          (blankBranch.transitions.map
            (sharedExitRetargetTransition
              taggedBranchBlankOffset blankBranch.halt 1)) =
        none := by
    apply (List.find?_eq_none).mpr
    intro t ht hmatch
    rcases List.mem_map.mp ht with ⟨base, hbase, rfl⟩
    have hbaseSource : base.source < blankBranch.stateCount :=
      (hblank.left.right.right.right.left base hbase).left
    have hsource :
        taggedBranchBlankOffset + base.source =
          taggedBranchFalseOffset blankBranch + state := by
      have hpair :
          taggedBranchBlankOffset + base.source =
              taggedBranchFalseOffset blankBranch + state ∧
            base.read = cell := by
        simpa [MachineDescription.Matches,
          sharedExitRetargetTransition] using hmatch
      exact hpair.left
    simp [taggedBranchBlankOffset,
      taggedBranchFalseOffset] at hsource
    omega
  have hfindTrue :
      List.find?
          (MachineDescription.Matches
            (taggedBranchFalseOffset blankBranch + state) cell)
          (trueBranch.transitions.map
            (sharedExitRetargetTransition
              (taggedBranchTrueOffset blankBranch falseBranch)
              trueBranch.halt 1)) = none := by
    apply (List.find?_eq_none).mpr
    intro t ht hmatch
    rcases List.mem_map.mp ht with ⟨base, hbase, rfl⟩
    have hbaseSource : base.source < trueBranch.stateCount :=
      (htrue.left.right.right.right.left base hbase).left
    have hsource :
        taggedBranchTrueOffset blankBranch falseBranch +
            base.source =
          taggedBranchFalseOffset blankBranch + state := by
      have hpair :
          taggedBranchTrueOffset blankBranch falseBranch +
                base.source =
              taggedBranchFalseOffset blankBranch + state ∧
            base.read = cell := by
        simpa [MachineDescription.Matches,
          sharedExitRetargetTransition] using hmatch
      exact hpair.left
    simp [taggedBranchBlankOffset,
      taggedBranchFalseOffset,
      taggedBranchTrueOffset] at hsource
    omega
  have hpredicate :
      (MachineDescription.Matches
          (taggedBranchFalseOffset blankBranch + state) cell ∘
        sharedExitRetargetTransition
          (taggedBranchFalseOffset blankBranch)
          falseBranch.halt 1) =
        MachineDescription.Matches state cell := by
    funext t
    have hsourceBeq :
        (taggedBranchFalseOffset blankBranch + t.source ==
            taggedBranchFalseOffset blankBranch + state) =
          (t.source == state) := by
      by_cases hsource : t.source = state
      · have hoffset :
          taggedBranchFalseOffset blankBranch + t.source =
            taggedBranchFalseOffset blankBranch + state := by
          omega
        have hleft :
            (taggedBranchFalseOffset blankBranch + t.source ==
                taggedBranchFalseOffset blankBranch + state) =
              true := by
          rw [beq_iff_eq]
          exact hoffset
        have hright : (t.source == state) = true := by
          rw [beq_iff_eq]
          exact hsource
        rw [hleft, hright]
      · have hoffset :
          taggedBranchFalseOffset blankBranch + t.source ≠
            taggedBranchFalseOffset blankBranch + state := by
          omega
        have hleft :
            (taggedBranchFalseOffset blankBranch + t.source ==
                taggedBranchFalseOffset blankBranch + state) =
              false := by
          rw [beq_eq_false_iff_ne]
          exact hoffset
        have hright : (t.source == state) = false := by
          rw [beq_eq_false_iff_ne]
          exact hsource
        rw [hleft, hright]
    simp [Function.comp, MachineDescription.Matches,
      sharedExitRetargetTransition, hsourceBeq]
  have hfindControl' :
      List.find?
          (MachineDescription.Matches
            (2 + blankBranch.stateCount + state) cell)
          [ MachineDescription.transition
              0 none (some false) Direction.right
              (if blankBranch.start = blankBranch.halt then 1
                else 2 + blankBranch.start)
          , MachineDescription.transition
              0 (some false) (some false) Direction.right
              (if falseBranch.start = falseBranch.halt then 1
                else 2 + blankBranch.stateCount + falseBranch.start)
          , MachineDescription.transition
              0 (some true) (some false) Direction.right
              (if trueBranch.start = trueBranch.halt then 1
                else 2 + blankBranch.stateCount + falseBranch.stateCount +
                  trueBranch.start)
          ] = none := by
    simpa [taggedBranchBlankOffset,
      taggedBranchFalseOffset,
      taggedBranchTrueOffset] using hfindControl
  have hfindBlank' :
      List.find?
          (MachineDescription.Matches
            (2 + blankBranch.stateCount + state) cell)
          (blankBranch.transitions.map
            (sharedExitRetargetTransition 2
              blankBranch.halt 1)) = none := by
    simpa [taggedBranchBlankOffset,
      taggedBranchFalseOffset] using hfindBlank
  have hfindTrue' :
      List.find?
          (MachineDescription.Matches
            (2 + blankBranch.stateCount + state) cell)
          (trueBranch.transitions.map
            (sharedExitRetargetTransition
              (2 + blankBranch.stateCount + falseBranch.stateCount)
              trueBranch.halt 1)) = none := by
    simpa [taggedBranchBlankOffset,
      taggedBranchFalseOffset,
      taggedBranchTrueOffset] using hfindTrue
  change
    List.find?
        (MachineDescription.Matches
          (2 + blankBranch.stateCount + state) cell)
        ([ MachineDescription.transition
              0 none (some false) Direction.right
              (if blankBranch.start = blankBranch.halt then 1
                else 2 + blankBranch.start)
          , MachineDescription.transition
              0 (some false) (some false) Direction.right
              (if falseBranch.start = falseBranch.halt then 1
                else 2 + blankBranch.stateCount + falseBranch.start)
          , MachineDescription.transition
              0 (some true) (some false) Direction.right
              (if trueBranch.start = trueBranch.halt then 1
                else 2 + blankBranch.stateCount + falseBranch.stateCount +
                  trueBranch.start)
          ] ++
          (blankBranch.transitions.map
            (sharedExitRetargetTransition 2 blankBranch.halt 1) ++
          falseBranch.transitions.map
            (sharedExitRetargetTransition
              (2 + blankBranch.stateCount) falseBranch.halt 1) ++
          trueBranch.transitions.map
            (sharedExitRetargetTransition
              (2 + blankBranch.stateCount + falseBranch.stateCount)
              trueBranch.halt 1))) =
      Option.map
        (sharedExitRetargetTransition
          (2 + blankBranch.stateCount) falseBranch.halt 1)
        (List.find? (MachineDescription.Matches state cell)
          falseBranch.transitions)
  have hpredicate' :
      (MachineDescription.Matches
          (2 + blankBranch.stateCount + state) cell ∘
        sharedExitRetargetTransition
          (2 + blankBranch.stateCount) falseBranch.halt 1) =
        MachineDescription.Matches state cell := by
    simpa [taggedBranchBlankOffset,
      taggedBranchFalseOffset] using hpredicate
  have hblankMapNone :
      Option.map
          (sharedExitRetargetTransition 2 blankBranch.halt 1)
          (List.find?
            (MachineDescription.Matches
                (2 + blankBranch.stateCount + state) cell ∘
              sharedExitRetargetTransition 2
                blankBranch.halt 1)
            blankBranch.transitions) = none := by
    rw [← List.find?_map]
    exact hfindBlank'
  have htrueMapNone :
      Option.map
          (sharedExitRetargetTransition
            (2 + blankBranch.stateCount + falseBranch.stateCount)
            trueBranch.halt 1)
          (List.find?
            (MachineDescription.Matches
                (2 + blankBranch.stateCount + state) cell ∘
              sharedExitRetargetTransition
                (2 + blankBranch.stateCount + falseBranch.stateCount)
                trueBranch.halt 1)
            trueBranch.transitions) = none := by
    rw [← List.find?_map]
    exact hfindTrue'
  rw [List.find?_append, hfindControl']
  simp
  rw [hblankMapNone, hpredicate', htrueMapNone]
  cases hlocal :
      List.find? (MachineDescription.Matches state cell)
        falseBranch.transitions <;>
    simp

private theorem
    restoreFirstBitTaggedBrancherDescription_step_false
    {blankBranch falseBranch trueBranch : MachineDescription}
    (hblank : blankBranch.SubroutineReady)
    (hfalse : falseBranch.SubroutineReady)
    (htrue : trueBranch.SubroutineReady)
    {c : MachineDescription.Configuration}
    (hstate : c.state < falseBranch.stateCount) :
    (RestoreFirstBitTaggedBrancherDescription
      blankBranch falseBranch trueBranch).stepConfig
        (sharedExitBranchConfiguration
          (taggedBranchFalseOffset blankBranch)
          falseBranch.halt 1 c) =
      Option.map
        (sharedExitBranchConfiguration
          (taggedBranchFalseOffset blankBranch)
          falseBranch.halt 1)
        (falseBranch.stepConfig c) := by
  cases c with
  | mk state tape =>
      by_cases hhalt : state = falseBranch.halt
      · subst state
        have hfalseStep :
            falseBranch.stepConfig
                { state := falseBranch.halt, tape := tape } = none :=
          MachineDescription.stepConfig_halt_none hfalse.right tape
        have hbrancherStep :
            (RestoreFirstBitTaggedBrancherDescription
              blankBranch falseBranch trueBranch).stepConfig
                { state := 1, tape := tape } = none :=
          MachineDescription.stepConfig_halt_none
            (restoreFirstBitTaggedBrancherDescription_subroutineReady
              hblank hfalse htrue).right tape
        simp [sharedExitBranchConfiguration, hfalseStep,
          hbrancherStep]
      · have hlookup :=
          restoreFirstBitTaggedBrancherDescription_lookup_false
            hblank hfalse htrue (state := state)
            (cell := Tape.read tape) hstate
        simp [MachineDescription.stepConfig,
          sharedExitBranchConfiguration, hhalt, hlookup]
        cases hlocal :
            falseBranch.lookupTransition state (Tape.read tape) with
        | none =>
            simp
        | some t =>
            simp [sharedExitRetargetTransition,
              sharedExitBranchConfiguration]

private theorem restoreFirstBitTaggedBrancherDescription_run_false_branch
    {blankBranch falseBranch trueBranch : MachineDescription}
    (hblank : blankBranch.SubroutineReady)
    (hfalse : falseBranch.SubroutineReady)
    (htrue : trueBranch.SubroutineReady)
    (n : Nat) (c : MachineDescription.Configuration)
    (hstate : c.state < falseBranch.stateCount) :
    (RestoreFirstBitTaggedBrancherDescription
      blankBranch falseBranch trueBranch).runConfig n
        (sharedExitBranchConfiguration
          (taggedBranchFalseOffset blankBranch)
          falseBranch.halt 1 c) =
      sharedExitBranchConfiguration
        (taggedBranchFalseOffset blankBranch)
        falseBranch.halt 1
        (falseBranch.runConfig n c) := by
  induction n generalizing c with
  | zero =>
      rfl
  | succ n ih =>
      rw [MachineDescription.runConfig]
      rw [restoreFirstBitTaggedBrancherDescription_step_false
        hblank hfalse htrue hstate]
      cases hstep : falseBranch.stepConfig c with
      | none =>
          simp [MachineDescription.runConfig, hstep]
      | some next =>
          have hnextState : next.state < falseBranch.stateCount :=
            MachineDescription.stepConfig_state_bound hfalse.left hstep
          simp [MachineDescription.runConfig, hstep, ih next hnextState]

private theorem
    restoreFirstBitTaggedBrancherDescription_run_false
    {blankBranch falseBranch trueBranch : MachineDescription}
    (hblank : blankBranch.SubroutineReady)
    (hfalse : falseBranch.SubroutineReady)
    (htrue : trueBranch.SubroutineReady)
    {T Tout : Tape Bool}
    (hread : Tape.read T = some false)
    (hbranch :
      exists steps : Nat,
        falseBranch.runConfig steps
            { state := falseBranch.start
              tape := Tape.move Direction.right
                (Tape.write (some false) T) } =
          { state := falseBranch.halt, tape := Tout }) :
    exists steps : Nat,
      (RestoreFirstBitTaggedBrancherDescription
        blankBranch falseBranch trueBranch).runConfig steps
          { state :=
              (RestoreFirstBitTaggedBrancherDescription
                blankBranch falseBranch trueBranch).start
            tape := T } =
        { state :=
            (RestoreFirstBitTaggedBrancherDescription
              blankBranch falseBranch trueBranch).halt
          tape := Tout } := by
  rcases hbranch with ⟨n, hn⟩
  let D :=
    RestoreFirstBitTaggedBrancherDescription
      blankBranch falseBranch trueBranch
  let branchStart : MachineDescription.Configuration :=
    { state := falseBranch.start
      tape := Tape.move Direction.right (Tape.write (some false) T) }
  have hfirst :
      D.runConfig 1 { state := D.start, tape := T } =
        sharedExitBranchConfiguration
          (taggedBranchFalseOffset blankBranch)
          falseBranch.halt 1
          branchStart := by
    cases T with
    | mk left head right =>
        cases head with
        | none =>
            simp [Tape.read] at hread
        | some b =>
            cases b
            · simp [D, branchStart,
                RestoreFirstBitTaggedBrancherDescription,
                sharedExitBranchConfiguration,
                taggedBranchBlankOffset,
                taggedBranchFalseOffset,
                taggedBranchTrueOffset,
                MachineDescription.runConfig, MachineDescription.stepConfig,
                MachineDescription.lookupTransition,
                MachineDescription.Matches,
                MachineDescription.transition, Tape.read, Tape.write,
                Tape.move, Tape.moveRight]
            · simp [Tape.read] at hread
  refine ⟨1 + n, ?_⟩
  rw [MachineDescription.runConfig_add]
  rw [hfirst]
  have hstartBound : branchStart.state < falseBranch.stateCount := by
    exact hfalse.left.right.left
  rw [restoreFirstBitTaggedBrancherDescription_run_false_branch
    hblank hfalse htrue n branchStart hstartBound]
  rw [hn]
  simp [RestoreFirstBitTaggedBrancherDescription,
    sharedExitBranchConfiguration]

private theorem
    restoreFirstBitTaggedBrancherDescription_lookup_true
    {blankBranch falseBranch trueBranch : MachineDescription}
    (hblank : blankBranch.SubroutineReady)
    (hfalse : falseBranch.SubroutineReady)
    (_htrue : trueBranch.SubroutineReady)
    {state : Nat} {cell : Option Bool}
    (_hstate : state < trueBranch.stateCount) :
    (RestoreFirstBitTaggedBrancherDescription
      blankBranch falseBranch trueBranch).lookupTransition
        (taggedBranchTrueOffset blankBranch falseBranch + state)
        cell =
      Option.map
        (sharedExitRetargetTransition
          (taggedBranchTrueOffset blankBranch falseBranch)
          trueBranch.halt 1)
        (trueBranch.lookupTransition state cell) := by
  unfold MachineDescription.lookupTransition
  have hfindControl :
      List.find?
          (MachineDescription.Matches
            (taggedBranchTrueOffset blankBranch falseBranch +
              state) cell)
          [ MachineDescription.transition
              0 none (some false) Direction.right
              (if blankBranch.start = blankBranch.halt then 1
                else taggedBranchBlankOffset + blankBranch.start)
          , MachineDescription.transition
              0 (some false) (some false) Direction.right
              (if falseBranch.start = falseBranch.halt then 1
                else taggedBranchFalseOffset blankBranch +
                  falseBranch.start)
          , MachineDescription.transition
              0 (some true) (some false) Direction.right
              (if trueBranch.start = trueBranch.halt then 1
                else taggedBranchTrueOffset blankBranch falseBranch +
                  trueBranch.start)
          ] = none := by
    simp [MachineDescription.Matches, MachineDescription.transition,
      taggedBranchBlankOffset,
      taggedBranchFalseOffset,
      taggedBranchTrueOffset]
    omega
  have hfindBlank :
      List.find?
          (MachineDescription.Matches
            (taggedBranchTrueOffset blankBranch falseBranch +
              state) cell)
          (blankBranch.transitions.map
            (sharedExitRetargetTransition
              taggedBranchBlankOffset blankBranch.halt 1)) =
        none := by
    apply (List.find?_eq_none).mpr
    intro t ht hmatch
    rcases List.mem_map.mp ht with ⟨base, hbase, rfl⟩
    have hbaseSource : base.source < blankBranch.stateCount :=
      (hblank.left.right.right.right.left base hbase).left
    have hsource :
        taggedBranchBlankOffset + base.source =
          taggedBranchTrueOffset blankBranch falseBranch +
            state := by
      have hpair :
          taggedBranchBlankOffset + base.source =
              taggedBranchTrueOffset blankBranch falseBranch +
                state ∧
            base.read = cell := by
        simpa [MachineDescription.Matches,
          sharedExitRetargetTransition] using hmatch
      exact hpair.left
    simp [taggedBranchBlankOffset,
      taggedBranchFalseOffset,
      taggedBranchTrueOffset] at hsource
    omega
  have hfindFalse :
      List.find?
          (MachineDescription.Matches
            (taggedBranchTrueOffset blankBranch falseBranch +
              state) cell)
          (falseBranch.transitions.map
            (sharedExitRetargetTransition
              (taggedBranchFalseOffset blankBranch)
              falseBranch.halt 1)) = none := by
    apply (List.find?_eq_none).mpr
    intro t ht hmatch
    rcases List.mem_map.mp ht with ⟨base, hbase, rfl⟩
    have hbaseSource : base.source < falseBranch.stateCount :=
      (hfalse.left.right.right.right.left base hbase).left
    have hsource :
        taggedBranchFalseOffset blankBranch + base.source =
          taggedBranchTrueOffset blankBranch falseBranch +
            state := by
      have hpair :
          taggedBranchFalseOffset blankBranch + base.source =
              taggedBranchTrueOffset blankBranch falseBranch +
                state ∧
            base.read = cell := by
        simpa [MachineDescription.Matches,
          sharedExitRetargetTransition] using hmatch
      exact hpair.left
    simp [taggedBranchBlankOffset,
      taggedBranchFalseOffset,
      taggedBranchTrueOffset] at hsource
    omega
  have hpredicate :
      (MachineDescription.Matches
          (taggedBranchTrueOffset blankBranch falseBranch +
            state) cell ∘
        sharedExitRetargetTransition
          (taggedBranchTrueOffset blankBranch falseBranch)
          trueBranch.halt 1) =
        MachineDescription.Matches state cell := by
    funext t
    have hsourceBeq :
        (taggedBranchTrueOffset blankBranch falseBranch +
              t.source ==
            taggedBranchTrueOffset blankBranch falseBranch +
              state) =
          (t.source == state) := by
      by_cases hsource : t.source = state
      · have hoffset :
          taggedBranchTrueOffset blankBranch falseBranch +
                t.source =
            taggedBranchTrueOffset blankBranch falseBranch +
                state := by
          omega
        have hleft :
            (taggedBranchTrueOffset blankBranch falseBranch +
                  t.source ==
                taggedBranchTrueOffset blankBranch falseBranch +
                  state) = true := by
          rw [beq_iff_eq]
          exact hoffset
        have hright : (t.source == state) = true := by
          rw [beq_iff_eq]
          exact hsource
        rw [hleft, hright]
      · have hoffset :
          taggedBranchTrueOffset blankBranch falseBranch +
                t.source ≠
            taggedBranchTrueOffset blankBranch falseBranch +
                state := by
          omega
        have hleft :
            (taggedBranchTrueOffset blankBranch falseBranch +
                  t.source ==
                taggedBranchTrueOffset blankBranch falseBranch +
                  state) = false := by
          rw [beq_eq_false_iff_ne]
          exact hoffset
        have hright : (t.source == state) = false := by
          rw [beq_eq_false_iff_ne]
          exact hsource
        rw [hleft, hright]
    simp [Function.comp, MachineDescription.Matches,
      sharedExitRetargetTransition, hsourceBeq]
  have hfindControl' :
      List.find?
          (MachineDescription.Matches
            (2 + blankBranch.stateCount + falseBranch.stateCount + state)
            cell)
          [ MachineDescription.transition
              0 none (some false) Direction.right
              (if blankBranch.start = blankBranch.halt then 1
                else 2 + blankBranch.start)
          , MachineDescription.transition
              0 (some false) (some false) Direction.right
              (if falseBranch.start = falseBranch.halt then 1
                else 2 + blankBranch.stateCount + falseBranch.start)
          , MachineDescription.transition
              0 (some true) (some false) Direction.right
              (if trueBranch.start = trueBranch.halt then 1
                else 2 + blankBranch.stateCount + falseBranch.stateCount +
                  trueBranch.start)
          ] = none := by
    simpa [taggedBranchBlankOffset,
      taggedBranchFalseOffset,
      taggedBranchTrueOffset] using hfindControl
  have hfindBlank' :
      List.find?
          (MachineDescription.Matches
            (2 + blankBranch.stateCount + falseBranch.stateCount + state)
            cell)
          (blankBranch.transitions.map
            (sharedExitRetargetTransition 2
              blankBranch.halt 1)) = none := by
    simpa [taggedBranchBlankOffset,
      taggedBranchFalseOffset,
      taggedBranchTrueOffset] using hfindBlank
  have hfindFalse' :
      List.find?
          (MachineDescription.Matches
            (2 + blankBranch.stateCount + falseBranch.stateCount + state)
            cell)
          (falseBranch.transitions.map
            (sharedExitRetargetTransition
              (2 + blankBranch.stateCount)
              falseBranch.halt 1)) = none := by
    simpa [taggedBranchBlankOffset,
      taggedBranchFalseOffset,
      taggedBranchTrueOffset] using hfindFalse
  change
    List.find?
        (MachineDescription.Matches
          (2 + blankBranch.stateCount + falseBranch.stateCount + state)
          cell)
        ([ MachineDescription.transition
              0 none (some false) Direction.right
              (if blankBranch.start = blankBranch.halt then 1
                else 2 + blankBranch.start)
          , MachineDescription.transition
              0 (some false) (some false) Direction.right
              (if falseBranch.start = falseBranch.halt then 1
                else 2 + blankBranch.stateCount + falseBranch.start)
          , MachineDescription.transition
              0 (some true) (some false) Direction.right
              (if trueBranch.start = trueBranch.halt then 1
                else 2 + blankBranch.stateCount + falseBranch.stateCount +
                  trueBranch.start)
          ] ++
          (blankBranch.transitions.map
            (sharedExitRetargetTransition 2 blankBranch.halt 1) ++
          falseBranch.transitions.map
            (sharedExitRetargetTransition
              (2 + blankBranch.stateCount) falseBranch.halt 1) ++
          trueBranch.transitions.map
            (sharedExitRetargetTransition
              (2 + blankBranch.stateCount + falseBranch.stateCount)
              trueBranch.halt 1))) =
      Option.map
        (sharedExitRetargetTransition
          (2 + blankBranch.stateCount + falseBranch.stateCount)
          trueBranch.halt 1)
        (List.find? (MachineDescription.Matches state cell)
          trueBranch.transitions)
  have hpredicate' :
      (MachineDescription.Matches
          (2 + blankBranch.stateCount + falseBranch.stateCount + state)
          cell ∘
        sharedExitRetargetTransition
          (2 + blankBranch.stateCount + falseBranch.stateCount)
          trueBranch.halt 1) =
        MachineDescription.Matches state cell := by
    simpa [taggedBranchBlankOffset,
      taggedBranchFalseOffset,
      taggedBranchTrueOffset] using hpredicate
  have hblankMapNone :
      Option.map
          (sharedExitRetargetTransition 2 blankBranch.halt 1)
          (List.find?
            (MachineDescription.Matches
                (2 + blankBranch.stateCount + falseBranch.stateCount +
                  state) cell ∘
              sharedExitRetargetTransition 2
                blankBranch.halt 1)
            blankBranch.transitions) = none := by
    rw [← List.find?_map]
    exact hfindBlank'
  have hfalseMapNone :
      Option.map
          (sharedExitRetargetTransition
            (2 + blankBranch.stateCount) falseBranch.halt 1)
          (List.find?
            (MachineDescription.Matches
                (2 + blankBranch.stateCount + falseBranch.stateCount +
                  state) cell ∘
              sharedExitRetargetTransition
                (2 + blankBranch.stateCount) falseBranch.halt 1)
            falseBranch.transitions) = none := by
    rw [← List.find?_map]
    exact hfindFalse'
  rw [List.find?_append, hfindControl']
  simp
  rw [hblankMapNone, hfalseMapNone, hpredicate']
  cases hlocal :
      List.find? (MachineDescription.Matches state cell)
        trueBranch.transitions <;>
    simp

private theorem
    restoreFirstBitTaggedBrancherDescription_step_true
    {blankBranch falseBranch trueBranch : MachineDescription}
    (hblank : blankBranch.SubroutineReady)
    (hfalse : falseBranch.SubroutineReady)
    (htrue : trueBranch.SubroutineReady)
    {c : MachineDescription.Configuration}
    (hstate : c.state < trueBranch.stateCount) :
    (RestoreFirstBitTaggedBrancherDescription
      blankBranch falseBranch trueBranch).stepConfig
        (sharedExitBranchConfiguration
          (taggedBranchTrueOffset blankBranch falseBranch)
          trueBranch.halt 1 c) =
      Option.map
        (sharedExitBranchConfiguration
          (taggedBranchTrueOffset blankBranch falseBranch)
          trueBranch.halt 1)
        (trueBranch.stepConfig c) := by
  cases c with
  | mk state tape =>
      by_cases hhalt : state = trueBranch.halt
      · subst state
        have htrueStep :
            trueBranch.stepConfig
                { state := trueBranch.halt, tape := tape } = none :=
          MachineDescription.stepConfig_halt_none htrue.right tape
        have hbrancherStep :
            (RestoreFirstBitTaggedBrancherDescription
              blankBranch falseBranch trueBranch).stepConfig
                { state := 1, tape := tape } = none :=
          MachineDescription.stepConfig_halt_none
            (restoreFirstBitTaggedBrancherDescription_subroutineReady
              hblank hfalse htrue).right tape
        simp [sharedExitBranchConfiguration, htrueStep,
          hbrancherStep]
      · have hlookup :=
          restoreFirstBitTaggedBrancherDescription_lookup_true
            hblank hfalse htrue (state := state)
            (cell := Tape.read tape) hstate
        simp [MachineDescription.stepConfig,
          sharedExitBranchConfiguration, hhalt, hlookup]
        cases hlocal :
            trueBranch.lookupTransition state (Tape.read tape) with
        | none =>
            simp
        | some t =>
            simp [sharedExitRetargetTransition,
              sharedExitBranchConfiguration]

private theorem restoreFirstBitTaggedBrancherDescription_run_true_branch
    {blankBranch falseBranch trueBranch : MachineDescription}
    (hblank : blankBranch.SubroutineReady)
    (hfalse : falseBranch.SubroutineReady)
    (htrue : trueBranch.SubroutineReady)
    (n : Nat) (c : MachineDescription.Configuration)
    (hstate : c.state < trueBranch.stateCount) :
    (RestoreFirstBitTaggedBrancherDescription
      blankBranch falseBranch trueBranch).runConfig n
        (sharedExitBranchConfiguration
          (taggedBranchTrueOffset blankBranch falseBranch)
          trueBranch.halt 1 c) =
      sharedExitBranchConfiguration
        (taggedBranchTrueOffset blankBranch falseBranch)
        trueBranch.halt 1
        (trueBranch.runConfig n c) := by
  induction n generalizing c with
  | zero =>
      rfl
  | succ n ih =>
      rw [MachineDescription.runConfig]
      rw [restoreFirstBitTaggedBrancherDescription_step_true
        hblank hfalse htrue hstate]
      cases hstep : trueBranch.stepConfig c with
      | none =>
          simp [MachineDescription.runConfig, hstep]
      | some next =>
          have hnextState : next.state < trueBranch.stateCount :=
            MachineDescription.stepConfig_state_bound htrue.left hstep
          simp [MachineDescription.runConfig, hstep, ih next hnextState]

private theorem restoreFirstBitTaggedBrancherDescription_run_true
    {blankBranch falseBranch trueBranch : MachineDescription}
    (hblank : blankBranch.SubroutineReady)
    (hfalse : falseBranch.SubroutineReady)
    (htrue : trueBranch.SubroutineReady)
    {T Tout : Tape Bool}
    (hread : Tape.read T = some true)
    (hbranch :
      exists steps : Nat,
        trueBranch.runConfig steps
            { state := trueBranch.start
              tape := Tape.move Direction.right
                (Tape.write (some false) T) } =
          { state := trueBranch.halt, tape := Tout }) :
    exists steps : Nat,
      (RestoreFirstBitTaggedBrancherDescription
        blankBranch falseBranch trueBranch).runConfig steps
          { state :=
              (RestoreFirstBitTaggedBrancherDescription
                blankBranch falseBranch trueBranch).start
            tape := T } =
        { state :=
            (RestoreFirstBitTaggedBrancherDescription
              blankBranch falseBranch trueBranch).halt
          tape := Tout } := by
  rcases hbranch with ⟨n, hn⟩
  let D :=
    RestoreFirstBitTaggedBrancherDescription
      blankBranch falseBranch trueBranch
  let branchStart : MachineDescription.Configuration :=
    { state := trueBranch.start
      tape := Tape.move Direction.right (Tape.write (some false) T) }
  have hfirst :
      D.runConfig 1 { state := D.start, tape := T } =
        sharedExitBranchConfiguration
          (taggedBranchTrueOffset blankBranch falseBranch)
          trueBranch.halt 1
          branchStart := by
    cases T with
    | mk left head right =>
        cases head with
        | none =>
            simp [Tape.read] at hread
        | some b =>
            cases b
            · simp [Tape.read] at hread
            · simp [D, branchStart,
                RestoreFirstBitTaggedBrancherDescription,
                sharedExitBranchConfiguration,
                taggedBranchBlankOffset,
                taggedBranchFalseOffset,
                taggedBranchTrueOffset,
                MachineDescription.runConfig, MachineDescription.stepConfig,
                MachineDescription.lookupTransition,
                MachineDescription.Matches,
                MachineDescription.transition, Tape.read, Tape.write,
                Tape.move, Tape.moveRight]
  refine ⟨1 + n, ?_⟩
  rw [MachineDescription.runConfig_add]
  rw [hfirst]
  have hstartBound : branchStart.state < trueBranch.stateCount := by
    exact htrue.left.right.left
  rw [restoreFirstBitTaggedBrancherDescription_run_true_branch
    hblank hfalse htrue n branchStart hstartBound]
  rw [hn]
  simp [RestoreFirstBitTaggedBrancherDescription,
    sharedExitBranchConfiguration]

private def appendInputTapeHeadRouterTaggedTape
    (tag : Option Bool) (w : Word Bool) (stage : Nat)
    (suffixBits : Word Bool) : Tape Bool :=
  tapeAtCells [tag]
    (some false ::
      ((List.append [false, true]
        (List.append (stageInputBits w stage)
          suffixBits)).map some))

private def AppendInputTapeHeadRouterDescription :
    MachineDescription where
  stateCount := 32
  start := 0
  halt := 31
  transitions :=
    [ MachineDescription.transition
        0 (some false) none Direction.right 1
    , MachineDescription.transition
        1 (some false) (some false) Direction.right 2
    , MachineDescription.transition
        2 (some false) (some false) Direction.right 3
    , MachineDescription.transition
        3 (some true) (some true) Direction.right 4
    , MachineDescription.transition
        4 (some false) (some false) Direction.right 5
    , MachineDescription.transition
        5 (some false) (some false) Direction.right 6
    , MachineDescription.transition
        6 (some true) (some true) Direction.right 7
    , MachineDescription.transition
        7 (some true) (some true) Direction.left 20
    , MachineDescription.transition
        7 (some false) (some false) Direction.right 8
    , MachineDescription.transition
        8 (some false) (some false) Direction.right 9
    , MachineDescription.transition
        9 (some false) (some false) Direction.right 10
    , MachineDescription.transition
        10 (some true) (some true) Direction.right 11
    , MachineDescription.transition
        11 (some false) (some false) Direction.right 8
    , MachineDescription.transition
        11 (some true) (some true) Direction.right 12
    , MachineDescription.transition
        12 (some false) (some false) Direction.right 13
    , MachineDescription.transition
        13 (some true) (some true) Direction.right 14
    , MachineDescription.transition
        14 (some false) (some false) Direction.left 21
    , MachineDescription.transition
        14 (some true) (some true) Direction.left 22
    , MachineDescription.transition
        20 (some false) (some false) Direction.left 20
    , MachineDescription.transition
        20 (some true) (some true) Direction.left 20
    , MachineDescription.transition
        20 none none Direction.right 31
    , MachineDescription.transition
        21 (some false) (some false) Direction.left 21
    , MachineDescription.transition
        21 (some true) (some true) Direction.left 21
    , MachineDescription.transition
        21 none (some false) Direction.right 31
    , MachineDescription.transition
        22 (some false) (some false) Direction.left 22
    , MachineDescription.transition
        22 (some true) (some true) Direction.left 22
    , MachineDescription.transition
        22 none (some true) Direction.right 31
    , MachineDescription.transition
        23 (some false) none Direction.right 31
    , MachineDescription.transition
        24 (some false) (some false) Direction.right 31
    , MachineDescription.transition
        25 (some false) (some true) Direction.right 31
    ]

private theorem appendInputTapeHeadRouterDescription_wellFormed :
    AppendInputTapeHeadRouterDescription.WellFormed := by
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · intro t ht
    exact transition_wellFormed_of_all
      (l := AppendInputTapeHeadRouterDescription.transitions)
      (stateCount :=
        AppendInputTapeHeadRouterDescription.stateCount)
      (by
        native_decide) t ht
  · intro t u ht hu hkey
    exact transition_deterministic_of_all
      (l := AppendInputTapeHeadRouterDescription.transitions)
      (by
        native_decide) t u ht hu hkey

private theorem
    appendInputTapeHeadRouterDescription_haltTransitionFree :
    AppendInputTapeHeadRouterDescription.HaltTransitionFree := by
  intro t ht
  exact transition_notFrom_of_all
    (l := AppendInputTapeHeadRouterDescription.transitions)
    (state := AppendInputTapeHeadRouterDescription.halt)
    (by
      native_decide) t ht

private theorem appendInputTapeHeadRouterDescription_subroutineReady :
    AppendInputTapeHeadRouterDescription.SubroutineReady :=
  ⟨appendInputTapeHeadRouterDescription_wellFormed,
    appendInputTapeHeadRouterDescription_haltTransitionFree⟩

private theorem appendInputTapeHeadRouterDescription_run_return20
    (beforeRevBits : Word Bool) (current : Bool)
    (right : List (Option Bool)) :
    AppendInputTapeHeadRouterDescription.runConfig
        (beforeRevBits.length + 3)
        (config 20
          (List.append (beforeRevBits.map some)
            [some false, none])
          (some current :: right)) =
      config 31 [none]
        (some false ::
          List.append (beforeRevBits.reverse.map some)
            (some current :: right)) := by
  induction beforeRevBits generalizing current right with
  | nil =>
      cases current <;>
        simp [AppendInputTapeHeadRouterDescription,
          config, tapeAtCells,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, Tape.moveRight]
  | cons bit rest ih =>
      cases current
      · simpa [MachineDescription.runConfig, config,
          tapeAtCells,
          AppendInputTapeHeadRouterDescription,
          MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, List.append_assoc] using
          ih bit (some false :: right)
      · simpa [MachineDescription.runConfig, config,
          tapeAtCells,
          AppendInputTapeHeadRouterDescription,
          MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, List.append_assoc] using
          ih bit (some true :: right)

private theorem appendInputTapeHeadRouterDescription_run_return21
    (beforeRevBits : Word Bool) (current : Bool)
    (right : List (Option Bool)) :
    AppendInputTapeHeadRouterDescription.runConfig
        (beforeRevBits.length + 3)
        (config 21
          (List.append (beforeRevBits.map some)
            [some false, none])
          (some current :: right)) =
      config 31 [some false]
        (some false ::
          List.append (beforeRevBits.reverse.map some)
            (some current :: right)) := by
  induction beforeRevBits generalizing current right with
  | nil =>
      cases current <;>
        simp [AppendInputTapeHeadRouterDescription,
          config, tapeAtCells,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, Tape.moveRight]
  | cons bit rest ih =>
      cases current
      · simpa [MachineDescription.runConfig, config,
          tapeAtCells,
          AppendInputTapeHeadRouterDescription,
          MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, List.append_assoc] using
          ih bit (some false :: right)
      · simpa [MachineDescription.runConfig, config,
          tapeAtCells,
          AppendInputTapeHeadRouterDescription,
          MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, List.append_assoc] using
          ih bit (some true :: right)

private theorem appendInputTapeHeadRouterDescription_run_return22
    (beforeRevBits : Word Bool) (current : Bool)
    (right : List (Option Bool)) :
    AppendInputTapeHeadRouterDescription.runConfig
        (beforeRevBits.length + 3)
        (config 22
          (List.append (beforeRevBits.map some)
            [some false, none])
          (some current :: right)) =
      config 31 [some true]
        (some false ::
          List.append (beforeRevBits.reverse.map some)
            (some current :: right)) := by
  induction beforeRevBits generalizing current right with
  | nil =>
      cases current <;>
        simp [AppendInputTapeHeadRouterDescription,
          config, tapeAtCells,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, Tape.moveRight]
  | cons bit rest ih =>
      cases current
      · simpa [MachineDescription.runConfig, config,
          tapeAtCells,
          AppendInputTapeHeadRouterDescription,
          MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, List.append_assoc] using
          ih bit (some false :: right)
      · simpa [MachineDescription.runConfig, config,
          tapeAtCells,
          AppendInputTapeHeadRouterDescription,
          MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, List.append_assoc] using
          ih bit (some true :: right)

private theorem
    appendInputTapeHeadRouterDescription_run_state8_false
    (n : Nat) (beforeRevBits tailBits : Word Bool) :
    AppendInputTapeHeadRouterDescription.runConfig
        (beforeRevBits.length + 8 * n + 15)
        (config 8
          (List.append (beforeRevBits.map some)
            [some false, none])
          ((List.append (natBits n)
            (false :: true :: false :: true :: tailBits)).map some)) =
      config 31 [some false]
        (some false ::
          (List.append beforeRevBits.reverse
            (List.append (natBits n)
              (false :: true :: false :: true :: tailBits))).map some) := by
  induction n generalizing beforeRevBits with
  | zero =>
      let nextBefore : Word Bool :=
        List.append [false, true, true, false, false] beforeRevBits
      have hprefix :
          AppendInputTapeHeadRouterDescription.runConfig 7
              (config 8
                (List.append (beforeRevBits.map some)
                  [some false, none])
                ((List.append (natBits 0)
                  (false :: true :: false :: true :: tailBits)).map some)) =
            config 21
              (List.append (nextBefore.map some) [some false, none])
              (some true :: some false :: some true ::
                tailBits.map some) := by
        simp [nextBefore,
          AppendInputTapeHeadRouterDescription,
          config, tapeAtCells,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, Tape.moveRight]
      rw [show beforeRevBits.length + 8 * 0 + 15 =
        7 + (nextBefore.length + 3) by
          simp [nextBefore]
          omega]
      rw [MachineDescription.runConfig_add]
      rw [hprefix]
      simpa [nextBefore,
        List.map_append, List.reverse_append, List.append_assoc] using
        appendInputTapeHeadRouterDescription_run_return21
          nextBefore true (some false :: some true :: tailBits.map some)
  | succ n ih =>
      let nextBefore : Word Bool :=
        List.append [false, true, false, false] beforeRevBits
      have hprefix :
          AppendInputTapeHeadRouterDescription.runConfig 4
              (config 8
                (List.append (beforeRevBits.map some)
                  [some false, none])
                ((List.append (natBits (n + 1))
                  (false :: true :: false :: true :: tailBits)).map some)) =
            config 8
              (List.append (nextBefore.map some) [some false, none])
              ((List.append (natBits n)
                (false :: true :: false :: true :: tailBits)).map some) := by
        simp [nextBefore,
          AppendInputTapeHeadRouterDescription,
          config, tapeAtCells,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read, Tape.write, Tape.move,
          Tape.moveRight, List.map_append]
        cases
          List.map some (natBits n) ++
            some false :: some true :: some false :: some true ::
              List.map some tailBits <;>
          rfl
      rw [show beforeRevBits.length + 8 * (n + 1) + 15 =
        4 + (nextBefore.length + 8 * n + 15) by
          simp [nextBefore]
          omega]
      rw [MachineDescription.runConfig_add]
      rw [hprefix]
      simpa [nextBefore,
        List.map_append, List.reverse_append, List.append_assoc,
        Nat.mul_succ] using
        ih nextBefore

private theorem
    appendInputTapeHeadRouterDescription_run_state8_true
    (n : Nat) (beforeRevBits tailBits : Word Bool) :
    AppendInputTapeHeadRouterDescription.runConfig
        (beforeRevBits.length + 8 * n + 15)
        (config 8
          (List.append (beforeRevBits.map some)
            [some false, none])
          ((List.append (natBits n)
            (false :: true :: true :: false :: tailBits)).map some)) =
      config 31 [some true]
        (some false ::
          (List.append beforeRevBits.reverse
            (List.append (natBits n)
              (false :: true :: true :: false :: tailBits))).map some) := by
  induction n generalizing beforeRevBits with
  | zero =>
      let nextBefore : Word Bool :=
        List.append [false, true, true, false, false] beforeRevBits
      have hprefix :
          AppendInputTapeHeadRouterDescription.runConfig 7
              (config 8
                (List.append (beforeRevBits.map some)
                  [some false, none])
                ((List.append (natBits 0)
                  (false :: true :: true :: false :: tailBits)).map some)) =
            config 22
              (List.append (nextBefore.map some) [some false, none])
              (some true :: some true :: some false ::
                tailBits.map some) := by
        simp [nextBefore,
          AppendInputTapeHeadRouterDescription,
          config, tapeAtCells,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, Tape.moveRight]
      rw [show beforeRevBits.length + 8 * 0 + 15 =
        7 + (nextBefore.length + 3) by
          simp [nextBefore]
          omega]
      rw [MachineDescription.runConfig_add]
      rw [hprefix]
      simpa [nextBefore,
        List.map_append, List.reverse_append, List.append_assoc] using
        appendInputTapeHeadRouterDescription_run_return22
          nextBefore true (some true :: some false :: tailBits.map some)
  | succ n ih =>
      let nextBefore : Word Bool :=
        List.append [false, true, false, false] beforeRevBits
      have hprefix :
          AppendInputTapeHeadRouterDescription.runConfig 4
              (config 8
                (List.append (beforeRevBits.map some)
                  [some false, none])
                ((List.append (natBits (n + 1))
                  (false :: true :: true :: false :: tailBits)).map some)) =
            config 8
              (List.append (nextBefore.map some) [some false, none])
              ((List.append (natBits n)
                (false :: true :: true :: false :: tailBits)).map some) := by
        simp [nextBefore,
          AppendInputTapeHeadRouterDescription,
          config, tapeAtCells,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read, Tape.write, Tape.move,
          Tape.moveRight, List.map_append]
        cases
          List.map some (natBits n) ++
            some false :: some true :: some true :: some false ::
              List.map some tailBits <;>
          rfl
      rw [show beforeRevBits.length + 8 * (n + 1) + 15 =
        4 + (nextBefore.length + 8 * n + 15) by
          simp [nextBefore]
          omega]
      rw [MachineDescription.runConfig_add]
      rw [hprefix]
      simpa [nextBefore,
        List.map_append, List.reverse_append, List.append_assoc,
        Nat.mul_succ] using
        ih nextBefore

private def AppendInputTapeHeadRouterSpec
    (router : MachineDescription) : Prop :=
  router.SubroutineReady ∧
    (forall stage : Nat,
     forall suffixBits : Word Bool,
      exists steps : Nat,
        router.runConfig steps
            { state := router.start
              tape :=
                tapeAtCells []
                  (some false :: some false ::
                    ((List.append [false, true]
                      (List.append
                        (stageInputBits ([] : Word Bool) stage)
                        suffixBits)).map some)) } =
          { state := router.halt
            tape :=
              appendInputTapeHeadRouterTaggedTape
                none ([] : Word Bool) stage suffixBits }) ∧
    (forall b : Bool,
     forall rest : Word Bool,
     forall stage : Nat,
     forall suffixBits : Word Bool,
      exists steps : Nat,
        router.runConfig steps
            { state := router.start
              tape :=
                tapeAtCells []
                  (some false :: some false ::
                    ((List.append [false, true]
                      (List.append
                        (stageInputBits (b :: rest) stage)
                        suffixBits)).map some)) } =
          { state := router.halt
            tape :=
              appendInputTapeHeadRouterTaggedTape
                (some b) (b :: rest) stage suffixBits })

private theorem appendInputTapeHeadRouterDescription_spec :
    AppendInputTapeHeadRouterSpec
      AppendInputTapeHeadRouterDescription := by
  constructor
  · exact appendInputTapeHeadRouterDescription_subroutineReady
  constructor
  · intro stage suffixBits
    refine ⟨15, ?_⟩
    simp [appendInputTapeHeadRouterTaggedTape,
      stageInputBits, PairedRecognizerDovetailStageInputCode,
      MachineDescription.DovetailLayout.stageInputCode,
      MachineDescription.DovetailLayout.stageInputCodeAppend,
      MachineDescription.encodeBoolWordAppend,
      MachineDescription.encodeCellListAppend,
      MachineDescription.encodeNatAppend,
      MachineDescription.encodeNat,
      MachineDescription.encodeCellsAppend,
      MachineDescription.encodeCodeWordAsInput,
      MachineDescription.encodeCodeSymbolAsInput,
      AppendInputTapeHeadRouterDescription,
      tapeAtCells,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft, Tape.moveRight]
  · intro b rest stage suffixBits
    cases b
    · let beforeRevBits : Word Bool :=
        [false, true, false, false, true, false]
      let tailBits : Word Bool :=
        List.append
          (MachineDescription.encodeCodeWordAsInput
            (MachineDescription.encodeCellsAppend (rest.map some)
              (MachineDescription.encodeNatAppend stage [])))
          suffixBits
      let rawCells : List (Option Bool) :=
        List.append
          (List.map some
            (MachineDescription.encodeCodeWordAsInput
              (List.append (MachineDescription.encodeNat rest.length)
                (MachineCodeSymbol.zero ::
                  MachineDescription.encodeCellsAppend (rest.map some)
                    (MachineDescription.encodeNat stage)))))
          (List.map some suffixBits)
      refine ⟨8 * rest.length + 29, ?_⟩
      have hprefix :
          AppendInputTapeHeadRouterDescription.runConfig 8
              { state := AppendInputTapeHeadRouterDescription.start
                tape :=
                  tapeAtCells []
                    (some false :: some false ::
                      ((List.append [false, true]
                        (List.append
                          (stageInputBits (false :: rest) stage)
                          suffixBits)).map some)) } =
            config 8
              (List.append (beforeRevBits.map some) [some false, none])
              rawCells := by
        simp [beforeRevBits, rawCells,
          stageInputBits, PairedRecognizerDovetailStageInputCode,
          MachineDescription.DovetailLayout.stageInputCode,
          MachineDescription.DovetailLayout.stageInputCodeAppend,
          MachineDescription.encodeBoolWordAppend,
          MachineDescription.encodeCellListAppend,
          MachineDescription.encodeNatAppend,
          MachineDescription.encodeNat,
          MachineDescription.encodeCellsAppend,
          MachineDescription.encodeCellAppend,
          MachineDescription.encodeCell,
          AppendInputTapeHeadRouterDescription,
          config, tapeAtCells,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read, Tape.write, Tape.move,
          Tape.moveRight, List.map_append]
        cases
          (List.map some
            (MachineDescription.encodeCodeWordAsInput
              (List.append (MachineDescription.encodeNat rest.length)
                (MachineCodeSymbol.zero ::
                  MachineDescription.encodeCellsAppend (rest.map some)
                    (MachineDescription.encodeNat stage)))) ++
            List.map some suffixBits) <;>
          rfl
      have hcells :
          rawCells =
            ((List.append (natBits rest.length)
              (false :: true :: false :: true :: tailBits)).map some) := by
        simpa [rawCells, tailBits, MachineDescription.encodeNatAppend,
          List.map_append, List.append_assoc] using
          natBits_map_append_cell_false rest.length
            (MachineDescription.encodeCellsAppend (rest.map some)
              (MachineDescription.encodeNat stage))
            suffixBits
      rw [show 8 * rest.length + 29 =
        8 + (beforeRevBits.length + 8 * rest.length + 15) by
          simp [beforeRevBits]
          omega]
      rw [MachineDescription.runConfig_add]
      rw [hprefix]
      have hscan :=
        appendInputTapeHeadRouterDescription_run_state8_false
          rest.length beforeRevBits tailBits
      rw [← hcells] at hscan
      have htailRaw :
          List.map some (natBits rest.length) ++
              some false :: some true :: some false :: some true ::
                List.map some tailBits =
            rawCells := by
        simpa [List.map_append, List.append_assoc] using hcells.symm
      simpa [beforeRevBits, rawCells, htailRaw,
        appendInputTapeHeadRouterTaggedTape,
        stageInputBits, PairedRecognizerDovetailStageInputCode,
        MachineDescription.DovetailLayout.stageInputCode,
        MachineDescription.DovetailLayout.stageInputCodeAppend,
        MachineDescription.encodeBoolWordAppend,
        MachineDescription.encodeCellListAppend,
        MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat,
        MachineDescription.encodeCellsAppend,
        MachineDescription.encodeCellAppend,
        MachineDescription.encodeCell,
        List.map_append, List.reverse_append, List.append_assoc] using
        hscan
    · let beforeRevBits : Word Bool :=
        [false, true, false, false, true, false]
      let tailBits : Word Bool :=
        List.append
          (MachineDescription.encodeCodeWordAsInput
            (MachineDescription.encodeCellsAppend (rest.map some)
              (MachineDescription.encodeNatAppend stage [])))
          suffixBits
      let rawCells : List (Option Bool) :=
        List.append
          (List.map some
            (MachineDescription.encodeCodeWordAsInput
              (List.append (MachineDescription.encodeNat rest.length)
                (MachineCodeSymbol.one ::
                  MachineDescription.encodeCellsAppend (rest.map some)
                    (MachineDescription.encodeNat stage)))))
          (List.map some suffixBits)
      refine ⟨8 * rest.length + 29, ?_⟩
      have hprefix :
          AppendInputTapeHeadRouterDescription.runConfig 8
              { state := AppendInputTapeHeadRouterDescription.start
                tape :=
                  tapeAtCells []
                    (some false :: some false ::
                      ((List.append [false, true]
                        (List.append
                          (stageInputBits (true :: rest) stage)
                          suffixBits)).map some)) } =
            config 8
              (List.append (beforeRevBits.map some) [some false, none])
              rawCells := by
        simp [beforeRevBits, rawCells,
          stageInputBits, PairedRecognizerDovetailStageInputCode,
          MachineDescription.DovetailLayout.stageInputCode,
          MachineDescription.DovetailLayout.stageInputCodeAppend,
          MachineDescription.encodeBoolWordAppend,
          MachineDescription.encodeCellListAppend,
          MachineDescription.encodeNatAppend,
          MachineDescription.encodeNat,
          MachineDescription.encodeCellsAppend,
          MachineDescription.encodeCellAppend,
          MachineDescription.encodeCell,
          AppendInputTapeHeadRouterDescription,
          config, tapeAtCells,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read, Tape.write, Tape.move,
          Tape.moveRight, List.map_append]
        cases
          (List.map some
            (MachineDescription.encodeCodeWordAsInput
              (List.append (MachineDescription.encodeNat rest.length)
                (MachineCodeSymbol.one ::
                  MachineDescription.encodeCellsAppend (rest.map some)
                    (MachineDescription.encodeNat stage)))) ++
            List.map some suffixBits) <;>
          rfl
      have hcells :
          rawCells =
            ((List.append (natBits rest.length)
              (false :: true :: true :: false :: tailBits)).map some) := by
        simpa [rawCells, tailBits, MachineDescription.encodeNatAppend,
          List.map_append, List.append_assoc] using
          natBits_map_append_cell_true rest.length
            (MachineDescription.encodeCellsAppend (rest.map some)
              (MachineDescription.encodeNat stage))
            suffixBits
      rw [show 8 * rest.length + 29 =
        8 + (beforeRevBits.length + 8 * rest.length + 15) by
          simp [beforeRevBits]
          omega]
      rw [MachineDescription.runConfig_add]
      rw [hprefix]
      have hscan :=
        appendInputTapeHeadRouterDescription_run_state8_true
          rest.length beforeRevBits tailBits
      rw [← hcells] at hscan
      have htailRaw :
          List.map some (natBits rest.length) ++
              some false :: some true :: some true :: some false ::
                List.map some tailBits =
            rawCells := by
        simpa [List.map_append, List.append_assoc] using hcells.symm
      simpa [beforeRevBits, rawCells, htailRaw,
        appendInputTapeHeadRouterTaggedTape,
        stageInputBits, PairedRecognizerDovetailStageInputCode,
        MachineDescription.DovetailLayout.stageInputCode,
        MachineDescription.DovetailLayout.stageInputCodeAppend,
        MachineDescription.encodeBoolWordAppend,
        MachineDescription.encodeCellListAppend,
        MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat,
        MachineDescription.encodeCellsAppend,
        MachineDescription.encodeCellAppend,
        MachineDescription.encodeCell,
        List.map_append, List.reverse_append, List.append_assoc] using
        hscan

private def AppendInputTapeHeadTaggedBrancherSpec
    (brancher : MachineDescription) : Prop :=
  brancher.SubroutineReady ∧
    (forall stage : Nat,
     forall suffixBits : Word Bool,
      exists steps : Nat,
        brancher.runConfig steps
            { state := brancher.start
              tape :=
                Tape.move Direction.left
                  (appendInputTapeHeadRouterTaggedTape
                    none ([] : Word Bool) stage suffixBits) } =
          { state := brancher.halt
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append [false, true]
                    (List.append
                      (stageInputBits ([] : Word Bool) stage)
                      (List.append suffixBits
                        (inputTapeBits ([] : Word Bool))))).map
                    some)) }) ∧
    (forall b : Bool,
     forall rest : Word Bool,
     forall stage : Nat,
     forall suffixBits : Word Bool,
      exists steps : Nat,
        brancher.runConfig steps
            { state := brancher.start
              tape :=
                Tape.move Direction.left
                  (appendInputTapeHeadRouterTaggedTape
                    (some b) (b :: rest) stage suffixBits) } =
          { state := brancher.halt
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append [false, true]
                    (List.append
                      (stageInputBits (b :: rest) stage)
                      (List.append suffixBits
                        (inputTapeBits (b :: rest))))).map
                    some)) })

private def AppendInputTapeHeadTaggedBrancherConstruction :
    Prop :=
  forall rightCopier : MachineDescription,
    AppendInputTapeRightCellsReturnSpec rightCopier ->
      exists brancher : MachineDescription,
        AppendInputTapeHeadTaggedBrancherSpec brancher

private def AppendInputTapeHeadDispatcherSpec
    (dispatcher : MachineDescription) : Prop :=
  dispatcher.SubroutineReady ∧
    (forall stage : Nat,
     forall suffixBits : Word Bool,
      exists steps : Nat,
        dispatcher.runConfig steps
            { state := dispatcher.start
              tape :=
                tapeAtCells []
                  (some false :: some false ::
                    ((List.append [false, true]
                      (List.append
                        (stageInputBits ([] : Word Bool) stage)
                        suffixBits)).map some)) } =
          { state := dispatcher.halt
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append [false, true]
                    (List.append
                      (stageInputBits ([] : Word Bool) stage)
                      (List.append suffixBits
                        (inputTapeBits ([] : Word Bool))))).map
                    some)) }) ∧
    (forall b : Bool,
     forall rest : Word Bool,
     forall stage : Nat,
     forall suffixBits : Word Bool,
      exists steps : Nat,
        dispatcher.runConfig steps
            { state := dispatcher.start
              tape :=
                tapeAtCells []
                  (some false :: some false ::
                    ((List.append [false, true]
                      (List.append
                        (stageInputBits (b :: rest) stage)
                        suffixBits)).map some)) } =
          { state := dispatcher.halt
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append [false, true]
                    (List.append
                      (stageInputBits (b :: rest) stage)
                      (List.append suffixBits
                        (inputTapeBits (b :: rest))))).map
                    some)) })

private def AppendInputTapeHeadDispatcherConstruction :
    Prop :=
  forall rightCopier : MachineDescription,
    AppendInputTapeRightCellsReturnSpec rightCopier ->
      exists dispatcher : MachineDescription,
        AppendInputTapeHeadDispatcherSpec dispatcher

private def AppendInputTapeHeadDispatcherDescription
    (router brancher : MachineDescription) : MachineDescription :=
  MachineDescription.seqSubroutine router brancher Direction.left

private theorem appendInputTapeHeadDispatcherSpec_of_router_brancher
    {router brancher : MachineDescription}
    (hrouter : AppendInputTapeHeadRouterSpec router)
    (hbrancher :
      AppendInputTapeHeadTaggedBrancherSpec brancher) :
    AppendInputTapeHeadDispatcherSpec
      (AppendInputTapeHeadDispatcherDescription
        router brancher) := by
  constructor
  · exact MachineDescription.seqSubroutine_subroutineReady
      hrouter.left hbrancher.left
  constructor
  · intro stage suffixBits
    let A := router
    let B := brancher
    let Tmid :=
      appendInputTapeHeadRouterTaggedTape
        none ([] : Word Bool) stage suffixBits
    have hAready : A.SubroutineReady := hrouter.left
    have hBready : B.SubroutineReady := hbrancher.left
    rcases hrouter.right.left stage suffixBits with ⟨nA, hA⟩
    have hArun :
        A.runConfig nA
            { state := A.start
              tape :=
                tapeAtCells []
                  (some false :: some false ::
                    ((List.append [false, true]
                      (List.append
                        (stageInputBits ([] : Word Bool) stage)
                        suffixBits)).map some)) } =
          { state := A.halt, tape := Tmid } := by
      simpa [A, Tmid] using hA
    have hBReach :
        exists nB : Nat,
          B.runConfig nB
              { state := B.start
                tape := Tape.move Direction.left Tmid } =
            { state := B.halt
              tape :=
                tapeAtCells [some false]
                  (some false ::
                    ((List.append [false, true]
                      (List.append
                        (stageInputBits ([] : Word Bool) stage)
                        (List.append suffixBits
                          (inputTapeBits ([] : Word Bool))))).map
                      some)) } := by
      rcases hbrancher.right.left stage suffixBits with ⟨nB, hB⟩
      exact ⟨nB, by simpa [B, Tmid] using hB⟩
    rcases
        MachineDescription.seqSubroutine_reaches_of_runConfig_eq
          (A := A) (B := B) (handoffMove := Direction.left)
          hAready hBready hArun hBReach with
      ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [AppendInputTapeHeadDispatcherDescription,
      A, B] using hn
  · intro b rest stage suffixBits
    let A := router
    let B := brancher
    let Tmid :=
      appendInputTapeHeadRouterTaggedTape
        (some b) (b :: rest) stage suffixBits
    have hAready : A.SubroutineReady := hrouter.left
    have hBready : B.SubroutineReady := hbrancher.left
    rcases hrouter.right.right b rest stage suffixBits with ⟨nA, hA⟩
    have hArun :
        A.runConfig nA
            { state := A.start
              tape :=
                tapeAtCells []
                  (some false :: some false ::
                    ((List.append [false, true]
                      (List.append
                        (stageInputBits (b :: rest) stage)
                        suffixBits)).map some)) } =
          { state := A.halt, tape := Tmid } := by
      simpa [A, Tmid] using hA
    have hBReach :
        exists nB : Nat,
          B.runConfig nB
              { state := B.start
                tape := Tape.move Direction.left Tmid } =
            { state := B.halt
              tape :=
                tapeAtCells [some false]
                  (some false ::
                    ((List.append [false, true]
                      (List.append
                        (stageInputBits (b :: rest) stage)
                        (List.append suffixBits
                          (inputTapeBits (b :: rest))))).map
                      some)) } := by
      rcases hbrancher.right.right b rest stage suffixBits with ⟨nB, hB⟩
      exact ⟨nB, by simpa [B, Tmid] using hB⟩
    rcases
        MachineDescription.seqSubroutine_reaches_of_runConfig_eq
          (A := A) (B := B) (handoffMove := Direction.left)
          hAready hBready hArun hBReach with
      ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [AppendInputTapeHeadDispatcherDescription,
      A, B] using hn

private def AppendInputTapeReturnForwardSpec
    (copier : MachineDescription) : Prop :=
    forall w : Word Bool,
    forall stage : Nat,
    forall suffixBits : Word Bool,
      exists steps : Nat,
        copier.runConfig steps
            { state := copier.start
              tape :=
                tapeAtCells []
                  (some false :: some false ::
                    ((List.append [false, true]
                      (List.append
                        (stageInputBits w stage)
                        suffixBits)).map some)) } =
          { state := copier.halt
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append [false, true]
                      (List.append
                        (stageInputBits w stage)
                        (List.append suffixBits
                          (inputTapeBits w)))).map some)) }

private def AppendInputTapeReturnSpec
    (copier : MachineDescription) : Prop :=
  copier.SubroutineReady ∧
    AppendInputTapeReturnForwardSpec copier

private def AppendInputTapeRightCellsReturnConstruction : Prop :=
  exists rightCopier : MachineDescription,
    AppendInputTapeRightCellsReturnSpec rightCopier

private theorem appendInputTapeReturnSpec_of_headDispatcher
    {dispatcher : MachineDescription}
    (hdispatcher :
      AppendInputTapeHeadDispatcherSpec dispatcher) :
    AppendInputTapeReturnSpec dispatcher := by
  constructor
  · exact hdispatcher.left
  intro w stage suffixBits
  cases w with
  | nil =>
      exact hdispatcher.right.left stage suffixBits
  | cons b rest =>
      exact hdispatcher.right.right b rest stage suffixBits

private def StageInputValidatorForwardSpec
    (validator : MachineDescription) : Prop :=
  forall w : Word Bool,
  forall stage : Nat,
    exists steps : Nat,
      validator.runConfig steps
          (validator.initial (stageInputBits w stage)) =
        { state := validator.halt
          tape :=
            Tape.move Direction.right
              (Tape.input (stageInputBits w stage)) }

private def StageInputValidatorClosedSpec
    (validator : MachineDescription) : Prop :=
  forall code : Word MachineCodeSymbol,
  forall T : Tape Bool,
    validator.HaltsWithTape
        (MachineDescription.encodeCodeWordAsInput code) T ->
      exists w : Word Bool,
      exists stage : Nat,
        code = PairedRecognizerDovetailStageInputCode w stage ∧
          Tape.move Direction.left T =
            Tape.input (stageInputBits w stage)

private def StageInputValidatorSpec
    (validator : MachineDescription) : Prop :=
  validator.SubroutineReady ∧
    StageInputValidatorForwardSpec validator ∧
      StageInputValidatorClosedSpec validator

private def StageInputIdentityPrimitive :
    MachineDescription.TapeCodePrimitive where
  transform := fun code =>
    match MachineDescription.DovetailLayout.decodeStageInputComplete code with
    | some _ => some code
    | none => none

private theorem stageInputIdentityPrimitive_transform_eq_some_iff
    (code out : Word MachineCodeSymbol) :
    StageInputIdentityPrimitive.transform code = some out <->
      exists w : Word Bool,
      exists stage : Nat,
        code = PairedRecognizerDovetailStageInputCode w stage ∧
          out = PairedRecognizerDovetailStageInputCode w stage := by
  constructor
  · intro h
    unfold StageInputIdentityPrimitive at h
    cases hdecode :
        MachineDescription.DovetailLayout.decodeStageInputComplete code with
    | none =>
        simp [hdecode] at h
    | some parsed =>
        cases parsed with
        | mk w stage =>
            simp [hdecode] at h
            cases h
            exact
              ⟨w, stage,
                MachineDescription.DovetailLayout.decodeStageInputComplete_eq_some_stageInputCode
                  hdecode,
                MachineDescription.DovetailLayout.decodeStageInputComplete_eq_some_stageInputCode
                  hdecode⟩
  · intro h
    rcases h with ⟨w, stage, rfl, rfl⟩
    simp [StageInputIdentityPrimitive,
      PairedRecognizerDovetailStageInputCode,
      MachineDescription.DovetailLayout.decodeStageInputComplete_stageInputCode]

private def StageInputIdentityClosedHandoffConstruction : Prop :=
  exists validator : MachineDescription,
    TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      StageInputIdentityPrimitive validator
      tapeCodePrimitiveCodeWordHandoffMove

private def StageInputRecognizerSpec
    (recognizer : MachineDescription) : Prop :=
  recognizer.SubroutineReady ∧
    (forall w : Word Bool,
     forall stage : Nat,
      exists steps : Nat,
        recognizer.runConfig steps
            (recognizer.initial (stageInputBits w stage)) =
          { state := recognizer.halt
            tape := Tape.input (stageInputBits w stage) }) ∧
    (forall code : Word MachineCodeSymbol,
     forall T : Tape Bool,
      recognizer.HaltsWithTape
          (MachineDescription.encodeCodeWordAsInput code) T ->
        exists w : Word Bool,
        exists stage : Nat,
          code = PairedRecognizerDovetailStageInputCode w stage ∧
            T =
              Tape.input (MachineDescription.encodeCodeWordAsInput code))

private def StageInputRecognizerConstruction : Prop :=
  exists recognizer : MachineDescription,
    StageInputRecognizerSpec recognizer

private def stageInputSecondBitTail
    (w : Word Bool) (stage : Nat) : Word Bool :=
  match stageInputBits w stage with
  | _ :: _ :: tail => tail
  | _ => []

private theorem stageInputBits_eq_false_false_tail
    (w : Word Bool) (stage : Nat) :
    stageInputBits w stage =
      false :: false :: stageInputSecondBitTail w stage := by
  cases w with
  | nil =>
      simp [stageInputSecondBitTail, stageInputBits,
        PairedRecognizerDovetailStageInputCode,
        MachineDescription.DovetailLayout.stageInputCode,
        MachineDescription.DovetailLayout.stageInputCodeAppend,
        MachineDescription.encodeBoolWordAppend,
        MachineDescription.encodeCellListAppend,
        MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat,
        MachineDescription.encodeCodeWordAsInput,
        MachineDescription.encodeCodeSymbolAsInput]
  | cons b rest =>
      simp [stageInputSecondBitTail, stageInputBits,
        PairedRecognizerDovetailStageInputCode,
        MachineDescription.DovetailLayout.stageInputCode,
        MachineDescription.DovetailLayout.stageInputCodeAppend,
        MachineDescription.encodeBoolWordAppend,
        MachineDescription.encodeCellListAppend,
        MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat,
        MachineDescription.encodeCodeWordAsInput,
        MachineDescription.encodeCodeSymbolAsInput]

private def stageInputSecondBitMarkedTape
    (w : Word Bool) (stage : Nat) : Tape Bool :=
  tapeAtCells [some false]
    (none :: (stageInputSecondBitTail w stage).map some)

private def stageInputSecondBitMarkedHandoffTape
    (w : Word Bool) (stage : Nat) : Tape Bool :=
  Tape.move Direction.right
    (stageInputSecondBitMarkedTape w stage)

private theorem
    stageInputSecondBitMarkedHandoffTape_move_left
    (w : Word Bool) (stage : Nat) :
    Tape.move Direction.left
        (stageInputSecondBitMarkedHandoffTape w stage) =
      stageInputSecondBitMarkedTape w stage := by
  cases w with
  | nil =>
      simp [stageInputSecondBitMarkedHandoffTape,
        stageInputSecondBitMarkedTape,
        stageInputSecondBitTail, stageInputBits,
        PairedRecognizerDovetailStageInputCode,
        MachineDescription.DovetailLayout.stageInputCode,
        MachineDescription.DovetailLayout.stageInputCodeAppend,
        MachineDescription.encodeBoolWordAppend,
        MachineDescription.encodeCellListAppend,
        MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat,
        MachineDescription.encodeCodeWordAsInput,
        MachineDescription.encodeCodeSymbolAsInput,
        tapeAtCells, Tape.move, Tape.moveRight, Tape.moveLeft]
  | cons b rest =>
      simp [stageInputSecondBitMarkedHandoffTape,
        stageInputSecondBitMarkedTape,
        stageInputSecondBitTail, stageInputBits,
        PairedRecognizerDovetailStageInputCode,
        MachineDescription.DovetailLayout.stageInputCode,
        MachineDescription.DovetailLayout.stageInputCodeAppend,
        MachineDescription.encodeBoolWordAppend,
        MachineDescription.encodeCellListAppend,
        MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat,
        MachineDescription.encodeCodeWordAsInput,
        MachineDescription.encodeCodeSymbolAsInput,
        tapeAtCells, Tape.move, Tape.moveRight, Tape.moveLeft]

private def RestoreStageInputSecondBitDescription :
    MachineDescription where
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [ MachineDescription.transition
        0 none (some false) Direction.left 1 ]

private theorem
    restoreStageInputSecondBitDescription_wellFormed :
    RestoreStageInputSecondBitDescription.WellFormed := by
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · intro t ht
    exact transition_wellFormed_of_all
      (l := RestoreStageInputSecondBitDescription.transitions)
      (stateCount :=
        RestoreStageInputSecondBitDescription.stateCount)
      (by
        native_decide) t ht
  · intro t u ht hu hkey
    exact transition_deterministic_of_all
      (l := RestoreStageInputSecondBitDescription.transitions)
      (by
        native_decide) t u ht hu hkey

private theorem
    restoreStageInputSecondBitDescription_haltTransitionFree :
    RestoreStageInputSecondBitDescription.HaltTransitionFree := by
  intro t ht
  exact transition_notFrom_of_all
    (l := RestoreStageInputSecondBitDescription.transitions)
    (state := RestoreStageInputSecondBitDescription.halt)
    (by
      native_decide) t ht

private theorem
    restoreStageInputSecondBitDescription_subroutineReady :
    RestoreStageInputSecondBitDescription.SubroutineReady :=
  ⟨restoreStageInputSecondBitDescription_wellFormed,
    restoreStageInputSecondBitDescription_haltTransitionFree⟩

private theorem restoreStageInputSecondBitDescription_run
    (w : Word Bool) (stage : Nat) :
    RestoreStageInputSecondBitDescription.runConfig 1
        { state := RestoreStageInputSecondBitDescription.start
          tape := stageInputSecondBitMarkedTape w stage } =
      { state := RestoreStageInputSecondBitDescription.halt
        tape := Tape.input (stageInputBits w stage) } := by
  rw [stageInputBits_eq_false_false_tail w stage]
  simp [RestoreStageInputSecondBitDescription,
    stageInputSecondBitMarkedTape,
    stageInputSecondBitTail,
    tapeAtCells, MachineDescription.runConfig,
    MachineDescription.stepConfig, MachineDescription.lookupTransition,
    MachineDescription.Matches, MachineDescription.transition,
    Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.input]

private theorem restoreStageInputSecondBitDescription_run_succ
    (n : Nat) (w : Word Bool) (stage : Nat) :
    RestoreStageInputSecondBitDescription.runConfig (n + 1)
        { state := RestoreStageInputSecondBitDescription.start
          tape := stageInputSecondBitMarkedTape w stage } =
      { state := RestoreStageInputSecondBitDescription.halt
        tape := Tape.input (stageInputBits w stage) } := by
  rw [show n + 1 = 1 + n by omega]
  rw [MachineDescription.runConfig_add]
  rw [restoreStageInputSecondBitDescription_run]
  exact
    MachineDescription.runConfig_halt
      restoreStageInputSecondBitDescription_haltTransitionFree
      (Tape.input (stageInputBits w stage)) n

private def MarkStageInputSecondBitDescription :
    MachineDescription where
  stateCount := 4
  start := 0
  halt := 3
  transitions :=
    [ MachineDescription.transition
        0 (some false) (some false) Direction.right 1
    , MachineDescription.transition
        1 (some false) none Direction.left 2
    , MachineDescription.transition
        2 (some false) (some false) Direction.right 3
    ]

private theorem markStageInputSecondBitDescription_wellFormed :
    MarkStageInputSecondBitDescription.WellFormed := by
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · intro t ht
    exact transition_wellFormed_of_all
      (l := MarkStageInputSecondBitDescription.transitions)
      (stateCount :=
        MarkStageInputSecondBitDescription.stateCount)
      (by
        native_decide) t ht
  · intro t u ht hu hkey
    exact transition_deterministic_of_all
      (l := MarkStageInputSecondBitDescription.transitions)
      (by
        native_decide) t u ht hu hkey

private theorem
    markStageInputSecondBitDescription_haltTransitionFree :
    MarkStageInputSecondBitDescription.HaltTransitionFree := by
  intro t ht
  exact transition_notFrom_of_all
    (l := MarkStageInputSecondBitDescription.transitions)
    (state := MarkStageInputSecondBitDescription.halt)
    (by
      native_decide) t ht

private theorem
    markStageInputSecondBitDescription_subroutineReady :
    MarkStageInputSecondBitDescription.SubroutineReady :=
  ⟨markStageInputSecondBitDescription_wellFormed,
    markStageInputSecondBitDescription_haltTransitionFree⟩

private theorem markStageInputSecondBitDescription_run
    (w : Word Bool) (stage : Nat) :
    MarkStageInputSecondBitDescription.runConfig 3
        (MarkStageInputSecondBitDescription.initial
          (stageInputBits w stage)) =
      { state := MarkStageInputSecondBitDescription.halt
        tape := stageInputSecondBitMarkedTape w stage } := by
  rw [stageInputBits_eq_false_false_tail w stage]
  simp [MarkStageInputSecondBitDescription,
    stageInputSecondBitMarkedTape,
    stageInputSecondBitTail,
    tapeAtCells, MachineDescription.initial,
    MachineDescription.runConfig, MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition, Tape.input, Tape.read, Tape.write,
    Tape.move, Tape.moveLeft, Tape.moveRight]

private theorem markStageInputSecondBitDescription_run_bits
    (tail : Word Bool) :
    MarkStageInputSecondBitDescription.runConfig 3
        (MarkStageInputSecondBitDescription.initial
          (false :: false :: tail)) =
      { state := MarkStageInputSecondBitDescription.halt
        tape := tapeAtCells [some false]
          (none :: tail.map some) } := by
  simp [MarkStageInputSecondBitDescription,
    tapeAtCells, MachineDescription.initial,
    MachineDescription.runConfig, MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition, Tape.input, Tape.read, Tape.write,
    Tape.move, Tape.moveLeft, Tape.moveRight]

private theorem markStageInputSecondBitDescription_haltsWithTape_inv
    {bits : Word Bool} {T : Tape Bool}
    (h :
      MarkStageInputSecondBitDescription.HaltsWithTape
        bits T) :
    exists tail : Word Bool,
      bits = false :: false :: tail ∧
        T =
          tapeAtCells [some false]
            (none :: tail.map some) := by
  rcases
      MachineDescription.runConfig_eq_halt_of_haltsWithTape h with
    ⟨n, hn⟩
  cases bits with
  | nil =>
      have hstep :
          MarkStageInputSecondBitDescription.stepConfig
              (MarkStageInputSecondBitDescription.initial []) =
            none := by
        native_decide
      have hrun :=
        MachineDescription.runConfig_of_stepConfig_none hstep n
      have hstate : 0 = 3 := by
        simpa [MarkStageInputSecondBitDescription,
          MachineDescription.initial] using
          congrArg MachineDescription.Configuration.state
            (hrun.symm.trans hn)
      omega
  | cons b rest =>
      cases b
      · cases rest with
        | nil =>
            cases n with
            | zero =>
              simp [MarkStageInputSecondBitDescription,
                  MachineDescription.runConfig]
                  at hn
            | succ n =>
                let c1 : MachineDescription.Configuration :=
                  { state := 1
                    tape := tapeAtCells [some false] [] }
                have hstep0 :
                    MarkStageInputSecondBitDescription.stepConfig
                        (MarkStageInputSecondBitDescription.initial
                          [false]) =
                      some c1 := by
                  simp [c1, MarkStageInputSecondBitDescription,
                    tapeAtCells, MachineDescription.initial,
                    MachineDescription.stepConfig,
                    MachineDescription.lookupTransition,
                    MachineDescription.Matches,
                    MachineDescription.transition, Tape.input, Tape.read,
                    Tape.write, Tape.move, Tape.moveRight]
                have hrun :
                    MarkStageInputSecondBitDescription.runConfig
                        (Nat.succ n)
                        (MarkStageInputSecondBitDescription.initial
                          [false]) =
                      MarkStageInputSecondBitDescription.runConfig
                        n c1 := by
                  simp [MachineDescription.runConfig, hstep0]
                have hstep1 :
                    MarkStageInputSecondBitDescription.stepConfig
                        c1 = none := by
                  simp [c1, MarkStageInputSecondBitDescription,
                    tapeAtCells,
                    MachineDescription.stepConfig,
                    MachineDescription.lookupTransition,
                    MachineDescription.Matches,
                    MachineDescription.transition, Tape.read]
                have hstay :=
                  MachineDescription.runConfig_of_stepConfig_none hstep1 n
                have hrunFinal :
                    MarkStageInputSecondBitDescription.runConfig
                        (Nat.succ n)
                        (MarkStageInputSecondBitDescription.initial
                          [false]) =
                      c1 :=
                  hrun.trans hstay
                have hstate : 1 = 3 := by
                  simpa [c1, MarkStageInputSecondBitDescription]
                    using
                    congrArg MachineDescription.Configuration.state
                      (hrunFinal.symm.trans hn)
                omega
        | cons c tail =>
            cases c
            · refine ⟨tail, rfl, ?_⟩
              cases n with
              | zero =>
                  simp [MarkStageInputSecondBitDescription,
                    MachineDescription.runConfig]
                    at hn
              | succ n =>
                  cases n with
                  | zero =>
                      simp [MarkStageInputSecondBitDescription,
                        MachineDescription.runConfig,
                        MachineDescription.stepConfig,
                        MachineDescription.lookupTransition,
                        MachineDescription.Matches,
                        MachineDescription.transition, Tape.input,
                        Tape.read, Tape.write, Tape.move, Tape.moveRight]
                        at hn
                  | succ n =>
                      cases n with
                      | zero =>
                          simp [
                            MarkStageInputSecondBitDescription,
                            MachineDescription.runConfig,
                            MachineDescription.stepConfig,
                            MachineDescription.lookupTransition,
                            MachineDescription.Matches,
                            MachineDescription.transition, Tape.input,
                            Tape.read, Tape.write, Tape.move,
                            Tape.moveLeft, Tape.moveRight] at hn
                      | succ k =>
                          have hrun :
                              MarkStageInputSecondBitDescription.runConfig
                                  (Nat.succ (Nat.succ (Nat.succ k)))
                                  (MarkStageInputSecondBitDescription.initial
                                    (false :: false :: tail)) =
                                { state :=
                                    MarkStageInputSecondBitDescription.halt
                                  tape :=
                                    tapeAtCells [some false]
                                      (none :: tail.map some) } := by
                            rw [show
                              Nat.succ (Nat.succ (Nat.succ k)) =
                                3 + k by omega]
                            rw [MachineDescription.runConfig_add]
                            rw [markStageInputSecondBitDescription_run_bits
                              tail]
                            exact
                              MachineDescription.runConfig_halt
                                markStageInputSecondBitDescription_haltTransitionFree
                                (tapeAtCells [some false]
                                  (none :: tail.map some)) k
                          let cfgGood :
                              MachineDescription.Configuration :=
                            { state :=
                                MarkStageInputSecondBitDescription.halt,
                              tape :=
                                tapeAtCells [some false]
                                  (none :: tail.map some) }
                          have hcfg :
                              cfgGood =
                                { state :=
                                    MarkStageInputSecondBitDescription.halt,
                                  tape := T } := by
                            simpa [cfgGood] using hrun.symm.trans hn
                          exact
                            (congrArg
                              MachineDescription.Configuration.tape
                              hcfg).symm
            · cases n with
              | zero =>
                  simp [MarkStageInputSecondBitDescription,
                    MachineDescription.runConfig]
                    at hn
              | succ n =>
                  let c1 : MachineDescription.Configuration :=
                    { state := 1
                      tape :=
                        tapeAtCells [some false]
                          (some true :: tail.map some) }
                  have hstep0 :
                      MarkStageInputSecondBitDescription.stepConfig
                          (MarkStageInputSecondBitDescription.initial
                            (false :: true :: tail)) =
                        some c1 := by
                    simp [c1, MarkStageInputSecondBitDescription,
                      tapeAtCells, MachineDescription.initial,
                      MachineDescription.stepConfig,
                      MachineDescription.lookupTransition,
                      MachineDescription.Matches,
                      MachineDescription.transition, Tape.input, Tape.read,
                      Tape.write, Tape.move, Tape.moveRight]
                  have hrun :
                      MarkStageInputSecondBitDescription.runConfig
                          (Nat.succ n)
                          (MarkStageInputSecondBitDescription.initial
                            (false :: true :: tail)) =
                        MarkStageInputSecondBitDescription.runConfig
                          n c1 := by
                    simp [MachineDescription.runConfig, hstep0]
                  have hstep1 :
                      MarkStageInputSecondBitDescription.stepConfig
                          c1 = none := by
                    simp [c1, MarkStageInputSecondBitDescription,
                      tapeAtCells,
                      MachineDescription.stepConfig,
                      MachineDescription.lookupTransition,
                      MachineDescription.Matches,
                      MachineDescription.transition, Tape.read]
                  have hstay :=
                    MachineDescription.runConfig_of_stepConfig_none hstep1 n
                  have hrunFinal :
                      MarkStageInputSecondBitDescription.runConfig
                          (Nat.succ n)
                          (MarkStageInputSecondBitDescription.initial
                            (false :: true :: tail)) =
                        c1 :=
                    hrun.trans hstay
                  have hstate : 1 = 3 := by
                    simpa [c1, MarkStageInputSecondBitDescription]
                      using
                      congrArg MachineDescription.Configuration.state
                        (hrunFinal.symm.trans hn)
                  omega
      · have hstep :
            MarkStageInputSecondBitDescription.stepConfig
                (MarkStageInputSecondBitDescription.initial
                  (true :: rest)) =
              none := by
          simp [MarkStageInputSecondBitDescription,
            MachineDescription.initial,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.input, Tape.read]
        have hrun :=
          MachineDescription.runConfig_of_stepConfig_none hstep n
        have hstate : 0 = 3 := by
          simpa [MarkStageInputSecondBitDescription,
            MachineDescription.initial] using
            congrArg MachineDescription.Configuration.state
              (hrun.symm.trans hn)
        omega

private def StageInputMarkedScannerSpec
    (scanner : MachineDescription) : Prop :=
  scanner.SubroutineReady ∧
    (forall w : Word Bool,
     forall stage : Nat,
      exists steps : Nat,
        scanner.runConfig steps
            { state := scanner.start
              tape :=
                stageInputSecondBitMarkedHandoffTape w stage } =
          { state := scanner.halt
            tape :=
              stageInputSecondBitMarkedHandoffTape w stage }) ∧
    (forall code : Word MachineCodeSymbol,
     forall Tmark T : Tape Bool,
      MarkStageInputSecondBitDescription.HaltsWithTape
          (MachineDescription.encodeCodeWordAsInput code) Tmark ->
        (exists steps : Nat,
          scanner.runConfig steps
              { state := scanner.start
                tape := Tape.move Direction.right Tmark } =
            { state := scanner.halt, tape := T }) ->
          exists w : Word Bool,
          exists stage : Nat,
            code = PairedRecognizerDovetailStageInputCode w stage ∧
              T =
                stageInputSecondBitMarkedHandoffTape w stage)

private def StageInputMarkedScannerConstruction : Prop :=
  exists scanner : MachineDescription,
    StageInputMarkedScannerSpec scanner

private def StageInputMarkedCoreSpec
    (markedCore : MachineDescription) : Prop :=
  markedCore.SubroutineReady ∧
    (forall w : Word Bool,
     forall stage : Nat,
      exists steps : Nat,
        markedCore.runConfig steps
            (markedCore.initial (stageInputBits w stage)) =
          { state := markedCore.halt
            tape :=
              stageInputSecondBitMarkedHandoffTape w stage }) ∧
    (forall code : Word MachineCodeSymbol,
     forall T : Tape Bool,
      markedCore.HaltsWithTape
          (MachineDescription.encodeCodeWordAsInput code) T ->
        exists w : Word Bool,
        exists stage : Nat,
          code = PairedRecognizerDovetailStageInputCode w stage ∧
            T =
              stageInputSecondBitMarkedHandoffTape w stage)

private def StageInputMarkedCoreConstruction : Prop :=
  exists markedCore : MachineDescription,
    StageInputMarkedCoreSpec markedCore

private def StageInputMarkedCoreDescription
    (scanner : MachineDescription) : MachineDescription :=
  MachineDescription.seqSubroutine
    MarkStageInputSecondBitDescription scanner Direction.right

private theorem stageInputMarkedCoreDescription_subroutineReady
    {scanner : MachineDescription}
    (hscanner : StageInputMarkedScannerSpec scanner) :
    (StageInputMarkedCoreDescription scanner).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    markStageInputSecondBitDescription_subroutineReady
    hscanner.left

private theorem stageInputMarkedCoreSpec_of_markedScanner
    {scanner : MachineDescription}
    (hscanner : StageInputMarkedScannerSpec scanner) :
    StageInputMarkedCoreSpec
      (StageInputMarkedCoreDescription scanner) := by
  constructor
  · exact
      stageInputMarkedCoreDescription_subroutineReady hscanner
  constructor
  · intro w stage
    let A := MarkStageInputSecondBitDescription
    let B := scanner
    let Tmid := stageInputSecondBitMarkedTape w stage
    have hAready : A.SubroutineReady :=
      markStageInputSecondBitDescription_subroutineReady
    have hBready : B.SubroutineReady := hscanner.left
    have hArun :
        A.runConfig 3
            { state := A.start
              tape := Tape.input (stageInputBits w stage) } =
          { state := A.halt, tape := Tmid } := by
      simpa [A, Tmid, MachineDescription.initial] using
        markStageInputSecondBitDescription_run w stage
    have hBReach :
        exists nB : Nat,
          B.runConfig nB
              { state := B.start
                tape := Tape.move Direction.right Tmid } =
            { state := B.halt
              tape :=
                stageInputSecondBitMarkedHandoffTape w stage } := by
      rcases hscanner.right.left w stage with ⟨nB, hB⟩
      refine ⟨nB, ?_⟩
      simpa [B, Tmid,
        stageInputSecondBitMarkedHandoffTape] using hB
    rcases
        MachineDescription.seqSubroutine_reaches_of_runConfig_eq
          (A := A) (B := B) (handoffMove := Direction.right)
          hAready hBready hArun hBReach with
      ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [StageInputMarkedCoreDescription, A, B,
      MachineDescription.initial] using hn
  · intro code T hhalt
    let A := MarkStageInputSecondBitDescription
    let B := scanner
    have hAready : A.SubroutineReady :=
      markStageInputSecondBitDescription_subroutineReady
    have hBready : B.SubroutineReady := hscanner.left
    rcases
        MachineDescription.seqSubroutine_haltsWithTape_inv
          (A := A) (B := B) (handoffMove := Direction.right)
          hAready hBready hhalt with
      ⟨Tmark, hAhalt, hBReach⟩
    exact hscanner.right.right code Tmark T hAhalt hBReach

private def StageInputRecognizerDescription
    (markedCore : MachineDescription) : MachineDescription :=
  MachineDescription.seqSubroutine markedCore
    RestoreStageInputSecondBitDescription Direction.left

private theorem stageInputRecognizerDescription_subroutineReady
    {markedCore : MachineDescription}
    (hmarkedCore : StageInputMarkedCoreSpec markedCore) :
    (StageInputRecognizerDescription markedCore).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    hmarkedCore.left
    restoreStageInputSecondBitDescription_subroutineReady

private theorem stageInputRecognizerSpec_of_markedCore
    {markedCore : MachineDescription}
    (hmarkedCore : StageInputMarkedCoreSpec markedCore) :
    StageInputRecognizerSpec
      (StageInputRecognizerDescription markedCore) := by
  constructor
  · exact stageInputRecognizerDescription_subroutineReady
      hmarkedCore
  constructor
  · intro w stage
    let A := markedCore
    let B := RestoreStageInputSecondBitDescription
    have hAready : A.SubroutineReady := hmarkedCore.left
    have hBready : B.SubroutineReady :=
      restoreStageInputSecondBitDescription_subroutineReady
    rcases hmarkedCore.right.left w stage with ⟨nA, hA⟩
    have hArun :
        A.runConfig nA
            { state := A.start
              tape := Tape.input (stageInputBits w stage) } =
          { state := A.halt
            tape :=
              stageInputSecondBitMarkedHandoffTape w stage } := by
      simpa [A, MachineDescription.initial] using hA
    have hBReach :
        exists nB : Nat,
          B.runConfig nB
              { state := B.start
                tape :=
                  Tape.move Direction.left
                    (stageInputSecondBitMarkedHandoffTape
                      w stage) } =
            { state := B.halt
              tape := Tape.input (stageInputBits w stage) } := by
      refine ⟨1, ?_⟩
      rw [stageInputSecondBitMarkedHandoffTape_move_left]
      simpa [B] using
        restoreStageInputSecondBitDescription_run w stage
    rcases
        MachineDescription.seqSubroutine_reaches_of_runConfig_eq
          (A := A) (B := B) (handoffMove := Direction.left)
          hAready hBready hArun hBReach with
      ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [StageInputRecognizerDescription, A, B,
      MachineDescription.initial] using hn
  · intro code T hhalt
    let A := markedCore
    let B := RestoreStageInputSecondBitDescription
    have hAready : A.SubroutineReady := hmarkedCore.left
    have hBready : B.SubroutineReady :=
      restoreStageInputSecondBitDescription_subroutineReady
    rcases
        MachineDescription.seqSubroutine_haltsWithTape_inv
          (A := A) (B := B) (handoffMove := Direction.left)
          hAready hBready hhalt with
      ⟨Tmid, hAhalt, hBReach⟩
    rcases hmarkedCore.right.right code Tmid hAhalt with
      ⟨w, stage, hcode, hTmid⟩
    rcases hBReach with ⟨nB, hBRun⟩
    have hBRunMarked :
        B.runConfig nB
            { state := B.start
              tape := stageInputSecondBitMarkedTape w stage } =
          { state := B.halt, tape := T } := by
      simpa [B, hTmid,
        stageInputSecondBitMarkedHandoffTape_move_left]
        using hBRun
    have hT :
        T = Tape.input (MachineDescription.encodeCodeWordAsInput code) := by
      cases nB with
      | zero =>
          have hstate : 0 = 1 := by
            simpa [B, RestoreStageInputSecondBitDescription,
              MachineDescription.runConfig] using
              congrArg MachineDescription.Configuration.state hBRunMarked
          omega
      | succ nB =>
          have htarget :
              B.runConfig (nB + 1)
                  { state := B.start
                    tape :=
                      stageInputSecondBitMarkedTape w stage } =
                { state := B.halt
                  tape :=
                    Tape.input
                      (MachineDescription.encodeCodeWordAsInput code) } := by
            rw [hcode]
            simpa [B, stageInputBits] using
              restoreStageInputSecondBitDescription_run_succ
                nB w stage
          have hcfg :
              ({ state := B.halt, tape := T } :
                  MachineDescription.Configuration) =
                { state := B.halt
                  tape :=
                    Tape.input
                      (MachineDescription.encodeCodeWordAsInput code) } :=
            hBRunMarked.symm.trans htarget
          exact congrArg MachineDescription.Configuration.tape hcfg
    exact ⟨w, stage, hcode, hT⟩

private theorem exactIdentityDescription_runConfig_from_start
    (n : Nat) (T : Tape Bool) :
    MachineDescription.ExactIdentityDescription.runConfig n
        { state := MachineDescription.ExactIdentityDescription.start
          tape := T } =
      { state := MachineDescription.ExactIdentityDescription.halt
        tape := T } := by
  cases n <;>
    simp [MachineDescription.ExactIdentityDescription,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition]

private def StageInputIdentityDescription
    (recognizer : MachineDescription) : MachineDescription :=
  MachineDescription.seqSubroutine recognizer
    MachineDescription.ExactIdentityDescription Direction.right

private theorem stageInputIdentityDescription_subroutineReady
    {recognizer : MachineDescription}
    (hrecognizer : StageInputRecognizerSpec recognizer) :
    (StageInputIdentityDescription recognizer).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    hrecognizer.left
    ⟨MachineDescription.exactIdentityDescription_wellFormed,
      MachineDescription.exactIdentityDescription_haltTransitionFree⟩

private theorem
    stageInputIdentityDescription_haltsWithTape_of_transform_eq_some
    {recognizer : MachineDescription}
    (hrecognizer : StageInputRecognizerSpec recognizer)
    {code out : Word MachineCodeSymbol}
    (htransform :
      StageInputIdentityPrimitive.transform code = some out) :
    (StageInputIdentityDescription recognizer).HaltsWithTape
      (MachineDescription.encodeCodeWordAsInput code)
      (Tape.move Direction.right
        (Tape.input (MachineDescription.encodeCodeWordAsInput out))) := by
  rcases
      (stageInputIdentityPrimitive_transform_eq_some_iff
        code out).mp htransform with
    ⟨w, stage, hcode, hout⟩
  let A := recognizer
  let B := MachineDescription.ExactIdentityDescription
  let Tmid :=
    Tape.input (MachineDescription.encodeCodeWordAsInput code)
  let Tout :=
    Tape.move Direction.right
      (Tape.input (MachineDescription.encodeCodeWordAsInput out))
  have hAready : A.SubroutineReady := hrecognizer.left
  have hBready : B.SubroutineReady :=
    ⟨MachineDescription.exactIdentityDescription_wellFormed,
      MachineDescription.exactIdentityDescription_haltTransitionFree⟩
  rcases hrecognizer.right.left w stage with ⟨nA, hA⟩
  have hArun :
      A.runConfig nA
          { state := A.start
            tape :=
              Tape.input
                (MachineDescription.encodeCodeWordAsInput code) } =
        { state := A.halt, tape := Tmid } := by
    simpa [A, Tmid, stageInputBits, hcode]
      using hA
  have hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start
              tape := Tape.move Direction.right Tmid } =
          { state := B.halt, tape := Tout } := by
    refine ⟨0, ?_⟩
    simp [B, Tmid, Tout, hcode, hout,
      MachineDescription.runConfig,
      MachineDescription.ExactIdentityDescription]
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.right)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  have hn' :
      (StageInputIdentityDescription recognizer).runConfig n
          ((StageInputIdentityDescription recognizer).initial
            (MachineDescription.encodeCodeWordAsInput code)) =
        { state := (StageInputIdentityDescription recognizer).halt
          tape :=
            Tape.move Direction.right
              (Tape.input (MachineDescription.encodeCodeWordAsInput out)) } := by
    simpa [StageInputIdentityDescription, A, B, Tout] using hn
  constructor
  · exact congrArg MachineDescription.Configuration.state hn'
  · exact congrArg MachineDescription.Configuration.tape hn'

private theorem
    stageInputIdentityDescription_haltsWithTape_inv
    {recognizer : MachineDescription}
    (hrecognizer : StageInputRecognizerSpec recognizer)
    {code : Word MachineCodeSymbol} {T : Tape Bool}
    (hhalt :
      (StageInputIdentityDescription recognizer).HaltsWithTape
        (MachineDescription.encodeCodeWordAsInput code) T) :
    exists w : Word Bool,
    exists stage : Nat,
      code = PairedRecognizerDovetailStageInputCode w stage ∧
        T =
          Tape.move Direction.right
            (Tape.input (MachineDescription.encodeCodeWordAsInput code)) := by
  let A := recognizer
  let B := MachineDescription.ExactIdentityDescription
  have hAready : A.SubroutineReady := hrecognizer.left
  have hBready : B.SubroutineReady :=
    ⟨MachineDescription.exactIdentityDescription_wellFormed,
      MachineDescription.exactIdentityDescription_haltTransitionFree⟩
  rcases
      MachineDescription.seqSubroutine_haltsWithTape_inv
        (A := A) (B := B) (handoffMove := Direction.right)
        hAready hBready hhalt with
    ⟨Tmid, hAhalt, hBReach⟩
  rcases hrecognizer.right.right code Tmid hAhalt with
    ⟨w, stage, hcode, hTmid⟩
  rcases hBReach with ⟨nB, hBRun⟩
  have hBRun' :
      MachineDescription.Configuration.mk B.halt
          (Tape.move Direction.right Tmid) =
        MachineDescription.Configuration.mk B.halt T := by
    simpa [B] using
      ((exactIdentityDescription_runConfig_from_start
          nB (Tape.move Direction.right Tmid)).symm.trans hBRun)
  have hT :
      T = Tape.move Direction.right Tmid := by
    exact (congrArg MachineDescription.Configuration.tape hBRun').symm
  refine ⟨w, stage, hcode, ?_⟩
  rw [hT, hTmid]

private theorem
    stageInputIdentityClosedHandoffConstruction_of_recognizer
    {recognizer : MachineDescription}
    (hrecognizer : StageInputRecognizerSpec recognizer) :
    TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      StageInputIdentityPrimitive
      (StageInputIdentityDescription recognizer)
      tapeCodePrimitiveCodeWordHandoffMove := by
  constructor
  · constructor
    · constructor
      · exact
          (stageInputIdentityDescription_subroutineReady
            hrecognizer).left
      · intro code out
        constructor
        · intro houtput
          rcases houtput with ⟨n, hn⟩
          let D := StageInputIdentityDescription recognizer
          let T : Tape Bool :=
            (D.runConfig n
              (D.initial
                (MachineDescription.encodeCodeWordAsInput code))).tape
          have hhalt : D.HaltsWithTape
              (MachineDescription.encodeCodeWordAsInput code) T := by
            refine ⟨n, ?_⟩
            exact ⟨hn.left, rfl⟩
          rcases
              stageInputIdentityDescription_haltsWithTape_inv
                hrecognizer hhalt with
            ⟨w, stage, hcode, hT⟩
          have hnorm :
              Tape.normalizedOutput T =
                MachineDescription.encodeCodeWordAsInput code := by
            rw [hT]
            exact
              tape_normalizedOutput_move_right_input
                (MachineDescription.encodeCodeWordAsInput code)
          have hout :
              MachineDescription.encodeCodeWordAsInput code =
                MachineDescription.encodeCodeWordAsInput out := by
            simpa [D, T, hnorm] using hn.right
          have houtCode : out = code :=
            (MachineDescription.encodeCodeWordAsInput_injective hout).symm
          rw [houtCode]
          exact
            (stageInputIdentityPrimitive_transform_eq_some_iff
              code code).mpr ⟨w, stage, hcode, hcode⟩
        · intro htransform
          have hhalt :=
            stageInputIdentityDescription_haltsWithTape_of_transform_eq_some
              hrecognizer htransform
          rcases hhalt with ⟨n, hn⟩
          refine ⟨n, ?_⟩
          constructor
          · exact hn.left
          · rcases
                (stageInputIdentityPrimitive_transform_eq_some_iff
                  code out).mp htransform with
              ⟨w, stage, hcode, hout⟩
            rw [hn.right]
            rw [hout]
            exact
              tape_normalizedOutput_move_right_input
                (MachineDescription.encodeCodeWordAsInput
                  (PairedRecognizerDovetailStageInputCode w stage))
    · exact
        (stageInputIdentityDescription_subroutineReady
          hrecognizer).right
  · intro code T hhalt
    rcases
        stageInputIdentityDescription_haltsWithTape_inv
          hrecognizer hhalt with
      ⟨w, stage, hcode, hT⟩
    refine ⟨code, ?_, ?_, ?_⟩
    · exact
        (stageInputIdentityPrimitive_transform_eq_some_iff
          code code).mpr ⟨w, stage, hcode, hcode⟩
    · rw [hT]
      exact
        tape_normalizedOutput_move_right_input
          (MachineDescription.encodeCodeWordAsInput code)
    · rw [hT, hcode]
      simpa [tapeCodePrimitiveCodeWordHandoffMove,
        stageInputBits] using
        stageInputBits_move_left_move_right_input w stage

private theorem stageInputValidatorSpec_of_identityClosedHandoff
    {validator : MachineDescription}
    (hvalidator :
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        StageInputIdentityPrimitive validator
        tapeCodePrimitiveCodeWordHandoffMove) :
    StageInputValidatorSpec validator := by
  constructor
  · exact
      tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_subroutineReady
        hvalidator
  constructor
  · intro w stage
    let code := PairedRecognizerDovetailStageInputCode w stage
    have htransform :
        StageInputIdentityPrimitive.transform code =
          some code := by
      exact
        (stageInputIdentityPrimitive_transform_eq_some_iff
          code code).mpr ⟨w, stage, rfl, rfl⟩
    rcases
        tapeCodePrimitiveHandoffCompiledSubroutineByDescription_haltsWithTape_of_transform_eq_some
          (tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_handoffCompiled
            hvalidator)
          htransform with
      ⟨T, hhalt, hmove⟩
    rcases hhalt with ⟨steps, hsteps⟩
    have hT :
        T =
          Tape.move Direction.right
            (Tape.input (stageInputBits w stage)) := by
      have hmove' :
          Tape.move Direction.left T =
            Tape.input (stageInputBits w stage) := by
        simpa [tapeCodePrimitiveCodeWordHandoffMove,
          stageInputBits, code] using hmove
      rcases stageInputBits_exists_cons_cons w stage with
        ⟨a, b, rest, hbits⟩
      rw [hbits] at hmove' ⊢
      exact
        tape_eq_move_right_input_of_move_left_eq_input_cons_cons
          hmove'
    refine ⟨steps, ?_⟩
    have hrunRaw :
        validator.runConfig steps
            (validator.initial
              (MachineDescription.encodeCodeWordAsInput code)) =
          { state := validator.halt, tape := T } := by
      cases hconfig :
          validator.runConfig steps
            (validator.initial
              (MachineDescription.encodeCodeWordAsInput code)) with
      | mk state tape =>
          have hstate : state = validator.halt := by
            simpa [MachineDescription.HaltsWithTapeIn,
              hconfig] using hsteps.left
          have htape : tape = T := by
            simpa [MachineDescription.HaltsWithTapeIn,
              hconfig] using hsteps.right
          cases hstate
          cases htape
          rfl
    have hrun :
        validator.runConfig steps
            (validator.initial (stageInputBits w stage)) =
          { state := validator.halt, tape := T } := by
      simpa [stageInputBits, code] using hrunRaw
    rw [hrun, hT]
  · intro code T hhalt
    rcases
        tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_haltsWithTape_output
          hvalidator hhalt with
      ⟨out, htransform, _hnorm, hmove⟩
    rcases
        (stageInputIdentityPrimitive_transform_eq_some_iff
          code out).mp htransform with
      ⟨w, stage, hcode, hout⟩
    refine ⟨w, stage, hcode, ?_⟩
    simpa [stageInputBits, hout] using hmove

private def finalBoolFlagsCode :
    Word MachineCodeSymbol :=
  MachineDescription.encodeBoolAppend false
    (MachineDescription.encodeBoolAppend false [])

private theorem finalBoolFlagsCode_ne_nil :
    finalBoolFlagsCode ≠ [] := by
  simp [finalBoolFlagsCode,
    MachineDescription.encodeBoolAppend,
    MachineDescription.encodeCellAppend,
    MachineDescription.encodeCell]

private def AppendFinalBoolFlagsReturnDescription :
    MachineDescription :=
  TransitionPrefixedFirstBitAppendCodeWordReturnDescription
    finalBoolFlagsCode

private theorem
    appendFinalBoolFlagsReturnDescription_subroutineReady :
    AppendFinalBoolFlagsReturnDescription.SubroutineReady := by
  exact
    transitionPrefixedFirstBitAppendCodeWordReturnDescription_subroutineReady
      finalBoolFlagsCode
      finalBoolFlagsCode_ne_nil

private def AppendSecondInputTapeAndFlagsDescription
    (copier : MachineDescription) : MachineDescription :=
  MachineDescription.seqSubroutine
    copier
    AppendFinalBoolFlagsReturnDescription
    Direction.left

private theorem
    appendSecondInputTapeAndFlagsDescription_subroutineReady
    {copier : MachineDescription}
    (hcopier : AppendInputTapeReturnSpec copier) :
    (AppendSecondInputTapeAndFlagsDescription
      copier).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    hcopier.left
    appendFinalBoolFlagsReturnDescription_subroutineReady

private def AppendRejectThenInputTapeAndFlagsDescription
    (reject copier : MachineDescription) : MachineDescription :=
  MachineDescription.seqSubroutine
    (TransitionPrefixedFirstBitAppendNatReturnDescription
      reject.start)
    (AppendSecondInputTapeAndFlagsDescription copier)
    Direction.left

private theorem
    appendRejectThenInputTapeAndFlagsDescription_subroutineReady
    {reject copier : MachineDescription}
    (hcopier : AppendInputTapeReturnSpec copier) :
    (AppendRejectThenInputTapeAndFlagsDescription
      reject copier).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    (transitionPrefixedFirstBitAppendNatReturnDescription_subroutineReady
      reject.start)
    (appendSecondInputTapeAndFlagsDescription_subroutineReady
      hcopier)

private def AppendFirstInputTapeThenRejectDescription
    (reject copier : MachineDescription) : MachineDescription :=
  MachineDescription.seqSubroutine
    copier
    (AppendRejectThenInputTapeAndFlagsDescription reject copier)
    Direction.left

private theorem
    appendFirstInputTapeThenRejectDescription_subroutineReady
    {reject copier : MachineDescription}
    (hcopier : AppendInputTapeReturnSpec copier) :
    (AppendFirstInputTapeThenRejectDescription
      reject copier).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    hcopier.left
    (appendRejectThenInputTapeAndFlagsDescription_subroutineReady
      hcopier)

private def DescriptionWithCopier
    (accept reject copier : MachineDescription) : MachineDescription :=
  MachineDescription.seqSubroutine
    (MarkedPrefixAppendNatReturnDescription accept.start)
    (AppendFirstInputTapeThenRejectDescription reject copier)
    Direction.left

private theorem
    descriptionWithCopier_subroutineReady
    {accept reject copier : MachineDescription}
    (hcopier : AppendInputTapeReturnSpec copier) :
    (DescriptionWithCopier
      accept reject copier).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    (markedPrefixAppendNatReturnDescription_subroutineReady
      accept.start)
    (appendFirstInputTapeThenRejectDescription_subroutineReady
      hcopier)

private theorem
    appendSecondInputTapeAndFlagsDescription_run
    {copier : MachineDescription}
    (hcopier : AppendInputTapeReturnSpec copier)
    (w : Word Bool) (stage : Nat) (suffixBits : Word Bool) :
    exists steps : Nat,
      (AppendSecondInputTapeAndFlagsDescription
        copier).runConfig steps
          { state :=
              (AppendSecondInputTapeAndFlagsDescription
                copier).start
            tape :=
              tapeAtCells []
                (some false :: some false ::
                  ((List.append [false, true]
                    (List.append (stageInputBits w stage)
                      suffixBits)).map some)) } =
        { state :=
            (AppendSecondInputTapeAndFlagsDescription
              copier).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append [false, true]
                  (List.append (stageInputBits w stage)
                    (List.append suffixBits
                      (List.append (inputTapeBits w)
                        (MachineDescription.encodeCodeWordAsInput
                          finalBoolFlagsCode))))).map some)) } := by
  let A := copier
  let B := AppendFinalBoolFlagsReturnDescription
  let copiedSuffix :=
    List.append (stageInputBits w stage)
      (List.append suffixBits (inputTapeBits w))
  let Tmid :=
    tapeAtCells [some false]
      (some false ::
        ((List.append [false, true] copiedSuffix).map some))
  have hAready : A.SubroutineReady := hcopier.left
  have hBready : B.SubroutineReady :=
    appendFinalBoolFlagsReturnDescription_subroutineReady
  rcases hcopier.right w stage suffixBits with ⟨nA, hArunBase⟩
  have hArun :
      A.runConfig nA
          { state := A.start
            tape :=
              tapeAtCells []
                (some false :: some false ::
                  ((List.append [false, true]
                    (List.append (stageInputBits w stage)
                      suffixBits)).map some)) } =
        { state := A.halt, tape := Tmid } := by
    simpa [A, Tmid, copiedSuffix, List.append_assoc] using hArunBase
  have hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start
              tape := Tape.move Direction.left Tmid } =
          { state := B.halt
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append [false, true]
                    (List.append (stageInputBits w stage)
                      (List.append suffixBits
                        (List.append (inputTapeBits w)
                          (MachineDescription.encodeCodeWordAsInput
                            finalBoolFlagsCode))))).map some)) } := by
    rcases
        transitionPrefixedFirstBitAppendCodeWordReturnDescription_run
          finalBoolFlagsCode
          finalBoolFlagsCode_ne_nil
          copiedSuffix with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    simpa [B, AppendFinalBoolFlagsReturnDescription,
      Tmid, copiedSuffix, tapeAtCells, Tape.move, Tape.moveLeft,
      List.append_assoc] using hB
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.left)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [AppendSecondInputTapeAndFlagsDescription,
    A, B] using hn

private theorem
    appendRejectThenInputTapeAndFlagsDescription_run
    {reject copier : MachineDescription}
    (hcopier : AppendInputTapeReturnSpec copier)
    (w : Word Bool) (stage : Nat) (suffixBits : Word Bool) :
    exists steps : Nat,
      (AppendRejectThenInputTapeAndFlagsDescription
        reject copier).runConfig steps
          { state :=
              (AppendRejectThenInputTapeAndFlagsDescription
                reject copier).start
            tape :=
              tapeAtCells []
                (some false :: some false ::
                  ((List.append [false, true]
                    (List.append (stageInputBits w stage)
                      suffixBits)).map some)) } =
        { state :=
            (AppendRejectThenInputTapeAndFlagsDescription
              reject copier).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append [false, true]
                  (List.append (stageInputBits w stage)
                    (List.append suffixBits
                      (List.append (natBits reject.start)
                        (List.append (inputTapeBits w)
                          (MachineDescription.encodeCodeWordAsInput
                            finalBoolFlagsCode)))))).map some)) } := by
  let A :=
    TransitionPrefixedFirstBitAppendNatReturnDescription
      reject.start
  let B := AppendSecondInputTapeAndFlagsDescription copier
  let rejectSuffix :=
    List.append (stageInputBits w stage)
      (List.append suffixBits (natBits reject.start))
  let Tmid :=
    tapeAtCells [some false]
      (some false ::
        ((List.append [false, true] rejectSuffix).map some))
  have hAready : A.SubroutineReady := by
    exact
      transitionPrefixedFirstBitAppendNatReturnDescription_subroutineReady
        reject.start
  have hBready : B.SubroutineReady := by
    exact
      appendSecondInputTapeAndFlagsDescription_subroutineReady
        hcopier
  rcases
      transitionPrefixedFirstBitAppendNatReturnDescription_run
        reject.start
        (List.append (stageInputBits w stage) suffixBits) with
    ⟨nA, hA⟩
  have hArun :
      A.runConfig nA
          { state := A.start
            tape :=
              tapeAtCells []
                (some false :: some false ::
                  ((List.append [false, true]
                    (List.append (stageInputBits w stage)
                      suffixBits)).map some)) } =
        { state := A.halt, tape := Tmid } := by
    simpa [A, Tmid, rejectSuffix, natBits,
      List.append_assoc] using hA
  have hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start
              tape := Tape.move Direction.left Tmid } =
          { state := B.halt
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append [false, true]
                    (List.append (stageInputBits w stage)
                      (List.append suffixBits
                        (List.append (natBits reject.start)
                          (List.append (inputTapeBits w)
                            (MachineDescription.encodeCodeWordAsInput
                              finalBoolFlagsCode)))))).map some)) } := by
    rcases
        appendSecondInputTapeAndFlagsDescription_run
          hcopier w stage
          (List.append suffixBits (natBits reject.start)) with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    simpa [B, Tmid, rejectSuffix, tapeAtCells,
      Tape.move, Tape.moveLeft, List.append_assoc] using hB
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.left)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [AppendRejectThenInputTapeAndFlagsDescription,
    A, B] using hn

private theorem
    appendFirstInputTapeThenRejectDescription_run
    {reject copier : MachineDescription}
    (hcopier : AppendInputTapeReturnSpec copier)
    (w : Word Bool) (stage : Nat) (suffixBits : Word Bool) :
    exists steps : Nat,
      (AppendFirstInputTapeThenRejectDescription
        reject copier).runConfig steps
          { state :=
              (AppendFirstInputTapeThenRejectDescription
                reject copier).start
            tape :=
              tapeAtCells []
                (some false :: some false ::
                  ((List.append [false, true]
                    (List.append (stageInputBits w stage)
                      suffixBits)).map some)) } =
        { state :=
            (AppendFirstInputTapeThenRejectDescription
              reject copier).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append [false, true]
                  (List.append (stageInputBits w stage)
                    (List.append suffixBits
                      (List.append (inputTapeBits w)
                        (List.append (natBits reject.start)
                          (List.append (inputTapeBits w)
                            (MachineDescription.encodeCodeWordAsInput
                              finalBoolFlagsCode))))))).map some)) } := by
  let A := copier
  let B := AppendRejectThenInputTapeAndFlagsDescription
    reject copier
  let firstTapeSuffix :=
    List.append (stageInputBits w stage)
      (List.append suffixBits (inputTapeBits w))
  let Tmid :=
    tapeAtCells [some false]
      (some false ::
        ((List.append [false, true] firstTapeSuffix).map some))
  have hAready : A.SubroutineReady := hcopier.left
  have hBready : B.SubroutineReady := by
    exact
      appendRejectThenInputTapeAndFlagsDescription_subroutineReady
        hcopier
  rcases hcopier.right w stage suffixBits with ⟨nA, hA⟩
  have hArun :
      A.runConfig nA
          { state := A.start
            tape :=
              tapeAtCells []
                (some false :: some false ::
                  ((List.append [false, true]
                    (List.append (stageInputBits w stage)
                      suffixBits)).map some)) } =
        { state := A.halt, tape := Tmid } := by
    simpa [A, Tmid, firstTapeSuffix, List.append_assoc] using hA
  have hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start
              tape := Tape.move Direction.left Tmid } =
          { state := B.halt
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append [false, true]
                    (List.append (stageInputBits w stage)
                      (List.append suffixBits
                        (List.append (inputTapeBits w)
                          (List.append (natBits reject.start)
                            (List.append (inputTapeBits w)
                              (MachineDescription.encodeCodeWordAsInput
                                finalBoolFlagsCode))))))).map some)) } := by
    rcases
        appendRejectThenInputTapeAndFlagsDescription_run
          (reject := reject) hcopier w stage
          (List.append suffixBits (inputTapeBits w)) with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    simpa [B, Tmid, firstTapeSuffix, tapeAtCells,
      Tape.move, Tape.moveLeft, List.append_assoc] using hB
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.left)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [AppendFirstInputTapeThenRejectDescription,
    A, B] using hn

private theorem
    descriptionWithCopier_run_bits
    {accept reject copier : MachineDescription}
    (hcopier : AppendInputTapeReturnSpec copier)
    (w : Word Bool) (stage : Nat) :
    exists steps : Nat,
      (DescriptionWithCopier
        accept reject copier).runConfig steps
          ((DescriptionWithCopier
            accept reject copier).initial
            (MachineDescription.encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w stage))) =
        { state :=
            (DescriptionWithCopier
              accept reject copier).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append [false, true]
                  (List.append (stageInputBits w stage)
                    (List.append (natBits accept.start)
                      (List.append (inputTapeBits w)
                        (List.append (natBits reject.start)
                          (List.append (inputTapeBits w)
                            (MachineDescription.encodeCodeWordAsInput
                              finalBoolFlagsCode))))))).map some)) } := by
  let A := MarkedPrefixAppendNatReturnDescription accept.start
  let B := AppendFirstInputTapeThenRejectDescription
    reject copier
  let acceptSuffix :=
    List.append (stageInputBits w stage)
      (natBits accept.start)
  let Tmid :=
    tapeAtCells [some false]
      (some false ::
        ((List.append [false, true] acceptSuffix).map some))
  have hAready : A.SubroutineReady := by
    exact
      markedPrefixAppendNatReturnDescription_subroutineReady
        accept.start
  have hBready : B.SubroutineReady := by
    exact
      appendFirstInputTapeThenRejectDescription_subroutineReady
        hcopier
  rcases
      markedPrefixAppendNatReturnDescription_run_stageInput
        accept.start w stage with
    ⟨nA, hA⟩
  have hArun :
      A.runConfig nA
          { state := A.start
            tape :=
              Tape.input
                (MachineDescription.encodeCodeWordAsInput
                  (PairedRecognizerDovetailStageInputCode w stage)) } =
        { state := A.halt, tape := Tmid } := by
    simpa [A, Tmid, acceptSuffix, stageInputBits,
      natBits, MachineDescription.initial, List.append_assoc]
      using hA
  have hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start
              tape := Tape.move Direction.left Tmid } =
          { state := B.halt
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append [false, true]
                    (List.append (stageInputBits w stage)
                      (List.append (natBits accept.start)
                        (List.append (inputTapeBits w)
                          (List.append (natBits reject.start)
                            (List.append (inputTapeBits w)
                              (MachineDescription.encodeCodeWordAsInput
                                finalBoolFlagsCode))))))).map some)) } := by
    rcases
        appendFirstInputTapeThenRejectDescription_run
          (reject := reject) hcopier w stage
          (natBits accept.start) with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    simpa [B, Tmid, acceptSuffix, tapeAtCells,
      Tape.move, Tape.moveLeft, List.append_assoc] using hB
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.left)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [DescriptionWithCopier,
    MachineDescription.initial, A, B] using hn

private theorem codeCells_encodeNat
    (n : Nat) :
    codeCells (MachineDescription.encodeNat n) =
      natCodeCells n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        List.append
            (codeSymbolCells MachineCodeSymbol.tick)
            (codeCells (MachineDescription.encodeNat n)) =
          List.append
            (codeSymbolCells MachineCodeSymbol.tick)
            (natCodeCells n)
      rw [ih]

private theorem codeCells_encodeNatAppend
    (n : Nat) (suffix : Word MachineCodeSymbol) :
    codeCells
        (MachineDescription.encodeNatAppend n suffix) =
      List.append (natCodeCells n)
        (codeCells suffix) := by
  rw [MachineDescription.encodeNatAppend, codeCells_append,
    codeCells_encodeNat]

private theorem codeCells_encodeCell
    (cell : Option Bool) :
    codeCells (MachineDescription.encodeCell cell) =
      cellCodeCells cell := by
  cases cell with
  | none =>
      rfl
  | some b =>
      cases b <;> rfl

private theorem codeCells_encodeCellAppend
    (cell : Option Bool) (suffix : Word MachineCodeSymbol) :
    codeCells
        (MachineDescription.encodeCellAppend cell suffix) =
      List.append (cellCodeCells cell)
        (codeCells suffix) := by
  rw [MachineDescription.encodeCellAppend, codeCells_append,
    codeCells_encodeCell]

private theorem codeCells_encodeCellsAppend
    (cells : List (Option Bool)) (suffix : Word MachineCodeSymbol) :
    codeCells
        (MachineDescription.encodeCellsAppend cells suffix) =
      List.append (cellsCodeCells cells)
        (codeCells suffix) := by
  induction cells with
  | nil =>
      rfl
  | cons cell rest ih =>
      rw [MachineDescription.encodeCellsAppend,
        codeCells_encodeCellAppend, ih]
      simp [cellsCodeCells, List.append_assoc]

private theorem codeCells_encodeCellListAppend
    (cells : List (Option Bool)) (suffix : Word MachineCodeSymbol) :
    codeCells
        (MachineDescription.encodeCellListAppend cells suffix) =
      List.append (natCodeCells cells.length)
        (List.append (cellsCodeCells cells)
          (codeCells suffix)) := by
  rw [MachineDescription.encodeCellListAppend,
    codeCells_encodeNatAppend,
    codeCells_encodeCellsAppend]

private def inputTapeCodeCells :
    Word Bool -> List (Option Bool)
  | [] =>
      List.append (natCodeCells 0)
        (List.append (cellCodeCells none)
          (natCodeCells 0))
  | b :: rest =>
      List.append (natCodeCells 0)
        (List.append (cellCodeCells (some b))
          (List.append (natCodeCells rest.length)
            (cellsCodeCells (rest.map some))))

private theorem codeCells_encodeTapeAppend_input
    (w : Word Bool) (suffix : Word MachineCodeSymbol) :
    codeCells
        (MachineDescription.encodeTapeAppend (Tape.input w) suffix) =
      List.append (inputTapeCodeCells w)
        (codeCells suffix) := by
  cases w with
  | nil =>
      rw [encodeTapeAppend_input_nil,
        codeCells_encodeCellListAppend,
        codeCells_encodeCellAppend,
        codeCells_encodeCellListAppend]
      simp [inputTapeCodeCells, cellsCodeCells,
        List.append_assoc]
  | cons b rest =>
      rw [encodeTapeAppend_input_cons,
        codeCells_encodeCellListAppend,
        codeCells_encodeCellAppend,
        codeCells_encodeCellListAppend]
      simp [inputTapeCodeCells, cellsCodeCells,
        List.append_assoc]

private def boolCodeCells (b : Bool) :
    List (Option Bool) :=
  cellCodeCells (some b)

private theorem codeCells_encodeBoolAppend
    (b : Bool) (suffix : Word MachineCodeSymbol) :
    codeCells
        (MachineDescription.encodeBoolAppend b suffix) =
      List.append (boolCodeCells b)
        (codeCells suffix) := by
  rw [MachineDescription.encodeBoolAppend,
    codeCells_encodeCellAppend]
  rfl

private theorem codeCells_encodeBoolWordAppend
    (w : Word Bool) (suffix : Word MachineCodeSymbol) :
    codeCells
        (MachineDescription.encodeBoolWordAppend w suffix) =
      List.append (boolWordCells w)
        (codeCells suffix) := by
  rw [MachineDescription.encodeBoolWordAppend,
    codeCells_encodeCellListAppend]
  simp [boolWordCells, boolPayloadCells,
    List.append_assoc]

private theorem stageInputCells_eq_bool_word_nat
    (w : Word Bool) (stage : Nat) :
    stageInputCells w stage =
      List.append (boolWordCells w)
        (natCodeCells stage) := by
  rw [stageInputCells, PairedRecognizerDovetailStageInputCode,
    MachineDescription.DovetailLayout.stageInputCode,
    MachineDescription.DovetailLayout.stageInputCodeAppend,
    codeCells_encodeBoolWordAppend,
    codeCells_encodeNatAppend]
  simp [codeCells, MachineDescription.encodeCodeWordAsInput]

private theorem suffixCells_eq_field_blocks
    (accept reject : MachineDescription)
    (w : Word Bool) :
    suffixCells accept reject w =
      List.append (natCodeCells accept.start)
        (List.append (inputTapeCodeCells w)
          (List.append (natCodeCells reject.start)
            (List.append (inputTapeCodeCells w)
              (List.append (boolCodeCells false)
                (boolCodeCells false))))) := by
  rw [suffixCells, SuffixCode,
    codeCells_encodeNatAppend,
    codeCells_encodeTapeAppend_input,
    codeCells_encodeNatAppend,
    codeCells_encodeTapeAppend_input,
    codeCells_encodeBoolAppend,
    codeCells_encodeBoolAppend]
  simp [codeCells, MachineDescription.encodeCodeWordAsInput]

private theorem outputCells_eq_stageInput_append_suffix
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    outputCells accept reject w stage =
      List.append [some false, some false, some false, some true]
        (List.append
          (stageInputCells w stage)
          (suffixCells accept reject w)) := by
  rw [outputCells, stageInputCells,
    suffixCells,
    outputCode_eq_stageInput_append_suffix]
  unfold codeCells
  simp [MachineDescription.encodeCodeWordAsInput,
    MachineDescription.encodeCodeSymbolAsInput]
  change
    List.map some
        (MachineDescription.encodeCodeWordAsInput
          (List.append
            (PairedRecognizerDovetailStageInputCode w stage)
            (SuffixCode accept reject w))) =
      List.append
        (List.map some
          (MachineDescription.encodeCodeWordAsInput
            (PairedRecognizerDovetailStageInputCode w stage)))
        (List.map some
          (MachineDescription.encodeCodeWordAsInput
            (SuffixCode accept reject w)))
  rw [MachineDescription.encodeCodeWordAsInput_append]
  exact map_some_append
    (MachineDescription.encodeCodeWordAsInput
      (PairedRecognizerDovetailStageInputCode w stage))
    (MachineDescription.encodeCodeWordAsInput
      (SuffixCode accept reject w))

private theorem outputCells_eq_phase_blocks
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    outputCells accept reject w stage =
      List.append [some false, some false, some false, some true]
        (List.append (boolWordCells w)
          (List.append (natCodeCells stage)
            (suffixCells accept reject w))) := by
  rw [outputCells_eq_stageInput_append_suffix,
    stageInputCells_eq_bool_word_nat]
  simp [List.append_assoc]

private theorem outputCells_eq_full_field_blocks
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    outputCells accept reject w stage =
      List.append [some false, some false, some false, some true]
        (List.append (boolWordCells w)
          (List.append (natCodeCells stage)
            (List.append (natCodeCells accept.start)
              (List.append (inputTapeCodeCells w)
                (List.append (natCodeCells reject.start)
                  (List.append (inputTapeCodeCells w)
                    (List.append (boolCodeCells false)
                      (boolCodeCells false)))))))) := by
  rw [outputCells_eq_phase_blocks,
    suffixCells_eq_field_blocks]

private theorem tapeAtCells_eq_input_transition_prefixed
    (tail : Word Bool) :
    tapeAtCells []
        ((List.append
          (MachineDescription.encodeCodeSymbolAsInput
            MachineCodeSymbol.transition) tail).map some) =
      Tape.input
        (List.append
          (MachineDescription.encodeCodeSymbolAsInput
            MachineCodeSymbol.transition) tail) := by
  simp [tapeAtCells,
    MachineDescription.encodeCodeSymbolAsInput, Tape.input]

private theorem tapeAtCells_right_eq_move_right_input_transition_prefixed
    (tail : Word Bool) :
    tapeAtCells
        [some false]
        (List.append [some false, some false, some true]
          (tail.map some)) =
      Tape.move Direction.right
        (Tape.input
          (List.append
            (MachineDescription.encodeCodeSymbolAsInput
              MachineCodeSymbol.transition) tail)) := by
  simp [tapeAtCells,
    MachineDescription.encodeCodeSymbolAsInput, Tape.input,
    Tape.move, Tape.moveRight]

private theorem outputTape_eq_cells
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    OutputTape accept reject w stage =
      tapeAtCells
        [some false]
        (List.append [some false, some false, some true]
          (List.append
            ((MachineDescription.encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w stage)).map some)
            ((MachineDescription.encodeCodeWordAsInput
              (SuffixCode
                accept reject w)).map some))) := by
  rw [outputTape_eq_stageInput_append_suffix]
  rw [← tapeAtCells_right_eq_move_right_input_transition_prefixed
    (tail :=
      List.append
        (MachineDescription.encodeCodeWordAsInput
          (PairedRecognizerDovetailStageInputCode w stage))
        (MachineDescription.encodeCodeWordAsInput
          (SuffixCode
            accept reject w)))]
  rw [map_some_append]

private theorem natCodeCells_eq_bits
    (n : Nat) :
    natCodeCells n =
      (natBits n).map some := by
  rw [← codeCells_encodeNat n]
  rfl

private theorem inputTapeCodeCells_eq_bits
    (w : Word Bool) :
    inputTapeCodeCells w =
      (inputTapeBits w).map some := by
  have h :=
    codeCells_encodeTapeAppend_input
      w ([] : Word MachineCodeSymbol)
  simpa [inputTapeBits, codeCells,
    MachineDescription.encodeCodeWordAsInput] using h.symm

private theorem finalBoolFlagsCodeCells_eq_bits :
    List.append (boolCodeCells false)
        (boolCodeCells false) =
      (MachineDescription.encodeCodeWordAsInput
        finalBoolFlagsCode).map some := by
  simp [finalBoolFlagsCode, boolCodeCells,
    cellCodeCells, codeSymbolCells,
    MachineDescription.encodeBoolAppend, MachineDescription.encodeCellAppend,
    MachineDescription.encodeCell,
    MachineDescription.encodeCodeWordAsInput,
    MachineDescription.encodeCodeSymbolAsInput]

private theorem outputTape_eq_bits
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    OutputTape accept reject w stage =
      tapeAtCells [some false]
        (some false ::
          ((List.append [false, true]
            (List.append (stageInputBits w stage)
              (List.append (natBits accept.start)
                (List.append (inputTapeBits w)
                    (List.append (natBits reject.start)
                      (List.append (inputTapeBits w)
                        (MachineDescription.encodeCodeWordAsInput
                          finalBoolFlagsCode))))))).map some)) := by
  rw [outputTape_eq_cells]
  change
    tapeAtCells [some false]
        (List.append [some false, some false, some true]
          (List.append (stageInputCells w stage)
            (suffixCells accept reject w))) =
      tapeAtCells [some false]
        (some false ::
          ((List.append [false, true]
            (List.append (stageInputBits w stage)
              (List.append (natBits accept.start)
                (List.append (inputTapeBits w)
                  (List.append (natBits reject.start)
                    (List.append (inputTapeBits w)
                      (MachineDescription.encodeCodeWordAsInput
                        finalBoolFlagsCode))))))).map some))
  rw [suffixCells_eq_field_blocks]
  simp only [natCodeCells_eq_bits,
    inputTapeCodeCells_eq_bits]
  rw [finalBoolFlagsCodeCells_eq_bits]
  simp [stageInputCells, stageInputBits,
    codeCells, List.map_append]

private theorem
    descriptionWithCopier_forward
    {accept reject copier : MachineDescription}
    (hcopier : AppendInputTapeReturnSpec copier) :
    ForwardSpec
      accept reject
      (DescriptionWithCopier
        accept reject copier) := by
  intro w stage
  rcases
      descriptionWithCopier_run_bits
        (accept := accept) (reject := reject) hcopier w stage with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  constructor
  · simpa [MachineDescription.HaltsWithTapeIn] using
      congrArg MachineDescription.Configuration.state hn
  · have htape :=
      congrArg MachineDescription.Configuration.tape hn
    exact htape.trans
      (outputTape_eq_bits
        accept reject w stage).symm

private theorem appendInputTapeRightCellsReturnSpec_realizer :
    AppendInputTapeRightCellsReturnConstruction := by
  sorry

private theorem appendInputTapeHeadTaggedBrancher_realizer :
    AppendInputTapeHeadTaggedBrancherConstruction := by
  intro rightCopier hrightCopier
  let blankBranch := AppendEmptyInputTapeSecondBitReturnDescription
  let falseBranch :=
    AppendKnownHeadInputTapeSecondBitReturnDescription
      false rightCopier
  let trueBranch :=
    AppendKnownHeadInputTapeSecondBitReturnDescription
      true rightCopier
  let brancher :=
    RestoreFirstBitTaggedBrancherDescription
      blankBranch falseBranch trueBranch
  have hblankReady : blankBranch.SubroutineReady := by
    exact appendEmptyInputTapeSecondBitReturnDescription_subroutineReady
  have hfalseReady : falseBranch.SubroutineReady := by
    exact
      appendKnownHeadInputTapeSecondBitReturnDescription_subroutineReady
        hrightCopier false
  have htrueReady : trueBranch.SubroutineReady := by
    exact
      appendKnownHeadInputTapeSecondBitReturnDescription_subroutineReady
        hrightCopier true
  refine ⟨brancher, ?_⟩
  constructor
  · exact
      restoreFirstBitTaggedBrancherDescription_subroutineReady
        hblankReady hfalseReady htrueReady
  constructor
  · intro stage suffixBits
    let T :=
      Tape.move Direction.left
        (appendInputTapeHeadRouterTaggedTape
          none ([] : Word Bool) stage suffixBits)
    let Tout :=
      tapeAtCells [some false]
        (some false ::
          ((List.append [false, true]
            (List.append
              (stageInputBits ([] : Word Bool) stage)
              (List.append suffixBits
                (inputTapeBits ([] : Word Bool))))).map some))
    have hread : Tape.read T = none := by
      simp [T, appendInputTapeHeadRouterTaggedTape,
        tapeAtCells, Tape.move, Tape.moveLeft, Tape.read]
    have hbranch :
        exists steps : Nat,
          blankBranch.runConfig steps
              { state := blankBranch.start
                tape :=
                  Tape.move Direction.right (Tape.write (some false) T) } =
            { state := blankBranch.halt, tape := Tout } := by
      rcases
          appendEmptyInputTapeSecondBitReturnDescription_run
            stage suffixBits with
        ⟨steps, hsteps⟩
      refine ⟨steps, ?_⟩
      simpa [blankBranch, T, Tout,
        appendInputTapeHeadRouterTaggedTape,
        tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight,
        Tape.write, List.append_assoc] using hsteps
    rcases
        restoreFirstBitTaggedBrancherDescription_run_none
          hblankReady hfalseReady htrueReady hread hbranch with
      ⟨steps, hsteps⟩
    refine ⟨steps, ?_⟩
    simpa [brancher, T, Tout] using hsteps
  · intro b rest stage suffixBits
    cases b
    · let T :=
        Tape.move Direction.left
          (appendInputTapeHeadRouterTaggedTape
            (some false) (false :: rest) stage suffixBits)
      let Tout :=
        tapeAtCells [some false]
          (some false ::
            ((List.append [false, true]
              (List.append
                (stageInputBits (false :: rest) stage)
                (List.append suffixBits
                  (inputTapeBits
                    (false :: rest))))).map some))
      have hread : Tape.read T = some false := by
        simp [T, appendInputTapeHeadRouterTaggedTape,
          tapeAtCells, Tape.move, Tape.moveLeft, Tape.read]
      have hbranch :
          exists steps : Nat,
            falseBranch.runConfig steps
                { state := falseBranch.start
                  tape :=
                    Tape.move Direction.right (Tape.write (some false) T) } =
              { state := falseBranch.halt, tape := Tout } := by
        rcases
            appendKnownHeadInputTapeSecondBitReturnDescription_run
              hrightCopier false rest stage suffixBits with
          ⟨steps, hsteps⟩
        refine ⟨steps, ?_⟩
        simpa [falseBranch, T, Tout,
          appendInputTapeHeadRouterTaggedTape,
          tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight,
          Tape.write, List.append_assoc] using hsteps
      rcases
          restoreFirstBitTaggedBrancherDescription_run_false
            hblankReady hfalseReady htrueReady hread hbranch with
        ⟨steps, hsteps⟩
      refine ⟨steps, ?_⟩
      simpa [brancher, T, Tout] using hsteps
    · let T :=
        Tape.move Direction.left
          (appendInputTapeHeadRouterTaggedTape
            (some true) (true :: rest) stage suffixBits)
      let Tout :=
        tapeAtCells [some false]
          (some false ::
            ((List.append [false, true]
              (List.append
                (stageInputBits (true :: rest) stage)
                (List.append suffixBits
                  (inputTapeBits
                    (true :: rest))))).map some))
      have hread : Tape.read T = some true := by
        simp [T, appendInputTapeHeadRouterTaggedTape,
          tapeAtCells, Tape.move, Tape.moveLeft, Tape.read]
      have hbranch :
          exists steps : Nat,
            trueBranch.runConfig steps
                { state := trueBranch.start
                  tape :=
                    Tape.move Direction.right (Tape.write (some false) T) } =
              { state := trueBranch.halt, tape := Tout } := by
        rcases
            appendKnownHeadInputTapeSecondBitReturnDescription_run
              hrightCopier true rest stage suffixBits with
          ⟨steps, hsteps⟩
        refine ⟨steps, ?_⟩
        simpa [trueBranch, T, Tout,
          appendInputTapeHeadRouterTaggedTape,
          tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight,
          Tape.write, List.append_assoc] using hsteps
      rcases
          restoreFirstBitTaggedBrancherDescription_run_true
            hblankReady hfalseReady htrueReady hread hbranch with
        ⟨steps, hsteps⟩
      refine ⟨steps, ?_⟩
      simpa [brancher, T, Tout] using hsteps

private theorem appendInputTapeHeadDispatcher_realizer :
    AppendInputTapeHeadDispatcherConstruction := by
  intro rightCopier hrightCopier
  rcases
      appendInputTapeHeadTaggedBrancher_realizer
        rightCopier hrightCopier with
    ⟨brancher, hbrancher⟩
  exact
    ⟨AppendInputTapeHeadDispatcherDescription
        AppendInputTapeHeadRouterDescription brancher,
      appendInputTapeHeadDispatcherSpec_of_router_brancher
        appendInputTapeHeadRouterDescription_spec hbrancher⟩

private theorem appendInputTapeReturnSpec_realizer :
    exists copier : MachineDescription,
      AppendInputTapeReturnSpec copier := by
  rcases appendInputTapeRightCellsReturnSpec_realizer with
    ⟨rightCopier, hrightCopier⟩
  rcases
      appendInputTapeHeadDispatcher_realizer
        rightCopier hrightCopier with
    ⟨copier, hcopier⟩
  exact
    ⟨copier,
      appendInputTapeReturnSpec_of_headDispatcher hcopier⟩

private theorem stageInputMarkedScanner_realizer :
    StageInputMarkedScannerConstruction := by
  sorry

private theorem stageInputMarkedCore_realizer :
    StageInputMarkedCoreConstruction := by
  rcases stageInputMarkedScanner_realizer with
    ⟨scanner, hscanner⟩
  exact
    ⟨StageInputMarkedCoreDescription scanner,
      stageInputMarkedCoreSpec_of_markedScanner hscanner⟩

private theorem stageInputRecognizer_realizer :
    StageInputRecognizerConstruction := by
  rcases stageInputMarkedCore_realizer with
    ⟨markedCore, hmarkedCore⟩
  exact
    ⟨StageInputRecognizerDescription markedCore,
      stageInputRecognizerSpec_of_markedCore hmarkedCore⟩

private theorem stageInputIdentityClosedHandoff_realizer :
    StageInputIdentityClosedHandoffConstruction := by
  rcases stageInputRecognizer_realizer with
    ⟨recognizer, hrecognizer⟩
  exact
    ⟨StageInputIdentityDescription recognizer,
      stageInputIdentityClosedHandoffConstruction_of_recognizer
        hrecognizer⟩

private theorem stageInputValidatorSpec_realizer :
    exists validator : MachineDescription,
      StageInputValidatorSpec validator := by
  rcases stageInputIdentityClosedHandoff_realizer with
    ⟨validator, hvalidator⟩
  exact
    ⟨validator,
      stageInputValidatorSpec_of_identityClosedHandoff
        hvalidator⟩

private def DescriptionWithValidatorCopier
    (accept reject validator copier : MachineDescription) :
    MachineDescription :=
  MachineDescription.seqSubroutine
    validator
    (DescriptionWithCopier
      accept reject copier)
    Direction.left

private theorem
    descriptionWithValidatorCopier_subroutineReady
    {accept reject validator copier : MachineDescription}
    (hvalidator : StageInputValidatorSpec validator)
    (hcopier : AppendInputTapeReturnSpec copier) :
    (DescriptionWithValidatorCopier
      accept reject validator copier).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    hvalidator.left
    (descriptionWithCopier_subroutineReady
      hcopier)

private theorem
    descriptionWithValidatorCopier_run_bits
    {accept reject validator copier : MachineDescription}
    (hvalidator : StageInputValidatorSpec validator)
    (hcopier : AppendInputTapeReturnSpec copier)
    (w : Word Bool) (stage : Nat) :
    exists steps : Nat,
      (DescriptionWithValidatorCopier
        accept reject validator copier).runConfig steps
          ((DescriptionWithValidatorCopier
            accept reject validator copier).initial
            (MachineDescription.encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w stage))) =
        { state :=
            (DescriptionWithValidatorCopier
              accept reject validator copier).halt
          tape :=
            OutputTape
              accept reject w stage } := by
  let A := validator
  let B :=
    DescriptionWithCopier
      accept reject copier
  let Tmid :=
    Tape.move Direction.right
      (Tape.input (stageInputBits w stage))
  have hAready : A.SubroutineReady := hvalidator.left
  have hBready : B.SubroutineReady :=
    descriptionWithCopier_subroutineReady
      hcopier
  rcases hvalidator.right.left w stage with ⟨nA, hA⟩
  have hArun :
      A.runConfig nA
          { state := A.start
            tape :=
              Tape.input
                (MachineDescription.encodeCodeWordAsInput
                  (PairedRecognizerDovetailStageInputCode w stage)) } =
        { state := A.halt, tape := Tmid } := by
    simpa [A, Tmid, stageInputBits,
      MachineDescription.initial] using hA
  have hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start
              tape := Tape.move Direction.left Tmid } =
          { state := B.halt
            tape :=
              OutputTape
                accept reject w stage } := by
    rcases
        descriptionWithCopier_run_bits
          (accept := accept) (reject := reject) hcopier w stage with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    have hmove :=
      stageInputBits_move_left_move_right_input w stage
    have hinput :
        Tape.move Direction.left
            (Tape.move Direction.right
              (Tape.input
                (MachineDescription.encodeCodeWordAsInput
                  (PairedRecognizerDovetailStageInputCode w stage)))) =
          Tape.input
            (MachineDescription.encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w stage)) := by
      simpa [stageInputBits] using hmove
    have hBout :
        B.runConfig nB
            (B.initial
              (MachineDescription.encodeCodeWordAsInput
                (PairedRecognizerDovetailStageInputCode w stage))) =
          { state := B.halt
            tape :=
              OutputTape
                accept reject w stage } := by
      exact hB.trans (by
        simp [B, outputTape_eq_bits])
    have hstart :
        { state := B.start
          tape := Tape.move Direction.left Tmid } =
        B.initial
          (MachineDescription.encodeCodeWordAsInput
            (PairedRecognizerDovetailStageInputCode w stage)) := by
      simp [B, Tmid, hinput, stageInputBits,
        MachineDescription.initial]
    rw [hstart]
    exact hBout
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.left)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [DescriptionWithValidatorCopier,
    A, B, MachineDescription.initial, stageInputBits] using hn

private theorem
    descriptionWithValidatorCopier_forward
    {accept reject validator copier : MachineDescription}
    (hvalidator : StageInputValidatorSpec validator)
    (hcopier : AppendInputTapeReturnSpec copier) :
    ForwardSpec
      accept reject
      (DescriptionWithValidatorCopier
        accept reject validator copier) := by
  intro w stage
  rcases
      descriptionWithValidatorCopier_run_bits
        (accept := accept) (reject := reject)
        hvalidator hcopier w stage with
    ⟨n, hn⟩
  exact ⟨n, by
    constructor
    · simpa [MachineDescription.HaltsWithTapeIn] using
        congrArg MachineDescription.Configuration.state hn
    · simpa [MachineDescription.HaltsWithTapeIn] using
        congrArg MachineDescription.Configuration.tape hn⟩

private theorem
    descriptionWithValidatorCopier_closed
    {accept reject validator copier : MachineDescription}
    (hvalidator : StageInputValidatorSpec validator)
    (hcopier : AppendInputTapeReturnSpec copier) :
    ClosedSpec
      accept reject
      (DescriptionWithValidatorCopier
        accept reject validator copier) := by
  intro code T hhalt
  let A := validator
  let B :=
    DescriptionWithCopier
      accept reject copier
  have hAready : A.SubroutineReady := hvalidator.left
  have hBready : B.SubroutineReady :=
    descriptionWithCopier_subroutineReady
      hcopier
  rcases
      MachineDescription.seqSubroutine_haltsWithTape_inv
        (A := A) (B := B) (handoffMove := Direction.left)
        hAready hBready hhalt with
    ⟨Tmid, hAhalt, nB, hBrun⟩
  rcases hvalidator.right.right code Tmid hAhalt with
    ⟨w, stage, hcode, hhandoff⟩
  subst code
  have hBhalt :
      B.HaltsWithTape (stageInputBits w stage) T := by
    refine ⟨nB, ?_⟩
    have hBrun' :
        B.runConfig nB
            (B.initial (stageInputBits w stage)) =
          { state := B.halt, tape := T } := by
      simpa [MachineDescription.initial, hhandoff] using hBrun
    constructor
    · simpa [MachineDescription.HaltsWithTapeIn] using
        congrArg MachineDescription.Configuration.state hBrun'
    · simpa [MachineDescription.HaltsWithTapeIn] using
        congrArg MachineDescription.Configuration.tape hBrun'
  have hBexpected :
      B.HaltsWithTape
        (stageInputBits w stage)
        (OutputTape
          accept reject w stage) := by
    simpa [B, stageInputBits] using
      descriptionWithCopier_forward
        (accept := accept) (reject := reject) hcopier w stage
  have hT :
      T =
        OutputTape accept reject w stage :=
    haltsWithTape_functional_of_haltTransitionFree
      hBready.right hBhalt hBexpected
  exact ⟨w, stage, rfl, hT⟩

theorem rightShiftedSpec_of_rightShiftedOutputCompiled
    {accept reject initializer : MachineDescription}
    (hinit :
      TapeCodePrimitiveRightShiftedOutputCompiledSubroutineByDescription
        (PairedRecognizerDovetailInitialLayoutCode accept reject)
        initializer) :
    RightShiftedSpec
      accept reject initializer := by
  constructor
  · exact ⟨hinit.left, hinit.right.left⟩
  constructor
  · intro w stage
    let code := PairedRecognizerDovetailStageInputCode w stage
    let out := OutputCode
      accept reject w stage
    have htransform :
        (PairedRecognizerDovetailInitialLayoutCode accept reject).transform
            code = some out := by
      simpa [code, out, OutputCode] using
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
        OutputTape accept reject w stage
      rw [hT]
      simp [out, OutputTape]
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

theorem concreteMachineConstruction_of_rightShiftedOutputCompiled
    (hcompile :
      RightShiftedOutputCompiledConstruction) :
    ConcreteMachineConstruction := by
  intro accept reject
  rcases hcompile accept reject with ⟨initializer, hinit⟩
  exact
    ⟨initializer,
      rightShiftedSpec_of_rightShiftedOutputCompiled
        hinit⟩

private theorem rightShiftedSpec_haltsWithOutput_iff
    {accept reject initializer : MachineDescription}
    (hinit :
      RightShiftedSpec
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
    simpa [OutputTape,
      OutputCode,
      tape_normalizedOutput_move_right_input] using
      MachineDescription.haltsWithOutput_of_haltsWithTape
        (hinit.right.left w stage)

private theorem tapeCodePrimitiveRightShiftedOutputCompiled_of_dovetailInitialLayoutSpec
    {accept reject initializer : MachineDescription}
    (hinit :
      RightShiftedSpec
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
          rightShiftedSpec_haltsWithOutput_iff
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

private theorem finiteDescription_realizer
    (accept reject : MachineDescription) :
    exists initializer : MachineDescription,
      RightShiftedSpec
        accept reject initializer := by
  rcases stageInputValidatorSpec_realizer with
    ⟨validator, hvalidator⟩
  rcases appendInputTapeReturnSpec_realizer with
    ⟨copier, hcopier⟩
  refine
    ⟨DescriptionWithValidatorCopier
      accept reject validator copier, ?_⟩
  constructor
  · exact
      descriptionWithValidatorCopier_subroutineReady
        hvalidator hcopier
  constructor
  · exact
      descriptionWithValidatorCopier_forward
        hvalidator hcopier
  · exact
      descriptionWithValidatorCopier_closed
        hvalidator hcopier

theorem finiteDescriptionConstruction_scaffold :
    FiniteDescriptionConstruction := by
  intro accept reject
  exact
    finiteDescription_realizer
      accept reject

theorem rightShiftedOutputCompiledConstruction :
    RightShiftedOutputCompiledConstruction := by
  intro accept reject
  rcases
      finiteDescriptionConstruction_scaffold
        accept reject with
    ⟨initializer, hinit⟩
  exact
    ⟨initializer,
      tapeCodePrimitiveRightShiftedOutputCompiled_of_dovetailInitialLayoutSpec
        hinit⟩

theorem concreteMachineConstruction :
    ConcreteMachineConstruction :=
  concreteMachineConstruction_of_rightShiftedOutputCompiled
    rightShiftedOutputCompiledConstruction

theorem machineConstruction :
    MachineConstruction := by
  intro accept reject
  exact
    concreteMachineConstruction
      accept reject

theorem pairedRecognizerDovetailInitialLayoutCode_rightShiftedSpecConstruction :
    PairedRecognizerDovetailInitialLayoutCodeRightShiftedSpecConstruction := by
  intro accept reject
  exact
    finiteDescriptionConstruction_scaffold
      accept reject

theorem pairedRecognizerDovetailInitialLayoutCode_rightShiftedOutputCompiledSubroutine
    (accept reject : MachineDescription) :
    exists initializer : MachineDescription,
      TapeCodePrimitiveRightShiftedOutputCompiledSubroutineByDescription
        (PairedRecognizerDovetailInitialLayoutCode accept reject)
        initializer :=
  rightShiftedOutputCompiledConstruction
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

end DovetailInitialLayoutInitializer

abbrev dovetailInitialLayoutCode_output_eq_expanded :=
  DovetailInitialLayoutInitializer.dovetailInitialLayoutCode_output_eq_expanded

theorem pairedRecognizerDovetailInitialLayoutCode_transform_eq_some_cons
    {accept reject : MachineDescription}
    {code out : Word MachineCodeSymbol}
    (h :
      (PairedRecognizerDovetailInitialLayoutCode accept reject).transform
          code = some out) :
    exists tail : Word MachineCodeSymbol,
      out = MachineCodeSymbol.transition :: tail :=
  DovetailInitialLayoutInitializer.pairedRecognizerDovetailInitialLayoutCode_transform_eq_some_cons h

abbrev TapeCodePrimitiveRightShiftedOutputCompiledSubroutineByDescription :=
  DovetailInitialLayoutInitializer.TapeCodePrimitiveRightShiftedOutputCompiledSubroutineByDescription

abbrev DovetailInitialLayoutInitializerOutputCode :=
  DovetailInitialLayoutInitializer.OutputCode

abbrev DovetailInitialLayoutInitializerSuffixCode :=
  DovetailInitialLayoutInitializer.SuffixCode

abbrev DovetailInitialLayoutInitializerOutputTape :=
  DovetailInitialLayoutInitializer.OutputTape

abbrev DovetailInitialLayoutInitializerReadySpec :=
  DovetailInitialLayoutInitializer.ReadySpec

abbrev DovetailInitialLayoutInitializerForwardSpec :=
  DovetailInitialLayoutInitializer.ForwardSpec

abbrev DovetailInitialLayoutInitializerClosedSpec :=
  DovetailInitialLayoutInitializer.ClosedSpec

abbrev DovetailInitialLayoutInitializerRightShiftedSpec :=
  DovetailInitialLayoutInitializer.RightShiftedSpec

abbrev DovetailInitialLayoutInitializerMachineConstruction :=
  DovetailInitialLayoutInitializer.MachineConstruction

abbrev PairedRecognizerDovetailInitialLayoutCodeRightShiftedSpecConstruction :=
  DovetailInitialLayoutInitializer.PairedRecognizerDovetailInitialLayoutCodeRightShiftedSpecConstruction

abbrev DovetailInitialLayoutInitializerConcreteMachineConstruction :=
  DovetailInitialLayoutInitializer.ConcreteMachineConstruction

abbrev DovetailInitialLayoutInitializerRightShiftedOutputCompiledConstruction :=
  DovetailInitialLayoutInitializer.RightShiftedOutputCompiledConstruction

abbrev DovetailInitialLayoutInitializerFiniteDescriptionConstruction :=
  DovetailInitialLayoutInitializer.FiniteDescriptionConstruction

abbrev dovetailInitialLayoutInitializerOutputCode_eq_expanded :=
  DovetailInitialLayoutInitializer.outputCode_eq_expanded

abbrev dovetailInitialLayoutInitializerOutputTape_eq_expanded :=
  DovetailInitialLayoutInitializer.outputTape_eq_expanded

abbrev dovetailInitialLayoutInitializerSuffixCode_eq_configurations :=
  DovetailInitialLayoutInitializer.suffixCode_eq_configurations

abbrev dovetailInitialLayoutInitializerOutputCode_eq_stageInput_append_suffix :=
  DovetailInitialLayoutInitializer.outputCode_eq_stageInput_append_suffix

abbrev dovetailInitialLayoutInitializerOutputBits_eq_stageInput_append_suffix :=
  DovetailInitialLayoutInitializer.outputBits_eq_stageInput_append_suffix

abbrev dovetailInitialLayoutInitializerOutputTape_eq_stageInput_append_suffix :=
  DovetailInitialLayoutInitializer.outputTape_eq_stageInput_append_suffix

theorem dovetailInitialLayoutInitializerRightShiftedSpec_of_rightShiftedOutputCompiled
    {accept reject initializer : MachineDescription}
    (hinit :
      TapeCodePrimitiveRightShiftedOutputCompiledSubroutineByDescription
        (PairedRecognizerDovetailInitialLayoutCode accept reject)
        initializer) :
    DovetailInitialLayoutInitializerRightShiftedSpec
      accept reject initializer :=
  DovetailInitialLayoutInitializer.rightShiftedSpec_of_rightShiftedOutputCompiled hinit

abbrev dovetailInitialLayoutInitializerConcreteMachineConstruction_of_rightShiftedOutputCompiled :=
  DovetailInitialLayoutInitializer.concreteMachineConstruction_of_rightShiftedOutputCompiled

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
  DovetailInitialLayoutInitializer.tapeCodePrimitiveClosedHandoffCompiled_of_rightShiftedOutputCompiled
      hD houtCons

abbrev dovetailInitialLayoutInitializerFiniteDescriptionConstruction_scaffold :=
  DovetailInitialLayoutInitializer.finiteDescriptionConstruction_scaffold

abbrev dovetailInitialLayoutInitializerRightShiftedOutputCompiledConstruction :=
  DovetailInitialLayoutInitializer.rightShiftedOutputCompiledConstruction

abbrev dovetailInitialLayoutInitializerConcreteMachineConstruction :=
  DovetailInitialLayoutInitializer.concreteMachineConstruction

abbrev dovetailInitialLayoutInitializerMachineConstruction :=
  DovetailInitialLayoutInitializer.machineConstruction

abbrev pairedRecognizerDovetailInitialLayoutCode_rightShiftedSpecConstruction :=
  DovetailInitialLayoutInitializer.pairedRecognizerDovetailInitialLayoutCode_rightShiftedSpecConstruction

abbrev pairedRecognizerDovetailInitialLayoutCode_rightShiftedOutputCompiledSubroutine :=
  DovetailInitialLayoutInitializer.pairedRecognizerDovetailInitialLayoutCode_rightShiftedOutputCompiledSubroutine

abbrev pairedRecognizerDovetailInitialLayoutCode_closedHandoffCompiledSubroutine :=
  DovetailInitialLayoutInitializer.pairedRecognizerDovetailInitialLayoutCode_closedHandoffCompiledSubroutine

end Computability
end FoC

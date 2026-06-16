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

theorem tape_normalizedOutput_move_right_input
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

theorem tape_move_left_move_right_input_encodeCodeWordAsInput_cons
    (symbol : MachineCodeSymbol) (code : Word MachineCodeSymbol) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (Tape.input
            (MachineDescription.encodeCodeWordAsInput (symbol :: code)))) =
      Tape.input
        (MachineDescription.encodeCodeWordAsInput (symbol :: code)) := by
  cases symbol <;> rfl

theorem tapeCodePrimitiveCodeWord_handoff_tape
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

theorem haltsWithTape_functional_of_haltTransitionFree
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

theorem encodeConfigurationAppend_initial
    (D : MachineDescription) (w : Word Bool)
    (suffix : Word MachineCodeSymbol) :
    MachineDescription.encodeConfigurationAppend (D.initial w) suffix =
      MachineDescription.encodeNatAppend D.start
        (MachineDescription.encodeTapeAppend (Tape.input w) suffix) := by
  rfl

theorem dovetailInitialLayoutCode_output_eq_transition_cons
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

theorem tapeCodePrimitiveClosedHandoffCompiled_of_halt_tape_move_right
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

def tapeAtCells
    (leftRev cells : List (Option Bool)) : Tape Bool :=
  match cells with
  | [] => { left := leftRev, head := none, right := [] }
  | cell :: rest => { left := leftRev, head := cell, right := rest }

def config
    (state : Nat) (leftRev cells : List (Option Bool)) :
    MachineDescription.Configuration :=
  { state := state, tape := tapeAtCells leftRev cells }

def codeCells
    (code : Word MachineCodeSymbol) : List (Option Bool) :=
  (MachineDescription.encodeCodeWordAsInput code).map some

def stageInputCells
    (w : Word Bool) (stage : Nat) : List (Option Bool) :=
  codeCells (PairedRecognizerDovetailStageInputCode w stage)

def suffixCells
    (accept reject : MachineDescription)
    (w : Word Bool) : List (Option Bool) :=
  codeCells
    (SuffixCode accept reject w)

def outputCells
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) : List (Option Bool) :=
  codeCells
    (OutputCode accept reject w stage)

theorem map_some_append
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

theorem codeCells_append
    (pre suffix : Word MachineCodeSymbol) :
    codeCells (List.append pre suffix) =
      List.append (codeCells pre) (codeCells suffix) := by
  unfold codeCells
  rw [MachineDescription.encodeCodeWordAsInput_append]
  exact map_some_append
    (MachineDescription.encodeCodeWordAsInput pre)
    (MachineDescription.encodeCodeWordAsInput suffix)

def codeSymbolCells
    (symbol : MachineCodeSymbol) : List (Option Bool) :=
  (MachineDescription.encodeCodeSymbolAsInput symbol).map some

def natCodeCells : Nat -> List (Option Bool)
  | 0 => codeSymbolCells MachineCodeSymbol.done
  | n + 1 =>
      List.append
        (codeSymbolCells MachineCodeSymbol.tick)
        (natCodeCells n)

def cellCodeCells :
    Option Bool -> List (Option Bool)
  | none => codeSymbolCells MachineCodeSymbol.blank
  | some false => codeSymbolCells MachineCodeSymbol.zero
  | some true => codeSymbolCells MachineCodeSymbol.one

def cellsCodeCells :
    List (Option Bool) -> List (Option Bool)
  | [] => []
  | cell :: rest =>
      List.append (cellCodeCells cell)
        (cellsCodeCells rest)

def boolPayloadCells
    (w : Word Bool) : List (Option Bool) :=
  cellsCodeCells (w.map some)

def boolWordCells
    (w : Word Bool) : List (Option Bool) :=
  List.append (natCodeCells w.length)
    (boolPayloadCells w)

def markedLengthTickCells : List (Option Bool) :=
  [none, some false, some true, some false]

def consumedLengthTickCells : List (Option Bool) :=
  [some false, none, some true, some false]

def markedCellCodeCells :
    Option Bool -> List (Option Bool)
  | none => cellCodeCells none
  | some false => [none, some true, some false, some true]
  | some true => [none, some true, some true, some false]

def repeatedCells
    (chunk : List (Option Bool)) : Nat -> List (Option Bool)
  | 0 => []
  | n + 1 => List.append chunk (repeatedCells chunk n)

def markedLengthTickPrefix (n : Nat) :
    List (Option Bool) :=
  repeatedCells markedLengthTickCells n

def consumedLengthTickPrefix (n : Nat) :
    List (Option Bool) :=
  repeatedCells consumedLengthTickCells n

def markedCellsCodeCells :
    List (Option Bool) -> List (Option Bool)
  | [] => []
  | cell :: rest =>
      List.append (markedCellCodeCells cell)
        (markedCellsCodeCells rest)

def markedBoolPayloadCells
    (w : Word Bool) : List (Option Bool) :=
  markedCellsCodeCells (w.map some)

def markedBoolWordCells
    (w : Word Bool) : List (Option Bool) :=
  List.append (markedLengthTickPrefix w.length)
    (List.append (codeSymbolCells MachineCodeSymbol.done)
      (markedBoolPayloadCells w))

def consumedBoolWordCells
    (w : Word Bool) : List (Option Bool) :=
  List.append (consumedLengthTickPrefix w.length)
    (List.append (codeSymbolCells MachineCodeSymbol.done)
      (markedBoolPayloadCells w))

theorem repeatedCells_append
    (chunk : List (Option Bool)) (n : Nat)
    (tail : List (Option Bool)) :
    List.append (repeatedCells chunk n) tail =
      match n with
      | 0 => tail
      | k + 1 =>
          List.append chunk
            (List.append (repeatedCells chunk k) tail) := by
  cases n <;> simp [repeatedCells, List.append_assoc]

theorem repeatedCells_succ_right
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

theorem repeatedCells_length
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

theorem repeatedCells_reverse
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

theorem natCodeCells_eq_tick_prefix_done
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

theorem markedCellCodeCells_restore
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

theorem codeCells_replicate_tick
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

theorem cellsCodeCells_append
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

@[simp] theorem boolPayloadCells_append
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

theorem markedCellsCodeCells_append
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

@[simp] theorem markedBoolPayloadCells_append
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

@[simp] theorem markedBoolPayloadCells_append_false
    (marked : Word Bool) :
    markedBoolPayloadCells (List.append marked [false]) =
      List.append (markedBoolPayloadCells marked)
        (markedCellCodeCells (some false)) := by
  simpa [markedBoolPayloadCells,
    markedCellsCodeCells] using
    markedBoolPayloadCells_append marked ([false] : Word Bool)

@[simp] theorem markedBoolPayloadCells_append_true
    (marked : Word Bool) :
    markedBoolPayloadCells (List.append marked [true]) =
      List.append (markedBoolPayloadCells marked)
        (markedCellCodeCells (some true)) := by
  simpa [markedBoolPayloadCells,
    markedCellsCodeCells] using
    markedBoolPayloadCells_append marked ([true] : Word Bool)

end DovetailInitialLayoutInitializer
end Computability
end FoC

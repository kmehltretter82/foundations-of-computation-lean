import FoC.Computability.Compiler.Core.FiniteRecognizer.Basic

set_option doc.verso true

/-!
# Generated-code API for finite recognizers

Stable builder names and parser facts for unary generated calls.  This module
is independent of the Universal/Ranges public wrappers, so the core finite
recognizer programming layer can use the generated-code convention directly.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace GeneratedCode

/-- Builder for a generated call with one unary natural field. -/
def stageCode
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend fuel input

/-- Builder for a generated nested call with inner and outer unary fields. -/
def nestedStageCode
    (input : Word MachineCodeSymbol) (inner outer : Nat) :
    Word MachineCodeSymbol :=
  stageCode (stageCode input inner) outer

theorem stageCode_eq_encodeNatAppend
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    stageCode input fuel =
      MachineDescription.encodeNatAppend fuel input := by
  rfl

theorem stageCode_decodeNat
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    MachineDescription.decodeNat (stageCode input fuel) =
      some (fuel, input) := by
  exact MachineDescription.decodeNat_encodeNatAppend fuel input

theorem stageCode_eq_of_decodeNat
    {tokens input : Word MachineCodeSymbol} {fuel : Nat}
    (h : MachineDescription.decodeNat tokens = some (fuel, input)) :
    tokens = stageCode input fuel := by
  exact MachineDescription.decodeNat_eq_some_encodeNatAppend h

theorem stageCode_decodeNat_eq_some_iff
    {tokens input : Word MachineCodeSymbol} {fuel : Nat} :
    MachineDescription.decodeNat tokens = some (fuel, input) <->
      tokens = stageCode input fuel := by
  constructor
  · exact stageCode_eq_of_decodeNat
  · intro h
    rw [h]
    exact stageCode_decodeNat input fuel

theorem stageCode_input_cells
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    Tape.cells (Tape.input (stageCode input fuel)) =
      match fuel with
      | 0 => some MachineCodeSymbol.done :: input.map some
      | fuel + 1 =>
          some MachineCodeSymbol.tick ::
            (stageCode input fuel).map some := by
  cases fuel <;>
    rfl

theorem stageCode_input_read
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    Tape.read (Tape.input (stageCode input fuel)) =
      match fuel with
      | 0 => some MachineCodeSymbol.done
      | _ + 1 => some MachineCodeSymbol.tick := by
  cases fuel <;>
    rfl

theorem stageCode_input_normalizedOutput
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    Tape.normalizedOutput (Tape.input (stageCode input fuel)) =
      stageCode input fuel := by
  simpa [Tape.output] using
    Tape.normalizedOutput_output (stageCode input fuel)

theorem stageCode_injective
    {input1 input2 : Word MachineCodeSymbol}
    {fuel1 fuel2 : Nat}
    (h : stageCode input1 fuel1 = stageCode input2 fuel2) :
    fuel1 = fuel2 /\ input1 = input2 := by
  have hdecode := congrArg MachineDescription.decodeNat h
  simp [stageCode, MachineDescription.decodeNat_encodeNatAppend]
    at hdecode
  exact ⟨hdecode.left, hdecode.right⟩

theorem stageCode_eq_iff
    {input1 input2 : Word MachineCodeSymbol}
    {fuel1 fuel2 : Nat} :
    stageCode input1 fuel1 = stageCode input2 fuel2 <->
      fuel1 = fuel2 /\ input1 = input2 := by
  constructor
  · exact stageCode_injective
  · intro h
    rcases h with ⟨hfuel, hinput⟩
    subst fuel2
    subst input2
    rfl

theorem nestedStageCode_eq
    (input : Word MachineCodeSymbol) (inner outer : Nat) :
    nestedStageCode input inner outer =
      stageCode (stageCode input inner) outer := by
  rfl

theorem nestedStageCode_decodeNat_outer
    (input : Word MachineCodeSymbol) (inner outer : Nat) :
    MachineDescription.decodeNat
        (nestedStageCode input inner outer) =
      some (outer, stageCode input inner) := by
  exact stageCode_decodeNat (stageCode input inner) outer

theorem nestedStageCode_decodeNat_inner
    (input : Word MachineCodeSymbol) (inner : Nat) :
    MachineDescription.decodeNat (stageCode input inner) =
      some (inner, input) :=
  stageCode_decodeNat input inner

theorem nestedStageCode_input_cells
    (input : Word MachineCodeSymbol) (inner outer : Nat) :
    Tape.cells
        (Tape.input (nestedStageCode input inner outer)) =
      match outer with
      | 0 =>
          some MachineCodeSymbol.done ::
            (stageCode input inner).map some
      | outer + 1 =>
          some MachineCodeSymbol.tick ::
            (nestedStageCode input inner outer).map some := by
  cases outer <;>
    rfl

theorem nestedStageCode_input_read
    (input : Word MachineCodeSymbol) (inner outer : Nat) :
    Tape.read
        (Tape.input (nestedStageCode input inner outer)) =
      match outer with
      | 0 => some MachineCodeSymbol.done
      | _ + 1 => some MachineCodeSymbol.tick := by
  cases outer <;>
    rfl

theorem nestedStageCode_input_normalizedOutput
    (input : Word MachineCodeSymbol) (inner outer : Nat) :
    Tape.normalizedOutput
        (Tape.input (nestedStageCode input inner outer)) =
      nestedStageCode input inner outer := by
  simpa [Tape.output] using
    Tape.normalizedOutput_output
      (nestedStageCode input inner outer)

theorem nestedStageCode_eq_of_decodeNat_outer_inner
    {tokens innerCode input : Word MachineCodeSymbol}
    {inner outer : Nat}
    (houter :
      MachineDescription.decodeNat tokens =
        some (outer, innerCode))
    (hinner :
      MachineDescription.decodeNat innerCode =
        some (inner, input)) :
    tokens = nestedStageCode input inner outer := by
  have htokens : tokens = stageCode innerCode outer :=
    stageCode_eq_of_decodeNat houter
  have hinnerCode : innerCode = stageCode input inner :=
    stageCode_eq_of_decodeNat hinner
  rw [htokens, hinnerCode]
  rfl

theorem nestedStageCode_decodeNat_outer_eq_some_iff
    {tokens input : Word MachineCodeSymbol}
    {inner outer : Nat} :
    MachineDescription.decodeNat tokens =
        some (outer, stageCode input inner) <->
      tokens = nestedStageCode input inner outer := by
  constructor
  · intro h
    exact
      nestedStageCode_eq_of_decodeNat_outer_inner h
        (nestedStageCode_decodeNat_inner input inner)
  · intro h
    rw [h]
    exact nestedStageCode_decodeNat_outer input inner outer

theorem nestedStageCode_decodeNat_pair_iff
    {tokens input : Word MachineCodeSymbol}
    {inner outer : Nat} :
    (exists innerCode : Word MachineCodeSymbol,
      MachineDescription.decodeNat tokens =
          some (outer, innerCode) /\
        MachineDescription.decodeNat innerCode =
          some (inner, input)) <->
      tokens = nestedStageCode input inner outer := by
  constructor
  · intro h
    rcases h with ⟨innerCode, houter, hinner⟩
    exact
      nestedStageCode_eq_of_decodeNat_outer_inner houter hinner
  · intro h
    subst tokens
    exact
      ⟨stageCode input inner,
        nestedStageCode_decodeNat_outer input inner outer,
        nestedStageCode_decodeNat_inner input inner⟩

theorem nestedStageCode_injective
    {input1 input2 : Word MachineCodeSymbol}
    {inner1 inner2 outer1 outer2 : Nat}
    (h :
      nestedStageCode input1 inner1 outer1 =
        nestedStageCode input2 inner2 outer2) :
    outer1 = outer2 /\ inner1 = inner2 /\ input1 = input2 := by
  rcases stageCode_injective h with ⟨houter, hinnerCode⟩
  rcases stageCode_injective hinnerCode with ⟨hinner, hinput⟩
  exact ⟨houter, hinner, hinput⟩

theorem nestedStageCode_eq_iff
    {input1 input2 : Word MachineCodeSymbol}
    {inner1 inner2 outer1 outer2 : Nat} :
    nestedStageCode input1 inner1 outer1 =
        nestedStageCode input2 inner2 outer2 <->
      outer1 = outer2 /\ inner1 = inner2 /\ input1 = input2 := by
  constructor
  · exact nestedStageCode_injective
  · intro h
    rcases h with ⟨houter, hinner, hinput⟩
    subst outer2
    subst inner2
    subst input2
    rfl

theorem exactFuelRunnerSpec_codePrefix
    {runnerState selectedState : Type}
    {runner : TuringMachine MachineCodeSymbol runnerState}
    {selected : TuringMachine MachineCodeSymbol selectedState} :
    ExactFuelRunnerSpec runner selected stageCode =
      (forall input : Word MachineCodeSymbol,
       forall fuel : Nat,
        TuringMachine.HaltsOnInput runner (stageCode input fuel) <->
          TuringMachine.HaltsOnInputIn selected fuel input) := by
  rfl

theorem generatedCallParserSpec_codePrefix
    {runnerState selectedState : Type}
    {runner : TuringMachine MachineCodeSymbol runnerState}
    {selected : TuringMachine MachineCodeSymbol selectedState} :
    GeneratedCallParserSpec runner selected stageCode =
      (forall tokens : Word MachineCodeSymbol,
        TuringMachine.HaltsOnInput runner tokens <->
          exists input : Word MachineCodeSymbol,
          exists fuel : Nat,
            tokens = stageCode input fuel /\
              TuringMachine.HaltsOnInput selected
                (stageCode input fuel)) := by
  rfl

theorem nestedPairEnumeratorSpec_codePrefix
    {searcherState selectedState : Type}
    {searcher : TuringMachine MachineCodeSymbol searcherState}
    {selected : TuringMachine MachineCodeSymbol selectedState} :
    NestedPairEnumeratorSpec searcher selected nestedStageCode =
      (forall input : Word MachineCodeSymbol,
        TuringMachine.HaltsOnInput searcher input <->
          exists inner : Nat,
          exists outer : Nat,
            TuringMachine.HaltsOnInput selected
              (nestedStageCode input inner outer)) := by
  rfl

theorem boundedNestedPairEnumeratorSpec_codePrefix
    {searcherState selectedState : Type}
    {searcher : TuringMachine MachineCodeSymbol searcherState}
    {selected : TuringMachine MachineCodeSymbol selectedState} :
    BoundedNestedPairEnumeratorSpec
        searcher selected stageCode nestedStageCode =
      (forall input : Word MachineCodeSymbol,
       forall budget : Nat,
        TuringMachine.HaltsOnInput searcher (stageCode input budget) <->
          exists inner : Nat,
          exists outer : Nat,
            inner <= budget /\
              outer <= budget /\
              TuringMachine.HaltsOnInput selected
                (nestedStageCode input inner outer)) := by
  rfl

theorem productExactFuelRunnerSpec_codePrefix
    {selectedState leftState rightState : Type}
    {selected : TuringMachine MachineCodeSymbol selectedState}
    {left : TuringMachine MachineCodeSymbol leftState}
    {right : TuringMachine MachineCodeSymbol rightState} :
    ProductExactFuelRunnerSpec selected left right nestedStageCode =
      (forall input : Word MachineCodeSymbol,
       forall leftFuel : Nat,
       forall rightFuel : Nat,
        TuringMachine.HaltsOnInput selected
            (nestedStageCode input rightFuel leftFuel) <->
          TuringMachine.HaltsOnInputIn left leftFuel input /\
            TuringMachine.HaltsOnInputIn right rightFuel input) := by
  rfl

theorem decodedDescriptionInterpreterSpec_codePrefix
    {runnerState : Type}
    {runner : TuringMachine MachineCodeSymbol runnerState} :
    DecodedDescriptionInterpreterSpec runner stageCode =
      (forall encoded : Word MachineCodeSymbol,
       forall input : Word MachineCodeSymbol,
       forall D : MachineDescription,
       forall fuel : Nat,
        MachineDescription.decodeDescriptionPrefix encoded =
            some (D, input) ->
          (TuringMachine.HaltsOnInput runner (stageCode encoded fuel) <->
            D.HaltsIn fuel
              (MachineDescription.encodeCodeWordAsInput input))) := by
  rfl

end GeneratedCode
end FiniteRecognizer

end Computability
end FoC

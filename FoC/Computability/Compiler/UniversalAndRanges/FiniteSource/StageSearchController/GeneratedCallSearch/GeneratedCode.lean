import FoC.Computability.Compiler.Core.FiniteRecognizer
import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.StageSearchController.GeneratedCallSearch.Basic

set_option doc.verso true

/-!
# Generated-code API for generated-call search

Stable builder names and parser facts for generated code-prefix calls.  These
facts are wrappers over the existing raw shape lemmas, so later exact-fuel,
product, and enumerator constructions can target one small API.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace GeneratedCode

/-- Builder for a generated code-prefix call with one unary fuel field. -/
def stageCode
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    Word MachineCodeSymbol :=
  CodePrefixRecognizerStageCode input fuel

/-- Builder for a generated nested call with inner and outer unary fields. -/
def nestedStageCode
    (input : Word MachineCodeSymbol) (inner outer : Nat) :
    Word MachineCodeSymbol :=
  NestedCodePrefixRecognizerStageCode input inner outer

theorem stageCode_eq
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    stageCode input fuel = CodePrefixRecognizerStageCode input fuel := by
  rfl

theorem stageCode_decodeNat
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    MachineDescription.decodeNat (stageCode input fuel) =
      some (fuel, input) := by
  simpa [stageCode] using
    codePrefixRecognizerStageCode_decodeNat input fuel

theorem stageCode_decodeNat_eq_some_iff
    {tokens input : Word MachineCodeSymbol} {fuel : Nat} :
    MachineDescription.decodeNat tokens = some (fuel, input) <->
      tokens = stageCode input fuel := by
  constructor
  · intro h
    simpa [stageCode] using
      codePrefixRecognizerStageCode_eq_of_decodeNat h
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
  simpa [stageCode] using
    codePrefixRecognizerStageCode_input_normalizedOutput input fuel

theorem stageCode_injective
    {input1 input2 : Word MachineCodeSymbol}
    {fuel1 fuel2 : Nat}
    (h : stageCode input1 fuel1 = stageCode input2 fuel2) :
    fuel1 = fuel2 /\ input1 = input2 := by
  simpa [stageCode] using
    codePrefixRecognizerStageCode_injective h

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
  simpa [nestedStageCode, stageCode] using
    nestedCodePrefixRecognizerStageCode_decodeNat_outer
      input inner outer

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
  simpa [nestedStageCode] using
    nestedCodePrefixRecognizerStageCode_input_normalizedOutput
      input inner outer

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
  simpa [nestedStageCode] using
    nestedCodePrefixRecognizerStageCode_eq_of_decodeNat_outer_inner
      houter hinner

theorem nestedStageCode_decodeNat_outer_eq_some_iff
    {tokens input : Word MachineCodeSymbol}
    {inner outer : Nat} :
    MachineDescription.decodeNat tokens =
        some (outer, stageCode input inner) <->
      tokens = nestedStageCode input inner outer := by
  simpa [nestedStageCode, stageCode] using
    nestedCodePrefixRecognizerStageCode_decodeNat_outer_eq_some_iff
      (tokens := tokens) (input := input) (inner := inner) (outer := outer)

theorem nestedStageCode_decodeNat_pair_iff
    {tokens input : Word MachineCodeSymbol}
    {inner outer : Nat} :
    (exists innerCode : Word MachineCodeSymbol,
      MachineDescription.decodeNat tokens =
          some (outer, innerCode) /\
        MachineDescription.decodeNat innerCode =
          some (inner, input)) <->
      tokens = nestedStageCode input inner outer := by
  simpa [nestedStageCode] using
    nestedCodePrefixRecognizerStageCode_decodeNat_pair_iff
      (tokens := tokens) (input := input) (inner := inner) (outer := outer)

theorem nestedStageCode_injective
    {input1 input2 : Word MachineCodeSymbol}
    {inner1 inner2 outer1 outer2 : Nat}
    (h :
      nestedStageCode input1 inner1 outer1 =
        nestedStageCode input2 inner2 outer2) :
    outer1 = outer2 /\ inner1 = inner2 /\ input1 = input2 := by
  simpa [nestedStageCode] using
    nestedCodePrefixRecognizerStageCode_injective h

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
          TuringMachine.HaltsOnInput runner (stageCode encoded fuel) <->
            D.HaltsIn fuel
              (MachineDescription.encodeCodeWordAsInput input)) := by
  rfl

end GeneratedCode
end FiniteRecognizer

end Computability
end FoC

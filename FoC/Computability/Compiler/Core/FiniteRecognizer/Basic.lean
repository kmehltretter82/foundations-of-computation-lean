import FoC.Computability.Encoding

set_option doc.verso true

/-!
# Finite recognizer programming contracts

This module provides dependency-light semantic contracts for the finite
recognizer programming layer.  The contracts are intentionally generic in the
input builder, so concrete generated-code parsers can expose stable names
without making the compiler core depend on Universal/Ranges modules.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer

universe uSymbol uState uRunner uSelected uLeft uRight

/-- A recognizer halts exactly on the words satisfying {lean}`P`. -/
def Recognizes
    {symbol : Type uSymbol} {state : Type uState}
    (recognizer : TuringMachine symbol state)
    (P : Word symbol -> Prop) : Prop :=
  forall input : Word symbol,
    TuringMachine.HaltsOnInput recognizer input <-> P input

/--
A recognizer halts exactly on the generated inputs satisfying an indexed
predicate.  The {lean}`build` argument is the code generator used by a concrete
finite programming layer.
-/
def RecognizesOn
    {symbol : Type uSymbol} {index : Type uState}
    {state : Type uRunner}
    (recognizer : TuringMachine symbol state)
    (build : index -> Word symbol)
    (P : index -> Prop) : Prop :=
  forall i : index,
    TuringMachine.HaltsOnInput recognizer (build i) <-> P i

/--
Exact-fuel semantics for a generated call.  A runner receives a generated
input built from the public input word and a fuel value, and halts exactly when
the selected machine halts in that many steps.
-/
def ExactFuelRunnerSpec
    {symbol : Type uSymbol}
    {runnerState : Type uRunner} {selectedState : Type uSelected}
    (runner : TuringMachine symbol runnerState)
    (selected : TuringMachine symbol selectedState)
    (build : Word symbol -> Nat -> Word symbol) : Prop :=
  forall input : Word symbol,
  forall fuel : Nat,
    TuringMachine.HaltsOnInput runner (build input fuel) <->
      TuringMachine.HaltsOnInputIn selected fuel input

/--
Parser semantics for generated calls when the wrapped recognizer is still an
ordinary halting recognizer rather than an exact-fuel simulator.
-/
def GeneratedCallParserSpec
    {symbol : Type uSymbol}
    {runnerState : Type uRunner} {selectedState : Type uSelected}
    (runner : TuringMachine symbol runnerState)
    (selected : TuringMachine symbol selectedState)
    (build : Word symbol -> Nat -> Word symbol) : Prop :=
  forall tokens : Word symbol,
    TuringMachine.HaltsOnInput runner tokens <->
      exists input : Word symbol,
      exists fuel : Nat,
        tokens = build input fuel /\
          TuringMachine.HaltsOnInput selected (build input fuel)

/--
Unbounded pair enumeration over generated nested calls.  The searcher runs on
the public input and halts exactly when the selected recognizer halts on some
nested generated call.
-/
def NestedPairEnumeratorSpec
    {symbol : Type uSymbol}
    {searcherState : Type uRunner} {selectedState : Type uSelected}
    (searcher : TuringMachine symbol searcherState)
    (selected : TuringMachine symbol selectedState)
    (build : Word symbol -> Nat -> Nat -> Word symbol) : Prop :=
  forall input : Word symbol,
    TuringMachine.HaltsOnInput searcher input <->
      exists inner : Nat,
      exists outer : Nat,
        TuringMachine.HaltsOnInput selected (build input inner outer)

/--
Bounded pair enumeration over generated nested calls.  The budget is provided
by a generated outer input, while both enumerated parameters are bounded by
that budget.
-/
def BoundedNestedPairEnumeratorSpec
    {symbol : Type uSymbol}
    {searcherState : Type uRunner} {selectedState : Type uSelected}
    (searcher : TuringMachine symbol searcherState)
    (selected : TuringMachine symbol selectedState)
    (outerBuild : Word symbol -> Nat -> Word symbol)
    (nestedBuild : Word symbol -> Nat -> Nat -> Word symbol) : Prop :=
  forall input : Word symbol,
  forall budget : Nat,
    TuringMachine.HaltsOnInput searcher (outerBuild input budget) <->
      exists inner : Nat,
      exists outer : Nat,
        inner <= budget /\
          outer <= budget /\
          TuringMachine.HaltsOnInput selected
            (nestedBuild input inner outer)

/--
Product exact-fuel semantics for recognizer intersection.  The generated
nested call carries one fuel for each recognizer.
-/
def ProductExactFuelRunnerSpec
    {symbol : Type uSymbol}
    {selectedState : Type uRunner}
    {leftState : Type uLeft} {rightState : Type uRight}
    (selected : TuringMachine symbol selectedState)
    (left : TuringMachine symbol leftState)
    (right : TuringMachine symbol rightState)
    (build : Word symbol -> Nat -> Nat -> Word symbol) : Prop :=
  forall input : Word symbol,
  forall leftFuel : Nat,
  forall rightFuel : Nat,
    TuringMachine.HaltsOnInput selected
        (build input rightFuel leftFuel) <->
      TuringMachine.HaltsOnInputIn left leftFuel input /\
        TuringMachine.HaltsOnInputIn right rightFuel input

/--
Uniform decoded-description interpreter semantics.  The runner receives a
generated code-prefix input and halts exactly when the decoded description
halts within the generated fuel.
-/
def DecodedDescriptionInterpreterSpec
    {runnerState : Type uRunner}
    (runner : TuringMachine MachineCodeSymbol runnerState)
    (build : Word MachineCodeSymbol -> Nat -> Word MachineCodeSymbol) :
    Prop :=
  forall encoded : Word MachineCodeSymbol,
  forall input : Word MachineCodeSymbol,
  forall D : MachineDescription,
  forall fuel : Nat,
    MachineDescription.decodeDescriptionPrefix encoded =
        some (D, input) ->
      TuringMachine.HaltsOnInput runner (build encoded fuel) <->
        D.HaltsIn fuel
          (MachineDescription.encodeCodeWordAsInput input)

/--
Total-token decoded-description interpreter semantics.  Unlike
{name}`DecodedDescriptionInterpreterSpec`, this contract specifies rejection
for malformed inputs by quantifying over every source token word.
-/
def DecodedDescriptionInterpreterTotalSpec
    {runnerState : Type uRunner}
    (runner : TuringMachine MachineCodeSymbol runnerState) : Prop :=
  forall tokens : Word MachineCodeSymbol,
    TuringMachine.HaltsOnInput runner tokens <->
      exists fuel : Nat,
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeNat tokens =
            some (fuel,
              List.append (MachineDescription.encodeDescription D) input) ∧
          D.HaltsIn fuel
            (MachineDescription.encodeCodeWordAsInput input)

/--
Ordinary halting is existential exact-fuel halting.  This is the semantic
bridge used by unbounded generated searches.
-/
theorem haltsOnInput_iff_exists_exactFuel
    {symbol : Type uSymbol} {state : Type uState}
    (M : TuringMachine symbol state) (input : Word symbol) :
    TuringMachine.HaltsOnInput M input <->
      exists fuel : Nat,
        TuringMachine.HaltsOnInputIn M fuel input :=
  TuringMachine.halts_on_input_iff_exists_halts_on_input_in M input

end FiniteRecognizer

end Computability
end FoC

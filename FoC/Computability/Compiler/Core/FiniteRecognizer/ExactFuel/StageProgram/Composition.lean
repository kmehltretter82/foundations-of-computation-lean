import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StageProgram.Spec

set_option doc.verso true

/-!
# Stage-program exact-output contracts

Contracts relating partial code-word transformers to exact output tapes, plus
the empty-output halting bridge used by finite-recognizer consumers.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StageProgram

universe uProducer

/--
Exact-output contract for a partial transformer. Unlike normalized-output
observations, this records the producer's concrete {name}`Tape.output` endpoint.
-/
def ExactOutputSpec
    (machine : TuringMachine MachineCodeSymbol producerState)
    (f : Word MachineCodeSymbol -> Option (Word MachineCodeSymbol)) :
    Prop :=
  forall input output : Word MachineCodeSymbol,
    TuringMachine.HaltsWithExactOutput machine input output <->
      f input = some output

/--
Every halted producer final tape is a canonical exact output governed by the
same partial transformer.  This side condition is needed for sequencing:
{name}`ExactOutputSpec` alone only characterizes already-canonical output
tapes, and an arbitrary producer could otherwise halt on a non-output-shaped
tape.
-/
def ExactOutputCanonicalSpec
    (machine : TuringMachine MachineCodeSymbol producerState)
    (f : Word MachineCodeSymbol -> Option (Word MachineCodeSymbol)) :
    Prop :=
  forall input : Word MachineCodeSymbol,
  forall final : TuringMachine.Configuration MachineCodeSymbol producerState,
    TuringMachine.Computes machine (TuringMachine.initial machine input)
      final ->
    TuringMachine.Halted machine final ->
      exists output : Word MachineCodeSymbol,
        f input = some output /\ final.tape = Tape.output output

theorem haltsOnInput_iff_some_empty_of_exactOutput
    {machine : TuringMachine MachineCodeSymbol producerState}
    {f : Word MachineCodeSymbol -> Option (Word MachineCodeSymbol)}
    (hexact : ExactOutputSpec machine f)
    (hcanonical : ExactOutputCanonicalSpec machine f)
    (hempty :
      forall {input output : Word MachineCodeSymbol},
        f input = some output -> output = ([] : Word MachineCodeSymbol))
    (input : Word MachineCodeSymbol) :
    TuringMachine.HaltsOnInput machine input <->
      f input = some ([] : Word MachineCodeSymbol) := by
  constructor
  · intro hhalt
    rcases hhalt with ⟨final, hcomp, hfinalHalt⟩
    rcases hcanonical input final hcomp hfinalHalt with
      ⟨output, houtput, _htape⟩
    have houtputEmpty : output = ([] : Word MachineCodeSymbol) :=
      hempty houtput
    subst output
    exact houtput
  · intro houtput
    rcases (hexact input ([] : Word MachineCodeSymbol)).mpr houtput with
      ⟨final, hcomp, hfinalHalt, _htape⟩
    exact ⟨final, hcomp, hfinalHalt⟩

end StageProgram
end ExactFuel
end FiniteRecognizer

end Computability
end FoC

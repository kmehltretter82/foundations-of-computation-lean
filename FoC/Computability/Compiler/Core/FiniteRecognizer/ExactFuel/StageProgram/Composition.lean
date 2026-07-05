import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StageProgram.Spec

set_option doc.verso true

/-!
# Stage-program composition contracts

Contract layer for composing an output-producing finite machine with a
recognizer.  The exact-fuel stage-program construction will use this to keep
raw generated-code parsing and protected-layout recognition separate.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StageProgram

universe uProducer uRecognizer uPipeline

/-- A machine realizes a partial output transformer on code words. -/
def OutputSpec
    (machine : TuringMachine MachineCodeSymbol producerState)
    (f : Word MachineCodeSymbol -> Option (Word MachineCodeSymbol)) :
    Prop :=
  forall input output : Word MachineCodeSymbol,
    TuringMachine.HaltsWithOutput machine input output <->
      f input = some output

/--
A pipeline first applies a partial output transformer and then recognizes the
produced word with predicate {lean}`P`.
-/
def OutputThenRecognizeSpec
    (pipeline : TuringMachine MachineCodeSymbol pipelineState)
    (producer : Word MachineCodeSymbol -> Option (Word MachineCodeSymbol))
    (P : Word MachineCodeSymbol -> Prop) : Prop :=
  forall input : Word MachineCodeSymbol,
    TuringMachine.HaltsOnInput pipeline input <->
      exists output : Word MachineCodeSymbol,
        producer input = some output /\ P output

/--
Finite-machine construction boundary for output-then-recognize composition.
This is intentionally a contract, not a semantic shortcut: a later construction
must provide the concrete sequencing machine.
-/
def OutputThenRecognizeConstruction : Prop :=
  forall {producerState recognizerState : Type}
    (producer : TuringMachine MachineCodeSymbol producerState)
    (recognizer : TuringMachine MachineCodeSymbol recognizerState)
    (f : Word MachineCodeSymbol -> Option (Word MachineCodeSymbol))
    (P : Word MachineCodeSymbol -> Prop),
      OutputSpec producer f ->
      FiniteRecognizer.Recognizes recognizer P ->
        exists pipelineState : Type,
        exists pipeline : TuringMachine MachineCodeSymbol pipelineState,
          OutputThenRecognizeSpec pipeline f P

theorem outputThenRecognizeConstructionFiniteLeaf :
    OutputThenRecognizeConstruction := by
  sorry

theorem outputThenRecognizeSpec_of_recognizer
    {pipelineState recognizerState : Type}
    {pipeline : TuringMachine MachineCodeSymbol pipelineState}
    {recognizer : TuringMachine MachineCodeSymbol recognizerState}
    {producer : Word MachineCodeSymbol -> Option (Word MachineCodeSymbol)}
    {P : Word MachineCodeSymbol -> Prop}
    (hpipeline : OutputThenRecognizeSpec pipeline producer P)
    (hrecognizer : FiniteRecognizer.Recognizes recognizer P) :
    forall input : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput pipeline input <->
        exists output : Word MachineCodeSymbol,
          producer input = some output /\
            TuringMachine.HaltsOnInput recognizer output := by
  intro input
  rw [hpipeline input]
  constructor
  · intro h
    rcases h with ⟨output, hproducer, hP⟩
    exact ⟨output, hproducer, (hrecognizer output).mpr hP⟩
  · intro h
    rcases h with ⟨output, hproducer, hhalt⟩
    exact ⟨output, hproducer, (hrecognizer output).mp hhalt⟩

end StageProgram
end ExactFuel
end FiniteRecognizer

end Computability
end FoC

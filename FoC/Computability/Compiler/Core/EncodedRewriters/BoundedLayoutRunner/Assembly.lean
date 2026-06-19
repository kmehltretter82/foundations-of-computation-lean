import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.Emitter

set_option doc.verso true

/-!
# Bounded-layout runner assembly

The assembly leaf sequences the parser, configuration runner, and emitter
phases into the public
{name (full := FoC.Computability.EncodedRewriters.BoundedLayoutRunner.Spec)}`Spec`
for
{name (full := FoC.Computability.PairedRecognizerDovetailLayoutCode)}`PairedRecognizerDovetailLayoutCode`.
-/

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters
namespace BoundedLayoutRunner

def PhaseAssemblyConstruction : Prop :=
  forall accept reject : MachineDescription,
    LayoutParserConstruction ->
      (exists configRunner : MachineDescription,
        AcceptRejectConfigRunnerSpec accept reject configRunner) ->
        (exists emitter : MachineDescription,
          OutputEmitterSpec accept reject emitter) ->
          exists runner : MachineDescription,
            Spec accept reject runner

theorem phaseAssemblyConstruction_scaffold :
    PhaseAssemblyConstruction := by
  intro accept reject hparser hconfig hem
  sorry

theorem finiteDescriptionConstruction_scaffold :
    FiniteDescriptionConstruction := by
  intro accept reject
  exact
    phaseAssemblyConstruction_scaffold
      accept reject
      layoutParserConstruction_scaffold
      (acceptRejectConfigRunnerConstruction_scaffold accept reject)
      (outputEmitterConstruction_scaffold accept reject)

theorem rightShiftedOutputCompiledConstruction_scaffold :
    RightShiftedOutputCompiledConstruction := by
  intro accept reject
  rcases finiteDescriptionConstruction_scaffold accept reject with
    ⟨runner, hrunner⟩
  exact
    ⟨runner,
      rightShiftedOutputCompiled_of_spec hrunner⟩

theorem closedHandoffCompiledSubroutine
    (accept reject : MachineDescription) :
    exists runner : MachineDescription,
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        (PairedRecognizerDovetailLayoutCode accept reject)
        runner tapeCodePrimitiveCodeWordHandoffMove := by
  rcases
      rightShiftedOutputCompiledConstruction_scaffold accept reject with
    ⟨runner, hrunner⟩
  refine ⟨runner, ?_⟩
  exact
    closedHandoffCompiled_of_rightShiftedOutputCompiled
      hrunner
      (by
        intro code out htransform
        rcases
            pairedRecognizerDovetailLayoutCode_transform_eq_some_cons
              htransform with
          ⟨tail, hout⟩
        exact ⟨MachineCodeSymbol.transition, tail, hout⟩)

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC

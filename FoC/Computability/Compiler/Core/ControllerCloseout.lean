import FoC.Computability.Compiler.Core.ConstructionTargets

set_option doc.verso true

/-!
# Dovetail controller closeouts
-/

namespace FoC
namespace Computability

open Languages

theorem pairedRecognizerDovetailTotalStageAttemptControllerSearchDriverCompiler_of_finiteStageLoopController
    (hloop :
      PairedRecognizerDovetailFiniteStageLoopControllerConstruction) :
    PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverCompilerConstruction :=
  fun _accept _reject attempt => hloop attempt

/-!
The finite controller route for paired-recognizer dovetailing has two
machine-construction pieces: a total stage-attempt subroutine and a controller
that loops over stage bounds, inspecting the subroutine's normalized output.
Packaging them together gives downstream closeouts a finite-source target
without appealing to an arbitrary staged-program compiler.
-/

structure PairedRecognizerDovetailControllerCompilerCloseout where
  totalStageAttemptSubroutine :
    PairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction
  controllerSearchDriver :
    PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverCompilerConstruction

structure PairedRecognizerDovetailFiniteControllerCompilerCloseout where
  totalStageAttemptSubroutine :
    PairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction
  finiteStageLoopController :
    PairedRecognizerDovetailFiniteStageLoopControllerConstruction

private def pairedRecognizerDovetailControllerCompilerCloseout_of_finiteStageLoopController
    (hattempt :
      PairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction)
    (hloop :
      PairedRecognizerDovetailFiniteStageLoopControllerConstruction) :
    PairedRecognizerDovetailControllerCompilerCloseout where
  totalStageAttemptSubroutine := hattempt
  controllerSearchDriver :=
    pairedRecognizerDovetailTotalStageAttemptControllerSearchDriverCompiler_of_finiteStageLoopController
      hloop

def pairedRecognizerDovetailControllerCompilerCloseout_of_finiteControllerCloseout
    (hclose : PairedRecognizerDovetailFiniteControllerCompilerCloseout) :
    PairedRecognizerDovetailControllerCompilerCloseout :=
  pairedRecognizerDovetailControllerCompilerCloseout_of_finiteStageLoopController
    hclose.totalStageAttemptSubroutine
    hclose.finiteStageLoopController

namespace PairedRecognizerDovetail

namespace TotalStageAttemptCodeOutputCompiledSubroutineConstruction

theorem of_outputFiniteSourceComponents
    (hinitializer :
      PairedRecognizerDovetailStageInputInitializerClosedHandoffCompiledSubroutineConstruction)
    (hrunner :
      PairedRecognizerDovetailBoundedLayoutRunnerSpecConstruction)
    (hemitter :
      PairedRecognizerDovetailTotalOutputEmitterOutputSubroutineRealizerConstruction)
    (hseq :
      PairedRecognizerDovetailTotalStageAttemptOutputSubroutineSequencingConstruction) :
    PairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction := by
  intro accept reject
  rcases hinitializer accept reject with
    ⟨initializer, hinitializer⟩
  rcases hrunner accept reject with ⟨runner, hrunner⟩
  change
    exists emitter : MachineDescription,
      TapeCodePrimitiveOutputSubroutineRealizedByDescription
        PairedRecognizerDovetailTotalOutputCode emitter at hemitter
  rcases hemitter with ⟨emitter, hemitter⟩
  rcases hseq accept reject initializer runner emitter
      hinitializer hrunner hemitter with
    ⟨attempt, hattempt⟩
  exact
    ⟨attempt,
      tapeCodePrimitiveOutputCompiledSubroutineByDescription_congr
        (pairedRecognizerDovetailTotalStageAttemptSourceCode_transform_eq
          accept reject)
        hattempt⟩

end TotalStageAttemptCodeOutputCompiledSubroutineConstruction

end PairedRecognizerDovetail

theorem pairedRecognizerDovetailStageInputInitializerCompiledSubroutineConstruction_of_closedHandoff
    (h :
      PairedRecognizerDovetailStageInputInitializerClosedHandoffCompiledSubroutineConstruction) :
    PairedRecognizerDovetailStageInputInitializerCompiledSubroutineConstruction :=
  fun accept reject =>
    Exists.elim (h accept reject) fun initializer hinitializer =>
      ⟨initializer,
      tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_outputCompiled
        hinitializer⟩

theorem pairedRecognizerDovetailFiniteStageLoopControllerConstruction_of_components
    (hinit :
      PairedRecognizerDovetailControllerInputInitializerConstruction)
    (hencoder :
      PairedRecognizerDovetailControllerStageInputEncoderConstruction)
    (hinvoke :
      PairedRecognizerDovetailStageAttemptInvocationConstruction)
    (hemit :
      PairedRecognizerDovetailControllerResultEmitterConstruction)
    (hcontinue :
      PairedRecognizerDovetailControllerContinueConstruction)
    (hseq :
      PairedRecognizerDovetailFiniteStageLoopSequencingConstruction) :
    PairedRecognizerDovetailFiniteStageLoopControllerConstruction := by
  intro attempt hattempt
  rcases hinit with ⟨initializer, hinitializer⟩
  rcases hencoder with ⟨encoder, hencoder⟩
  rcases hinvoke attempt encoder hattempt hencoder with
    ⟨invoker, hinvoker⟩
  rcases hemit with ⟨emitter, hemitter⟩
  rcases hcontinue with ⟨continuer, hcontinuer⟩
  exact hseq attempt initializer encoder invoker emitter continuer
    hattempt hinitializer hencoder hinvoker hemitter hcontinuer

end Computability
end FoC

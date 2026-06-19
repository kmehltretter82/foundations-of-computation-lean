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
    PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverCompilerConstruction := by
  intro _accept _reject attempt hattemptReady
  exact hloop attempt hattemptReady

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

def pairedRecognizerDovetailControllerCompilerCloseout_of_constructions
    (hattempt :
      PairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction)
    (hdriver :
      PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverCompilerConstruction) :
    PairedRecognizerDovetailControllerCompilerCloseout where
  totalStageAttemptSubroutine := hattempt
  controllerSearchDriver := hdriver

structure PairedRecognizerDovetailFiniteControllerCompilerCloseout where
  totalStageAttemptSubroutine :
    PairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction
  finiteStageLoopController :
    PairedRecognizerDovetailFiniteStageLoopControllerConstruction

def pairedRecognizerDovetailControllerCompilerCloseout_of_finiteStageLoopController
    (hattempt :
      PairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction)
    (hloop :
      PairedRecognizerDovetailFiniteStageLoopControllerConstruction) :
    PairedRecognizerDovetailControllerCompilerCloseout :=
  pairedRecognizerDovetailControllerCompilerCloseout_of_constructions
    hattempt
    (pairedRecognizerDovetailTotalStageAttemptControllerSearchDriverCompiler_of_finiteStageLoopController
      hloop)

def pairedRecognizerDovetailControllerCompilerCloseout_of_finiteControllerCloseout
    (hclose : PairedRecognizerDovetailFiniteControllerCompilerCloseout) :
    PairedRecognizerDovetailControllerCompilerCloseout :=
  pairedRecognizerDovetailControllerCompilerCloseout_of_finiteStageLoopController
    hclose.totalStageAttemptSubroutine
    hclose.finiteStageLoopController

theorem pairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction_of_finiteSourceComponents
    (hinitializer :
      PairedRecognizerDovetailStageInputInitializerClosedHandoffCompiledSubroutineConstruction)
    (hrunner :
      PairedRecognizerDovetailBoundedLayoutRunnerClosedHandoffCompiledSubroutineConstruction)
    (hemitter :
      PairedRecognizerDovetailTotalOutputEmitterOutputSubroutineRealizerConstruction)
    (hseq :
      PairedRecognizerDovetailTotalStageAttemptSubroutineSequencingConstruction) :
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

theorem pairedRecognizerDovetailStageInputInitializerHandoffCompiledSubroutineConstruction_of_closedHandoff
    (h :
      PairedRecognizerDovetailStageInputInitializerClosedHandoffCompiledSubroutineConstruction) :
    PairedRecognizerDovetailStageInputInitializerHandoffCompiledSubroutineConstruction := by
  intro accept reject
  rcases h accept reject with ⟨initializer, hinitializer⟩
  exact
    ⟨initializer,
      tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_handoffCompiled
        hinitializer⟩

theorem pairedRecognizerDovetailBoundedLayoutRunnerHandoffCompiledSubroutineConstruction_of_closedHandoff
    (h :
      PairedRecognizerDovetailBoundedLayoutRunnerClosedHandoffCompiledSubroutineConstruction) :
    PairedRecognizerDovetailBoundedLayoutRunnerHandoffCompiledSubroutineConstruction := by
  intro accept reject
  rcases h accept reject with ⟨runner, hrunner⟩
  exact
    ⟨runner,
      tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_handoffCompiled
        hrunner⟩

theorem pairedRecognizerDovetailTotalOutputEmitterHandoffCompiledSubroutineConstruction_of_closedHandoff
    (h :
      PairedRecognizerDovetailTotalOutputEmitterClosedHandoffCompiledSubroutineConstruction) :
    PairedRecognizerDovetailTotalOutputEmitterHandoffCompiledSubroutineConstruction := by
  rcases h with ⟨emitter, hemitter⟩
  exact
    ⟨emitter,
      tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_handoffCompiled
        hemitter⟩

theorem pairedRecognizerDovetailStageInputInitializerCompiledSubroutineConstruction_of_closedHandoff
    (h :
      PairedRecognizerDovetailStageInputInitializerClosedHandoffCompiledSubroutineConstruction) :
    PairedRecognizerDovetailStageInputInitializerCompiledSubroutineConstruction := by
  intro accept reject
  rcases h accept reject with ⟨initializer, hinitializer⟩
  exact
    ⟨initializer,
      tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_outputCompiled
        hinitializer⟩

theorem pairedRecognizerDovetailBoundedLayoutRunnerCompiledSubroutineConstruction_of_closedHandoff
    (h :
      PairedRecognizerDovetailBoundedLayoutRunnerClosedHandoffCompiledSubroutineConstruction) :
    PairedRecognizerDovetailBoundedLayoutRunnerCompiledSubroutineConstruction := by
  intro accept reject
  rcases h accept reject with ⟨runner, hrunner⟩
  exact
    ⟨runner,
      tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_outputCompiled
        hrunner⟩

theorem pairedRecognizerDovetailTotalOutputEmitterCompiledSubroutineConstruction_of_closedHandoff
    (h :
      PairedRecognizerDovetailTotalOutputEmitterClosedHandoffCompiledSubroutineConstruction) :
    PairedRecognizerDovetailTotalOutputEmitterCompiledSubroutineConstruction := by
  rcases h with ⟨emitter, hemitter⟩
  exact
    ⟨emitter,
      tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_outputCompiled
        hemitter⟩

theorem pairedRecognizerDovetailStageInputInitializerCompiledSubroutineConstruction_of_handoff
    (h :
      PairedRecognizerDovetailStageInputInitializerHandoffCompiledSubroutineConstruction) :
    PairedRecognizerDovetailStageInputInitializerCompiledSubroutineConstruction := by
  intro accept reject
  rcases h accept reject with ⟨initializer, hinitializer⟩
  exact
    ⟨initializer,
      tapeCodePrimitiveHandoffCompiledSubroutineByDescription_outputCompiled
        hinitializer⟩

theorem pairedRecognizerDovetailBoundedLayoutRunnerCompiledSubroutineConstruction_of_handoff
    (h :
      PairedRecognizerDovetailBoundedLayoutRunnerHandoffCompiledSubroutineConstruction) :
    PairedRecognizerDovetailBoundedLayoutRunnerCompiledSubroutineConstruction := by
  intro accept reject
  rcases h accept reject with ⟨runner, hrunner⟩
  exact
    ⟨runner,
      tapeCodePrimitiveHandoffCompiledSubroutineByDescription_outputCompiled
        hrunner⟩

theorem pairedRecognizerDovetailTotalOutputEmitterCompiledSubroutineConstruction_of_handoff
    (h :
      PairedRecognizerDovetailTotalOutputEmitterHandoffCompiledSubroutineConstruction) :
    PairedRecognizerDovetailTotalOutputEmitterCompiledSubroutineConstruction := by
  rcases h with ⟨emitter, hemitter⟩
  exact
    ⟨emitter,
      tapeCodePrimitiveHandoffCompiledSubroutineByDescription_outputCompiled
        hemitter⟩

theorem pairedRecognizerDovetailTotalStageAttemptCodeHandoffSubroutineRealizerConstruction_of_finiteSourceHandoffComponents
    (hinitializer :
      PairedRecognizerDovetailStageInputInitializerHandoffCompiledSubroutineConstruction)
    (hrunner :
      PairedRecognizerDovetailBoundedLayoutRunnerHandoffCompiledSubroutineConstruction)
    (hemitter :
      PairedRecognizerDovetailTotalOutputEmitterHandoffCompiledSubroutineConstruction)
    (hseq :
      PairedRecognizerDovetailTotalStageAttemptHandoffSubroutineRealizerSequencingConstruction) :
    PairedRecognizerDovetailTotalStageAttemptCodeHandoffSubroutineRealizerConstruction := by
  intro accept reject
  rcases hinitializer accept reject with
    ⟨initializer, hinitializer⟩
  rcases hrunner accept reject with ⟨runner, hrunner⟩
  rcases hemitter with ⟨emitter, hemitter⟩
  rcases hseq accept reject initializer runner emitter
      hinitializer hrunner hemitter with
    ⟨attempt, hattempt⟩
  exact
    ⟨attempt,
      tapeCodePrimitiveHandoffSubroutineRealizedByDescription_congr
        (pairedRecognizerDovetailTotalStageAttemptSourceCode_transform_eq
          accept reject)
        hattempt⟩

theorem pairedRecognizerDovetailTotalStageAttemptCodeOutputSubroutineRealizerConstruction_of_handoff
    (h :
      PairedRecognizerDovetailTotalStageAttemptCodeHandoffSubroutineRealizerConstruction) :
    PairedRecognizerDovetailTotalStageAttemptCodeOutputSubroutineRealizerConstruction := by
  intro accept reject
  rcases h accept reject with ⟨attempt, hattempt⟩
  exact ⟨attempt, hattempt.left⟩

theorem pairedRecognizerDovetailTotalStageAttemptCodeOutputSubroutineRealizerConstruction_of_outputCompiled
    (h :
      PairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction) :
    PairedRecognizerDovetailTotalStageAttemptCodeOutputSubroutineRealizerConstruction := by
  intro accept reject
  rcases h accept reject with ⟨attempt, hattempt⟩
  exact
    ⟨attempt,
      tapeCodePrimitiveOutputSubroutineRealizedByDescription_of_outputCompiled
        hattempt⟩

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

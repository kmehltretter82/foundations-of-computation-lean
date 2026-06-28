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

namespace PairedRecognizerDovetail

namespace TotalStageAttemptCodeOutputCompiledSubroutineConstruction

theorem of_finiteSourceComponents
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

theorem pairedRecognizerDovetailStageInputInitializerHandoffCompiledSubroutineConstruction_of_closedHandoff
    (h :
      PairedRecognizerDovetailStageInputInitializerClosedHandoffCompiledSubroutineConstruction) :
    PairedRecognizerDovetailStageInputInitializerHandoffCompiledSubroutineConstruction :=
  fun accept reject =>
    Exists.elim (h accept reject) fun initializer hinitializer =>
      ⟨initializer,
      tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_handoffCompiled
        hinitializer⟩

theorem pairedRecognizerDovetailBoundedLayoutRunnerHandoffCompiledSubroutineConstruction_of_closedHandoff
    (h :
      PairedRecognizerDovetailBoundedLayoutRunnerClosedHandoffCompiledSubroutineConstruction) :
    PairedRecognizerDovetailBoundedLayoutRunnerHandoffCompiledSubroutineConstruction :=
  fun accept reject =>
    Exists.elim (h accept reject) fun runner hrunner =>
      ⟨runner,
      tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_handoffCompiled
        hrunner⟩

theorem pairedRecognizerDovetailTotalOutputEmitterHandoffCompiledSubroutineConstruction_of_closedHandoff
    (h :
      PairedRecognizerDovetailTotalOutputEmitterClosedHandoffCompiledSubroutineConstruction) :
    PairedRecognizerDovetailTotalOutputEmitterHandoffCompiledSubroutineConstruction :=
  Exists.elim h fun emitter hemitter =>
    ⟨emitter,
      tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_handoffCompiled
        hemitter⟩

theorem pairedRecognizerDovetailStageInputInitializerCompiledSubroutineConstruction_of_closedHandoff
    (h :
      PairedRecognizerDovetailStageInputInitializerClosedHandoffCompiledSubroutineConstruction) :
    PairedRecognizerDovetailStageInputInitializerCompiledSubroutineConstruction :=
  fun accept reject =>
    Exists.elim (h accept reject) fun initializer hinitializer =>
      ⟨initializer,
      tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_outputCompiled
        hinitializer⟩

theorem pairedRecognizerDovetailBoundedLayoutRunnerCompiledSubroutineConstruction_of_closedHandoff
    (h :
      PairedRecognizerDovetailBoundedLayoutRunnerClosedHandoffCompiledSubroutineConstruction) :
    PairedRecognizerDovetailBoundedLayoutRunnerCompiledSubroutineConstruction :=
  fun accept reject =>
    Exists.elim (h accept reject) fun runner hrunner =>
      ⟨runner,
      tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_outputCompiled
        hrunner⟩

theorem pairedRecognizerDovetailTotalOutputEmitterCompiledSubroutineConstruction_of_closedHandoff
    (h :
      PairedRecognizerDovetailTotalOutputEmitterClosedHandoffCompiledSubroutineConstruction) :
    PairedRecognizerDovetailTotalOutputEmitterCompiledSubroutineConstruction :=
  Exists.elim h fun emitter hemitter =>
    ⟨emitter,
      tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_outputCompiled
        hemitter⟩

theorem pairedRecognizerDovetailStageInputInitializerCompiledSubroutineConstruction_of_handoff
    (h :
      PairedRecognizerDovetailStageInputInitializerHandoffCompiledSubroutineConstruction) :
    PairedRecognizerDovetailStageInputInitializerCompiledSubroutineConstruction :=
  fun accept reject =>
    Exists.elim (h accept reject) fun initializer hinitializer =>
      ⟨initializer,
      tapeCodePrimitiveHandoffCompiledSubroutineByDescription_outputCompiled
        hinitializer⟩

theorem pairedRecognizerDovetailBoundedLayoutRunnerCompiledSubroutineConstruction_of_handoff
    (h :
      PairedRecognizerDovetailBoundedLayoutRunnerHandoffCompiledSubroutineConstruction) :
    PairedRecognizerDovetailBoundedLayoutRunnerCompiledSubroutineConstruction :=
  fun accept reject =>
    Exists.elim (h accept reject) fun runner hrunner =>
      ⟨runner,
      tapeCodePrimitiveHandoffCompiledSubroutineByDescription_outputCompiled
        hrunner⟩

theorem pairedRecognizerDovetailTotalOutputEmitterCompiledSubroutineConstruction_of_handoff
    (h :
      PairedRecognizerDovetailTotalOutputEmitterHandoffCompiledSubroutineConstruction) :
    PairedRecognizerDovetailTotalOutputEmitterCompiledSubroutineConstruction :=
  Exists.elim h fun emitter hemitter =>
    ⟨emitter,
      tapeCodePrimitiveHandoffCompiledSubroutineByDescription_outputCompiled
        hemitter⟩

namespace PairedRecognizerDovetail

namespace TotalStageAttemptCodeHandoffSubroutineRealizerConstruction

theorem of_finiteSourceHandoffComponents
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

end TotalStageAttemptCodeHandoffSubroutineRealizerConstruction

end PairedRecognizerDovetail

theorem pairedRecognizerDovetailTotalStageAttemptCodeOutputSubroutineRealizerConstruction_of_handoff
    (h :
      PairedRecognizerDovetailTotalStageAttemptCodeHandoffSubroutineRealizerConstruction) :
    PairedRecognizerDovetailTotalStageAttemptCodeOutputSubroutineRealizerConstruction :=
  fun accept reject =>
    Exists.elim (h accept reject) fun attempt hattempt =>
      ⟨attempt, hattempt.left⟩

theorem pairedRecognizerDovetailTotalStageAttemptCodeOutputSubroutineRealizerConstruction_of_outputCompiled
    (h :
      PairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction) :
    PairedRecognizerDovetailTotalStageAttemptCodeOutputSubroutineRealizerConstruction :=
  fun accept reject =>
    Exists.elim (h accept reject) fun attempt hattempt =>
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

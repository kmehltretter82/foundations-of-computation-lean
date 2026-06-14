import FoC.Computability.Compiler.Core.SearchDrivers

set_option doc.verso true

/-!
# Machine-description compiler closeout
-/

namespace FoC
namespace Computability

open Languages

structure MachineDescriptionCompilerCloseout where
  stepCodeOutput :
    FixedDescriptionStepCodeOutputRealizerConstruction
  stepConfiguration :
    FixedDescriptionStepCodeConfigurationRealizerConstruction
  boundedSimulatorCodeOutput :
    FixedDescriptionBoundedSimulatorCodeOutputRealizerConstruction
  boundedSimulatorTable :
    FixedDescriptionBoundedSimulatorTableCompilerConstruction
  dovetailInitialLayoutCodeOutput :
    PairedRecognizerDovetailInitialLayoutCodeOutputRealizerConstruction
  dovetailLayoutCodeOutput :
    PairedRecognizerDovetailLayoutCodeOutputRealizerConstruction
  dovetailOutputCodeOutput :
    PairedRecognizerDovetailOutputCodeOutputRealizerConstruction
  dovetailStageAttemptCodeOutput :
    PairedRecognizerDovetailStageAttemptCodeOutputRealizerConstruction
  dovetailTotalStageAttemptCodeOutput :
    PairedRecognizerDovetailTotalStageAttemptCodeOutputRealizerConstruction
  dovetailControllerContinueCodeOutput :
    PairedRecognizerDovetailControllerContinueCodeOutputRealizerConstruction
  dovetailControllerEmitCodeOutput :
    PairedRecognizerDovetailControllerEmitCodeOutputRealizerConstruction

def machineDescriptionCompilerCloseout_of_tapeCodeOutputCompiler
    (hcompile : MachineDescriptionTapeCodeOutputCompilerConstruction) :
    MachineDescriptionCompilerCloseout where
  stepCodeOutput := by
    intro D
    exact hcompile (FixedDescriptionStepCode D)
  stepConfiguration :=
    fixedDescriptionStepCodeConfigurationRealizerConstruction_of_outputRealizerConstruction
      (by
        intro D
        exact hcompile (FixedDescriptionStepCode D))
  boundedSimulatorCodeOutput := by
    intro D
    exact hcompile (FixedDescriptionBoundedSimulatorCode D)
  boundedSimulatorTable :=
    fixedDescriptionBoundedSimulatorTableCompiler_of_codeOutputRealizer
      (by
        intro D
        exact hcompile (FixedDescriptionBoundedSimulatorCode D))
  dovetailLayoutCodeOutput := by
    intro accept reject
    exact hcompile (PairedRecognizerDovetailLayoutCode accept reject)
  dovetailInitialLayoutCodeOutput := by
    intro accept reject
    exact hcompile
      (PairedRecognizerDovetailInitialLayoutCode accept reject)
  dovetailOutputCodeOutput :=
    hcompile PairedRecognizerDovetailOutputCode
  dovetailStageAttemptCodeOutput := by
    intro accept reject
    exact hcompile
      (PairedRecognizerDovetailStageAttemptCode accept reject)
  dovetailTotalStageAttemptCodeOutput := by
    intro accept reject
    exact hcompile
      (PairedRecognizerDovetailTotalStageAttemptCode accept reject)
  dovetailControllerContinueCodeOutput := by
    intro accept reject
    exact hcompile
      (PairedRecognizerDovetailControllerContinueCode accept reject)
  dovetailControllerEmitCodeOutput := by
    intro accept reject
    exact hcompile
      (PairedRecognizerDovetailControllerEmitCode accept reject)

theorem fixedDescriptionStepCodeConfigurationRealizerConstruction_of_tapeCodeOutputCompiler
    (hcompile : MachineDescriptionTapeCodeOutputCompilerConstruction) :
    FixedDescriptionStepCodeConfigurationRealizerConstruction :=
  (machineDescriptionCompilerCloseout_of_tapeCodeOutputCompiler
    hcompile).stepConfiguration

theorem fixedDescriptionBoundedSimulatorTableCompiler_of_tapeCodeOutputCompiler
    (hcompile : MachineDescriptionTapeCodeOutputCompilerConstruction) :
    FixedDescriptionBoundedSimulatorTableCompilerConstruction :=
  (machineDescriptionCompilerCloseout_of_tapeCodeOutputCompiler
    hcompile).boundedSimulatorTable

theorem pairedRecognizerDovetailLayoutCodeOutputRealizer_of_tapeCodeOutputCompiler
    (hcompile : MachineDescriptionTapeCodeOutputCompilerConstruction) :
    PairedRecognizerDovetailLayoutCodeOutputRealizerConstruction :=
  (machineDescriptionCompilerCloseout_of_tapeCodeOutputCompiler
    hcompile).dovetailLayoutCodeOutput

end Computability
end FoC

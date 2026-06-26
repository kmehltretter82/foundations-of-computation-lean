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
  stepCodeOutput := fun D => hcompile (FixedDescriptionStepCode D)
  stepConfiguration :=
    fixedDescriptionStepCodeConfigurationRealizerConstruction_of_outputRealizerConstruction
      (fun D => hcompile (FixedDescriptionStepCode D))
  boundedSimulatorCodeOutput :=
    fun D => hcompile (FixedDescriptionBoundedSimulatorCode D)
  boundedSimulatorTable :=
    fixedDescriptionBoundedSimulatorTableCompiler_of_codeOutputRealizer
      (fun D => hcompile (FixedDescriptionBoundedSimulatorCode D))
  dovetailLayoutCodeOutput :=
    fun accept reject =>
      hcompile (PairedRecognizerDovetailLayoutCode accept reject)
  dovetailInitialLayoutCodeOutput :=
    fun accept reject =>
      hcompile (PairedRecognizerDovetailInitialLayoutCode accept reject)
  dovetailOutputCodeOutput :=
    hcompile PairedRecognizerDovetailOutputCode
  dovetailStageAttemptCodeOutput :=
    fun accept reject =>
      hcompile (PairedRecognizerDovetailStageAttemptCode accept reject)
  dovetailTotalStageAttemptCodeOutput :=
    fun accept reject =>
      hcompile (PairedRecognizerDovetailTotalStageAttemptCode accept reject)
  dovetailControllerContinueCodeOutput :=
    fun accept reject =>
      hcompile (PairedRecognizerDovetailControllerContinueCode accept reject)
  dovetailControllerEmitCodeOutput :=
    fun accept reject =>
      hcompile (PairedRecognizerDovetailControllerEmitCode accept reject)

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

import FoC.Computability.Compiler.Core.CommonGround.Controller
import FoC.Computability.Compiler.Core.ControllerResultEmitter
import FoC.Computability.Compiler.Core.ControllerInputInitializer
import FoC.Computability.Compiler.Core.ControllerResultContinue

set_option doc.verso true

/-!
# Finite-source dovetail scaffolds

This file is the finite-source manifest for the dovetail controller route.  It
does not define new encodings; it connects the concrete encoded rewriter leaves
to the paired-recognizer construction targets used by the closeout theorems.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

/-- Forward half of an output-compiled tape-code primitive subroutine. -/
def TapeCodePrimitiveOutputCompiledForwardSpec
    (P : TapeCodePrimitive)
    (D : MachineDescription) : Prop :=
  forall code out : Word MachineCodeSymbol,
    P.transform code = some out ->
      D.HaltsWithOutput
        (encodeCodeWordAsInput code)
        (encodeCodeWordAsInput out)

/-- Closed half of an output-compiled tape-code primitive subroutine. -/
def TapeCodePrimitiveOutputCompiledClosedSpec
    (P : TapeCodePrimitive)
    (D : MachineDescription) : Prop :=
  forall code out : Word MachineCodeSymbol,
    D.HaltsWithOutput
        (encodeCodeWordAsInput code)
        (encodeCodeWordAsInput out) ->
      P.transform code = some out

theorem tapeCodePrimitiveOutputCompiledSubroutineByDescription_of_forward_closed
    {P : TapeCodePrimitive}
    {D : MachineDescription}
    (hready : D.SubroutineReady)
    (hforward : TapeCodePrimitiveOutputCompiledForwardSpec P D)
    (hclosed : TapeCodePrimitiveOutputCompiledClosedSpec P D) :
    TapeCodePrimitiveOutputCompiledSubroutineByDescription P D := by
  constructor
  · constructor
    · exact hready.left
    · intro code out
      constructor
      · exact hclosed code out
      · exact hforward code out
  · exact hready.right

theorem encodedTapeCodePrimitiveOutputCompiledSubroutineConstruction_of_forward_closed
    {P : TapeCodePrimitive}
    (h :
      exists D : MachineDescription,
        D.SubroutineReady ∧
          TapeCodePrimitiveOutputCompiledForwardSpec P D ∧
          TapeCodePrimitiveOutputCompiledClosedSpec P D) :
    EncodedTapeCodePrimitiveOutputCompiledSubroutineConstruction P := by
  rcases h with ⟨D, hready, hforward, hclosed⟩
  exact
    ⟨D,
      tapeCodePrimitiveOutputCompiledSubroutineByDescription_of_forward_closed
        hready hforward hclosed⟩

/-!
**Controller encoded leaves.**  These are the finite transition-table
obligations that are specific to the controller loop rather than to the
dovetail layout subroutines.  The projection and result-emitter machines are
already available from their concrete descriptions; the initializer and
continue-result code-word subroutine remain as concrete leaves.
-/

section EncodedControllerLeaves

/-- Controller input initializer data, already stated in the public contract. -/
def EncodedControllerInputInitializerConstructionData :
    Prop :=
  exists initializer : MachineDescription,
    PairedRecognizerDovetailControllerInputInitializerRealizes initializer

theorem encodedControllerInputInitializerRewriterConstruction_of_data
    (h : EncodedControllerInputInitializerConstructionData) :
    EncodedControllerInputInitializerRewriterConstruction := by
  rcases h with ⟨initializer, hinitializer⟩
  exact ⟨initializer, hinitializer.left, hinitializer.right⟩

theorem encodedControllerInputInitializerConstructionData_scaffold :
    EncodedControllerInputInitializerConstructionData := by
  exact controllerInputInitializerConstruction_scaffold

theorem encodedControllerInputInitializerRewriterConstruction_scaffold :
    EncodedControllerInputInitializerRewriterConstruction :=
  encodedControllerInputInitializerRewriterConstruction_of_data
    encodedControllerInputInitializerConstructionData_scaffold

theorem encodedControllerStageInputProjectionRewriterConstruction_scaffold :
    EncodedControllerStageInputProjectionRewriterConstruction :=
  encodedControllerStageInputProjectionRewriterConstruction_of_codeWordSubroutine
    ControllerStageInputProjection.encodedControllerStageInputProjectionCodeWordSubroutineConstruction_scaffold

theorem encodedControllerResultEmitterRewriterConstruction_scaffold :
    EncodedControllerResultEmitterRewriterConstruction :=
  encodedControllerResultEmitterRewriterConstruction_of_description

/--
Controller-result continuation data in the generic forward/closed primitive
format used by the code-word subroutine adapter.
-/
def EncodedControllerResultContinueConstructionData :
    Prop :=
  exists continuer : MachineDescription,
    continuer.SubroutineReady ∧
      TapeCodePrimitiveOutputCompiledForwardSpec
        PairedRecognizerDovetailControllerResultContinueCode
        continuer ∧
      TapeCodePrimitiveOutputCompiledClosedSpec
        PairedRecognizerDovetailControllerResultContinueCode
        continuer

theorem encodedControllerResultContinueCodeWordSubroutineConstruction_of_data
    (h : EncodedControllerResultContinueConstructionData) :
    EncodedControllerResultContinueCodeWordSubroutineConstruction :=
  encodedTapeCodePrimitiveOutputCompiledSubroutineConstruction_of_forward_closed
    h

theorem encodedControllerResultContinueConstructionData_scaffold :
    EncodedControllerResultContinueConstructionData := by
  exact controllerResultContinueConstruction_scaffold

theorem encodedControllerResultContinueCodeWordSubroutineConstruction_scaffold :
    EncodedControllerResultContinueCodeWordSubroutineConstruction :=
  encodedControllerResultContinueCodeWordSubroutineConstruction_of_data
    encodedControllerResultContinueConstructionData_scaffold

theorem encodedControllerContinueRewriterConstruction_scaffold :
    EncodedControllerContinueRewriterConstruction :=
  encodedControllerContinueRewriterConstruction_of_resultContinueCodeWordSubroutine
    encodedControllerResultContinueCodeWordSubroutineConstruction_scaffold

end EncodedControllerLeaves

/-!
**Contract bridges.**  The encoded rewriter contracts are stated in terms of
canonical code-word input and output.  The paired-recognizer construction
targets use the same machines packaged as output-compiled subroutines or as
controller component realizers.  These lemmas keep that repackaging explicit,
so the final scaffold section can name only construction dependencies.
-/

section ContractBridges

private theorem encodedTapeCodePrimitiveOutputCompiledSubroutineConstruction_of_rewriter
    {P : TapeCodePrimitive}
    (h : EncodedTapeCodePrimitiveRewriterConstruction P) :
    EncodedTapeCodePrimitiveOutputCompiledSubroutineConstruction P := by
  rcases h with ⟨rewriter, hready, hspec⟩
  exact ⟨rewriter, ⟨⟨hready.left, hspec⟩, hready.right⟩⟩

theorem pairedRecognizerDovetailStageInputInitializerCompiledSubroutineConstruction_of_encodedRewriter
    (h :
      EncodedDovetailStageInputToInitialLayoutRewriterConstruction) :
    PairedRecognizerDovetailStageInputInitializerCompiledSubroutineConstruction := by
  intro accept reject
  exact
    encodedTapeCodePrimitiveOutputCompiledSubroutineConstruction_of_rewriter
      (P := PairedRecognizerDovetailInitialLayoutCode accept reject)
      (h accept reject)

theorem pairedRecognizerDovetailBoundedLayoutRunnerCompiledSubroutineConstruction_of_encodedRewriter
    (h :
      EncodedDovetailLayoutBoundedRunnerRewriterConstruction) :
    PairedRecognizerDovetailBoundedLayoutRunnerCompiledSubroutineConstruction := by
  intro accept reject
  exact
    encodedTapeCodePrimitiveOutputCompiledSubroutineConstruction_of_rewriter
      (P := PairedRecognizerDovetailLayoutCode accept reject)
      (h accept reject)

theorem pairedRecognizerDovetailBoundedLayoutRunnerCompiledSubroutineConstruction_of_spec
    (h :
      PairedRecognizerDovetailBoundedLayoutRunnerSpecConstruction) :
    PairedRecognizerDovetailBoundedLayoutRunnerCompiledSubroutineConstruction := by
  intro accept reject
  rcases h accept reject with ⟨runner, hrunner⟩
  exact
    ⟨runner,
      EncodedRewriters.BoundedLayoutRunner.outputCompiledSubroutineByDescription_of_spec
        hrunner⟩

theorem pairedRecognizerDovetailTotalOutputEmitterOutputSubroutineRealizerConstruction_of_encodedRewriter
    (h :
      EncodedDovetailTotalOutputEmitterRewriterConstruction) :
    PairedRecognizerDovetailTotalOutputEmitterOutputSubroutineRealizerConstruction :=
  h

namespace PairedRecognizerDovetail

namespace StageInputInitializerHandoffCompiledSubroutineConstruction

theorem of_encodedRewriter
    (h :
      EncodedDovetailStageInputToInitialLayoutHandoffRewriterConstruction) :
    PairedRecognizerDovetailStageInputInitializerHandoffCompiledSubroutineConstruction :=
  h

end StageInputInitializerHandoffCompiledSubroutineConstruction

namespace BoundedLayoutRunnerHandoffCompiledSubroutineConstruction

theorem of_encodedRewriter
    (h :
      EncodedDovetailLayoutBoundedRunnerHandoffRewriterConstruction) :
    PairedRecognizerDovetailBoundedLayoutRunnerHandoffCompiledSubroutineConstruction :=
  h

end BoundedLayoutRunnerHandoffCompiledSubroutineConstruction

namespace TotalOutputEmitterHandoffCompiledSubroutineConstruction

theorem of_encodedRewriter
    (h :
      EncodedDovetailTotalOutputEmitterHandoffRewriterConstruction) :
    PairedRecognizerDovetailTotalOutputEmitterHandoffCompiledSubroutineConstruction :=
  h

end TotalOutputEmitterHandoffCompiledSubroutineConstruction

namespace StageInputInitializerClosedHandoffCompiledSubroutineConstruction

theorem of_encodedRewriter
    (h :
      EncodedDovetailStageInputToInitialLayoutClosedHandoffRewriterConstruction) :
    PairedRecognizerDovetailStageInputInitializerClosedHandoffCompiledSubroutineConstruction :=
  h

end StageInputInitializerClosedHandoffCompiledSubroutineConstruction

namespace BoundedLayoutRunnerClosedHandoffCompiledSubroutineConstruction

theorem of_encodedRewriter
    (h :
      EncodedDovetailLayoutBoundedRunnerClosedHandoffRewriterConstruction) :
    PairedRecognizerDovetailBoundedLayoutRunnerClosedHandoffCompiledSubroutineConstruction :=
  h

end BoundedLayoutRunnerClosedHandoffCompiledSubroutineConstruction

namespace TotalOutputEmitterClosedHandoffCompiledSubroutineConstruction

theorem of_encodedRewriter
    (h :
      EncodedDovetailTotalOutputEmitterClosedHandoffRewriterConstruction) :
    PairedRecognizerDovetailTotalOutputEmitterClosedHandoffCompiledSubroutineConstruction :=
  h

end TotalOutputEmitterClosedHandoffCompiledSubroutineConstruction

end PairedRecognizerDovetail

theorem pairedRecognizerDovetailControllerInputInitializerConstruction_of_encodedRewriter
    (h : EncodedControllerInputInitializerRewriterConstruction) :
    PairedRecognizerDovetailControllerInputInitializerConstruction :=
  h

theorem pairedRecognizerDovetailControllerStageInputEncoderConstruction_of_encodedRewriter
    (h : EncodedControllerStageInputProjectionRewriterConstruction) :
    PairedRecognizerDovetailControllerStageInputEncoderConstruction :=
  encodedTapeCodePrimitiveOutputCompiledSubroutineConstruction_of_rewriter
    (P := PairedRecognizerDovetailControllerStageInputCodePrimitive) h

theorem pairedRecognizerDovetailControllerResultEmitterConstruction_of_encodedRewriter
    (h : EncodedControllerResultEmitterRewriterConstruction) :
    PairedRecognizerDovetailControllerResultEmitterConstruction :=
  h

theorem pairedRecognizerDovetailControllerContinueConstruction_of_encodedRewriter
    (h : EncodedControllerContinueRewriterConstruction) :
    PairedRecognizerDovetailControllerContinueConstruction :=
  h

end ContractBridges

/-!
**Finite-source scaffold exports.**  These declarations are the remaining concrete
machine-construction leaves for the paired-recognizer dovetail controller
route. They are intentionally narrow: the source programs and controller layout
are the fixed finite targets above, not arbitrary staged programs or arbitrary
tape-code primitives.
-/


theorem pairedRecognizerDovetailStageInputInitializerCompiledSubroutineConstruction_scaffold :
    PairedRecognizerDovetailStageInputInitializerCompiledSubroutineConstruction :=
  pairedRecognizerDovetailStageInputInitializerCompiledSubroutineConstruction_of_closedHandoff
    (PairedRecognizerDovetail.StageInputInitializerClosedHandoffCompiledSubroutineConstruction.of_encodedRewriter
      encodedDovetailStageInputToInitialLayoutClosedHandoffRewriterConstruction_scaffold)

theorem pairedRecognizerDovetailBoundedLayoutRunnerSpecConstruction_scaffold :
    PairedRecognizerDovetailBoundedLayoutRunnerSpecConstruction :=
  EncodedRewriters.BoundedLayoutRunner.finiteDescriptionConstruction_scaffold

theorem pairedRecognizerDovetailBoundedLayoutRunnerCompiledSubroutineConstruction_scaffold :
    PairedRecognizerDovetailBoundedLayoutRunnerCompiledSubroutineConstruction :=
  pairedRecognizerDovetailBoundedLayoutRunnerCompiledSubroutineConstruction_of_spec
    pairedRecognizerDovetailBoundedLayoutRunnerSpecConstruction_scaffold

theorem pairedRecognizerDovetailTotalOutputEmitterOutputSubroutineRealizerConstruction_scaffold :
    PairedRecognizerDovetailTotalOutputEmitterOutputSubroutineRealizerConstruction :=
  pairedRecognizerDovetailTotalOutputEmitterOutputSubroutineRealizerConstruction_of_encodedRewriter
    encodedDovetailTotalOutputEmitterRewriterConstruction_scaffold

theorem pairedRecognizerDovetailStageInputInitializerHandoffCompiledSubroutineConstruction_scaffold :
    PairedRecognizerDovetailStageInputInitializerHandoffCompiledSubroutineConstruction :=
  PairedRecognizerDovetail.StageInputInitializerHandoffCompiledSubroutineConstruction.of_encodedRewriter
    encodedDovetailStageInputToInitialLayoutHandoffRewriterConstruction_scaffold

theorem pairedRecognizerDovetailStageInputInitializerClosedHandoffCompiledSubroutineConstruction_scaffold :
    PairedRecognizerDovetailStageInputInitializerClosedHandoffCompiledSubroutineConstruction :=
  PairedRecognizerDovetail.StageInputInitializerClosedHandoffCompiledSubroutineConstruction.of_encodedRewriter
    encodedDovetailStageInputToInitialLayoutClosedHandoffRewriterConstruction_scaffold

theorem pairedRecognizerDovetailControllerInputInitializerConstruction_scaffold :
    PairedRecognizerDovetailControllerInputInitializerConstruction :=
  pairedRecognizerDovetailControllerInputInitializerConstruction_of_encodedRewriter
    encodedControllerInputInitializerRewriterConstruction_scaffold

theorem pairedRecognizerDovetailControllerStageInputEncoderConstruction_scaffold :
    PairedRecognizerDovetailControllerStageInputEncoderConstruction :=
  pairedRecognizerDovetailControllerStageInputEncoderConstruction_of_encodedRewriter
    encodedControllerStageInputProjectionRewriterConstruction_scaffold

end Computability
end FoC

import FoC.Computability.Compiler.Core.CommonGround
import FoC.Computability.Compiler.Core.ConstructionTargets

set_option doc.verso true

/-!
# Controller Result Continuation

This module isolates the finite-machine leaf for the controller continuation
subroutine.  The machine recognizes successful
{name (full := FoC.Computability.PairedRecognizerDovetailControllerResultContinueCode)}`PairedRecognizerDovetailControllerResultContinueCode`
transforms over canonical encoded code words.
-/

namespace FoC
namespace Computability

open Languages

/--
Construction data for the controller continuation subroutine, stated directly
against the code-word transform.  Later scaffolds adapt this data to the public
controller-loop contract.
-/
def ControllerResultContinueConstructionData : Prop :=
  exists continuer : MachineDescription,
    continuer.SubroutineReady ∧
      (forall code out : Word MachineCodeSymbol,
        PairedRecognizerDovetailControllerResultContinueCode.transform code =
            some out ->
          continuer.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput code)
            (MachineDescription.encodeCodeWordAsInput out)) ∧
      (forall code out : Word MachineCodeSymbol,
        continuer.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput code)
            (MachineDescription.encodeCodeWordAsInput out) ->
          PairedRecognizerDovetailControllerResultContinueCode.transform code = some out)

def ControllerResultContinueForwardSpec
    (continuer : MachineDescription) : Prop :=
  forall code out : Word MachineCodeSymbol,
    PairedRecognizerDovetailControllerResultContinueCode.transform code =
        some out ->
      continuer.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out)

def ControllerResultContinueClosedSpec
    (continuer : MachineDescription) : Prop :=
  forall code out : Word MachineCodeSymbol,
    continuer.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out) ->
      PairedRecognizerDovetailControllerResultContinueCode.transform code =
        some out

def ControllerResultContinueSpec
    (continuer : MachineDescription) : Prop :=
  continuer.SubroutineReady ∧
    ControllerResultContinueForwardSpec continuer ∧
      ControllerResultContinueClosedSpec continuer

def ControllerResultContinueCanonicalForwardSpec
    (continuer : MachineDescription) : Prop :=
  forall C : MachineDescription.DovetailControllerLayout,
    PairedRecognizerDovetailControllerRawOutput C.result = none ->
      continuer.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.DovetailControllerLayout.encode C))
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.DovetailControllerLayout.encode
            (MachineDescription.DovetailControllerLayout.nextStage C)))

def ControllerResultContinueClosedLayoutSpec
    (continuer : MachineDescription) : Prop :=
  forall code out : Word MachineCodeSymbol,
    continuer.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out) ->
      exists C : MachineDescription.DovetailControllerLayout,
        code = MachineDescription.DovetailControllerLayout.encode C ∧
          PairedRecognizerDovetailControllerRawOutput C.result = none ∧
            out =
              MachineDescription.DovetailControllerLayout.encode
                (MachineDescription.DovetailControllerLayout.nextStage C)

def ControllerResultContinueComponentSpec
    (continuer : MachineDescription) : Prop :=
  continuer.SubroutineReady ∧
    ControllerResultContinueCanonicalForwardSpec continuer ∧
      ControllerResultContinueClosedLayoutSpec continuer

def ControllerResultContinueComponentConstruction : Prop :=
  exists continuer : MachineDescription,
    ControllerResultContinueComponentSpec continuer


end Computability
end FoC

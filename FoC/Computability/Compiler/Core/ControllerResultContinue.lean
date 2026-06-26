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

theorem controllerResultContinueConstruction_scaffold :
    ControllerResultContinueConstructionData := by
  sorry

end Computability
end FoC

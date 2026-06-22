import FoC.Computability.Compiler.Core.ConstructionTargets
set_option doc.verso true

/-!
# Controller Result Continuation

This module provides the machine component that handles continuing execution after a controller result.
-/


set_option doc.verso true

namespace FoC
namespace Computability

open Languages

def ControllerResultContinueConstructionData : Prop :=
  exists continuer : MachineDescription,
    continuer.SubroutineReady ∧
      (forall code out : Word MachineCodeSymbol,
        PairedRecognizerDovetailControllerResultContinueCode.transform code = some out ->
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

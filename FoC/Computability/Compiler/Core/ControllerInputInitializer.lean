import FoC.Computability.Compiler.Core.ConstructionTargets
set_option doc.verso true

/-!
# Controller Input Initializer

This module defines the machine component that initializes the controller input tape before execution.
-/


set_option doc.verso true

namespace FoC
namespace Computability

open Languages

theorem controllerInputInitializerConstruction_scaffold :
    exists initializer : MachineDescription,
      PairedRecognizerDovetailControllerInputInitializerRealizes initializer := by
  sorry

end Computability
end FoC

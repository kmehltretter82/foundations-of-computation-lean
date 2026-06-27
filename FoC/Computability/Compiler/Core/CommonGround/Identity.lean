import FoC.Computability.Compiler.DescriptionExecution

set_option doc.verso true

/-!
# Common exact-identity helpers

This module contains the reusable exact identity runner facts used when a
subroutine sequence needs a no-op second phase with explicit start/halt
configurations.
-/

namespace FoC
namespace Computability

namespace CommonGround
namespace Identity

theorem exactIdentityDescription_subroutineReady :
    MachineDescription.ExactIdentityDescription.SubroutineReady :=
  ⟨MachineDescription.exactIdentityDescription_wellFormed,
    MachineDescription.exactIdentityDescription_haltTransitionFree⟩

theorem exactIdentityDescription_haltsFromTape
    (T : Tape Bool) :
    MachineDescription.ExactIdentityDescription.HaltsFromTape T T := by
  refine ⟨0, ?_⟩
  constructor <;> rfl

theorem exactIdentityDescription_run_from_start
    (T : Tape Bool) :
    exists steps : Nat,
      MachineDescription.ExactIdentityDescription.runConfig steps
          { state := MachineDescription.ExactIdentityDescription.start
            tape := T } =
        { state := MachineDescription.ExactIdentityDescription.halt
          tape := T } := by
  refine ⟨0, ?_⟩
  simp [MachineDescription.ExactIdentityDescription,
    MachineDescription.runConfig]

theorem exactIdentityDescription_runConfig_from_start
    (n : Nat) (T : Tape Bool) :
    MachineDescription.ExactIdentityDescription.runConfig n
        { state := MachineDescription.ExactIdentityDescription.start
          tape := T } =
      { state := MachineDescription.ExactIdentityDescription.halt
        tape := T } := by
  cases n <;>
    simp [MachineDescription.ExactIdentityDescription,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition]

end Identity
end CommonGround

end Computability
end FoC

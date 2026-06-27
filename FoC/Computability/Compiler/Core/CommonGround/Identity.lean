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

open MachineDescription

namespace CommonGround
namespace Identity

theorem exactIdentityDescription_subroutineReady :
    ExactIdentityDescription.SubroutineReady :=
  ⟨exactIdentityDescription_wellFormed,
    exactIdentityDescription_haltTransitionFree⟩

theorem exactIdentityDescription_haltsFromTape
    (T : Tape Bool) :
    ExactIdentityDescription.HaltsFromTape T T := by
  refine ⟨0, ?_⟩
  constructor <;> rfl

theorem exactIdentityDescription_run_from_start
    (T : Tape Bool) :
    exists steps : Nat,
      ExactIdentityDescription.runConfig steps
          { state := ExactIdentityDescription.start
            tape := T } =
        { state := ExactIdentityDescription.halt
          tape := T } := by
  refine ⟨0, ?_⟩
  simp [ExactIdentityDescription,
    runConfig]

theorem exactIdentityDescription_runConfig_from_start
    (n : Nat) (T : Tape Bool) :
    ExactIdentityDescription.runConfig n
        { state := ExactIdentityDescription.start
          tape := T } =
      { state := ExactIdentityDescription.halt
        tape := T } := by
  cases n <;>
    simp [ExactIdentityDescription,
      runConfig, stepConfig,
      lookupTransition]

end Identity
end CommonGround

end Computability
end FoC

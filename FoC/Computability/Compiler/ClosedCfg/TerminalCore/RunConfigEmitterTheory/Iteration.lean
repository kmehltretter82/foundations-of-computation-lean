import FoC.Computability.Compiler.DescriptionExecution
import FoC.Computability.MachineBuilder.SimulatorLayout

set_option doc.verso true

/-!
# Fixed-description run-loop iteration

The #18 emitter must account for a halted configuration at stage zero and then
execute exactly the encoded number of fixed-description steps.  This module
states that executable loop independently of the eventual tape layout and
proves that it is exactly the semantic simulator-layout run.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace RunConfigEmitterTheory

/-- Initialize the accumulated hit bit with the stage-zero configuration. -/
def seedHit (D : MachineDescription) (L : SimulatorLayout) : SimulatorLayout :=
  { L with
    hit := L.hit || SimulatorLayout.haltedConfigBool D L.config }

/-- Execute the fixed-description one-step layout update exactly {lit}`n` times. -/
def iterateStep (D : MachineDescription) : Nat -> SimulatorLayout -> SimulatorLayout
  | 0, L => L
  | n + 1, L => SimulatorLayout.step D (iterateStep D n L)

theorem nextConfig_eq_runConfig_one
    (D : MachineDescription) (c : Configuration) :
    SimulatorLayout.nextConfig D c = D.runConfig 1 c := by
  cases hstep : D.stepConfig c <;>
    simp [SimulatorLayout.nextConfig, MachineDescription.runConfig, hstep]

/-- Seeding the stage-zero hit and iterating the executable one-step update is
exactly the semantic bounded simulator run, including its accumulated hit bit. -/
theorem iterateStep_seedHit_eq_run
    (D : MachineDescription) (L : SimulatorLayout) (n : Nat) :
    iterateStep D n (seedHit D L) = SimulatorLayout.run D n L := by
  induction n with
  | zero =>
      simp [iterateStep, seedHit, SimulatorLayout.run,
        SimulatorLayout.hitsFromConfigByBool,
        SimulatorLayout.haltedFromConfigInBool,
        SimulatorLayout.haltedConfigBool, MachineDescription.runConfig]
  | succ n ih =>
      simp only [iterateStep]
      rw [ih]
      cases L
      simp [SimulatorLayout.step, SimulatorLayout.run,
        nextConfig_eq_runConfig_one,
        SimulatorLayout.hitsFromConfigByBool,
        SimulatorLayout.haltedFromConfigInBool,
        SimulatorLayout.haltedConfigBool,
        MachineDescription.runConfig_add, Bool.or_assoc]

end RunConfigEmitterTheory
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC

import FoC.Computability.Compiler.DescriptionExecution

set_option doc.verso true

/-!
# Exact stuck execution semantics

This dependency-light module records exact finite-description runs that end at
a nonhalt configuration with no matching transition. It is split from the
core description semantics so the already-oversized implementation file does
not grow when sequential constructions consume this rejection currency.
-/

namespace FoC
namespace Computability
namespace MachineDescription

/-- If a later halt-stable run state is not the halt, no earlier state was the
halt either. -/
theorem runConfig_state_ne_halt_of_later_ne_halt
    {D : MachineDescription} {c : Configuration} {n k : Nat}
    (hD : D.HaltTransitionFree) (hle : n ≤ k)
    (hlater : (D.runConfig k c).state ≠ D.halt) :
    (D.runConfig n c).state ≠ D.halt := by
  intro hhalt
  have hk : k = n + (k - n) := by lia
  have hcfg : D.runConfig n c =
      { state := D.halt, tape := (D.runConfig n c).tape } := by
    cases hrun : D.runConfig n c with
    | mk state tape => simp [hrun] at hhalt ⊢; exact hhalt
  have hfinal : (D.runConfig k c).state = D.halt := by
    rw [hk, runConfig_add, hcfg, runConfig_halt hD]
  exact hlater hfinal

/-- Exact evidence that execution reaches a nonhalt configuration with no
matching transition. -/
def ReachesStuck (D : MachineDescription)
    (source : Configuration) (tape : Tape Bool) : Prop :=
  exists steps state : Nat,
    D.runConfig steps source = { state := state, tape := tape } ∧
      D.stepConfig { state := state, tape := tape } = none ∧
        state ≠ D.halt

/-- A word-start specialization of exact stuck-run evidence. -/
def StuckFromTape (D : MachineDescription)
    (input stuck : Tape Bool) : Prop :=
  D.ReachesStuck { state := D.start, tape := input } stuck

/-- Pull exact stuck-run evidence backward across an exact execution prefix. -/
theorem ReachesStuck.prepend
    {D : MachineDescription} {source middle : Configuration}
    {stuck : Tape Bool} {prefixSteps : Nat}
    (hprefix : D.runConfig prefixSteps source = middle)
    (hstuck : D.ReachesStuck middle stuck) :
    D.ReachesStuck source stuck := by
  rcases hstuck with ⟨stuckSteps, state, hrun, hstep, hstate⟩
  refine ⟨prefixSteps + stuckSteps, state, ?_, hstep, hstate⟩
  rw [runConfig_add, hprefix, hrun]

end MachineDescription
end Computability
end FoC

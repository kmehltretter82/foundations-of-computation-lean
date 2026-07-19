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

/-- A contiguous Boolean window split at the current head.  The left word is
stored in tape-stack order and both far edges carry an explicit blank. -/
def splitTape
    (leftRev right : Languages.Word Bool) (padding : Nat) : Tape Bool :=
  match right with
  | [] =>
      { left := List.append (leftRev.map some) [none]
        head := none
        right := List.replicate padding none }
  | bit :: rest =>
      { left := List.append (leftRev.map some) [none]
        head := some bit
        right := List.append (rest.map some)
          (List.replicate (padding + 1) none) }

/-- A tape whose represented window is one contiguous Boolean word between
explicit far-edge blanks. -/
def ContiguousTape (tape : Tape Bool) : Prop :=
  exists leftRev right : Languages.Word Bool, exists padding : Nat,
    tape = splitTape leftRev right padding

theorem contiguousTape_splitTape
    (leftRev right : Languages.Word Bool) (padding : Nat) :
    ContiguousTape (splitTape leftRev right padding) :=
  ⟨leftRev, right, padding, rfl⟩

/-- A missing configuration step is exactly a missing transition-table lookup
at the configuration's current state and tape symbol. -/
theorem lookupTransition_eq_none_of_stepConfig_eq_none
    {D : MachineDescription} {source : Configuration}
    (hstep : D.stepConfig source = none) :
    D.lookupTransition source.state (Tape.read source.tape) = none := by
  unfold MachineDescription.stepConfig at hstep
  cases hlookup :
      D.lookupTransition source.state (Tape.read source.tape) with
  | none => rfl
  | some row => simp [hlookup] at hstep

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

import FoC.Computability.Compiler.Structured.Lowering.DivergenceTransfer

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace BoundedFuelPairSearch
namespace U12LoweredInversion

/-!
Lowering inversion for the output-indexed fuel-pair search. The ordinary
forward lowerer theorem is not an inversion theorem. If a master trajectory
is defined outside halt and changes state or tapes at every selected step,
logical divergence transfers to physical divergence.
-/

theorem lowerStructured3Description_haltsFromTape_implies_haltsFromConfig
    {D : Description}
    (hDwf : D.WellFormed)
    (hDhtf : D.HaltTransitionFree)
    (hrows : SupportsReadWriteRows3 D)
    (c : CommonGround.FiniteTransducers.Structured.Configuration)
    (hcState : c.state = D.start)
    (hcTapes : c.tapes.length = D.tapeCount)
    (hdefined : forall k : Nat,
      (D.runConfig k c).state ≠ D.halt ->
        D.stepConfig (D.runConfig k c) ≠ none)
    (hconfigProgress :
      forall {a b : CommonGround.FiniteTransducers.Structured.Configuration},
        D.stepConfig a = some b ->
          a.state ≠ b.state \/ a.tapes ≠ b.tapes)
    {T : Tape Bool}
    (hhalt : (lowerStructured3Description D).HaltsFromTape
      (encodedGuardedStructuredTapes c.tapes) T) :
    D.HaltsFromConfig c := by
  apply Classical.byContradiction
  intro hnot
  have hneHalt : forall k : Nat,
      (D.runConfig k c).state ≠ D.halt := by
    intro k hk
    exact hnot ⟨k, hk⟩
  exact
    (lowerStructured3Description_not_halts_of_state_or_tape_progress
      hDwf hDhtf hrows c hcState hcTapes
      (fun k => hdefined k (hneHalt k)) hneHalt hconfigProgress T) hhalt

end U12LoweredInversion
end BoundedFuelPairSearch
end Computability
end FoC

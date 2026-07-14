import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.FieldDecomposition.CfgHitClose
import FoC.Computability.Compiler.Structured.Lowering.EncodedInjectivity

set_option doc.verso true

/-!
# Represented classified-boundary guardrail

The configuration/hit materializer deliberately returns concrete logical-tape
representatives.  Its configuration tape retains far-left blank workspace,
so it is only logically tape-equivalent to the canonical classified tape.

Guarded structured encoding observes that represented window.  In particular,
the represented guarded endpoint cannot be transported to the canonical
selector source with ordinary physical
{name (full := FoC.Computability.Tape.Equiv)}`Tape.Equiv`.  Downstream #18
integration must either run from the carried representative and serialize its
semantic boundary, or provide a concrete boundary-aware repair.
-/

namespace FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
namespace FieldDecomposition.MetadataPrefix.ConfigTapeAndHit

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

/-- The concrete configuration representative always retains a nonempty
far-left blank suffix beyond the exact source configuration window. -/
theorem actualConfigTape_left_eq
    (L : SimulatorLayout) :
    (actualConfigTape L).left =
      List.append L.config.tape.left
        (none :: reconstructionBaseLeft L) := by
  simp [actualConfigTape, tapeAtCells, emittedCells_eq_reverse_append]

/-- The represented configuration tape is never the exact canonical tape.
Its logical equivalence is intentional; equality would contradict the extra
far-left workspace cell. -/
theorem actualConfigTape_ne
    (L : SimulatorLayout) :
    actualConfigTape L ≠ L.config.tape := by
  intro h
  have hleft := congrArg Tape.left h
  rw [actualConfigTape_left_eq] at hleft
  have hlength := congrArg List.length hleft
  simp at hlength

/-- The actual {lit}`ConfigTapeAndHit` endpoint and the canonical classified-loop
source are not even physically tape-equivalent after guarded encoding.
Pointwise logical-tape equivalence therefore cannot close this join. -/
theorem represented_guarded_not_equiv_classified
    (D : MachineDescription) (L : SimulatorLayout) :
    ¬ Tape.Equiv
      (encodedGuardedStructuredTapes (representedTapes D L))
      (encodedGuardedStructuredTapes
        (ClassifiedBoundary.classifiedLoopTapes D L)) := by
  intro h
  have hexact := encodedGuardedStructuredTapes_three_equiv_inj h
  exact actualConfigTape_ne L hexact.left

end FieldDecomposition.MetadataPrefix.ConfigTapeAndHit
end FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore

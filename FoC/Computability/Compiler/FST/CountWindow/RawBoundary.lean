import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.EndpointSupport
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.UniformCore

set_option doc.verso true

/-!
# Count-window raw-boundary emitter

This module exposes the uniform two-pass raw-boundary construction used by the
count-window encoder.  The historical structured, bounded-branch, and
blank-sentinel routes have been retired; the implementation now has one
canonical endpoint and one construction theorem.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace CountWindowRawSourceEncoder
namespace RawBoundaryRightEdgeEmitter

/--
Canonical endpoint for the uniform raw-boundary emitter.  The encoded layout
is immediately left of the live tail, the head is on the first encoded bit,
and a blank sentinel remains on the left.
-/
def encodedLeftEdgeTape
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  tapeAtCells [none]
    (List.append
      ((encodedLayoutBits (List.append skipped count)).map some)
      (some tailFirst :: tail))

/-- Uniform raw-boundary emitter contract used by the count-window encoder. -/
def Spec (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall (skipped count : Word Bool)
      (tailFirst : Bool) (tail : List (Option Bool)),
      emitter.HaltsFromTapeEquiv
        (sourceTape skipped count (some tailFirst :: tail))
        (encodedLeftEdgeTape skipped count tailFirst tail)

/-- Existence of the uniform raw-boundary emitter. -/
def Construction : Prop :=
  exists emitter : MachineDescription, Spec emitter

/--
The canonical construction is the uniform two-pass core.  This is the only
RawBoundary implementation exported to the parent count-window construction.
-/
theorem construction_core : Construction := by
  refine ⟨rawBoundaryUniformEmitterCoreDescription, ?_⟩
  constructor
  · exact rawBoundaryUniformEmitterCoreDescription_subroutineReady
  · intro skipped count tailFirst tail
    rw [encodedLeftEdgeTape]
    exact
      rawBoundaryUniformEmitterCoreDescription_haltsFrom_sourceTape_encodedLeftEdgeCells
        skipped count tailFirst tail

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC

import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.Layout

set_option doc.verso true

/-!
# Structured tape projection contracts

This module records reusable finite-machine contracts for projecting logical
tapes out of the guarded structured one-tape encoding.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

/--
Finite-machine contract for extracting logical tape 2 from a guarded
three-logical-tape encoding.

The target is stated up to {name}`Tape.Equiv` so an implementation may preserve
or introduce harmless guard blanks around the extracted logical tape.
-/
def StructuredTape2ProjectorSpec
    (projector : MachineDescription) : Prop :=
  projector.SubroutineReady ∧
    forall T0 T1 T2 : Tape Bool,
      projector.HaltsFromTapeEquiv
        (encodedGuardedStructured3Tapes T0 T1 T2)
        T2

/-- Existence wrapper for {name}`StructuredTape2ProjectorSpec`. -/
def StructuredTape2ProjectorConstruction : Prop :=
  exists projector : MachineDescription,
    StructuredTape2ProjectorSpec projector

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC


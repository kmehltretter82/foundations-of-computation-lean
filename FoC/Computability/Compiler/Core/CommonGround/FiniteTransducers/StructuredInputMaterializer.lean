import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.Layout

set_option doc.verso true

/-!
# Structured input materializer contract

This module names the reusable boundary contract for entering a lowered
three-logical-tape computation from a public one-tape source.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers

/--
Physical target shape for a three-logical-tape input materializer.

Tape 0 is the public source tape, tape 1 is the blank scratch/counter tape, and
tape 2 is a caller-provided output-buffer tape determined by the same input
index as the source.
-/
def structured3InputMaterializerTargetTape
    (source output : Tape Bool) : Tape Bool :=
  Structured.MultiTapeLowering.encodedGuardedStructured3Tapes
    source Tape.blank output

/--
Reusable materializer contract for entering a three-logical-tape structured
subroutine.

The index fixes both the public source tape and the tape-2 output buffer.  This
keeps the target functional for each source family and avoids the impossible
legacy contracts that quantified over arbitrary output padding.
-/
def Structured3InputMaterializerSpec {ι : Type}
    (source output : ι -> Tape Bool)
    (materializer : MachineDescription) : Prop :=
  materializer.SubroutineReady ∧
    forall input : ι,
      materializer.HaltsFromTapeEquiv
        (source input)
        (structured3InputMaterializerTargetTape
          (source input) (output input))

def Structured3InputMaterializerConstruction {ι : Type}
    (source output : ι -> Tape Bool) : Prop :=
  exists materializer : MachineDescription,
    Structured3InputMaterializerSpec source output materializer

end FiniteTransducers
end CommonGround
end Computability
end FoC

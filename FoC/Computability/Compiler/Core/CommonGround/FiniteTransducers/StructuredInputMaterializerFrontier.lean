import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredInputMaterializer

set_option doc.verso true

/-!
# Structured input materializer frontier

Reusable weak input-materializer leaf for routes that only need
{lit}`HaltsFromTapeEquiv` into a guarded three-tape encoding with blank output.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers

/--
Weak structured input materializer construction for source families whose
logical tape 2 starts blank.
-/
def Structured3BlankOutputInputMaterializerConstruction
    {ι : Type}
    (source : ι -> Tape Bool) : Prop :=
  Structured3InputMaterializerConstruction
    source
    (fun _input => Tape.blank)

theorem structured3BlankOutputInputMaterializerConstruction_core
    {ι : Type}
    (source : ι -> Tape Bool) :
    Structured3BlankOutputInputMaterializerConstruction source := by
  -- WARNING: This arbitrary-source frontier is too strong as stated. The
  -- target encodes the literal `Tape` representation, so equivalent inputs
  -- such as `Tape.blank` and `{ left := [none], head := none, right := [] }`
  -- can require non-equivalent encoded targets. Specialize this to a canonical
  -- source family or canonicalize the source before encoding.
  sorry

end FiniteTransducers
end CommonGround

end Computability
end FoC

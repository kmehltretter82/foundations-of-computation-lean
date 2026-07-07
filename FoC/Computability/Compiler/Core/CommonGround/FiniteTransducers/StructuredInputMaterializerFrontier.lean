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
  -- Remaining weak finite-machine leaf: materialize each source tape into the
  -- guarded three-tape input with blank scratch and blank output, up to tape
  -- equivalence.  Exact indexed closedness is source-family-specific and
  -- belongs in the target materializer leaves.
  sorry

end FiniteTransducers
end CommonGround

end Computability
end FoC

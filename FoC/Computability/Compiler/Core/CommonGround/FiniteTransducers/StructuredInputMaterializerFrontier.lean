import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredInputMaterializer

set_option doc.verso true

/-!
# Structured input materializer frontier

Reusable blank-output input-materializer aliases for routes that only need
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

theorem structured3BlankOutputInputMaterializerConstruction_iff
    {ι : Type}
    (source : ι -> Tape Bool) :
    Structured3BlankOutputInputMaterializerConstruction source <->
      Structured3InputMaterializerConstruction
        source (fun _input => Tape.blank) := by
  rfl

end FiniteTransducers
end CommonGround

end Computability
end FoC

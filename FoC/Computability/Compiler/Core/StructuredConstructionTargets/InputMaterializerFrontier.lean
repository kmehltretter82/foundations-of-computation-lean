import FoC.Computability.Compiler.Core.StructuredConstructionTargets.Base

set_option doc.verso true

/-!
# Structured target input materializer frontier

Reusable exact indexed materializer leaf for target endpoints whose public
input is materialized into three logical tapes with blank scratch and blank
output.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace StructuredConstructionTargets

/--
Exact indexed materializer construction for canonical target endpoints with
blank logical tape 1 and blank logical tape 2.
-/
def Structured3EndpointBlankOutputMaterializerConstruction
    {ι : Type}
    (source : ι -> Tape Bool) : Prop :=
  Structured3EndpointIndexedMaterializerConstruction
    source
    (fun input =>
      CommonGround.FiniteTransducers.structured3InputMaterializerTargetTape
        (source input) Tape.blank)

theorem structured3EndpointBlankOutputMaterializerConstruction_core
    {ι : Type}
    (source : ι -> Tape Bool) :
    Structured3EndpointBlankOutputMaterializerConstruction source := by
  -- Remaining finite-machine leaf: exactly materialize each public source
  -- tape into the guarded three-tape endpoint input with blank scratch and
  -- blank output, and prove indexed closedness for that source family.
  sorry

end StructuredConstructionTargets

end Computability
end FoC

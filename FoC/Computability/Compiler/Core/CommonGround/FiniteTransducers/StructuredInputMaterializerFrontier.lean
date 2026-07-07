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
Indexed exact closedness for a materializer frontier.

Any halt from any tape must be one of the indexed source/target pairs.
-/
def InputMaterializerExactClosedIndexedFromTape {ι : Type}
    (D : MachineDescription)
    (source target : ι -> Tape Bool) : Prop :=
  forall Tin T : Tape Bool,
    D.HaltsFromTape Tin T ->
      exists input : ι, Tin = source input ∧ T = target input

/--
Exact indexed blank-output materializer construction.

This is the concrete lower frontier used by both the weak raw-head ingress
route and the exact target endpoint materializer wrappers.
-/
def Structured3BlankOutputExactInputMaterializerConstruction
    {ι : Type}
    (source : ι -> Tape Bool) : Prop :=
  exists materializer : MachineDescription,
    materializer.SubroutineReady ∧
      (forall input : ι,
        materializer.HaltsFromTape
          (source input)
          (structured3InputMaterializerTargetTape
            (source input) Tape.blank)) ∧
      InputMaterializerExactClosedIndexedFromTape
        materializer
        source
        (fun input =>
          structured3InputMaterializerTargetTape
            (source input) Tape.blank)

theorem structured3BlankOutputExactInputMaterializerConstruction_core
    {ι : Type}
    (source : ι -> Tape Bool) :
    Structured3BlankOutputExactInputMaterializerConstruction source := by
  -- Remaining finite-machine leaf: exactly materialize each source tape into
  -- the guarded three-tape input with blank scratch and blank output, and
  -- prove indexed closedness for that source family.
  sorry

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

theorem structured3BlankOutputInputMaterializerConstruction_of_exact
    {ι : Type}
    {source : ι -> Tape Bool}
    (hexact :
      Structured3BlankOutputExactInputMaterializerConstruction source) :
    Structured3BlankOutputInputMaterializerConstruction source := by
  rcases hexact with
    ⟨materializer, hready, hforward, _hclosedIndex⟩
  refine ⟨materializer, ?_⟩
  constructor
  · exact hready
  · intro input
    exact (hforward input).toEquiv

theorem structured3BlankOutputInputMaterializerConstruction_core
    {ι : Type}
    (source : ι -> Tape Bool) :
    Structured3BlankOutputInputMaterializerConstruction source := by
  exact
    structured3BlankOutputInputMaterializerConstruction_of_exact
      (structured3BlankOutputExactInputMaterializerConstruction_core source)

end FiniteTransducers
end CommonGround

end Computability
end FoC

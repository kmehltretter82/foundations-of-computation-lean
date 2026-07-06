import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Quoter.RawCells

set_option doc.verso true

/-!
This module packages the selected-projection input quoter construction. It
states the exact-shape specification and exposes the scaffold construction used
by padded projection.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
def SelectedProjectionInputQuoterExactShapeSpec
    (quoter : MachineDescription) : Prop :=
  quoter.SubroutineReady ∧
    forall L : DovetailLayout,
      quoter.HaltsFromTape
        (SelectedProjectionInputQuoterExactSourceTape L)
        (SelectedProjectionInputQuoterExactTargetTape L)

theorem selectedProjectionInputQuoterSpec_of_exactShape
    {quoter : MachineDescription}
    (hquoter : SelectedProjectionInputQuoterExactShapeSpec quoter) :
    SelectedProjectionInputQuoterSpec quoter := by
  constructor
  · exact hquoter.left
  · intro L
    have hrun := hquoter.right L
    rw [parsedLayoutCheckedTape_eq_inputQuoterExactSourceTape L]
    rw [sourceTape_outputPrefix_eq_inputQuoterExactTargetTape L]
    exact hrun

/--
Finite-machine leaf for selected projection under the equivalence-based phase
contract.  The checked parser supplies the canonical checked parsed-layout
input.  This first phase quotes the input field and positions the remaining
layout fields for the selected padded tail emitter.
-/
theorem selectedProjectionInputQuoterConstruction_scaffold :
    SelectedProjectionInputQuoterConstruction := by
  rcases
      SelectedProjectionInputQuoterFiniteLeaf.selectedProjectionInputQuoterPostBoundaryConstruction with
    ⟨post, hpost⟩
  refine
    ⟨SeqViaCanonical
        SelectedProjectionInputQuoterFiniteLeaf.AssemblyPrefixDescription
        post,
      selectedProjectionInputQuoterSpec_of_exactShape ?_⟩
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        SelectedProjectionInputQuoterFiniteLeaf.assemblyPrefixDescription_subroutineReady
        hpost.left
  · intro L
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        SelectedProjectionInputQuoterFiniteLeaf.assemblyPrefixDescription_subroutineReady
        hpost.left
        (SelectedProjectionInputQuoterFiniteLeaf.assemblyPrefixDescription_haltsFrom_exactSourceTape_to_prefixBoundary
          L)
        (by rfl)
        (hpost.right L)

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC

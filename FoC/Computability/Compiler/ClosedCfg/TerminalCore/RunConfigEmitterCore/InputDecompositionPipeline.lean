import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.FieldDecomposition
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.InputMaterializer
import FoC.Computability.Compiler.Core.CommonGround.SameHeadComposition

set_option doc.verso true

/-!
# Input-to-decomposition pipeline

This module composes the checked right-end-left materializer with the honest
field-decomposition boundary.  It handles the explicit left-window blank left
by the materializer through tape-equivalence transport and same-head
composition.  Therefore the remaining parser work is exactly
`FieldDecomposition.Construction`; no additional ingress adapter is hidden at
this boundary.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace RunConfigEmitterCore
namespace InputDecompositionPipeline

/-- Same physical head after the mandatory left/right composition bridge. -/
def sameHeadRepresentative (T : Tape Bool) : Tape Bool :=
  Tape.move Direction.right (Tape.move Direction.left T)

theorem sameHeadRepresentative_equiv (T : Tape Bool) :
    Tape.Equiv (sameHeadRepresentative T) T := by
  cases T with
  | mk left head right =>
      cases left with
      | nil =>
          simp [sameHeadRepresentative, Tape.Equiv, Tape.move,
            Tape.moveLeft, Tape.moveRight, Tape.dropTrailingNone]
      | cons cell rest =>
          simp [sameHeadRepresentative, Tape.Equiv, Tape.move,
            Tape.moveLeft, Tape.moveRight]

private theorem haltsFromTapeEquiv_of_equiv_input
    {D : MachineDescription} {Tin Tin' Tout : Tape Bool}
    (hin : Tape.Equiv Tin Tin')
    (h : D.HaltsFromTapeEquiv Tin Tout) :
    D.HaltsFromTapeEquiv Tin' Tout := by
  rcases h with ⟨actual, hactual, hactualEquiv⟩
  rcases HaltsFromTapeEquiv_of_input_equiv hin hactual with
    ⟨transported, htransported, htransportedEquiv⟩
  exact
    ⟨transported, htransported,
      Tape.Equiv.trans htransportedEquiv hactualEquiv⟩

/-- Concrete pipeline obtained from a field decomposer implementation. -/
def description (decomposer : MachineDescription) : MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    InputMaterializer.description decomposer

/-- Forward contract from the generic right-end-left source to the exact
logical field family, up to proof-transparent physical padding. -/
def Spec (pipeline : MachineDescription) : Prop :=
  pipeline.SubroutineReady ∧
    forall L : SimulatorLayout,
      pipeline.HaltsFromTapeEquiv
        (InputMaterializer.rightEndLeftSourceTape
          (SimulatorLayout.asBoolInput L))
        (FieldDecomposition.loopTargetTape L)

def Construction : Prop :=
  exists pipeline : MachineDescription, Spec pipeline

theorem description_spec
    {decomposer : MachineDescription}
    (hdecomposer : FieldDecomposition.Spec decomposer) :
    Spec (description decomposer) := by
  constructor
  · exact
      CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
        InputMaterializer.description_subroutineReady hdecomposer.left
  · intro L
    have hbits : SimulatorLayout.asBoolInput L ≠ [] :=
      RunConfigEmitterTheory.simulatorLayout_asBoolInput_ne_nil L
    have hmaterializer :=
      InputMaterializer.description_haltsFromTapeEquiv
        (SimulatorLayout.asBoolInput L) hbits
    have hdecomposerCanonical := hdecomposer.right L
    have hdecomposerPadded :
        decomposer.HaltsFromTapeEquiv
          (sameHeadRepresentative (FieldDecomposition.embeddedSourceTape L))
          (FieldDecomposition.loopTargetTape L) :=
      haltsFromTapeEquiv_of_equiv_input
        (Tape.Equiv.symm
          (sameHeadRepresentative_equiv
            (FieldDecomposition.embeddedSourceTape L)))
        hdecomposerCanonical
    unfold description
    exact
      CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTapeEquiv_of_haltsFromTapeEquiv
        InputMaterializer.description_subroutineReady hdecomposer.left
        hmaterializer rfl hdecomposerPadded

theorem construction_of_fieldDecomposition
    (hdecomposer : FieldDecomposition.Construction) : Construction := by
  rcases hdecomposer with ⟨decomposer, hdecomposer⟩
  exact ⟨description decomposer, description_spec hdecomposer⟩

end InputDecompositionPipeline
end RunConfigEmitterCore
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC

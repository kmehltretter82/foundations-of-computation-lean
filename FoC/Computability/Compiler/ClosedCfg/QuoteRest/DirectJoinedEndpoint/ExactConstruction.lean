import FoC.Computability.Compiler.ClosedCfg.QuoteRest.DirectJoinedEndpoint.Construction
import FoC.Computability.Compiler.ClosedCfg.QuoteRest.DirectJoinedEndpoint.RawTailPositioner

set_option doc.verso true

/-!
# Exact direct joined source-rest construction

This module composes the joined-output construction with the canonical
raw-tail positioner.  The result retains the normalized output of the direct
route while restoring the exact head currency used by selected projection.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionInputQuoterFiniteLeaf

open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

def directJoinedAssemblyEquivDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription
    directJoinedAssemblyOutputDescription
    joinedOutputRawTailPositionerDescription

theorem directJoinedAssemblyEquivDescription_subroutineReady :
    directJoinedAssemblyEquivDescription.SubroutineReady := by
  exact
    canonicalPrimitiveSeqDescription_subroutineReady
      directJoinedAssemblyOutputDescription_subroutineReady
      joinedOutputRawTailPositionerDescription_subroutineReady

theorem directJoinedAssemblyEquivDescription_haltsFrom_assembly
    (p : AssemblySourceRestLiveTailEmitterParam) :
    directJoinedAssemblyEquivDescription.HaltsFromTapeEquiv
      (structuredLiveTailEmitterAssemblySourceTape p)
      (assemblySourceRestFinishTargetTape
        p.w p.sourceRestBits p.stage) := by
  exact
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      directJoinedAssemblyOutputDescription_subroutineReady
      joinedOutputRawTailPositionerDescription_subroutineReady
      (directJoinedAssemblyOutputDescription_haltsFrom_assembly p)
      (joinedOutputRawTailPositionerDescription_haltsFrom_joinedOutput
        p.w p.sourceRestBits p.stage).toEquiv

theorem directJoinedAssemblyEquivDescription_spec :
    MixedParserStackSourceRestFinishAssemblyEquivSpec
      directJoinedAssemblyEquivDescription := by
  refine ⟨directJoinedAssemblyEquivDescription_subroutineReady, ?_⟩
  intro w sourceRestBits stage
  let p : AssemblySourceRestLiveTailEmitterParam :=
    { w := w, sourceRestBits := sourceRestBits, stage := stage }
  rw [← structuredLiveTailEmitterAssemblySourceTape_eq_defaultedInternalMarker p]
  simpa [p] using
    directJoinedAssemblyEquivDescription_haltsFrom_assembly p

theorem directJoinedSourceRestFinishAssemblyEquivConstruction :
    MixedParserStackSourceRestFinishAssemblyEquivConstruction :=
  ⟨directJoinedAssemblyEquivDescription,
    directJoinedAssemblyEquivDescription_spec⟩

end SelectedProjectionInputQuoterFiniteLeaf
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC

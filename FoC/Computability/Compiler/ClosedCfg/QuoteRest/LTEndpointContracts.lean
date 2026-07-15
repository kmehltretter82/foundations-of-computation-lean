import FoC.Computability.Compiler.ClosedCfg.QuoteRest.LTStructuredOutputBridge
import FoC.Computability.Compiler.Structured.Lowering.ConcreteRefresh

set_option doc.verso true

/-!
# Structured live-tail emitter endpoint

This module retains the static lowerer and encoded endpoint facts consumed by
the direct joined QuoteRest construction.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionInputQuoterFiniteLeaf

def StructuredLiveTailEmitterStaticLowererReadiness : Prop :=
  structuredMixedOptionCellQuoteLiveTailEmitterDescription.WellFormed ∧
    structuredMixedOptionCellQuoteLiveTailEmitterDescription.HaltTransitionFree

theorem StructuredLiveTailEmitterStaticLowererReadiness.wellFormed
    (h : StructuredLiveTailEmitterStaticLowererReadiness) :
    structuredMixedOptionCellQuoteLiveTailEmitterDescription.WellFormed :=
  h.left

theorem StructuredLiveTailEmitterStaticLowererReadiness.haltTransitionFree
    (h : StructuredLiveTailEmitterStaticLowererReadiness) :
    structuredMixedOptionCellQuoteLiveTailEmitterDescription.HaltTransitionFree :=
  h.right

theorem structuredLiveTailEmitterStaticLowerer_supported :
    Structured.MultiTapeLowering.SupportsReadWriteRows3
      structuredMixedOptionCellQuoteLiveTailEmitterDescription :=
  structuredMixedOptionCellQuoteLiveTailEmitterDescription_supported

def loweredStructuredLiveTailEmitterDescription : MachineDescription :=
  Structured.MultiTapeLowering.lowerStructured3Description
    structuredMixedOptionCellQuoteLiveTailEmitterDescription

theorem loweredStructuredLiveTailEmitterDescription_subroutineReady
    (hready : StructuredLiveTailEmitterStaticLowererReadiness) :
    loweredStructuredLiveTailEmitterDescription.SubroutineReady := by
  simpa [loweredStructuredLiveTailEmitterDescription] using
    Structured.MultiTapeLowering.lowerStructured3Description_subroutineReady
      hready.wellFormed
      structuredLiveTailEmitterStaticLowerer_supported

def structuredLiveTailEmitterAssemblyEncodedInitialTape
    (p : AssemblySourceRestLiveTailEmitterParam) : Tape Bool :=
  Structured.MultiTapeLowering.encodedGuardedStructuredTapes
    (structuredLiveTailEmitterAssemblyInitialConfig p []).tapes

def structuredLiveTailEmitterAssemblyEncodedFinalTape
    (p : AssemblySourceRestLiveTailEmitterParam) : Tape Bool :=
  Structured.MultiTapeLowering.encodedGuardedStructuredTapes
    (structuredLiveTailEmitterAssemblyFinalConfig p []).tapes

theorem structuredLiveTailEmitterAssemblyEncodedInitialTape_eq_encoded3
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailEmitterAssemblyEncodedInitialTape p =
      Structured.MultiTapeLowering.encodedGuardedStructured3Tapes
        (structuredMixedOptionCellQuoteLiveTailCellPassSourceTape
          [] (structuredLiveTailEmitterAssemblyInputBits p))
        (structuredMixedOptionCellQuoteLiveTailCountMarkerTape 0)
        (structuredMixedOptionCellQuoteLiveTailOutputTape []) := by
  rfl

theorem structuredLiveTailEmitterAssemblyEncodedFinalTape_eq_encoded3
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailEmitterAssemblyEncodedFinalTape p =
      Structured.MultiTapeLowering.encodedGuardedStructured3Tapes
        (structuredMixedOptionCellQuoteLiveTailCellPassSourceTape
          (structuredLiveTailEmitterAssemblyInputBits p).reverse [])
        (structuredMixedOptionCellQuoteLiveTailRewindScratchTape 0
          (structuredLiveTailEmitterAssemblyInputBits p).length)
        (structuredMixedOptionCellQuoteLiveTailOutputTape
          (structuredLiveTailEmitterAssemblyOutputBits p [])) := by
  rfl

theorem loweredStructuredLiveTailEmitterDescription_haltsFromAssemblyEncoded
    (hready : StructuredLiveTailEmitterStaticLowererReadiness)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    loweredStructuredLiveTailEmitterDescription.HaltsFromTapeEquiv
      (structuredLiveTailEmitterAssemblyEncodedInitialTape p)
      (structuredLiveTailEmitterAssemblyEncodedFinalTape p) := by
  have hhalts :
      structuredMixedOptionCellQuoteLiveTailEmitterDescription.HaltsWithTapes
        (structuredLiveTailEmitterAssemblyInitialConfig p [])
        (structuredLiveTailEmitterAssemblyFinalConfig p []).tapes := by
    refine ⟨structuredLiveTailEmitterAssemblyRunSteps p, ?_⟩
    exact
      structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_assembly
        p []
  simpa [loweredStructuredLiveTailEmitterDescription,
    structuredLiveTailEmitterAssemblyEncodedInitialTape,
    structuredLiveTailEmitterAssemblyEncodedFinalTape] using
    Structured.MultiTapeLowering.lowerStructured3Description_haltsFromConfigWithTapes
      hready.wellFormed
      hready.haltTransitionFree
      structuredLiveTailEmitterStaticLowerer_supported
      (by rfl)
      (by rfl)
      hhalts

end SelectedProjectionInputQuoterFiniteLeaf
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC

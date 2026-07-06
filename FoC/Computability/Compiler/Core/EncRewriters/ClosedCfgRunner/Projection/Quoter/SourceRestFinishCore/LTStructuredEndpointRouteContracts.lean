import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.ConcreteRefresh
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.Composition
import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Quoter.SourceRestFinishCore.LTStructuredOutputBridge

set_option doc.verso true

/-!
# Structured live-tail endpoint route contracts

This module names the concrete static-lowering route for the live-tail emitter
and joiner without hiding the endpoint work that remains.  The structured
machines already have run proofs.  The static lowerer additionally needs finite
table readiness proofs, and the public one-tape construction needs initializer
and projector machines between the public layout and the guarded structured
three-tape layout.

The contracts below keep those obligations explicit:

* a lowerer-readiness gate for each structured table;
* encoded structured input/output endpoint tapes for the assembly family;
* conditional lowered runs from the structured run facts;
* initializer/projector component specs; and
* output-level adapters back to the existing live-tail construction surface.

The exact construction leaves still need either exact endpoint projectors or an
ordinary-machine wrapper that preserves the public cursor position.  These
contracts provide the bottom-up boundary for that work.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncRewriters
namespace BoundedLayoutRunner

namespace SelectedProjectionInputQuoterFiniteLeaf

open DovetailInitialLayoutInitializer

private theorem haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
    {D : MachineDescription} {Tin Tout : Tape Bool}
    (h : D.HaltsFromTapeEquiv Tin Tout) :
    D.HaltsFromTapeWithOutput Tin (Tape.normalizedOutput Tout) :=
  MachineDescription.haltsFromTapeWithOutput_of_haltsFromTapeEquiv h

/-! ## Static lowerer readiness -/

def StructuredLiveTailEmitterStaticLowererReadiness : Prop :=
  structuredMixedOptionCellQuoteLiveTailEmitterDescription.WellFormed ∧
    structuredMixedOptionCellQuoteLiveTailEmitterDescription.HaltTransitionFree

def StructuredLiveTailJoinerStaticLowererReadiness : Prop :=
  structuredRawTailInsertionJoinerDescription.WellFormed ∧
    structuredRawTailInsertionJoinerDescription.HaltTransitionFree

theorem StructuredLiveTailEmitterStaticLowererReadiness.wellFormed
    (h : StructuredLiveTailEmitterStaticLowererReadiness) :
    structuredMixedOptionCellQuoteLiveTailEmitterDescription.WellFormed :=
  h.left

theorem StructuredLiveTailEmitterStaticLowererReadiness.haltTransitionFree
    (h : StructuredLiveTailEmitterStaticLowererReadiness) :
    structuredMixedOptionCellQuoteLiveTailEmitterDescription.HaltTransitionFree :=
  h.right

theorem StructuredLiveTailJoinerStaticLowererReadiness.wellFormed
    (h : StructuredLiveTailJoinerStaticLowererReadiness) :
    structuredRawTailInsertionJoinerDescription.WellFormed :=
  h.left

theorem StructuredLiveTailJoinerStaticLowererReadiness.haltTransitionFree
    (h : StructuredLiveTailJoinerStaticLowererReadiness) :
    structuredRawTailInsertionJoinerDescription.HaltTransitionFree :=
  h.right

theorem structuredLiveTailEmitterStaticLowerer_supported :
    Structured.MultiTapeLowering.SupportsReadWriteRows3
      structuredMixedOptionCellQuoteLiveTailEmitterDescription :=
  structuredMixedOptionCellQuoteLiveTailEmitterDescription_supported

theorem structuredLiveTailJoinerStaticLowerer_supported :
    Structured.MultiTapeLowering.SupportsReadWriteRows3
      structuredRawTailInsertionJoinerDescription :=
  by
    simpa [structuredRawTailInsertionJoinerDescription] using
      Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.description_supported

def loweredStructuredLiveTailEmitterDescription : MachineDescription :=
  Structured.MultiTapeLowering.lowerStructured3Description
    structuredMixedOptionCellQuoteLiveTailEmitterDescription

def loweredStructuredLiveTailJoinerDescription : MachineDescription :=
  Structured.MultiTapeLowering.lowerStructured3Description
    structuredRawTailInsertionJoinerDescription

theorem loweredStructuredLiveTailEmitterDescription_subroutineReady
    (hready : StructuredLiveTailEmitterStaticLowererReadiness) :
    loweredStructuredLiveTailEmitterDescription.SubroutineReady := by
  simpa [loweredStructuredLiveTailEmitterDescription] using
    Structured.MultiTapeLowering.lowerStructured3Description_subroutineReady
      hready.wellFormed
      structuredLiveTailEmitterStaticLowerer_supported

theorem loweredStructuredLiveTailJoinerDescription_subroutineReady
    (hready : StructuredLiveTailJoinerStaticLowererReadiness) :
    loweredStructuredLiveTailJoinerDescription.SubroutineReady := by
  simpa [loweredStructuredLiveTailJoinerDescription] using
    Structured.MultiTapeLowering.lowerStructured3Description_subroutineReady
      hready.wellFormed
      structuredLiveTailJoinerStaticLowerer_supported

/-! ## Emitter encoded endpoints -/

def structuredLiveTailEmitterAssemblyEncodedInitialTape
    (p : AssemblySourceRestLiveTailEmitterParam) : Tape Bool :=
  Structured.MultiTapeLowering.encodedGuardedStructuredTapes
    (structuredLiveTailEmitterAssemblyInitialConfig p []).tapes

def structuredLiveTailEmitterAssemblyEncodedFinalTape
    (p : AssemblySourceRestLiveTailEmitterParam) : Tape Bool :=
  Structured.MultiTapeLowering.encodedGuardedStructuredTapes
    (structuredLiveTailEmitterAssemblyFinalConfig p []).tapes

def structuredLiveTailEmitterAssemblyEncodedInitialTapeWithOutput
    (p : AssemblySourceRestLiveTailEmitterParam)
    (outputBits : Word Bool) : Tape Bool :=
  Structured.MultiTapeLowering.encodedGuardedStructuredTapes
    (structuredLiveTailEmitterAssemblyInitialConfig p outputBits).tapes

def structuredLiveTailEmitterAssemblyEncodedFinalTapeWithOutput
    (p : AssemblySourceRestLiveTailEmitterParam)
    (outputBits : Word Bool) : Tape Bool :=
  Structured.MultiTapeLowering.encodedGuardedStructuredTapes
    (structuredLiveTailEmitterAssemblyFinalConfig p outputBits).tapes

theorem structuredLiveTailEmitterAssemblyEncodedInitialTape_eq_output_nil
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailEmitterAssemblyEncodedInitialTape p =
      structuredLiveTailEmitterAssemblyEncodedInitialTapeWithOutput p [] := by
  rfl

theorem structuredLiveTailEmitterAssemblyEncodedFinalTape_eq_output_nil
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailEmitterAssemblyEncodedFinalTape p =
      structuredLiveTailEmitterAssemblyEncodedFinalTapeWithOutput p [] := by
  rfl

theorem structuredLiveTailEmitterAssemblyEncodedInitialTapeWithOutput_eq_encoded3
    (p : AssemblySourceRestLiveTailEmitterParam)
    (outputBits : Word Bool) :
    structuredLiveTailEmitterAssemblyEncodedInitialTapeWithOutput p outputBits =
      Structured.MultiTapeLowering.encodedGuardedStructured3Tapes
        (structuredMixedOptionCellQuoteLiveTailCellPassSourceTape
          [] (structuredLiveTailEmitterAssemblyInputBits p))
        (structuredMixedOptionCellQuoteLiveTailCountMarkerTape 0)
        (structuredMixedOptionCellQuoteLiveTailOutputTape outputBits) := by
  rfl

theorem structuredLiveTailEmitterAssemblyEncodedFinalTapeWithOutput_eq_encoded3
    (p : AssemblySourceRestLiveTailEmitterParam)
    (outputBits : Word Bool) :
    structuredLiveTailEmitterAssemblyEncodedFinalTapeWithOutput p outputBits =
      Structured.MultiTapeLowering.encodedGuardedStructured3Tapes
        (structuredMixedOptionCellQuoteLiveTailCellPassSourceTape
          (structuredLiveTailEmitterAssemblyInputBits p).reverse [])
        (structuredMixedOptionCellQuoteLiveTailRewindScratchTape 0
          (structuredLiveTailEmitterAssemblyInputBits p).length)
        (structuredMixedOptionCellQuoteLiveTailOutputTape
          (structuredLiveTailEmitterAssemblyOutputBits p outputBits)) := by
  rfl

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

theorem loweredStructuredLiveTailEmitterDescription_haltsFromAssemblyEncodedWithOutput
    (hready : StructuredLiveTailEmitterStaticLowererReadiness)
    (p : AssemblySourceRestLiveTailEmitterParam)
    (outputBits : Word Bool) :
    loweredStructuredLiveTailEmitterDescription.HaltsFromTapeEquiv
      (structuredLiveTailEmitterAssemblyEncodedInitialTapeWithOutput
        p outputBits)
      (structuredLiveTailEmitterAssemblyEncodedFinalTapeWithOutput
        p outputBits) := by
  have hhalts :
      structuredMixedOptionCellQuoteLiveTailEmitterDescription.HaltsWithTapes
        (structuredLiveTailEmitterAssemblyInitialConfig p outputBits)
        (structuredLiveTailEmitterAssemblyFinalConfig p outputBits).tapes := by
    refine ⟨structuredLiveTailEmitterAssemblyRunSteps p, ?_⟩
    exact
      structuredMixedOptionCellQuoteLiveTailEmitterDescription_structuredAssemblyOutputSpec.run
        p outputBits
  simpa [loweredStructuredLiveTailEmitterDescription,
    structuredLiveTailEmitterAssemblyEncodedInitialTapeWithOutput,
    structuredLiveTailEmitterAssemblyEncodedFinalTapeWithOutput] using
    Structured.MultiTapeLowering.lowerStructured3Description_haltsFromConfigWithTapes
      hready.wellFormed
      hready.haltTransitionFree
      structuredLiveTailEmitterStaticLowerer_supported
      (by rfl)
      (by rfl)
      hhalts

theorem loweredStructuredLiveTailEmitterDescription_haltsFromAssemblyEncoded
    (hready : StructuredLiveTailEmitterStaticLowererReadiness)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    loweredStructuredLiveTailEmitterDescription.HaltsFromTapeEquiv
      (structuredLiveTailEmitterAssemblyEncodedInitialTape p)
      (structuredLiveTailEmitterAssemblyEncodedFinalTape p) := by
  simpa [structuredLiveTailEmitterAssemblyEncodedInitialTape_eq_output_nil,
    structuredLiveTailEmitterAssemblyEncodedFinalTape_eq_output_nil] using
    loweredStructuredLiveTailEmitterDescription_haltsFromAssemblyEncodedWithOutput
      hready p []

/-! ## Joiner encoded endpoints -/

def structuredLiveTailJoinerAssemblyEncodedInitialTape
    (p : AssemblySourceRestLiveTailEmitterParam) : Tape Bool :=
  Structured.MultiTapeLowering.encodedGuardedStructuredTapes
    (structuredLiveTailJoinerAssemblyInitialConfig p).tapes

def structuredLiveTailJoinerAssemblyEncodedRestoreTape
    (p : AssemblySourceRestLiveTailEmitterParam) : Tape Bool :=
  Structured.MultiTapeLowering.encodedGuardedStructuredTapes
    (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.restoreTailHandoffConfig
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (assemblySourceRestLiveTailEmitterRawTail p)
        (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes

theorem structuredLiveTailJoinerAssemblyEncodedInitialTape_eq_encoded3
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailJoinerAssemblyEncodedInitialTape p =
      Structured.MultiTapeLowering.encodedGuardedStructured3Tapes
        (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.sourceTape
          (assemblySourceRestLiveTailEmitterEmittedPrefix p)
          (assemblySourceRestLiveTailEmitterRawTail p)
          (assemblySourceRestLiveTailEmitterQuoteRest p))
        (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.scratchTape
          (assemblySourceRestLiveTailEmitterQuoteRest p))
        structuredMixedOptionCellQuoteLiveTailJoinerWorkTape := by
  rfl

theorem structuredLiveTailJoinerAssemblyEncodedRestoreTape_eq_runConfig
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailJoinerAssemblyEncodedRestoreTape p =
      Structured.MultiTapeLowering.encodedGuardedStructuredTapes
        (structuredLiveTailJoinerAssemblyRunConfig
          structuredRawTailInsertionJoinerDescription p).tapes := by
  have hrun :
      structuredLiveTailJoinerAssemblyRunConfig
          structuredRawTailInsertionJoinerDescription p =
        Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.restoreTailHandoffConfig
            (assemblySourceRestLiveTailEmitterEmittedPrefix p)
            (assemblySourceRestLiveTailEmitterRawTail p)
            (assemblySourceRestLiveTailEmitterQuoteRest p) :=
    structuredRawTailInsertionJoinerDescription_assemblyRestoreSpec.run p
  simp [structuredLiveTailJoinerAssemblyEncodedRestoreTape, hrun]

theorem loweredStructuredLiveTailJoinerDescription_haltsFromAssemblyEncoded
    (hready : StructuredLiveTailJoinerStaticLowererReadiness)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    loweredStructuredLiveTailJoinerDescription.HaltsFromTapeEquiv
      (structuredLiveTailJoinerAssemblyEncodedInitialTape p)
      (structuredLiveTailJoinerAssemblyEncodedRestoreTape p) := by
  have hhalts :
      structuredRawTailInsertionJoinerDescription.HaltsWithTapes
        (structuredLiveTailJoinerAssemblyInitialConfig p)
        (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.restoreTailHandoffConfig
            (assemblySourceRestLiveTailEmitterEmittedPrefix p)
            (assemblySourceRestLiveTailEmitterRawTail p)
            (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes := by
    refine ⟨structuredLiveTailJoinerAssemblyRunFuel p, ?_⟩
    exact
      structuredRawTailInsertionJoinerDescription_assemblyRestoreSpec.run p
  simpa [loweredStructuredLiveTailJoinerDescription,
    structuredLiveTailJoinerAssemblyEncodedInitialTape,
    structuredLiveTailJoinerAssemblyEncodedRestoreTape] using
    Structured.MultiTapeLowering.lowerStructured3Description_haltsFromConfigWithTapes
      hready.wellFormed
      hready.haltTransitionFree
      structuredLiveTailJoinerStaticLowerer_supported
      (by rfl)
      (by rfl)
      hhalts

/-! ## Emitter endpoint components -/

def StructuredLiveTailEmitterEndpointInitializerSpec
    (initializer : MachineDescription) : Prop :=
  initializer.SubroutineReady ∧
    forall p : AssemblySourceRestLiveTailEmitterParam,
      initializer.HaltsFromTapeEquiv
        (structuredLiveTailEmitterAssemblySourceTape p)
        (structuredLiveTailEmitterAssemblyEncodedInitialTape p)

def StructuredLiveTailEmitterEndpointProjectorSpec
    (projector : MachineDescription) : Prop :=
  projector.SubroutineReady ∧
    forall p : AssemblySourceRestLiveTailEmitterParam,
      projector.HaltsFromTapeEquiv
        (structuredLiveTailEmitterAssemblyEncodedFinalTape p)
        (structuredLiveTailEmitterAssemblyTargetTape p)

def StructuredLiveTailEmitterEndpointComponentsSpec
    (initializer projector : MachineDescription) : Prop :=
  StructuredLiveTailEmitterStaticLowererReadiness ∧
    StructuredLiveTailEmitterEndpointInitializerSpec initializer ∧
    StructuredLiveTailEmitterEndpointProjectorSpec projector

def StructuredLiveTailEmitterEndpointComponentsConstruction : Prop :=
  exists initializer projector : MachineDescription,
    StructuredLiveTailEmitterEndpointComponentsSpec initializer projector

theorem StructuredLiveTailEmitterEndpointInitializerSpec.subroutineReady
    {initializer : MachineDescription}
    (h : StructuredLiveTailEmitterEndpointInitializerSpec initializer) :
    initializer.SubroutineReady :=
  h.left

theorem StructuredLiveTailEmitterEndpointInitializerSpec.run
    {initializer : MachineDescription}
    (h : StructuredLiveTailEmitterEndpointInitializerSpec initializer)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    initializer.HaltsFromTapeEquiv
      (structuredLiveTailEmitterAssemblySourceTape p)
      (structuredLiveTailEmitterAssemblyEncodedInitialTape p) :=
  h.right p

theorem StructuredLiveTailEmitterEndpointProjectorSpec.subroutineReady
    {projector : MachineDescription}
    (h : StructuredLiveTailEmitterEndpointProjectorSpec projector) :
    projector.SubroutineReady :=
  h.left

theorem StructuredLiveTailEmitterEndpointProjectorSpec.run
    {projector : MachineDescription}
    (h : StructuredLiveTailEmitterEndpointProjectorSpec projector)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    projector.HaltsFromTapeEquiv
      (structuredLiveTailEmitterAssemblyEncodedFinalTape p)
      (structuredLiveTailEmitterAssemblyTargetTape p) :=
  h.right p

theorem StructuredLiveTailEmitterEndpointComponentsSpec.readiness
    {initializer projector : MachineDescription}
    (h :
      StructuredLiveTailEmitterEndpointComponentsSpec initializer projector) :
    StructuredLiveTailEmitterStaticLowererReadiness :=
  h.left

theorem StructuredLiveTailEmitterEndpointComponentsSpec.initializer
    {initializer projector : MachineDescription}
    (h :
      StructuredLiveTailEmitterEndpointComponentsSpec initializer projector) :
    StructuredLiveTailEmitterEndpointInitializerSpec initializer :=
  h.right.left

theorem StructuredLiveTailEmitterEndpointComponentsSpec.projector
    {initializer projector : MachineDescription}
    (h :
      StructuredLiveTailEmitterEndpointComponentsSpec initializer projector) :
    StructuredLiveTailEmitterEndpointProjectorSpec projector :=
  h.right.right

def structuredLiveTailEmitterEndpointBridgeDescription
    (initializer projector : MachineDescription) : MachineDescription :=
  Structured.MultiTapeLowering.structured3EndpointBridgeDescription
    initializer loweredStructuredLiveTailEmitterDescription projector

theorem structuredLiveTailEmitterEndpointBridgeDescription_subroutineReady
    {initializer projector : MachineDescription}
    (hcomponents :
      StructuredLiveTailEmitterEndpointComponentsSpec initializer projector) :
    (structuredLiveTailEmitterEndpointBridgeDescription
      initializer projector).SubroutineReady := by
  exact
    Structured.MultiTapeLowering.structured3EndpointBridgeDescription_subroutineReady
      hcomponents.initializer.subroutineReady
      (loweredStructuredLiveTailEmitterDescription_subroutineReady
        hcomponents.readiness)
      hcomponents.projector.subroutineReady

def StructuredLiveTailEmitterEndpointBridgeSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall p : AssemblySourceRestLiveTailEmitterParam,
      finish.HaltsFromTapeEquiv
        (structuredLiveTailEmitterAssemblySourceTape p)
        (structuredLiveTailEmitterAssemblyTargetTape p)

def StructuredLiveTailEmitterEndpointBridgeConstruction : Prop :=
  exists finish : MachineDescription,
    StructuredLiveTailEmitterEndpointBridgeSpec finish

theorem structuredLiveTailEmitterEndpointBridgeDescription_spec_of_components
    {initializer projector : MachineDescription}
    (hcomponents :
      StructuredLiveTailEmitterEndpointComponentsSpec initializer projector) :
    StructuredLiveTailEmitterEndpointBridgeSpec
      (structuredLiveTailEmitterEndpointBridgeDescription
        initializer projector) := by
  constructor
  · exact
      structuredLiveTailEmitterEndpointBridgeDescription_subroutineReady
        hcomponents
  · intro p
    have hinitializer := hcomponents.initializer.run p
    have hlowered :=
      loweredStructuredLiveTailEmitterDescription_haltsFromAssemblyEncoded
        hcomponents.readiness p
    have hprojector := hcomponents.projector.run p
    simpa [structuredLiveTailEmitterEndpointBridgeDescription,
      structuredLiveTailEmitterAssemblyEncodedInitialTape_eq_encoded3,
      structuredLiveTailEmitterAssemblyEncodedFinalTape_eq_encoded3] using
      Structured.MultiTapeLowering.structured3EndpointBridgeDescription_haltsFromTapeEquiv
        hcomponents.initializer.subroutineReady
        (loweredStructuredLiveTailEmitterDescription_subroutineReady
          hcomponents.readiness)
        hcomponents.projector.subroutineReady
        hinitializer hlowered hprojector

theorem structuredLiveTailEmitterEndpointBridgeConstruction_of_components
    (hcomponents :
      StructuredLiveTailEmitterEndpointComponentsConstruction) :
    StructuredLiveTailEmitterEndpointBridgeConstruction := by
  rcases hcomponents with ⟨initializer, projector, hcomponents⟩
  exact
    ⟨structuredLiveTailEmitterEndpointBridgeDescription
        initializer projector,
      structuredLiveTailEmitterEndpointBridgeDescription_spec_of_components
        hcomponents⟩

theorem StructuredLiveTailEmitterEndpointBridgeSpec.toOutputSpec
    {finish : MachineDescription}
    (hfinish : StructuredLiveTailEmitterEndpointBridgeSpec finish) :
    MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyOutputSpec finish := by
  constructor
  · exact hfinish.left
  · intro p
    have hrun := hfinish.right p
    simpa [MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyOutputSpec,
      structuredLiveTailEmitterAssemblySourceTape,
      structuredLiveTailEmitterAssemblyTargetTape] using
      haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target hrun

theorem StructuredLiveTailEmitterEndpointBridgeConstruction.toOutputConstruction
    (h :
      StructuredLiveTailEmitterEndpointBridgeConstruction) :
    MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyOutputConstruction := by
  rcases h with ⟨finish, hfinish⟩
  exact ⟨finish, hfinish.toOutputSpec⟩

theorem MixedOptionCellQuoteLiveTailEmitterOutputConstructionForAssemblySourceRest_of_endpointComponents
    (hcomponents :
      StructuredLiveTailEmitterEndpointComponentsConstruction) :
    MixedOptionCellQuoteLiveTailEmitterOutputConstructionForAssemblySourceRest :=
  MixedOptionCellQuoteLiveTailEmitterOutputConstructionForAssemblySourceRest_of_outputFamily
    (StructuredLiveTailEmitterEndpointBridgeConstruction.toOutputConstruction
      (structuredLiveTailEmitterEndpointBridgeConstruction_of_components
        hcomponents))

/-! ## Joiner endpoint components -/

def StructuredLiveTailJoinerEndpointInitializerSpec
    (initializer : MachineDescription) : Prop :=
  initializer.SubroutineReady ∧
    forall p : AssemblySourceRestLiveTailEmitterParam,
      initializer.HaltsFromTapeEquiv
        (structuredLiveTailJoinerAssemblySourceTape p)
        (structuredLiveTailJoinerAssemblyEncodedInitialTape p)

def StructuredLiveTailJoinerEndpointProjectorSpec
    (projector : MachineDescription) : Prop :=
  projector.SubroutineReady ∧
    forall p : AssemblySourceRestLiveTailEmitterParam,
      projector.HaltsFromTapeEquiv
        (structuredLiveTailJoinerAssemblyEncodedRestoreTape p)
        (structuredLiveTailJoinerAssemblyTargetTape p)

def StructuredLiveTailJoinerEndpointComponentsSpec
    (initializer projector : MachineDescription) : Prop :=
  StructuredLiveTailJoinerStaticLowererReadiness ∧
    StructuredLiveTailJoinerEndpointInitializerSpec initializer ∧
    StructuredLiveTailJoinerEndpointProjectorSpec projector

def StructuredLiveTailJoinerEndpointComponentsConstruction : Prop :=
  exists initializer projector : MachineDescription,
    StructuredLiveTailJoinerEndpointComponentsSpec initializer projector

theorem StructuredLiveTailJoinerEndpointInitializerSpec.subroutineReady
    {initializer : MachineDescription}
    (h : StructuredLiveTailJoinerEndpointInitializerSpec initializer) :
    initializer.SubroutineReady :=
  h.left

theorem StructuredLiveTailJoinerEndpointInitializerSpec.run
    {initializer : MachineDescription}
    (h : StructuredLiveTailJoinerEndpointInitializerSpec initializer)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    initializer.HaltsFromTapeEquiv
      (structuredLiveTailJoinerAssemblySourceTape p)
      (structuredLiveTailJoinerAssemblyEncodedInitialTape p) :=
  h.right p

theorem StructuredLiveTailJoinerEndpointProjectorSpec.subroutineReady
    {projector : MachineDescription}
    (h : StructuredLiveTailJoinerEndpointProjectorSpec projector) :
    projector.SubroutineReady :=
  h.left

theorem StructuredLiveTailJoinerEndpointProjectorSpec.run
    {projector : MachineDescription}
    (h : StructuredLiveTailJoinerEndpointProjectorSpec projector)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    projector.HaltsFromTapeEquiv
      (structuredLiveTailJoinerAssemblyEncodedRestoreTape p)
      (structuredLiveTailJoinerAssemblyTargetTape p) :=
  h.right p

theorem StructuredLiveTailJoinerEndpointComponentsSpec.readiness
    {initializer projector : MachineDescription}
    (h :
      StructuredLiveTailJoinerEndpointComponentsSpec initializer projector) :
    StructuredLiveTailJoinerStaticLowererReadiness :=
  h.left

theorem StructuredLiveTailJoinerEndpointComponentsSpec.initializer
    {initializer projector : MachineDescription}
    (h :
      StructuredLiveTailJoinerEndpointComponentsSpec initializer projector) :
    StructuredLiveTailJoinerEndpointInitializerSpec initializer :=
  h.right.left

theorem StructuredLiveTailJoinerEndpointComponentsSpec.projector
    {initializer projector : MachineDescription}
    (h :
      StructuredLiveTailJoinerEndpointComponentsSpec initializer projector) :
    StructuredLiveTailJoinerEndpointProjectorSpec projector :=
  h.right.right

def structuredLiveTailJoinerEndpointBridgeDescription
    (initializer projector : MachineDescription) : MachineDescription :=
  Structured.MultiTapeLowering.canonicalPrimitiveSeqDescription
    (Structured.MultiTapeLowering.canonicalPrimitiveSeqDescription
      initializer loweredStructuredLiveTailJoinerDescription)
    projector

theorem structuredLiveTailJoinerEndpointBridgeDescription_subroutineReady
    {initializer projector : MachineDescription}
    (hcomponents :
      StructuredLiveTailJoinerEndpointComponentsSpec initializer projector) :
    (structuredLiveTailJoinerEndpointBridgeDescription
      initializer projector).SubroutineReady := by
  exact
    Structured.MultiTapeLowering.canonicalPrimitiveSeqDescription_subroutineReady
      (Structured.MultiTapeLowering.canonicalPrimitiveSeqDescription_subroutineReady
        hcomponents.initializer.subroutineReady
        (loweredStructuredLiveTailJoinerDescription_subroutineReady
          hcomponents.readiness))
      hcomponents.projector.subroutineReady

def StructuredLiveTailJoinerEndpointBridgeSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall p : AssemblySourceRestLiveTailEmitterParam,
      finish.HaltsFromTapeEquiv
        (structuredLiveTailJoinerAssemblySourceTape p)
        (structuredLiveTailJoinerAssemblyTargetTape p)

def StructuredLiveTailJoinerEndpointBridgeConstruction : Prop :=
  exists finish : MachineDescription,
    StructuredLiveTailJoinerEndpointBridgeSpec finish

theorem structuredLiveTailJoinerEndpointBridgeDescription_spec_of_components
    {initializer projector : MachineDescription}
    (hcomponents :
      StructuredLiveTailJoinerEndpointComponentsSpec initializer projector) :
    StructuredLiveTailJoinerEndpointBridgeSpec
      (structuredLiveTailJoinerEndpointBridgeDescription
        initializer projector) := by
  constructor
  · exact
      structuredLiveTailJoinerEndpointBridgeDescription_subroutineReady
        hcomponents
  · intro p
    have hinitializer := hcomponents.initializer.run p
    have hlowered :=
      loweredStructuredLiveTailJoinerDescription_haltsFromAssemblyEncoded
        hcomponents.readiness p
    have hprojector := hcomponents.projector.run p
    have hfirst :
        (Structured.MultiTapeLowering.canonicalPrimitiveSeqDescription
          initializer loweredStructuredLiveTailJoinerDescription)
            |>.HaltsFromTapeEquiv
          (structuredLiveTailJoinerAssemblySourceTape p)
          (structuredLiveTailJoinerAssemblyEncodedRestoreTape p) :=
      Structured.MultiTapeLowering.canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
        hcomponents.initializer.subroutineReady
        (loweredStructuredLiveTailJoinerDescription_subroutineReady
          hcomponents.readiness)
        hinitializer hlowered
    exact
      Structured.MultiTapeLowering.canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
        (Structured.MultiTapeLowering.canonicalPrimitiveSeqDescription_subroutineReady
          hcomponents.initializer.subroutineReady
          (loweredStructuredLiveTailJoinerDescription_subroutineReady
            hcomponents.readiness))
        hcomponents.projector.subroutineReady
        hfirst hprojector

theorem structuredLiveTailJoinerEndpointBridgeConstruction_of_components
    (hcomponents :
      StructuredLiveTailJoinerEndpointComponentsConstruction) :
    StructuredLiveTailJoinerEndpointBridgeConstruction := by
  rcases hcomponents with ⟨initializer, projector, hcomponents⟩
  exact
    ⟨structuredLiveTailJoinerEndpointBridgeDescription
        initializer projector,
      structuredLiveTailJoinerEndpointBridgeDescription_spec_of_components
        hcomponents⟩

theorem StructuredLiveTailJoinerEndpointBridgeSpec.toOutputSpec
    {finish : MachineDescription}
    (hfinish : StructuredLiveTailJoinerEndpointBridgeSpec finish) :
    StructuredLiveTailJoinerAssemblyFamilyOutputSpec finish := by
  constructor
  · exact hfinish.left
  · intro p
    have hrun := hfinish.right p
    simpa [StructuredLiveTailJoinerAssemblyFamilyOutputSpec,
      structuredLiveTailJoinerAssemblySourceTape,
      structuredLiveTailJoinerAssemblyTargetTape] using
      haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target hrun

theorem StructuredLiveTailJoinerEndpointBridgeConstruction.toOutputConstruction
    (h :
      StructuredLiveTailJoinerEndpointBridgeConstruction) :
    StructuredLiveTailJoinerAssemblyFamilyOutputConstruction := by
  rcases h with ⟨finish, hfinish⟩
  exact ⟨finish, hfinish.toOutputSpec⟩

theorem MixedOptionCellQuoteLiveTailJoinerOutputConstructionForAssemblySourceRest_of_endpointComponents
    (hcomponents :
      StructuredLiveTailJoinerEndpointComponentsConstruction) :
    MixedOptionCellQuoteLiveTailJoinerOutputConstructionForAssemblySourceRest :=
  StructuredLiveTailJoinerOutputConstructionForAssemblySourceRest_of_outputFamily
    (StructuredLiveTailJoinerEndpointBridgeConstruction.toOutputConstruction
      (structuredLiveTailJoinerEndpointBridgeConstruction_of_components
        hcomponents))

/-! ## Combined endpoint route -/

def StructuredLiveTailEndpointRouteComponentsSpec
    (emitterInitializer emitterProjector
      joinerInitializer joinerProjector : MachineDescription) : Prop :=
  StructuredLiveTailEmitterEndpointComponentsSpec
      emitterInitializer emitterProjector ∧
    StructuredLiveTailJoinerEndpointComponentsSpec
      joinerInitializer joinerProjector

def StructuredLiveTailEndpointRouteComponentsConstruction : Prop :=
  exists emitterInitializer emitterProjector
      joinerInitializer joinerProjector : MachineDescription,
    StructuredLiveTailEndpointRouteComponentsSpec
      emitterInitializer emitterProjector
      joinerInitializer joinerProjector

def StructuredLiveTailEndpointOutputRouteConstruction : Prop :=
  MixedOptionCellQuoteLiveTailEmitterOutputConstructionForAssemblySourceRest ∧
    MixedOptionCellQuoteLiveTailJoinerOutputConstructionForAssemblySourceRest

theorem StructuredLiveTailEndpointRouteComponentsSpec.emitter
    {emitterInitializer emitterProjector
      joinerInitializer joinerProjector : MachineDescription}
    (h :
      StructuredLiveTailEndpointRouteComponentsSpec
        emitterInitializer emitterProjector
        joinerInitializer joinerProjector) :
    StructuredLiveTailEmitterEndpointComponentsSpec
      emitterInitializer emitterProjector :=
  h.left

theorem StructuredLiveTailEndpointRouteComponentsSpec.joiner
    {emitterInitializer emitterProjector
      joinerInitializer joinerProjector : MachineDescription}
    (h :
      StructuredLiveTailEndpointRouteComponentsSpec
        emitterInitializer emitterProjector
        joinerInitializer joinerProjector) :
    StructuredLiveTailJoinerEndpointComponentsSpec
      joinerInitializer joinerProjector :=
  h.right

theorem structuredLiveTailEndpointOutputRouteConstruction_of_components
    (h :
      StructuredLiveTailEndpointRouteComponentsConstruction) :
    StructuredLiveTailEndpointOutputRouteConstruction := by
  rcases h with
    ⟨emitterInitializer, emitterProjector,
      joinerInitializer, joinerProjector, hroute⟩
  exact
    ⟨MixedOptionCellQuoteLiveTailEmitterOutputConstructionForAssemblySourceRest_of_endpointComponents
        ⟨emitterInitializer, emitterProjector, hroute.emitter⟩,
      MixedOptionCellQuoteLiveTailJoinerOutputConstructionForAssemblySourceRest_of_endpointComponents
        ⟨joinerInitializer, joinerProjector, hroute.joiner⟩⟩

theorem StructuredLiveTailEndpointOutputRouteConstruction.emitter
    (h : StructuredLiveTailEndpointOutputRouteConstruction) :
    MixedOptionCellQuoteLiveTailEmitterOutputConstructionForAssemblySourceRest :=
  h.left

theorem StructuredLiveTailEndpointOutputRouteConstruction.joiner
    (h : StructuredLiveTailEndpointOutputRouteConstruction) :
    MixedOptionCellQuoteLiveTailJoinerOutputConstructionForAssemblySourceRest :=
  h.right

end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC

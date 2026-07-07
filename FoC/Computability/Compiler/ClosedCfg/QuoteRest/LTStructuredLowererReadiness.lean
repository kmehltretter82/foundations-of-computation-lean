import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTableChecks
import FoC.Computability.Compiler.ClosedCfg.QuoteRest.LTEndpointContracts

set_option doc.verso true

/-!
# Live-tail structured lowerer readiness

The live-tail emitter and joiner modules already prove structured logical-tape
runs.  The endpoint route contracts keep three lower-level obligations
separate: static table readiness, public-layout initialization, and final
projection back to the assembly tape.  This module discharges the static
readiness part for the two concrete structured tables and exposes smaller
endpoint-machine contracts that no longer ask downstream code to carry
well-formedness and halt-row proofs as hypotheses.

The remaining construction leaves are therefore precisely the public endpoint
machines: an initializer from the assembly tape into the guarded three-tape
encoding, and a projector from the lowered final encoding back to the public
assembly tape.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncRewriters
namespace BoundedLayoutRunner

namespace SelectedProjectionInputQuoterFiniteLeaf

/-! ## Concrete structured table readiness -/

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_wellFormed :
    structuredMixedOptionCellQuoteLiveTailEmitterDescription.WellFormed := by
  exact
    structuredDescription_wellFormed_of_transition_checks
      structuredMixedOptionCellQuoteLiveTailEmitterDescription
      (by decide)
      (by decide)
      (by decide)
      (by decide)
      (by decide)
      (by decide)

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_haltTransitionFree :
    structuredMixedOptionCellQuoteLiveTailEmitterDescription.HaltTransitionFree :=
  structuredDescription_haltTransitionFree_of_transition_checks
    structuredMixedOptionCellQuoteLiveTailEmitterDescription
    (by decide)

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_subroutineReady :
    structuredMixedOptionCellQuoteLiveTailEmitterDescription.SubroutineReady :=
  ⟨structuredMixedOptionCellQuoteLiveTailEmitterDescription_wellFormed,
    structuredMixedOptionCellQuoteLiveTailEmitterDescription_haltTransitionFree⟩

private def structuredRawTailInsertionJoinerTransitionChunks :
    List (List Structured.Transition) :=
  open Structured.MultiTapeLowering.ThreeTape in
  [ RawTailInsertion.rowsForSourceRead RawTailInsertion.copyTail (some false)
      eraseR keepS (writeBitR false) RawTailInsertion.copyTail
  , RawTailInsertion.rowsForSourceRead RawTailInsertion.copyTail (some true)
      eraseR keepS (writeBitR true) RawTailInsertion.copyTail
  , RawTailInsertion.rowsForSourceRead RawTailInsertion.copyTail none
      keepS keepS keepS RawTailInsertion.rewindTailEntry
  , allReadRows3 RawTailInsertion.rewindTailEntry
      RawTailInsertion.rewindTailLoop keepL keepS keepL
  , RawTailInsertion.rowsForWorkRead RawTailInsertion.rewindTailLoop
      (some false) keepL keepS keepL RawTailInsertion.rewindTailLoop
  , RawTailInsertion.rowsForWorkRead RawTailInsertion.rewindTailLoop
      (some true) keepL keepS keepL RawTailInsertion.rewindTailLoop
  , RawTailInsertion.rowsForWorkRead RawTailInsertion.rewindTailLoop none
      keepR keepS keepR RawTailInsertion.rewindScratchEntry
  , allReadRows3 RawTailInsertion.rewindScratchEntry
      RawTailInsertion.rewindScratchLoop keepS keepL keepS
  , RawTailInsertion.rowsForScratchRead RawTailInsertion.rewindScratchLoop
      (some false) keepS keepL keepS
      RawTailInsertion.rewindScratchLoop
  , RawTailInsertion.rowsForScratchRead RawTailInsertion.rewindScratchLoop
      (some true) keepS keepL keepS
      RawTailInsertion.rewindScratchLoop
  , RawTailInsertion.rowsForScratchRead RawTailInsertion.rewindScratchLoop
      none keepS keepR keepS RawTailInsertion.writeInsert
  , RawTailInsertion.rowsForScratchRead RawTailInsertion.writeInsert
      (some false) (writeBitR false) keepR keepS
      RawTailInsertion.writeInsert
  , RawTailInsertion.rowsForScratchRead RawTailInsertion.writeInsert
      (some true) (writeBitR true) keepR keepS
      RawTailInsertion.writeInsert
  , RawTailInsertion.rowsForScratchRead RawTailInsertion.writeInsert none
      keepS keepS keepS RawTailInsertion.restoreTail
  , RawTailInsertion.rowsForWorkRead RawTailInsertion.restoreTail
      (some false) (writeBitR false) keepS eraseR
      RawTailInsertion.restoreTail
  , RawTailInsertion.rowsForWorkRead RawTailInsertion.restoreTail
      (some true) (writeBitR true) keepS eraseR
      RawTailInsertion.restoreTail
  , RawTailInsertion.rowsForWorkRead RawTailInsertion.restoreTail none
      eraseR keepS keepS RawTailInsertion.halt ]

private theorem structuredRawTailInsertionJoinerTransitionChunks_flatten :
    structuredRawTailInsertionJoinerTransitionChunks.flatten =
      Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.rows := by
  rfl

private theorem structuredRawTailInsertionJoinerTransitionChunks_wellFormedBool :
    structuredRawTailInsertionJoinerTransitionChunks.all
        (fun rows =>
          rows.all
            (structuredTransitionWellFormedBool
              Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.stateCount
              3)) =
      true := by
  decide

private theorem structuredRawTailInsertionJoinerTransitionChunks_deterministicBool :
    structuredTransitionChunksDeterministicBool
        structuredRawTailInsertionJoinerTransitionChunks =
      true := by
  decide

theorem structuredRawTailInsertionJoinerDescription_wellFormed :
    structuredRawTailInsertionJoinerDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
  · intro t ht
    have ht' : t ∈ structuredRawTailInsertionJoinerTransitionChunks.flatten := by
      simpa [structuredRawTailInsertionJoinerDescription,
        Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.description,
        Structured.MultiTapeLowering.ThreeTape.description,
        structuredRawTailInsertionJoinerTransitionChunks_flatten] using ht
    have hrow :=
      structuredTransition_wellFormed_of_chunk_all
        structuredRawTailInsertionJoinerTransitionChunks_wellFormedBool
        t ht'
    simpa [structuredRawTailInsertionJoinerDescription,
      Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.description,
      Structured.MultiTapeLowering.ThreeTape.description] using hrow
  · intro t u ht hu hkey
    have ht' : t ∈ structuredRawTailInsertionJoinerTransitionChunks.flatten := by
      simpa [structuredRawTailInsertionJoinerDescription,
        Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.description,
        Structured.MultiTapeLowering.ThreeTape.description,
        structuredRawTailInsertionJoinerTransitionChunks_flatten] using ht
    have hu' : u ∈ structuredRawTailInsertionJoinerTransitionChunks.flatten := by
      simpa [structuredRawTailInsertionJoinerDescription,
        Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.description,
        Structured.MultiTapeLowering.ThreeTape.description,
        structuredRawTailInsertionJoinerTransitionChunks_flatten] using hu
    exact
      structuredTransition_deterministic_of_chunk_all
        structuredRawTailInsertionJoinerTransitionChunks_deterministicBool
        t u ht' hu' hkey

theorem structuredRawTailInsertionJoinerDescription_haltTransitionFree :
    structuredRawTailInsertionJoinerDescription.HaltTransitionFree :=
  structuredDescription_haltTransitionFree_of_transition_checks
    structuredRawTailInsertionJoinerDescription
    (by decide)

theorem structuredRawTailInsertionJoinerDescription_subroutineReady :
    structuredRawTailInsertionJoinerDescription.SubroutineReady :=
  ⟨structuredRawTailInsertionJoinerDescription_wellFormed,
    structuredRawTailInsertionJoinerDescription_haltTransitionFree⟩

theorem structuredLiveTailEmitterStaticLowererReadiness :
    StructuredLiveTailEmitterStaticLowererReadiness :=
  ⟨structuredMixedOptionCellQuoteLiveTailEmitterDescription_wellFormed,
    structuredMixedOptionCellQuoteLiveTailEmitterDescription_haltTransitionFree⟩

theorem structuredLiveTailJoinerStaticLowererReadiness :
    StructuredLiveTailJoinerStaticLowererReadiness :=
  ⟨structuredRawTailInsertionJoinerDescription_wellFormed,
    structuredRawTailInsertionJoinerDescription_haltTransitionFree⟩

/-! ## Premise-free lowered structured runs -/

theorem loweredStructuredLiveTailEmitterDescription_subroutineReady_static :
    loweredStructuredLiveTailEmitterDescription.SubroutineReady :=
  loweredStructuredLiveTailEmitterDescription_subroutineReady
    structuredLiveTailEmitterStaticLowererReadiness

theorem loweredStructuredLiveTailJoinerDescription_subroutineReady_static :
    loweredStructuredLiveTailJoinerDescription.SubroutineReady :=
  loweredStructuredLiveTailJoinerDescription_subroutineReady
    structuredLiveTailJoinerStaticLowererReadiness

theorem loweredStructuredLiveTailEmitterDescription_haltsFromAssemblyEncodedWithOutput_static
    (p : AssemblySourceRestLiveTailEmitterParam)
    (outputBits : Word Bool) :
    loweredStructuredLiveTailEmitterDescription.HaltsFromTapeEquiv
      (structuredLiveTailEmitterAssemblyEncodedInitialTapeWithOutput
        p outputBits)
      (structuredLiveTailEmitterAssemblyEncodedFinalTapeWithOutput
        p outputBits) :=
  loweredStructuredLiveTailEmitterDescription_haltsFromAssemblyEncodedWithOutput
    structuredLiveTailEmitterStaticLowererReadiness p outputBits

theorem loweredStructuredLiveTailEmitterDescription_haltsFromAssemblyEncoded_static
    (p : AssemblySourceRestLiveTailEmitterParam) :
    loweredStructuredLiveTailEmitterDescription.HaltsFromTapeEquiv
      (structuredLiveTailEmitterAssemblyEncodedInitialTape p)
      (structuredLiveTailEmitterAssemblyEncodedFinalTape p) :=
  loweredStructuredLiveTailEmitterDescription_haltsFromAssemblyEncoded
    structuredLiveTailEmitterStaticLowererReadiness p

theorem loweredStructuredLiveTailJoinerDescription_haltsFromAssemblyEncoded_static
    (p : AssemblySourceRestLiveTailEmitterParam) :
    loweredStructuredLiveTailJoinerDescription.HaltsFromTapeEquiv
      (structuredLiveTailJoinerAssemblyEncodedInitialTape p)
      (structuredLiveTailJoinerAssemblyEncodedRestoreTape p) :=
  loweredStructuredLiveTailJoinerDescription_haltsFromAssemblyEncoded
    structuredLiveTailJoinerStaticLowererReadiness p

/-! ## Emitter endpoint machines without a readiness premise -/

def StructuredLiveTailEmitterEndpointMachinesSpec
    (initializer projector : MachineDescription) : Prop :=
  StructuredLiveTailEmitterEndpointInitializerSpec initializer ∧
    StructuredLiveTailEmitterEndpointProjectorSpec projector

def StructuredLiveTailEmitterEndpointMachinesConstruction : Prop :=
  exists initializer projector : MachineDescription,
    StructuredLiveTailEmitterEndpointMachinesSpec initializer projector

theorem StructuredLiveTailEmitterEndpointMachinesSpec.initializer
    {initializer projector : MachineDescription}
    (h : StructuredLiveTailEmitterEndpointMachinesSpec
      initializer projector) :
    StructuredLiveTailEmitterEndpointInitializerSpec initializer :=
  h.left

theorem StructuredLiveTailEmitterEndpointMachinesSpec.projector
    {initializer projector : MachineDescription}
    (h : StructuredLiveTailEmitterEndpointMachinesSpec
      initializer projector) :
    StructuredLiveTailEmitterEndpointProjectorSpec projector :=
  h.right

theorem StructuredLiveTailEmitterEndpointMachinesSpec.components
    {initializer projector : MachineDescription}
    (h : StructuredLiveTailEmitterEndpointMachinesSpec
      initializer projector) :
    StructuredLiveTailEmitterEndpointComponentsSpec
      initializer projector :=
  ⟨structuredLiveTailEmitterStaticLowererReadiness,
    h.initializer, h.projector⟩

theorem StructuredLiveTailEmitterEndpointMachinesSpec.bridgeSubroutineReady
    {initializer projector : MachineDescription}
    (h : StructuredLiveTailEmitterEndpointMachinesSpec
      initializer projector) :
    (structuredLiveTailEmitterEndpointBridgeDescription
      initializer projector).SubroutineReady :=
  structuredLiveTailEmitterEndpointBridgeDescription_subroutineReady
    h.components

theorem StructuredLiveTailEmitterEndpointMachinesSpec.bridgeSpec
    {initializer projector : MachineDescription}
    (h : StructuredLiveTailEmitterEndpointMachinesSpec
      initializer projector) :
    StructuredLiveTailEmitterEndpointBridgeSpec
      (structuredLiveTailEmitterEndpointBridgeDescription
        initializer projector) :=
  structuredLiveTailEmitterEndpointBridgeDescription_spec_of_components
    h.components

theorem structuredLiveTailEmitterEndpointComponentsConstruction_of_machines
    (h : StructuredLiveTailEmitterEndpointMachinesConstruction) :
    StructuredLiveTailEmitterEndpointComponentsConstruction := by
  rcases h with ⟨initializer, projector, hmachines⟩
  exact ⟨initializer, projector, hmachines.components⟩

theorem structuredLiveTailEmitterEndpointBridgeConstruction_of_machines
    (h : StructuredLiveTailEmitterEndpointMachinesConstruction) :
    StructuredLiveTailEmitterEndpointBridgeConstruction :=
  structuredLiveTailEmitterEndpointBridgeConstruction_of_components
    (structuredLiveTailEmitterEndpointComponentsConstruction_of_machines h)

theorem MixedOptionCellQuoteLiveTailEmitterOutputConstructionForAssemblySourceRest_of_endpointMachines
    (h : StructuredLiveTailEmitterEndpointMachinesConstruction) :
    MixedOptionCellQuoteLiveTailEmitterOutputConstructionForAssemblySourceRest :=
  MixedOptionCellQuoteLiveTailEmitterOutputConstructionForAssemblySourceRest_of_endpointComponents
    (structuredLiveTailEmitterEndpointComponentsConstruction_of_machines h)

/-! ## Joiner endpoint machines without a readiness premise -/

def StructuredLiveTailJoinerEndpointMachinesSpec
    (initializer projector : MachineDescription) : Prop :=
  StructuredLiveTailJoinerEndpointInitializerSpec initializer ∧
    StructuredLiveTailJoinerEndpointProjectorSpec projector

def StructuredLiveTailJoinerEndpointMachinesConstruction : Prop :=
  exists initializer projector : MachineDescription,
    StructuredLiveTailJoinerEndpointMachinesSpec initializer projector

theorem StructuredLiveTailJoinerEndpointMachinesSpec.initializer
    {initializer projector : MachineDescription}
    (h : StructuredLiveTailJoinerEndpointMachinesSpec
      initializer projector) :
    StructuredLiveTailJoinerEndpointInitializerSpec initializer :=
  h.left

theorem StructuredLiveTailJoinerEndpointMachinesSpec.projector
    {initializer projector : MachineDescription}
    (h : StructuredLiveTailJoinerEndpointMachinesSpec
      initializer projector) :
    StructuredLiveTailJoinerEndpointProjectorSpec projector :=
  h.right

theorem StructuredLiveTailJoinerEndpointMachinesSpec.components
    {initializer projector : MachineDescription}
    (h : StructuredLiveTailJoinerEndpointMachinesSpec
      initializer projector) :
    StructuredLiveTailJoinerEndpointComponentsSpec
      initializer projector :=
  ⟨structuredLiveTailJoinerStaticLowererReadiness,
    h.initializer, h.projector⟩

theorem StructuredLiveTailJoinerEndpointMachinesSpec.bridgeSubroutineReady
    {initializer projector : MachineDescription}
    (h : StructuredLiveTailJoinerEndpointMachinesSpec
      initializer projector) :
    (structuredLiveTailJoinerEndpointBridgeDescription
      initializer projector).SubroutineReady :=
  structuredLiveTailJoinerEndpointBridgeDescription_subroutineReady
    h.components

theorem StructuredLiveTailJoinerEndpointMachinesSpec.bridgeSpec
    {initializer projector : MachineDescription}
    (h : StructuredLiveTailJoinerEndpointMachinesSpec
      initializer projector) :
    StructuredLiveTailJoinerEndpointBridgeSpec
      (structuredLiveTailJoinerEndpointBridgeDescription
        initializer projector) :=
  structuredLiveTailJoinerEndpointBridgeDescription_spec_of_components
    h.components

theorem structuredLiveTailJoinerEndpointComponentsConstruction_of_machines
    (h : StructuredLiveTailJoinerEndpointMachinesConstruction) :
    StructuredLiveTailJoinerEndpointComponentsConstruction := by
  rcases h with ⟨initializer, projector, hmachines⟩
  exact ⟨initializer, projector, hmachines.components⟩

theorem structuredLiveTailJoinerEndpointBridgeConstruction_of_machines
    (h : StructuredLiveTailJoinerEndpointMachinesConstruction) :
    StructuredLiveTailJoinerEndpointBridgeConstruction :=
  structuredLiveTailJoinerEndpointBridgeConstruction_of_components
    (structuredLiveTailJoinerEndpointComponentsConstruction_of_machines h)

theorem MixedOptionCellQuoteLiveTailJoinerOutputConstructionForAssemblySourceRest_of_endpointMachines
    (h : StructuredLiveTailJoinerEndpointMachinesConstruction) :
    MixedOptionCellQuoteLiveTailJoinerOutputConstructionForAssemblySourceRest :=
  MixedOptionCellQuoteLiveTailJoinerOutputConstructionForAssemblySourceRest_of_endpointComponents
    (structuredLiveTailJoinerEndpointComponentsConstruction_of_machines h)

/-! ## Combined endpoint route without readiness premises -/

def StructuredLiveTailEndpointMachinesSpec
    (emitterInitializer emitterProjector
      joinerInitializer joinerProjector : MachineDescription) : Prop :=
  StructuredLiveTailEmitterEndpointMachinesSpec
      emitterInitializer emitterProjector ∧
    StructuredLiveTailJoinerEndpointMachinesSpec
      joinerInitializer joinerProjector

def StructuredLiveTailEndpointMachinesConstruction : Prop :=
  exists emitterInitializer emitterProjector
      joinerInitializer joinerProjector : MachineDescription,
    StructuredLiveTailEndpointMachinesSpec
      emitterInitializer emitterProjector
      joinerInitializer joinerProjector

theorem StructuredLiveTailEndpointMachinesSpec.emitter
    {emitterInitializer emitterProjector
      joinerInitializer joinerProjector : MachineDescription}
    (h :
      StructuredLiveTailEndpointMachinesSpec
        emitterInitializer emitterProjector
        joinerInitializer joinerProjector) :
    StructuredLiveTailEmitterEndpointMachinesSpec
      emitterInitializer emitterProjector :=
  h.left

theorem StructuredLiveTailEndpointMachinesSpec.joiner
    {emitterInitializer emitterProjector
      joinerInitializer joinerProjector : MachineDescription}
    (h :
      StructuredLiveTailEndpointMachinesSpec
        emitterInitializer emitterProjector
        joinerInitializer joinerProjector) :
    StructuredLiveTailJoinerEndpointMachinesSpec
      joinerInitializer joinerProjector :=
  h.right

theorem StructuredLiveTailEndpointMachinesSpec.components
    {emitterInitializer emitterProjector
      joinerInitializer joinerProjector : MachineDescription}
    (h :
      StructuredLiveTailEndpointMachinesSpec
        emitterInitializer emitterProjector
        joinerInitializer joinerProjector) :
    StructuredLiveTailEndpointRouteComponentsSpec
      emitterInitializer emitterProjector
      joinerInitializer joinerProjector :=
  ⟨h.emitter.components, h.joiner.components⟩

theorem structuredLiveTailEndpointRouteComponentsConstruction_of_machines
    (h : StructuredLiveTailEndpointMachinesConstruction) :
    StructuredLiveTailEndpointRouteComponentsConstruction := by
  rcases h with
    ⟨emitterInitializer, emitterProjector,
      joinerInitializer, joinerProjector, hmachines⟩
  exact
    ⟨emitterInitializer, emitterProjector,
      joinerInitializer, joinerProjector, hmachines.components⟩

theorem structuredLiveTailEndpointOutputRouteConstruction_of_machines
    (h : StructuredLiveTailEndpointMachinesConstruction) :
    StructuredLiveTailEndpointOutputRouteConstruction :=
  structuredLiveTailEndpointOutputRouteConstruction_of_components
    (structuredLiveTailEndpointRouteComponentsConstruction_of_machines h)

end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC

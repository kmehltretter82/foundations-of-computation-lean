import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.ExactCloseout
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.FieldDecomposition
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.KnownStateLoop
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.OtherStateLoop

set_option doc.verso true

/-!
# Guarded egress semantics

The guarded serializer runs outside the inner structured loop and reads four
independent currencies from the physical endpoint:

* preserved input and original stage from compact tape-2 metadata;
* the final state, either emitted from known finite control or recovered from
  raw metadata on the unmatched branch;
* the exact final tape window from guarded logical tape 0;
* the final hit cell and original scratch-width markers from logical tape 2.

This module proves that those parts reconstruct exactly the semantic fields
and scratch width already named by the exact-closeout semantic record.
It deliberately contains no physical serializer claim.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace RunConfigEmitterCore
namespace EgressSemantics

open FieldDecomposition

/-- Reconstruct closeout fields from preserved compact metadata and the live
post-loop configuration components. -/
def fieldsFromParts
    (M : Metadata) (state : Nat) (tape : Tape Bool) (hit : Bool) :
    ExactCloseout.Fields :=
  { input := M.input
    stage := M.stage
    config := { state := state, tape := tape }
    hit := hit }

/-- The preserved metadata code is injective. -/
theorem Metadata.encode_injective : Function.Injective Metadata.encode := by
  intro M N hcode
  have hdecode := congrArg Metadata.decode hcode
  unfold Metadata.encode at hdecode
  rw [Metadata.decode_encodeAppend, Metadata.decode_encodeAppend] at hdecode
  exact congrArg Prod.fst (Option.some.inj hdecode)

/-- Correct injectivity statement for compact metadata: equality recovers
input, original stage, and raw state. -/
theorem metadata_eq_fields_of_metadataBits_eq
    {L K : SimulatorLayout}
    (hbits : metadataBits L = metadataBits K) :
    L.input = K.input ∧
      L.stage = K.stage ∧
      L.config.state = K.config.state := by
  have hmetadata : metadata L = metadata K :=
    Metadata.encode_injective (encodeCodeWordAsInput_injective hbits)
  exact
    ⟨congrArg Metadata.input hmetadata,
      congrArg Metadata.stage hmetadata,
      congrArg Metadata.state hmetadata⟩

/-- The compact metadata plus live final components is exactly the semantic
four-field closeout record. -/
theorem fieldsFromParts_semantic
    (D : MachineDescription) (L : SimulatorLayout) :
    fieldsFromParts (metadata L)
        (SimulatorLayout.run D L.stage L).config.state
        (SimulatorLayout.run D L.stage L).config.tape
        (SimulatorLayout.run D L.stage L).hit =
      ExactCloseout.semanticFields D L := by
  cases L
  rfl

/-- Scratch markers recover the independently required original width. -/
theorem scratchWidth_of_markers
    (L : SimulatorLayout) :
    (RunConfigEmitterTheory.scratchWidthMarkers L).length =
      FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
        L := by
  exact RunConfigEmitterTheory.scratchWidthMarkers_length L

/-- On the unmatched classifier branch, the final state is the raw state
already present in compact metadata. -/
theorem finalState_eq_metadataState_of_other
    (D : MachineDescription) (L : SimulatorLayout)
    (hclass : classifyState D L.config.state = StateClass.other) :
    (SimulatorLayout.run D L.stage L).config.state =
      (metadata L).state := by
  rw [simulatorLayout_run_eq_self_of_classifyState_other
    D L L.stage hclass]
  rfl

/-- On a known branch, the final state remains in the fixed finite state list
and can therefore be emitted by a state-indexed closeout block. -/
theorem finalState_mem_fixedStepValues_of_known
    (D : MachineDescription) (L : SimulatorLayout)
    (hstate : L.config.state ∈ fixedStepValues D) :
    (SimulatorLayout.run D L.stage L).config.state ∈
      fixedStepValues D := by
  rw [← RunConfigEmitterTheory.iterateStep_seedHit_eq_run]
  exact iterateStep_config_state_mem_fixedStepValues D
    (RunConfigEmitterTheory.seedHit D L)
    (by simpa [RunConfigEmitterTheory.seedHit] using hstate)
    L.stage

/-- Total state-source split exposed to the physical closeout.  The known
branch supplies a finite-list membership witness; the other branch identifies
the final state with preserved raw metadata. -/
theorem finalState_source_cases
    (D : MachineDescription) (L : SimulatorLayout) :
    (exists hstate : L.config.state ∈ fixedStepValues D,
      classifyState D L.config.state =
          StateClass.known L.config.state hstate ∧
        (SimulatorLayout.run D L.stage L).config.state ∈
          fixedStepValues D) ∨
      (classifyState D L.config.state = StateClass.other ∧
        (SimulatorLayout.run D L.stage L).config.state =
          (metadata L).state) := by
  by_cases hstate : L.config.state ∈ fixedStepValues D
  · exact Or.inl
      ⟨hstate, classifyState_of_mem hstate,
        finalState_mem_fixedStepValues_of_known D L hstate⟩
  · have hclass := classifyState_of_not_mem hstate
    exact Or.inr
      ⟨hclass, finalState_eq_metadataState_of_other D L hclass⟩

end EgressSemantics
end RunConfigEmitterCore
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC

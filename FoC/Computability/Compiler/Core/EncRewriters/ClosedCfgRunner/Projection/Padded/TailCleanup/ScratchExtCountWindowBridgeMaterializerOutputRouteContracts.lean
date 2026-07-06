import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.TailCleanup.ScratchExtCountWindowBridgeMaterializerRouteContracts

set_option doc.verso true

/-!
# Count-window structured input materializer output-route contracts

This module mirrors the exact count-window materializer route contracts at the
normalized-output level.  It is for downstream routes that only inspect the
word emitted by the input materializer and do not depend on the final cursor
position of the guarded structured tape.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

namespace CountWindowPostFieldDecodedPrefixStructuredMaterializerOutputRouteContracts

open CountWindowPostFieldDecodedPrefixStructuredMaterializerRouteContracts

/-!
## Output route contract

The output route records the four normalized-output views of the same
count-window materializer: the indexed Boolean-word source, the bool-word
source, the public input-materializer source, and the initializer view.
-/

structure OutputRouteSpec
    (useAccept : Bool) (materializer : MachineDescription) : Prop where
  indexedOutput :
    CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerOutputSpec
      useAccept materializer
  boolWordOutput :
    CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputSpec
      useAccept materializer
  inputOutput :
    CountWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputSpec
      useAccept materializer
  initializerOutput :
    CountWindowPostFieldDecodedPrefixStructuredInputInitializerOutputSpec
      useAccept materializer

def OutputRouteConstruction : Prop :=
  forall useAccept : Bool,
    exists materializer : MachineDescription,
      OutputRouteSpec useAccept materializer

theorem outputRouteSpec_of_indexedOutputSpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerOutputSpec
        useAccept materializer) :
    OutputRouteSpec useAccept materializer := by
  have hbool :
      CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputSpec
        useAccept materializer :=
    countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputSpec_of_indexedSpec
      hmaterializer
  have hinput :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputSpec
        useAccept materializer :=
    countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputSpec_of_boolWordSpec
      hbool
  have hinitializer :
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerOutputSpec
        useAccept materializer :=
    countWindowPostFieldDecodedPrefixStructuredInputInitializerOutputSpec_of_structured3InputMaterializerOutputSpec
      hinput
  exact
    { indexedOutput := hmaterializer
      boolWordOutput := hbool
      inputOutput := hinput
      initializerOutput := hinitializer }

theorem outputRouteSpec_of_boolWordOutputSpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputSpec
        useAccept materializer) :
    OutputRouteSpec useAccept materializer :=
  outputRouteSpec_of_indexedOutputSpec
    (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerOutputSpec_of_boolWordSpec
      hmaterializer)

theorem outputRouteSpec_of_inputOutputSpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputSpec
        useAccept materializer) :
    OutputRouteSpec useAccept materializer :=
  outputRouteSpec_of_boolWordOutputSpec
    (countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputSpec_of_inputSpec
      hmaterializer)

theorem outputRouteSpec_of_initializerOutputSpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hinitializer :
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerOutputSpec
        useAccept materializer) :
    OutputRouteSpec useAccept materializer :=
  outputRouteSpec_of_inputOutputSpec
    (countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputSpec_of_initializerOutputSpec
      hinitializer)

theorem outputRouteSpec_of_exactRouteSpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hroute : ExactRouteSpec useAccept materializer) :
    OutputRouteSpec useAccept materializer :=
  outputRouteSpec_of_indexedOutputSpec
    (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerOutputSpec_of_exact
      hroute.indexedMaterializer)

theorem outputRouteSpec_of_indexedMaterializerSpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerSpec
        useAccept materializer) :
    OutputRouteSpec useAccept materializer :=
  outputRouteSpec_of_indexedOutputSpec
    (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerOutputSpec_of_exact
      hmaterializer)

theorem outputRouteSpec_of_boolWordMaterializerSpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec
        useAccept materializer) :
    OutputRouteSpec useAccept materializer :=
  outputRouteSpec_of_boolWordOutputSpec
    (countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputSpec_of_exact
      hmaterializer)

theorem outputRouteSpec_of_inputMaterializerSpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec
        useAccept materializer) :
    OutputRouteSpec useAccept materializer :=
  outputRouteSpec_of_inputOutputSpec
    (countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputSpec_of_exact
      hmaterializer)

theorem outputRouteSpec_of_inputInitializerSpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hinitializer :
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerSpec
        useAccept materializer) :
    OutputRouteSpec useAccept materializer :=
  outputRouteSpec_of_initializerOutputSpec
    (countWindowPostFieldDecodedPrefixStructuredInputInitializerOutputSpec_of_exact
      hinitializer)

/-!
## Output route construction adapters
-/

theorem outputRouteConstruction_of_indexedOutputConstruction
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerOutputConstruction) :
    OutputRouteConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      outputRouteSpec_of_indexedOutputSpec hspec⟩

theorem indexedOutputConstruction_of_outputRouteConstruction
    (hroute : OutputRouteConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerOutputConstruction := by
  intro useAccept
  rcases hroute useAccept with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.indexedOutput⟩

theorem outputRouteConstruction_iff_indexedOutputConstruction :
    OutputRouteConstruction ↔
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerOutputConstruction := by
  constructor
  · exact indexedOutputConstruction_of_outputRouteConstruction
  · exact outputRouteConstruction_of_indexedOutputConstruction

theorem outputRouteConstruction_of_boolWordOutputConstruction
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputConstruction) :
    OutputRouteConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      outputRouteSpec_of_boolWordOutputSpec hspec⟩

theorem boolWordOutputConstruction_of_outputRouteConstruction
    (hroute : OutputRouteConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputConstruction := by
  intro useAccept
  rcases hroute useAccept with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.boolWordOutput⟩

theorem outputRouteConstruction_iff_boolWordOutputConstruction :
    OutputRouteConstruction ↔
      CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputConstruction := by
  constructor
  · exact boolWordOutputConstruction_of_outputRouteConstruction
  · exact outputRouteConstruction_of_boolWordOutputConstruction

theorem outputRouteConstruction_of_inputOutputConstruction
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputConstruction) :
    OutputRouteConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      outputRouteSpec_of_inputOutputSpec hspec⟩

theorem inputOutputConstruction_of_outputRouteConstruction
    (hroute : OutputRouteConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputConstruction := by
  intro useAccept
  rcases hroute useAccept with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.inputOutput⟩

theorem outputRouteConstruction_iff_inputOutputConstruction :
    OutputRouteConstruction ↔
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputConstruction := by
  constructor
  · exact inputOutputConstruction_of_outputRouteConstruction
  · exact outputRouteConstruction_of_inputOutputConstruction

theorem outputRouteConstruction_of_initializerOutputConstruction
    (hinitializer :
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerOutputConstruction) :
    OutputRouteConstruction := by
  intro useAccept
  rcases hinitializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      outputRouteSpec_of_initializerOutputSpec hspec⟩

theorem initializerOutputConstruction_of_outputRouteConstruction
    (hroute : OutputRouteConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredInputInitializerOutputConstruction := by
  intro useAccept
  rcases hroute useAccept with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.initializerOutput⟩

theorem outputRouteConstruction_iff_initializerOutputConstruction :
    OutputRouteConstruction ↔
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerOutputConstruction := by
  constructor
  · exact initializerOutputConstruction_of_outputRouteConstruction
  · exact outputRouteConstruction_of_initializerOutputConstruction

theorem outputRouteConstruction_of_exactRouteConstruction
    (hroute : ExactRouteConstruction) :
    OutputRouteConstruction := by
  intro useAccept
  rcases hroute useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      outputRouteSpec_of_exactRouteSpec hspec⟩

theorem outputRouteConstruction_of_indexedMaterializerConstruction
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerConstruction) :
    OutputRouteConstruction :=
  outputRouteConstruction_of_exactRouteConstruction
    (exactRouteConstruction_of_indexedMaterializerConstruction hmaterializer)

theorem outputRouteConstruction_of_boolWordMaterializerConstruction
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerConstruction) :
    OutputRouteConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      outputRouteSpec_of_boolWordMaterializerSpec hspec⟩

theorem outputRouteConstruction_of_inputMaterializerConstruction
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerConstruction) :
    OutputRouteConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      outputRouteSpec_of_inputMaterializerSpec hspec⟩

theorem outputRouteConstruction_of_inputInitializerConstruction
    (hinitializer :
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction) :
    OutputRouteConstruction := by
  intro useAccept
  rcases hinitializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      outputRouteSpec_of_inputInitializerSpec hspec⟩

theorem outputRouteConstruction_core :
    OutputRouteConstruction :=
  outputRouteConstruction_of_exactRouteConstruction
    exactRouteConstruction_core

/-!
## Output branch packaging
-/

def AcceptOutputRouteSpec (materializer : MachineDescription) : Prop :=
  OutputRouteSpec true materializer

def RejectOutputRouteSpec (materializer : MachineDescription) : Prop :=
  OutputRouteSpec false materializer

def AcceptOutputRouteConstruction : Prop :=
  exists materializer : MachineDescription,
    AcceptOutputRouteSpec materializer

def RejectOutputRouteConstruction : Prop :=
  exists materializer : MachineDescription,
    RejectOutputRouteSpec materializer

def OutputRouteBranchConstruction : Prop :=
  AcceptOutputRouteConstruction ∧ RejectOutputRouteConstruction

theorem acceptOutputRouteConstruction_of_outputRouteConstruction
    (hroute : OutputRouteConstruction) :
    AcceptOutputRouteConstruction :=
  hroute true

theorem rejectOutputRouteConstruction_of_outputRouteConstruction
    (hroute : OutputRouteConstruction) :
    RejectOutputRouteConstruction :=
  hroute false

theorem outputRouteBranchConstruction_of_outputRouteConstruction
    (hroute : OutputRouteConstruction) :
    OutputRouteBranchConstruction :=
  ⟨acceptOutputRouteConstruction_of_outputRouteConstruction hroute,
    rejectOutputRouteConstruction_of_outputRouteConstruction hroute⟩

theorem outputRouteConstruction_of_branchConstruction
    (hroute : OutputRouteBranchConstruction) :
    OutputRouteConstruction := by
  intro useAccept
  cases useAccept
  · exact hroute.right
  · exact hroute.left

theorem outputRouteConstruction_iff_branchConstruction :
    OutputRouteConstruction ↔ OutputRouteBranchConstruction := by
  constructor
  · exact outputRouteBranchConstruction_of_outputRouteConstruction
  · exact outputRouteConstruction_of_branchConstruction

theorem acceptOutputRouteConstruction_of_acceptExactRouteConstruction
    (hroute : AcceptExactRouteConstruction) :
    AcceptOutputRouteConstruction := by
  rcases hroute with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      outputRouteSpec_of_exactRouteSpec hspec⟩

theorem rejectOutputRouteConstruction_of_rejectExactRouteConstruction
    (hroute : RejectExactRouteConstruction) :
    RejectOutputRouteConstruction := by
  rcases hroute with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      outputRouteSpec_of_exactRouteSpec hspec⟩

theorem outputRouteBranchConstruction_of_exactBranchConstruction
    (hroute : ExactRouteBranchConstruction) :
    OutputRouteBranchConstruction :=
  ⟨acceptOutputRouteConstruction_of_acceptExactRouteConstruction hroute.left,
    rejectOutputRouteConstruction_of_rejectExactRouteConstruction hroute.right⟩

theorem outputRouteBranchConstruction_of_exactRouteConstruction
    (hroute : ExactRouteConstruction) :
    OutputRouteBranchConstruction :=
  outputRouteBranchConstruction_of_outputRouteConstruction
    (outputRouteConstruction_of_exactRouteConstruction hroute)

theorem outputRouteBranchConstruction_of_indexedOutputConstruction
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerOutputConstruction) :
    OutputRouteBranchConstruction :=
  outputRouteBranchConstruction_of_outputRouteConstruction
    (outputRouteConstruction_of_indexedOutputConstruction hmaterializer)

theorem outputRouteBranchConstruction_of_boolWordOutputConstruction
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputConstruction) :
    OutputRouteBranchConstruction :=
  outputRouteBranchConstruction_of_outputRouteConstruction
    (outputRouteConstruction_of_boolWordOutputConstruction hmaterializer)

theorem outputRouteBranchConstruction_of_inputOutputConstruction
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputConstruction) :
    OutputRouteBranchConstruction :=
  outputRouteBranchConstruction_of_outputRouteConstruction
    (outputRouteConstruction_of_inputOutputConstruction hmaterializer)

theorem outputRouteBranchConstruction_of_initializerOutputConstruction
    (hinitializer :
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerOutputConstruction) :
    OutputRouteBranchConstruction :=
  outputRouteBranchConstruction_of_outputRouteConstruction
    (outputRouteConstruction_of_initializerOutputConstruction hinitializer)

theorem indexedOutputConstruction_of_outputRouteBranchConstruction
    (hroute : OutputRouteBranchConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerOutputConstruction :=
  indexedOutputConstruction_of_outputRouteConstruction
    (outputRouteConstruction_of_branchConstruction hroute)

theorem outputRouteBranchConstruction_iff_indexedOutputConstruction :
    OutputRouteBranchConstruction ↔
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerOutputConstruction := by
  constructor
  · exact indexedOutputConstruction_of_outputRouteBranchConstruction
  · exact outputRouteBranchConstruction_of_indexedOutputConstruction

theorem outputRouteBranchConstruction_of_indexedMaterializerConstruction
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerConstruction) :
    OutputRouteBranchConstruction :=
  outputRouteBranchConstruction_of_exactRouteConstruction
    (exactRouteConstruction_of_indexedMaterializerConstruction hmaterializer)

theorem outputRouteBranchConstruction_core :
    OutputRouteBranchConstruction :=
  outputRouteBranchConstruction_of_outputRouteConstruction
    outputRouteConstruction_core

/-!
## Branch field projections

These projections are small, but they keep later accept/reject proofs from
opening the route structure just to recover one normalized-output view.
-/

theorem acceptIndexedOutputConstruction_of_branchConstruction
    (hroute : OutputRouteBranchConstruction) :
    exists materializer : MachineDescription,
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerOutputSpec
        true materializer := by
  rcases hroute.left with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.indexedOutput⟩

theorem rejectIndexedOutputConstruction_of_branchConstruction
    (hroute : OutputRouteBranchConstruction) :
    exists materializer : MachineDescription,
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerOutputSpec
        false materializer := by
  rcases hroute.right with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.indexedOutput⟩

theorem acceptBoolWordOutputConstruction_of_branchConstruction
    (hroute : OutputRouteBranchConstruction) :
    exists materializer : MachineDescription,
      CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputSpec
        true materializer := by
  rcases hroute.left with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.boolWordOutput⟩

theorem rejectBoolWordOutputConstruction_of_branchConstruction
    (hroute : OutputRouteBranchConstruction) :
    exists materializer : MachineDescription,
      CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerOutputSpec
        false materializer := by
  rcases hroute.right with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.boolWordOutput⟩

theorem acceptInputOutputConstruction_of_branchConstruction
    (hroute : OutputRouteBranchConstruction) :
    exists materializer : MachineDescription,
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputSpec
        true materializer := by
  rcases hroute.left with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.inputOutput⟩

theorem rejectInputOutputConstruction_of_branchConstruction
    (hroute : OutputRouteBranchConstruction) :
    exists materializer : MachineDescription,
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputSpec
        false materializer := by
  rcases hroute.right with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.inputOutput⟩

theorem acceptInitializerOutputConstruction_of_branchConstruction
    (hroute : OutputRouteBranchConstruction) :
    exists materializer : MachineDescription,
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerOutputSpec
        true materializer := by
  rcases hroute.left with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.initializerOutput⟩

theorem rejectInitializerOutputConstruction_of_branchConstruction
    (hroute : OutputRouteBranchConstruction) :
    exists materializer : MachineDescription,
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerOutputSpec
        false materializer := by
  rcases hroute.right with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.initializerOutput⟩

end CountWindowPostFieldDecodedPrefixStructuredMaterializerOutputRouteContracts

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters
end Computability
end FoC

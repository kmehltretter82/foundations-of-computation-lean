import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.TailCleanup.ScratchExtCountWindowBridgeMaterializerOutputRouteContracts

set_option doc.verso true

/-!
# Count-window structured materializer branch routes

This module records branch-local projections for the count-window structured
input materializer route.  The exact route already packages all materializer,
initializer, and target-family views; the lemmas here make the accept/reject
split usable without reopening the large route structure at each downstream
handoff.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

namespace CountWindowPostFieldDecodedPrefixStructuredMaterializerBranchRouteContracts

open CountWindowPostFieldDecodedPrefixStructuredMaterializerRouteContracts
open CountWindowPostFieldDecodedPrefixStructuredMaterializerOutputRouteContracts
open CountWindowPostFieldDecodedPrefixStructuredMaterializerEndpointContracts
open CountWindowPostFieldDecodedPrefixStructuredMaterializerGenericContracts

/-!
## Exact and output route pairs

The branch construction is convenient for case splits, while the pair
construction is convenient when a caller wants to carry both branch machines as
named witnesses.
-/

structure ExactRoutePairSpec
    (acceptMaterializer rejectMaterializer : MachineDescription) : Prop where
  accept : AcceptExactRouteSpec acceptMaterializer
  reject : RejectExactRouteSpec rejectMaterializer

def ExactRoutePairConstruction : Prop :=
  exists acceptMaterializer : MachineDescription,
    exists rejectMaterializer : MachineDescription,
      ExactRoutePairSpec acceptMaterializer rejectMaterializer

structure OutputRoutePairSpec
    (acceptMaterializer rejectMaterializer : MachineDescription) : Prop where
  accept : AcceptOutputRouteSpec acceptMaterializer
  reject : RejectOutputRouteSpec rejectMaterializer

def OutputRoutePairConstruction : Prop :=
  exists acceptMaterializer : MachineDescription,
    exists rejectMaterializer : MachineDescription,
      OutputRoutePairSpec acceptMaterializer rejectMaterializer

theorem exactRoutePairConstruction_of_branchConstruction
    (hroute : ExactRouteBranchConstruction) :
    ExactRoutePairConstruction := by
  rcases hroute.left with ⟨acceptMaterializer, haccept⟩
  rcases hroute.right with ⟨rejectMaterializer, hreject⟩
  exact
    ⟨acceptMaterializer, rejectMaterializer,
      { accept := haccept, reject := hreject }⟩

theorem exactRouteBranchConstruction_of_pairConstruction
    (hroute : ExactRoutePairConstruction) :
    ExactRouteBranchConstruction := by
  rcases hroute with
    ⟨acceptMaterializer, rejectMaterializer, hspec⟩
  exact
    ⟨⟨acceptMaterializer, hspec.accept⟩,
      ⟨rejectMaterializer, hspec.reject⟩⟩

theorem exactRoutePairConstruction_iff_branchConstruction :
    ExactRoutePairConstruction ↔ ExactRouteBranchConstruction := by
  constructor
  · exact exactRouteBranchConstruction_of_pairConstruction
  · exact exactRoutePairConstruction_of_branchConstruction

theorem exactRoutePairConstruction_of_exactRouteConstruction
    (hroute : ExactRouteConstruction) :
    ExactRoutePairConstruction :=
  exactRoutePairConstruction_of_branchConstruction
    (exactRouteBranchConstruction_of_exactRouteConstruction hroute)

theorem exactRouteConstruction_of_pairConstruction
    (hroute : ExactRoutePairConstruction) :
    ExactRouteConstruction :=
  exactRouteConstruction_of_branchConstruction
    (exactRouteBranchConstruction_of_pairConstruction hroute)

theorem exactRoutePairConstruction_iff_exactRouteConstruction :
    ExactRoutePairConstruction ↔ ExactRouteConstruction := by
  constructor
  · exact exactRouteConstruction_of_pairConstruction
  · exact exactRoutePairConstruction_of_exactRouteConstruction

theorem exactRoutePairConstruction_core :
    ExactRoutePairConstruction :=
  exactRoutePairConstruction_of_exactRouteConstruction
    exactRouteConstruction_core

theorem outputRoutePairConstruction_of_outputBranchConstruction
    (hroute : OutputRouteBranchConstruction) :
    OutputRoutePairConstruction := by
  rcases hroute.left with ⟨acceptMaterializer, haccept⟩
  rcases hroute.right with ⟨rejectMaterializer, hreject⟩
  exact
    ⟨acceptMaterializer, rejectMaterializer,
      { accept := haccept, reject := hreject }⟩

theorem outputRouteBranchConstruction_of_pairConstruction
    (hroute : OutputRoutePairConstruction) :
    OutputRouteBranchConstruction := by
  rcases hroute with
    ⟨acceptMaterializer, rejectMaterializer, hspec⟩
  exact
    ⟨⟨acceptMaterializer, hspec.accept⟩,
      ⟨rejectMaterializer, hspec.reject⟩⟩

theorem outputRoutePairConstruction_iff_branchConstruction :
    OutputRoutePairConstruction ↔ OutputRouteBranchConstruction := by
  constructor
  · exact outputRouteBranchConstruction_of_pairConstruction
  · exact outputRoutePairConstruction_of_outputBranchConstruction

theorem outputRoutePairConstruction_of_outputRouteConstruction
    (hroute : OutputRouteConstruction) :
    OutputRoutePairConstruction :=
  outputRoutePairConstruction_of_outputBranchConstruction
    (outputRouteBranchConstruction_of_outputRouteConstruction hroute)

theorem outputRouteConstruction_of_pairConstruction
    (hroute : OutputRoutePairConstruction) :
    OutputRouteConstruction :=
  outputRouteConstruction_of_branchConstruction
    (outputRouteBranchConstruction_of_pairConstruction hroute)

theorem outputRoutePairConstruction_iff_outputRouteConstruction :
    OutputRoutePairConstruction ↔ OutputRouteConstruction := by
  constructor
  · exact outputRouteConstruction_of_pairConstruction
  · exact outputRoutePairConstruction_of_outputRouteConstruction

theorem outputRoutePairConstruction_of_exactPairConstruction
    (hroute : ExactRoutePairConstruction) :
    OutputRoutePairConstruction := by
  rcases hroute with
    ⟨acceptMaterializer, rejectMaterializer, hspec⟩
  exact
    ⟨acceptMaterializer, rejectMaterializer,
      { accept := outputRouteSpec_of_exactRouteSpec hspec.accept
        reject := outputRouteSpec_of_exactRouteSpec hspec.reject }⟩

theorem outputRouteBranchConstruction_of_exactPairConstruction
    (hroute : ExactRoutePairConstruction) :
    OutputRouteBranchConstruction :=
  outputRouteBranchConstruction_of_pairConstruction
    (outputRoutePairConstruction_of_exactPairConstruction hroute)

theorem outputRoutePairConstruction_of_exactBranchConstruction
    (hroute : ExactRouteBranchConstruction) :
    OutputRoutePairConstruction :=
  outputRoutePairConstruction_of_exactPairConstruction
    (exactRoutePairConstruction_of_branchConstruction hroute)

theorem outputRoutePairConstruction_of_exactRouteConstruction
    (hroute : ExactRouteConstruction) :
    OutputRoutePairConstruction :=
  outputRoutePairConstruction_of_exactPairConstruction
    (exactRoutePairConstruction_of_exactRouteConstruction hroute)

theorem outputRoutePairConstruction_core :
    OutputRoutePairConstruction :=
  outputRoutePairConstruction_of_exactRouteConstruction
    exactRouteConstruction_core

/-!
## Exact branch field projections
-/

theorem acceptIndexedMaterializerConstruction_of_branchConstruction
    (hroute : ExactRouteBranchConstruction) :
    exists materializer : MachineDescription,
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerSpec
        true materializer := by
  rcases hroute.left with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.indexedMaterializer⟩

theorem rejectIndexedMaterializerConstruction_of_branchConstruction
    (hroute : ExactRouteBranchConstruction) :
    exists materializer : MachineDescription,
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerSpec
        false materializer := by
  rcases hroute.right with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.indexedMaterializer⟩

theorem acceptBoolWordMaterializerConstruction_of_branchConstruction
    (hroute : ExactRouteBranchConstruction) :
    exists materializer : MachineDescription,
      CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec
        true materializer := by
  rcases hroute.left with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.boolWordMaterializer⟩

theorem rejectBoolWordMaterializerConstruction_of_branchConstruction
    (hroute : ExactRouteBranchConstruction) :
    exists materializer : MachineDescription,
      CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec
        false materializer := by
  rcases hroute.right with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.boolWordMaterializer⟩

theorem acceptInputMaterializerConstruction_of_branchConstruction
    (hroute : ExactRouteBranchConstruction) :
    exists materializer : MachineDescription,
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec
        true materializer := by
  rcases hroute.left with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.inputMaterializer⟩

theorem rejectInputMaterializerConstruction_of_branchConstruction
    (hroute : ExactRouteBranchConstruction) :
    exists materializer : MachineDescription,
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec
        false materializer := by
  rcases hroute.right with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.inputMaterializer⟩

theorem acceptInputInitializerConstruction_of_branchConstruction
    (hroute : ExactRouteBranchConstruction) :
    exists materializer : MachineDescription,
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerSpec
        true materializer := by
  rcases hroute.left with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.inputInitializer⟩

theorem rejectInputInitializerConstruction_of_branchConstruction
    (hroute : ExactRouteBranchConstruction) :
    exists materializer : MachineDescription,
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerSpec
        false materializer := by
  rcases hroute.right with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.inputInitializer⟩

theorem acceptGenericEndpointTargetFamilyConstruction_of_branchConstruction
    (hroute : ExactRouteBranchConstruction) :
    exists materializer : MachineDescription,
      GenericIndexedEndpointTargetFamilySpec true materializer := by
  rcases hroute.left with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.genericEndpointTarget⟩

theorem rejectGenericEndpointTargetFamilyConstruction_of_branchConstruction
    (hroute : ExactRouteBranchConstruction) :
    exists materializer : MachineDescription,
      GenericIndexedEndpointTargetFamilySpec false materializer := by
  rcases hroute.right with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.genericEndpointTarget⟩

theorem acceptGenericNamedTargetFamilyConstruction_of_branchConstruction
    (hroute : ExactRouteBranchConstruction) :
    exists materializer : MachineDescription,
      GenericIndexedNamedTargetFamilySpec true materializer := by
  rcases hroute.left with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.genericNamedTarget⟩

theorem rejectGenericNamedTargetFamilyConstruction_of_branchConstruction
    (hroute : ExactRouteBranchConstruction) :
    exists materializer : MachineDescription,
      GenericIndexedNamedTargetFamilySpec false materializer := by
  rcases hroute.right with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.genericNamedTarget⟩

theorem acceptGenericInitializerConstruction_of_branchConstruction
    (hroute : ExactRouteBranchConstruction) :
    exists materializer : MachineDescription,
      GenericIndexedInitializerSpec true materializer := by
  rcases hroute.left with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.genericInitializer⟩

theorem rejectGenericInitializerConstruction_of_branchConstruction
    (hroute : ExactRouteBranchConstruction) :
    exists materializer : MachineDescription,
      GenericIndexedInitializerSpec false materializer := by
  rcases hroute.right with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.genericInitializer⟩

theorem acceptIndexedBoolWordTargetFamilyConstruction_of_branchConstruction
    (hroute : ExactRouteBranchConstruction) :
    exists materializer : MachineDescription,
      IndexedBoolWordTargetFamilySpec true materializer := by
  rcases hroute.left with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.indexedBoolWordTarget⟩

theorem rejectIndexedBoolWordTargetFamilyConstruction_of_branchConstruction
    (hroute : ExactRouteBranchConstruction) :
    exists materializer : MachineDescription,
      IndexedBoolWordTargetFamilySpec false materializer := by
  rcases hroute.right with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.indexedBoolWordTarget⟩

theorem acceptBoolWordTargetFamilyConstruction_of_branchConstruction
    (hroute : ExactRouteBranchConstruction) :
    exists materializer : MachineDescription,
      BoolWordTargetFamilySpec true materializer := by
  rcases hroute.left with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.boolWordTarget⟩

theorem rejectBoolWordTargetFamilyConstruction_of_branchConstruction
    (hroute : ExactRouteBranchConstruction) :
    exists materializer : MachineDescription,
      BoolWordTargetFamilySpec false materializer := by
  rcases hroute.right with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.boolWordTarget⟩

theorem acceptBoolWordInputTargetFamilyConstruction_of_branchConstruction
    (hroute : ExactRouteBranchConstruction) :
    exists materializer : MachineDescription,
      BoolWordInputTargetFamilySpec true materializer := by
  rcases hroute.left with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.boolWordInputTarget⟩

theorem rejectBoolWordInputTargetFamilyConstruction_of_branchConstruction
    (hroute : ExactRouteBranchConstruction) :
    exists materializer : MachineDescription,
      BoolWordInputTargetFamilySpec false materializer := by
  rcases hroute.right with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.boolWordInputTarget⟩

theorem acceptBoolWordEncodedInputTargetFamilyConstruction_of_branchConstruction
    (hroute : ExactRouteBranchConstruction) :
    exists materializer : MachineDescription,
      BoolWordEncodedInputTargetFamilySpec true materializer := by
  rcases hroute.left with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.boolWordEncodedInputTarget⟩

theorem rejectBoolWordEncodedInputTargetFamilyConstruction_of_branchConstruction
    (hroute : ExactRouteBranchConstruction) :
    exists materializer : MachineDescription,
      BoolWordEncodedInputTargetFamilySpec false materializer := by
  rcases hroute.right with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.boolWordEncodedInputTarget⟩

theorem acceptInputTargetFamilyConstruction_of_branchConstruction
    (hroute : ExactRouteBranchConstruction) :
    exists materializer : MachineDescription,
      InputTargetFamilySpec true materializer := by
  rcases hroute.left with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.inputTarget⟩

theorem rejectInputTargetFamilyConstruction_of_branchConstruction
    (hroute : ExactRouteBranchConstruction) :
    exists materializer : MachineDescription,
      InputTargetFamilySpec false materializer := by
  rcases hroute.right with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.inputTarget⟩

theorem acceptEncodedInputTargetFamilyConstruction_of_branchConstruction
    (hroute : ExactRouteBranchConstruction) :
    exists materializer : MachineDescription,
      EncodedInputTargetFamilySpec true materializer := by
  rcases hroute.left with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.encodedInputTarget⟩

theorem rejectEncodedInputTargetFamilyConstruction_of_branchConstruction
    (hroute : ExactRouteBranchConstruction) :
    exists materializer : MachineDescription,
      EncodedInputTargetFamilySpec false materializer := by
  rcases hroute.right with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.encodedInputTarget⟩

/-!
## Exact pair field projections
-/

theorem acceptIndexedMaterializerConstruction_of_pairConstruction
    (hroute : ExactRoutePairConstruction) :
    exists materializer : MachineDescription,
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerSpec
        true materializer :=
  acceptIndexedMaterializerConstruction_of_branchConstruction
    (exactRouteBranchConstruction_of_pairConstruction hroute)

theorem rejectIndexedMaterializerConstruction_of_pairConstruction
    (hroute : ExactRoutePairConstruction) :
    exists materializer : MachineDescription,
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerSpec
        false materializer :=
  rejectIndexedMaterializerConstruction_of_branchConstruction
    (exactRouteBranchConstruction_of_pairConstruction hroute)

theorem acceptBoolWordMaterializerConstruction_of_pairConstruction
    (hroute : ExactRoutePairConstruction) :
    exists materializer : MachineDescription,
      CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec
        true materializer :=
  acceptBoolWordMaterializerConstruction_of_branchConstruction
    (exactRouteBranchConstruction_of_pairConstruction hroute)

theorem rejectBoolWordMaterializerConstruction_of_pairConstruction
    (hroute : ExactRoutePairConstruction) :
    exists materializer : MachineDescription,
      CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec
        false materializer :=
  rejectBoolWordMaterializerConstruction_of_branchConstruction
    (exactRouteBranchConstruction_of_pairConstruction hroute)

theorem acceptInputMaterializerConstruction_of_pairConstruction
    (hroute : ExactRoutePairConstruction) :
    exists materializer : MachineDescription,
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec
        true materializer :=
  acceptInputMaterializerConstruction_of_branchConstruction
    (exactRouteBranchConstruction_of_pairConstruction hroute)

theorem rejectInputMaterializerConstruction_of_pairConstruction
    (hroute : ExactRoutePairConstruction) :
    exists materializer : MachineDescription,
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec
        false materializer :=
  rejectInputMaterializerConstruction_of_branchConstruction
    (exactRouteBranchConstruction_of_pairConstruction hroute)

theorem acceptInputInitializerConstruction_of_pairConstruction
    (hroute : ExactRoutePairConstruction) :
    exists materializer : MachineDescription,
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerSpec
        true materializer :=
  acceptInputInitializerConstruction_of_branchConstruction
    (exactRouteBranchConstruction_of_pairConstruction hroute)

theorem rejectInputInitializerConstruction_of_pairConstruction
    (hroute : ExactRoutePairConstruction) :
    exists materializer : MachineDescription,
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerSpec
        false materializer :=
  rejectInputInitializerConstruction_of_branchConstruction
    (exactRouteBranchConstruction_of_pairConstruction hroute)

/-!
## Reassembling branches from field-local witnesses
-/

theorem branchConstruction_of_acceptRejectIndexedMaterializerConstructions
    (haccept :
      exists materializer : MachineDescription,
        CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerSpec
          true materializer)
    (hreject :
      exists materializer : MachineDescription,
        CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerSpec
          false materializer) :
    ExactRouteBranchConstruction := by
  constructor
  · rcases haccept with ⟨materializer, hspec⟩
    exact
      ⟨materializer,
        exactRouteSpec_of_indexedMaterializerSpec hspec⟩
  · rcases hreject with ⟨materializer, hspec⟩
    exact
      ⟨materializer,
        exactRouteSpec_of_indexedMaterializerSpec hspec⟩

theorem branchConstruction_iff_acceptRejectIndexedMaterializerConstructions :
    ExactRouteBranchConstruction ↔
      (exists materializer : MachineDescription,
        CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerSpec
          true materializer) ∧
      (exists materializer : MachineDescription,
        CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerSpec
          false materializer) := by
  constructor
  · intro hroute
    exact
      ⟨acceptIndexedMaterializerConstruction_of_branchConstruction hroute,
        rejectIndexedMaterializerConstruction_of_branchConstruction hroute⟩
  · intro hroute
    exact
      branchConstruction_of_acceptRejectIndexedMaterializerConstructions
        hroute.left hroute.right

theorem branchConstruction_of_acceptRejectBoolWordMaterializerConstructions
    (haccept :
      exists materializer : MachineDescription,
        CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec
          true materializer)
    (hreject :
      exists materializer : MachineDescription,
        CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec
          false materializer) :
    ExactRouteBranchConstruction := by
  constructor
  · rcases haccept with ⟨materializer, hspec⟩
    exact
      ⟨materializer,
        exactRouteSpec_of_boolWordMaterializerSpec hspec⟩
  · rcases hreject with ⟨materializer, hspec⟩
    exact
      ⟨materializer,
        exactRouteSpec_of_boolWordMaterializerSpec hspec⟩

theorem branchConstruction_iff_acceptRejectBoolWordMaterializerConstructions :
    ExactRouteBranchConstruction ↔
      (exists materializer : MachineDescription,
        CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec
          true materializer) ∧
      (exists materializer : MachineDescription,
        CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec
          false materializer) := by
  constructor
  · intro hroute
    exact
      ⟨acceptBoolWordMaterializerConstruction_of_branchConstruction hroute,
        rejectBoolWordMaterializerConstruction_of_branchConstruction hroute⟩
  · intro hroute
    exact
      branchConstruction_of_acceptRejectBoolWordMaterializerConstructions
        hroute.left hroute.right

theorem branchConstruction_of_acceptRejectInputMaterializerConstructions
    (haccept :
      exists materializer : MachineDescription,
        CountWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec
          true materializer)
    (hreject :
      exists materializer : MachineDescription,
        CountWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec
          false materializer) :
    ExactRouteBranchConstruction := by
  constructor
  · rcases haccept with ⟨materializer, hspec⟩
    exact
      ⟨materializer,
        exactRouteSpec_of_inputMaterializerSpec hspec⟩
  · rcases hreject with ⟨materializer, hspec⟩
    exact
      ⟨materializer,
        exactRouteSpec_of_inputMaterializerSpec hspec⟩

theorem branchConstruction_iff_acceptRejectInputMaterializerConstructions :
    ExactRouteBranchConstruction ↔
      (exists materializer : MachineDescription,
        CountWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec
          true materializer) ∧
      (exists materializer : MachineDescription,
        CountWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec
          false materializer) := by
  constructor
  · intro hroute
    exact
      ⟨acceptInputMaterializerConstruction_of_branchConstruction hroute,
        rejectInputMaterializerConstruction_of_branchConstruction hroute⟩
  · intro hroute
    exact
      branchConstruction_of_acceptRejectInputMaterializerConstructions
        hroute.left hroute.right

theorem branchConstruction_of_acceptRejectInputInitializerConstructions
    (haccept :
      exists materializer : MachineDescription,
        CountWindowPostFieldDecodedPrefixStructuredInputInitializerSpec
          true materializer)
    (hreject :
      exists materializer : MachineDescription,
        CountWindowPostFieldDecodedPrefixStructuredInputInitializerSpec
          false materializer) :
    ExactRouteBranchConstruction := by
  constructor
  · rcases haccept with ⟨materializer, hspec⟩
    exact
      ⟨materializer,
        exactRouteSpec_of_inputInitializerSpec hspec⟩
  · rcases hreject with ⟨materializer, hspec⟩
    exact
      ⟨materializer,
        exactRouteSpec_of_inputInitializerSpec hspec⟩

theorem branchConstruction_iff_acceptRejectInputInitializerConstructions :
    ExactRouteBranchConstruction ↔
      (exists materializer : MachineDescription,
        CountWindowPostFieldDecodedPrefixStructuredInputInitializerSpec
          true materializer) ∧
      (exists materializer : MachineDescription,
        CountWindowPostFieldDecodedPrefixStructuredInputInitializerSpec
          false materializer) := by
  constructor
  · intro hroute
    exact
      ⟨acceptInputInitializerConstruction_of_branchConstruction hroute,
        rejectInputInitializerConstruction_of_branchConstruction hroute⟩
  · intro hroute
    exact
      branchConstruction_of_acceptRejectInputInitializerConstructions
        hroute.left hroute.right

theorem branchConstruction_of_acceptRejectGenericEndpointTargetFamilyConstructions
    (haccept :
      exists materializer : MachineDescription,
        GenericIndexedEndpointTargetFamilySpec true materializer)
    (hreject :
      exists materializer : MachineDescription,
        GenericIndexedEndpointTargetFamilySpec false materializer) :
    ExactRouteBranchConstruction := by
  constructor
  · rcases haccept with ⟨materializer, hspec⟩
    exact
      ⟨materializer,
        exactRouteSpec_of_genericEndpointTargetFamilySpec hspec⟩
  · rcases hreject with ⟨materializer, hspec⟩
    exact
      ⟨materializer,
        exactRouteSpec_of_genericEndpointTargetFamilySpec hspec⟩

theorem branchConstruction_iff_acceptRejectGenericEndpointTargetFamilyConstructions :
    ExactRouteBranchConstruction ↔
      (exists materializer : MachineDescription,
        GenericIndexedEndpointTargetFamilySpec true materializer) ∧
      (exists materializer : MachineDescription,
        GenericIndexedEndpointTargetFamilySpec false materializer) := by
  constructor
  · intro hroute
    exact
      ⟨acceptGenericEndpointTargetFamilyConstruction_of_branchConstruction
          hroute,
        rejectGenericEndpointTargetFamilyConstruction_of_branchConstruction
          hroute⟩
  · intro hroute
    exact
      branchConstruction_of_acceptRejectGenericEndpointTargetFamilyConstructions
        hroute.left hroute.right

theorem branchConstruction_of_acceptRejectGenericNamedTargetFamilyConstructions
    (haccept :
      exists materializer : MachineDescription,
        GenericIndexedNamedTargetFamilySpec true materializer)
    (hreject :
      exists materializer : MachineDescription,
        GenericIndexedNamedTargetFamilySpec false materializer) :
    ExactRouteBranchConstruction := by
  constructor
  · rcases haccept with ⟨materializer, hspec⟩
    exact
      ⟨materializer,
        exactRouteSpec_of_genericNamedTargetFamilySpec hspec⟩
  · rcases hreject with ⟨materializer, hspec⟩
    exact
      ⟨materializer,
        exactRouteSpec_of_genericNamedTargetFamilySpec hspec⟩

theorem branchConstruction_iff_acceptRejectGenericNamedTargetFamilyConstructions :
    ExactRouteBranchConstruction ↔
      (exists materializer : MachineDescription,
        GenericIndexedNamedTargetFamilySpec true materializer) ∧
      (exists materializer : MachineDescription,
        GenericIndexedNamedTargetFamilySpec false materializer) := by
  constructor
  · intro hroute
    exact
      ⟨acceptGenericNamedTargetFamilyConstruction_of_branchConstruction
          hroute,
        rejectGenericNamedTargetFamilyConstruction_of_branchConstruction
          hroute⟩
  · intro hroute
    exact
      branchConstruction_of_acceptRejectGenericNamedTargetFamilyConstructions
        hroute.left hroute.right

theorem branchConstruction_of_acceptRejectGenericInitializerConstructions
    (haccept :
      exists materializer : MachineDescription,
        GenericIndexedInitializerSpec true materializer)
    (hreject :
      exists materializer : MachineDescription,
        GenericIndexedInitializerSpec false materializer) :
    ExactRouteBranchConstruction := by
  constructor
  · rcases haccept with ⟨materializer, hspec⟩
    exact
      ⟨materializer,
        exactRouteSpec_of_genericInitializerSpec hspec⟩
  · rcases hreject with ⟨materializer, hspec⟩
    exact
      ⟨materializer,
        exactRouteSpec_of_genericInitializerSpec hspec⟩

theorem branchConstruction_iff_acceptRejectGenericInitializerConstructions :
    ExactRouteBranchConstruction ↔
      (exists materializer : MachineDescription,
        GenericIndexedInitializerSpec true materializer) ∧
      (exists materializer : MachineDescription,
        GenericIndexedInitializerSpec false materializer) := by
  constructor
  · intro hroute
    exact
      ⟨acceptGenericInitializerConstruction_of_branchConstruction hroute,
        rejectGenericInitializerConstruction_of_branchConstruction hroute⟩
  · intro hroute
    exact
      branchConstruction_of_acceptRejectGenericInitializerConstructions
        hroute.left hroute.right

theorem branchConstruction_of_acceptRejectIndexedBoolWordTargetFamilyConstructions
    (haccept :
      exists materializer : MachineDescription,
        IndexedBoolWordTargetFamilySpec true materializer)
    (hreject :
      exists materializer : MachineDescription,
        IndexedBoolWordTargetFamilySpec false materializer) :
    ExactRouteBranchConstruction := by
  constructor
  · rcases haccept with ⟨materializer, hspec⟩
    exact
      ⟨materializer,
        exactRouteSpec_of_indexedBoolWordTargetFamilySpec hspec⟩
  · rcases hreject with ⟨materializer, hspec⟩
    exact
      ⟨materializer,
        exactRouteSpec_of_indexedBoolWordTargetFamilySpec hspec⟩

theorem branchConstruction_iff_acceptRejectIndexedBoolWordTargetFamilyConstructions :
    ExactRouteBranchConstruction ↔
      (exists materializer : MachineDescription,
        IndexedBoolWordTargetFamilySpec true materializer) ∧
      (exists materializer : MachineDescription,
        IndexedBoolWordTargetFamilySpec false materializer) := by
  constructor
  · intro hroute
    exact
      ⟨acceptIndexedBoolWordTargetFamilyConstruction_of_branchConstruction
          hroute,
        rejectIndexedBoolWordTargetFamilyConstruction_of_branchConstruction
          hroute⟩
  · intro hroute
    exact
      branchConstruction_of_acceptRejectIndexedBoolWordTargetFamilyConstructions
        hroute.left hroute.right

theorem branchConstruction_of_acceptRejectBoolWordTargetFamilyConstructions
    (haccept :
      exists materializer : MachineDescription,
        BoolWordTargetFamilySpec true materializer)
    (hreject :
      exists materializer : MachineDescription,
        BoolWordTargetFamilySpec false materializer) :
    ExactRouteBranchConstruction := by
  constructor
  · rcases haccept with ⟨materializer, hspec⟩
    exact
      ⟨materializer,
        exactRouteSpec_of_boolWordTargetFamilySpec hspec⟩
  · rcases hreject with ⟨materializer, hspec⟩
    exact
      ⟨materializer,
        exactRouteSpec_of_boolWordTargetFamilySpec hspec⟩

theorem branchConstruction_iff_acceptRejectBoolWordTargetFamilyConstructions :
    ExactRouteBranchConstruction ↔
      (exists materializer : MachineDescription,
        BoolWordTargetFamilySpec true materializer) ∧
      (exists materializer : MachineDescription,
        BoolWordTargetFamilySpec false materializer) := by
  constructor
  · intro hroute
    exact
      ⟨acceptBoolWordTargetFamilyConstruction_of_branchConstruction
          hroute,
        rejectBoolWordTargetFamilyConstruction_of_branchConstruction
          hroute⟩
  · intro hroute
    exact
      branchConstruction_of_acceptRejectBoolWordTargetFamilyConstructions
        hroute.left hroute.right

theorem branchConstruction_of_acceptRejectBoolWordInputTargetFamilyConstructions
    (haccept :
      exists materializer : MachineDescription,
        BoolWordInputTargetFamilySpec true materializer)
    (hreject :
      exists materializer : MachineDescription,
        BoolWordInputTargetFamilySpec false materializer) :
    ExactRouteBranchConstruction := by
  constructor
  · rcases haccept with ⟨materializer, hspec⟩
    exact
      ⟨materializer,
        exactRouteSpec_of_boolWordInputTargetFamilySpec hspec⟩
  · rcases hreject with ⟨materializer, hspec⟩
    exact
      ⟨materializer,
        exactRouteSpec_of_boolWordInputTargetFamilySpec hspec⟩

theorem branchConstruction_iff_acceptRejectBoolWordInputTargetFamilyConstructions :
    ExactRouteBranchConstruction ↔
      (exists materializer : MachineDescription,
        BoolWordInputTargetFamilySpec true materializer) ∧
      (exists materializer : MachineDescription,
        BoolWordInputTargetFamilySpec false materializer) := by
  constructor
  · intro hroute
    exact
      ⟨acceptBoolWordInputTargetFamilyConstruction_of_branchConstruction
          hroute,
        rejectBoolWordInputTargetFamilyConstruction_of_branchConstruction
          hroute⟩
  · intro hroute
    exact
      branchConstruction_of_acceptRejectBoolWordInputTargetFamilyConstructions
        hroute.left hroute.right

theorem branchConstruction_of_acceptRejectBoolWordEncodedInputTargetFamilyConstructions
    (haccept :
      exists materializer : MachineDescription,
        BoolWordEncodedInputTargetFamilySpec true materializer)
    (hreject :
      exists materializer : MachineDescription,
        BoolWordEncodedInputTargetFamilySpec false materializer) :
    ExactRouteBranchConstruction := by
  constructor
  · rcases haccept with ⟨materializer, hspec⟩
    exact
      ⟨materializer,
        exactRouteSpec_of_boolWordEncodedInputTargetFamilySpec hspec⟩
  · rcases hreject with ⟨materializer, hspec⟩
    exact
      ⟨materializer,
        exactRouteSpec_of_boolWordEncodedInputTargetFamilySpec hspec⟩

theorem branchConstruction_iff_acceptRejectBoolWordEncodedInputTargetFamilyConstructions :
    ExactRouteBranchConstruction ↔
      (exists materializer : MachineDescription,
        BoolWordEncodedInputTargetFamilySpec true materializer) ∧
      (exists materializer : MachineDescription,
        BoolWordEncodedInputTargetFamilySpec false materializer) := by
  constructor
  · intro hroute
    exact
      ⟨acceptBoolWordEncodedInputTargetFamilyConstruction_of_branchConstruction
          hroute,
        rejectBoolWordEncodedInputTargetFamilyConstruction_of_branchConstruction
          hroute⟩
  · intro hroute
    exact
      branchConstruction_of_acceptRejectBoolWordEncodedInputTargetFamilyConstructions
        hroute.left hroute.right

theorem branchConstruction_of_acceptRejectInputTargetFamilyConstructions
    (haccept :
      exists materializer : MachineDescription,
        InputTargetFamilySpec true materializer)
    (hreject :
      exists materializer : MachineDescription,
        InputTargetFamilySpec false materializer) :
    ExactRouteBranchConstruction := by
  constructor
  · rcases haccept with ⟨materializer, hspec⟩
    exact
      ⟨materializer,
        exactRouteSpec_of_inputTargetFamilySpec hspec⟩
  · rcases hreject with ⟨materializer, hspec⟩
    exact
      ⟨materializer,
        exactRouteSpec_of_inputTargetFamilySpec hspec⟩

theorem branchConstruction_iff_acceptRejectInputTargetFamilyConstructions :
    ExactRouteBranchConstruction ↔
      (exists materializer : MachineDescription,
        InputTargetFamilySpec true materializer) ∧
      (exists materializer : MachineDescription,
        InputTargetFamilySpec false materializer) := by
  constructor
  · intro hroute
    exact
      ⟨acceptInputTargetFamilyConstruction_of_branchConstruction hroute,
        rejectInputTargetFamilyConstruction_of_branchConstruction hroute⟩
  · intro hroute
    exact
      branchConstruction_of_acceptRejectInputTargetFamilyConstructions
        hroute.left hroute.right

theorem branchConstruction_of_acceptRejectEncodedInputTargetFamilyConstructions
    (haccept :
      exists materializer : MachineDescription,
        EncodedInputTargetFamilySpec true materializer)
    (hreject :
      exists materializer : MachineDescription,
        EncodedInputTargetFamilySpec false materializer) :
    ExactRouteBranchConstruction := by
  constructor
  · rcases haccept with ⟨materializer, hspec⟩
    exact
      ⟨materializer,
        exactRouteSpec_of_encodedInputTargetFamilySpec hspec⟩
  · rcases hreject with ⟨materializer, hspec⟩
    exact
      ⟨materializer,
        exactRouteSpec_of_encodedInputTargetFamilySpec hspec⟩

theorem branchConstruction_iff_acceptRejectEncodedInputTargetFamilyConstructions :
    ExactRouteBranchConstruction ↔
      (exists materializer : MachineDescription,
        EncodedInputTargetFamilySpec true materializer) ∧
      (exists materializer : MachineDescription,
        EncodedInputTargetFamilySpec false materializer) := by
  constructor
  · intro hroute
    exact
      ⟨acceptEncodedInputTargetFamilyConstruction_of_branchConstruction
          hroute,
        rejectEncodedInputTargetFamilyConstruction_of_branchConstruction
          hroute⟩
  · intro hroute
    exact
      branchConstruction_of_acceptRejectEncodedInputTargetFamilyConstructions
        hroute.left hroute.right

/-!
## Core branch projections
-/

theorem acceptIndexedMaterializerConstruction_core :
    exists materializer : MachineDescription,
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerSpec
        true materializer :=
  acceptIndexedMaterializerConstruction_of_branchConstruction
    branchConstruction_core

theorem rejectIndexedMaterializerConstruction_core :
    exists materializer : MachineDescription,
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerSpec
        false materializer :=
  rejectIndexedMaterializerConstruction_of_branchConstruction
    branchConstruction_core

theorem acceptInputInitializerConstruction_core :
    exists materializer : MachineDescription,
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerSpec
        true materializer :=
  acceptInputInitializerConstruction_of_branchConstruction
    branchConstruction_core

theorem rejectInputInitializerConstruction_core :
    exists materializer : MachineDescription,
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerSpec
        false materializer :=
  rejectInputInitializerConstruction_of_branchConstruction
    branchConstruction_core

end CountWindowPostFieldDecodedPrefixStructuredMaterializerBranchRouteContracts

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters
end Computability
end FoC

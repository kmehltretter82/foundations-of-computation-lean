import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.Mat.Output

set_option doc.verso true

/-!
# Count-window structured input materializer route contracts

This module packages the endpoint, target-family, exact materializer, and
normalized-output views of the count-window structured input materializer into
route-level contracts.  The remaining finite-machine leaf is still the indexed
Boolean-word materializer; these route contracts make that leaf usable from the
accept/reject branch surface and from output-only downstream routes without
reopening the large bridge module.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

namespace CountWindowPostFieldDecodedPrefixStructuredMaterializerRouteContracts

open CountWindowPostFieldDecodedPrefixStructuredMaterializerEndpointContracts
open CountWindowPostFieldDecodedPrefixStructuredMaterializerGenericContracts

/-!
## Exact route contract

The exact route contract is intentionally redundant.  Each field names one
view that later bridge proofs commonly need after splitting on the
{lit}`useAccept` branch.  The constructor below proves that all fields are just
adapters around the indexed bool-word materializer specification.
-/

structure ExactRouteSpec
    (useAccept : Bool) (materializer : MachineDescription) : Prop where
  indexedMaterializer :
    CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerSpec
      useAccept materializer
  boolWordMaterializer :
    CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec
      useAccept materializer
  inputMaterializer :
    CountWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec
      useAccept materializer
  inputInitializer :
    CountWindowPostFieldDecodedPrefixStructuredInputInitializerSpec
      useAccept materializer
  genericEndpointTarget :
    GenericIndexedEndpointTargetFamilySpec useAccept materializer
  genericNamedTarget :
    GenericIndexedNamedTargetFamilySpec useAccept materializer
  genericInitializer :
    GenericIndexedInitializerSpec useAccept materializer
  indexedBoolWordTarget :
    IndexedBoolWordTargetFamilySpec useAccept materializer
  boolWordTarget :
    BoolWordTargetFamilySpec useAccept materializer
  boolWordInputTarget :
    BoolWordInputTargetFamilySpec useAccept materializer
  boolWordEncodedInputTarget :
    BoolWordEncodedInputTargetFamilySpec useAccept materializer
  inputTarget :
    InputTargetFamilySpec useAccept materializer
  encodedInputTarget :
    EncodedInputTargetFamilySpec useAccept materializer

def ExactRouteConstruction : Prop :=
  forall useAccept : Bool,
    exists materializer : MachineDescription,
      ExactRouteSpec useAccept materializer

theorem exactRouteSpec_of_indexedMaterializerSpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerSpec
        useAccept materializer) :
    ExactRouteSpec useAccept materializer := by
  have hbool :
      CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec
        useAccept materializer :=
    countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec_of_indexedSpec
      hmaterializer
  have hinput :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec
        useAccept materializer :=
    countWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec_of_boolWordSpec
      hbool
  have hinitializer :
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerSpec
        useAccept materializer :=
    countWindowPostFieldDecodedPrefixStructuredInputInitializerSpec_of_structured3InputMaterializerSpec
      hinput
  have hgeneric :
      GenericIndexedEndpointTargetFamilySpec useAccept materializer :=
    genericEndpointTargetFamilySpec_of_indexedMaterializerSpec
      hmaterializer
  have hgenericNamed :
      GenericIndexedNamedTargetFamilySpec useAccept materializer :=
    genericNamedTargetFamilySpec_of_endpointTargetFamilySpec
      hgeneric
  have hgenericInitializer :
      GenericIndexedInitializerSpec useAccept materializer :=
    genericInitializerSpec_of_namedTargetFamilySpec
      hgenericNamed
  have hindexedTarget :
      IndexedBoolWordTargetFamilySpec useAccept materializer :=
    indexedBoolWordTargetFamilySpec_of_indexedBoolWordMaterializerSpec
      hmaterializer
  have hboolTarget :
      BoolWordTargetFamilySpec useAccept materializer :=
    boolWordTargetFamilySpec_of_indexedBoolWordTargetFamilySpec
      hindexedTarget
  have hboolInputTarget :
      BoolWordInputTargetFamilySpec useAccept materializer :=
    boolWordInputTargetFamilySpec_of_boolWordTargetFamilySpec
      hboolTarget
  have hboolEncodedTarget :
      BoolWordEncodedInputTargetFamilySpec useAccept materializer :=
    boolWordEncodedInputTargetFamilySpec_of_boolWordInputTargetFamilySpec
      hboolInputTarget
  have hinputTarget :
      InputTargetFamilySpec useAccept materializer :=
    inputTargetFamilySpec_of_genericEndpointTargetFamilySpec
      hgeneric
  have hencodedTarget :
      EncodedInputTargetFamilySpec useAccept materializer :=
    encodedInputTargetFamilySpec_of_genericEndpointTargetFamilySpec
      hgeneric
  exact
    { indexedMaterializer := hmaterializer
      boolWordMaterializer := hbool
      inputMaterializer := hinput
      inputInitializer := hinitializer
      genericEndpointTarget := hgeneric
      genericNamedTarget := hgenericNamed
      genericInitializer := hgenericInitializer
      indexedBoolWordTarget := hindexedTarget
      boolWordTarget := hboolTarget
      boolWordInputTarget := hboolInputTarget
      boolWordEncodedInputTarget := hboolEncodedTarget
      inputTarget := hinputTarget
      encodedInputTarget := hencodedTarget }

theorem exactRouteSpec_of_boolWordMaterializerSpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec
        useAccept materializer) :
    ExactRouteSpec useAccept materializer :=
  exactRouteSpec_of_indexedMaterializerSpec
    (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerSpec_of_boolWordSpec
      hmaterializer)

theorem exactRouteSpec_of_inputMaterializerSpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec
        useAccept materializer) :
    ExactRouteSpec useAccept materializer :=
  exactRouteSpec_of_boolWordMaterializerSpec
    (countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec_of_inputSpec
      hmaterializer)

theorem exactRouteSpec_of_inputInitializerSpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hinitializer :
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerSpec
        useAccept materializer) :
    ExactRouteSpec useAccept materializer :=
  exactRouteSpec_of_inputMaterializerSpec
    (countWindowPostFieldDecodedPrefixStructuredInputMaterializerSpec_of_initializerSpec
      hinitializer)

theorem exactRouteSpec_of_genericEndpointTargetFamilySpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      GenericIndexedEndpointTargetFamilySpec useAccept materializer) :
    ExactRouteSpec useAccept materializer :=
  exactRouteSpec_of_indexedMaterializerSpec
    (indexedMaterializerSpec_of_genericEndpointTargetFamilySpec
      hmaterializer)

theorem exactRouteSpec_of_genericNamedTargetFamilySpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      GenericIndexedNamedTargetFamilySpec useAccept materializer) :
    ExactRouteSpec useAccept materializer :=
  exactRouteSpec_of_genericEndpointTargetFamilySpec
    (genericEndpointTargetFamilySpec_of_namedTargetFamilySpec
      hmaterializer)

theorem exactRouteSpec_of_genericInitializerSpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hinitializer :
      GenericIndexedInitializerSpec useAccept materializer) :
    ExactRouteSpec useAccept materializer :=
  exactRouteSpec_of_genericNamedTargetFamilySpec
    (genericNamedTargetFamilySpec_of_initializerSpec
      hinitializer)

theorem exactRouteSpec_of_indexedBoolWordTargetFamilySpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      IndexedBoolWordTargetFamilySpec useAccept materializer) :
    ExactRouteSpec useAccept materializer :=
  exactRouteSpec_of_indexedMaterializerSpec
    (indexedBoolWordMaterializerSpec_of_indexedBoolWordTargetFamilySpec
      hmaterializer)

theorem exactRouteSpec_of_boolWordTargetFamilySpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      BoolWordTargetFamilySpec useAccept materializer) :
    ExactRouteSpec useAccept materializer :=
  exactRouteSpec_of_indexedBoolWordTargetFamilySpec
    (indexedBoolWordTargetFamilySpec_of_boolWordTargetFamilySpec
      hmaterializer)

theorem exactRouteSpec_of_boolWordInputTargetFamilySpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      BoolWordInputTargetFamilySpec useAccept materializer) :
    ExactRouteSpec useAccept materializer :=
  exactRouteSpec_of_boolWordTargetFamilySpec
    (boolWordTargetFamilySpec_of_boolWordInputTargetFamilySpec
      hmaterializer)

theorem exactRouteSpec_of_boolWordEncodedInputTargetFamilySpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      BoolWordEncodedInputTargetFamilySpec useAccept materializer) :
    ExactRouteSpec useAccept materializer :=
  exactRouteSpec_of_genericEndpointTargetFamilySpec
    (genericEndpointTargetFamilySpec_of_boolWordEncodedInputTargetFamilySpec
      hmaterializer)

theorem exactRouteSpec_of_inputTargetFamilySpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      InputTargetFamilySpec useAccept materializer) :
    ExactRouteSpec useAccept materializer :=
  exactRouteSpec_of_inputMaterializerSpec
    (inputMaterializerSpec_of_inputTargetFamilySpec hmaterializer)

theorem exactRouteSpec_of_encodedInputTargetFamilySpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      EncodedInputTargetFamilySpec useAccept materializer) :
    ExactRouteSpec useAccept materializer :=
  exactRouteSpec_of_inputMaterializerSpec
    (inputMaterializerSpec_of_encodedInputTargetFamilySpec hmaterializer)

/-!
## Exact route construction adapters
-/

theorem exactRouteConstruction_of_indexedMaterializerConstruction
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerConstruction) :
    ExactRouteConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      exactRouteSpec_of_indexedMaterializerSpec hspec⟩

theorem indexedMaterializerConstruction_of_exactRouteConstruction
    (hroute : ExactRouteConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerConstruction := by
  intro useAccept
  rcases hroute useAccept with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.indexedMaterializer⟩

theorem exactRouteConstruction_iff_indexedMaterializerConstruction :
    ExactRouteConstruction ↔
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerConstruction := by
  constructor
  · exact indexedMaterializerConstruction_of_exactRouteConstruction
  · exact exactRouteConstruction_of_indexedMaterializerConstruction

theorem exactRouteConstruction_of_boolWordMaterializerConstruction
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerConstruction) :
    ExactRouteConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      exactRouteSpec_of_boolWordMaterializerSpec hspec⟩

theorem boolWordMaterializerConstruction_of_exactRouteConstruction
    (hroute : ExactRouteConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerConstruction := by
  intro useAccept
  rcases hroute useAccept with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.boolWordMaterializer⟩

theorem exactRouteConstruction_iff_boolWordMaterializerConstruction :
    ExactRouteConstruction ↔
      CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerConstruction := by
  constructor
  · exact boolWordMaterializerConstruction_of_exactRouteConstruction
  · exact exactRouteConstruction_of_boolWordMaterializerConstruction

theorem exactRouteConstruction_of_inputMaterializerConstruction
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerConstruction) :
    ExactRouteConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      exactRouteSpec_of_inputMaterializerSpec hspec⟩

theorem inputMaterializerConstruction_of_exactRouteConstruction
    (hroute : ExactRouteConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredInputMaterializerConstruction := by
  intro useAccept
  rcases hroute useAccept with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.inputMaterializer⟩

theorem exactRouteConstruction_iff_inputMaterializerConstruction :
    ExactRouteConstruction ↔
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerConstruction := by
  constructor
  · exact inputMaterializerConstruction_of_exactRouteConstruction
  · exact exactRouteConstruction_of_inputMaterializerConstruction

theorem exactRouteConstruction_of_inputInitializerConstruction
    (hinitializer :
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction) :
    ExactRouteConstruction := by
  intro useAccept
  rcases hinitializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      exactRouteSpec_of_inputInitializerSpec hspec⟩

theorem inputInitializerConstruction_of_exactRouteConstruction
    (hroute : ExactRouteConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction := by
  intro useAccept
  rcases hroute useAccept with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.inputInitializer⟩

theorem exactRouteConstruction_iff_inputInitializerConstruction :
    ExactRouteConstruction ↔
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction := by
  constructor
  · exact inputInitializerConstruction_of_exactRouteConstruction
  · exact exactRouteConstruction_of_inputInitializerConstruction

theorem exactRouteConstruction_of_genericEndpointTargetFamilyConstruction
    (hmaterializer :
      GenericIndexedEndpointTargetFamilyConstruction) :
    ExactRouteConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      exactRouteSpec_of_genericEndpointTargetFamilySpec hspec⟩

theorem genericEndpointTargetFamilyConstruction_of_exactRouteConstruction
    (hroute : ExactRouteConstruction) :
    GenericIndexedEndpointTargetFamilyConstruction := by
  intro useAccept
  rcases hroute useAccept with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.genericEndpointTarget⟩

theorem exactRouteConstruction_iff_genericEndpointTargetFamilyConstruction :
    ExactRouteConstruction ↔
      GenericIndexedEndpointTargetFamilyConstruction := by
  constructor
  · exact genericEndpointTargetFamilyConstruction_of_exactRouteConstruction
  · exact exactRouteConstruction_of_genericEndpointTargetFamilyConstruction

theorem exactRouteConstruction_of_genericNamedTargetFamilyConstruction
    (hmaterializer :
      GenericIndexedNamedTargetFamilyConstruction) :
    ExactRouteConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      exactRouteSpec_of_genericNamedTargetFamilySpec hspec⟩

theorem genericNamedTargetFamilyConstruction_of_exactRouteConstruction
    (hroute : ExactRouteConstruction) :
    GenericIndexedNamedTargetFamilyConstruction := by
  intro useAccept
  rcases hroute useAccept with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.genericNamedTarget⟩

theorem exactRouteConstruction_iff_genericNamedTargetFamilyConstruction :
    ExactRouteConstruction ↔
      GenericIndexedNamedTargetFamilyConstruction := by
  constructor
  · exact genericNamedTargetFamilyConstruction_of_exactRouteConstruction
  · exact exactRouteConstruction_of_genericNamedTargetFamilyConstruction

theorem exactRouteConstruction_of_genericInitializerConstruction
    (hinitializer :
      GenericIndexedInitializerConstruction) :
    ExactRouteConstruction := by
  intro useAccept
  rcases hinitializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      exactRouteSpec_of_genericInitializerSpec hspec⟩

theorem genericInitializerConstruction_of_exactRouteConstruction
    (hroute : ExactRouteConstruction) :
    GenericIndexedInitializerConstruction := by
  intro useAccept
  rcases hroute useAccept with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.genericInitializer⟩

theorem exactRouteConstruction_iff_genericInitializerConstruction :
    ExactRouteConstruction ↔ GenericIndexedInitializerConstruction := by
  constructor
  · exact genericInitializerConstruction_of_exactRouteConstruction
  · exact exactRouteConstruction_of_genericInitializerConstruction

theorem exactRouteConstruction_of_indexedBoolWordTargetFamilyConstruction
    (hmaterializer : IndexedBoolWordTargetFamilyConstruction) :
    ExactRouteConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      exactRouteSpec_of_indexedBoolWordTargetFamilySpec hspec⟩

theorem indexedBoolWordTargetFamilyConstruction_of_exactRouteConstruction
    (hroute : ExactRouteConstruction) :
    IndexedBoolWordTargetFamilyConstruction := by
  intro useAccept
  rcases hroute useAccept with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.indexedBoolWordTarget⟩

theorem exactRouteConstruction_iff_indexedBoolWordTargetFamilyConstruction :
    ExactRouteConstruction ↔ IndexedBoolWordTargetFamilyConstruction := by
  constructor
  · exact indexedBoolWordTargetFamilyConstruction_of_exactRouteConstruction
  · exact exactRouteConstruction_of_indexedBoolWordTargetFamilyConstruction

theorem exactRouteConstruction_of_boolWordTargetFamilyConstruction
    (hmaterializer : BoolWordTargetFamilyConstruction) :
    ExactRouteConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      exactRouteSpec_of_boolWordTargetFamilySpec hspec⟩

theorem boolWordTargetFamilyConstruction_of_exactRouteConstruction
    (hroute : ExactRouteConstruction) :
    BoolWordTargetFamilyConstruction := by
  intro useAccept
  rcases hroute useAccept with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.boolWordTarget⟩

theorem exactRouteConstruction_iff_boolWordTargetFamilyConstruction :
    ExactRouteConstruction ↔ BoolWordTargetFamilyConstruction := by
  constructor
  · exact boolWordTargetFamilyConstruction_of_exactRouteConstruction
  · exact exactRouteConstruction_of_boolWordTargetFamilyConstruction

theorem exactRouteConstruction_of_boolWordEncodedInputTargetFamilyConstruction
    (hmaterializer : BoolWordEncodedInputTargetFamilyConstruction) :
    ExactRouteConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      exactRouteSpec_of_boolWordEncodedInputTargetFamilySpec hspec⟩

theorem boolWordEncodedInputTargetFamilyConstruction_of_exactRouteConstruction
    (hroute : ExactRouteConstruction) :
    BoolWordEncodedInputTargetFamilyConstruction := by
  intro useAccept
  rcases hroute useAccept with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.boolWordEncodedInputTarget⟩

theorem exactRouteConstruction_iff_boolWordEncodedInputTargetFamilyConstruction :
    ExactRouteConstruction ↔ BoolWordEncodedInputTargetFamilyConstruction := by
  constructor
  · exact boolWordEncodedInputTargetFamilyConstruction_of_exactRouteConstruction
  · exact exactRouteConstruction_of_boolWordEncodedInputTargetFamilyConstruction

theorem exactRouteConstruction_of_inputTargetFamilyConstruction
    (hmaterializer : InputTargetFamilyConstruction) :
    ExactRouteConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      exactRouteSpec_of_inputTargetFamilySpec hspec⟩

theorem inputTargetFamilyConstruction_of_exactRouteConstruction
    (hroute : ExactRouteConstruction) :
    InputTargetFamilyConstruction := by
  intro useAccept
  rcases hroute useAccept with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.inputTarget⟩

theorem exactRouteConstruction_iff_inputTargetFamilyConstruction :
    ExactRouteConstruction ↔ InputTargetFamilyConstruction := by
  constructor
  · exact inputTargetFamilyConstruction_of_exactRouteConstruction
  · exact exactRouteConstruction_of_inputTargetFamilyConstruction

theorem exactRouteConstruction_of_encodedInputTargetFamilyConstruction
    (hmaterializer : EncodedInputTargetFamilyConstruction) :
    ExactRouteConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      exactRouteSpec_of_encodedInputTargetFamilySpec hspec⟩

theorem encodedInputTargetFamilyConstruction_of_exactRouteConstruction
    (hroute : ExactRouteConstruction) :
    EncodedInputTargetFamilyConstruction := by
  intro useAccept
  rcases hroute useAccept with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.encodedInputTarget⟩

theorem exactRouteConstruction_iff_encodedInputTargetFamilyConstruction :
    ExactRouteConstruction ↔ EncodedInputTargetFamilyConstruction := by
  constructor
  · exact encodedInputTargetFamilyConstruction_of_exactRouteConstruction
  · exact exactRouteConstruction_of_encodedInputTargetFamilyConstruction

theorem exactRouteConstruction_core :
    ExactRouteConstruction :=
  exactRouteConstruction_of_indexedMaterializerConstruction
    countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerConstruction_core

/-!
## Exact route branch packaging

Most later count-window bridge proofs split on the accept/reject selector
before opening the materializer route.  These branch contracts let those proofs
carry a single branch-local materializer obligation and then reassemble the
uniform construction when needed.
-/

def AcceptExactRouteSpec (materializer : MachineDescription) : Prop :=
  ExactRouteSpec true materializer

def RejectExactRouteSpec (materializer : MachineDescription) : Prop :=
  ExactRouteSpec false materializer

def AcceptExactRouteConstruction : Prop :=
  exists materializer : MachineDescription,
    AcceptExactRouteSpec materializer

def RejectExactRouteConstruction : Prop :=
  exists materializer : MachineDescription,
    RejectExactRouteSpec materializer

def ExactRouteBranchConstruction : Prop :=
  AcceptExactRouteConstruction ∧ RejectExactRouteConstruction

theorem acceptExactRouteConstruction_of_exactRouteConstruction
    (hroute : ExactRouteConstruction) :
    AcceptExactRouteConstruction := by
  exact hroute true

theorem rejectExactRouteConstruction_of_exactRouteConstruction
    (hroute : ExactRouteConstruction) :
    RejectExactRouteConstruction := by
  exact hroute false

theorem exactRouteBranchConstruction_of_exactRouteConstruction
    (hroute : ExactRouteConstruction) :
    ExactRouteBranchConstruction := by
  exact
    ⟨acceptExactRouteConstruction_of_exactRouteConstruction hroute,
      rejectExactRouteConstruction_of_exactRouteConstruction hroute⟩

theorem exactRouteConstruction_of_branchConstruction
    (hroute : ExactRouteBranchConstruction) :
    ExactRouteConstruction := by
  intro useAccept
  cases useAccept
  · exact hroute.right
  · exact hroute.left

theorem exactRouteConstruction_iff_branchConstruction :
    ExactRouteConstruction ↔ ExactRouteBranchConstruction := by
  constructor
  · exact exactRouteBranchConstruction_of_exactRouteConstruction
  · exact exactRouteConstruction_of_branchConstruction

theorem acceptExactRouteConstruction_of_indexedMaterializerConstruction
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerConstruction) :
    AcceptExactRouteConstruction :=
  acceptExactRouteConstruction_of_exactRouteConstruction
    (exactRouteConstruction_of_indexedMaterializerConstruction hmaterializer)

theorem rejectExactRouteConstruction_of_indexedMaterializerConstruction
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerConstruction) :
    RejectExactRouteConstruction :=
  rejectExactRouteConstruction_of_exactRouteConstruction
    (exactRouteConstruction_of_indexedMaterializerConstruction hmaterializer)

theorem branchConstruction_of_indexedMaterializerConstruction
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerConstruction) :
    ExactRouteBranchConstruction :=
  exactRouteBranchConstruction_of_exactRouteConstruction
    (exactRouteConstruction_of_indexedMaterializerConstruction hmaterializer)

theorem indexedMaterializerConstruction_of_branchConstruction
    (hroute : ExactRouteBranchConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerConstruction :=
  indexedMaterializerConstruction_of_exactRouteConstruction
    (exactRouteConstruction_of_branchConstruction hroute)

theorem branchConstruction_iff_indexedMaterializerConstruction :
    ExactRouteBranchConstruction ↔
      CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerConstruction := by
  constructor
  · exact indexedMaterializerConstruction_of_branchConstruction
  · exact branchConstruction_of_indexedMaterializerConstruction

theorem branchConstruction_core :
    ExactRouteBranchConstruction :=
  exactRouteBranchConstruction_of_exactRouteConstruction
    exactRouteConstruction_core

end CountWindowPostFieldDecodedPrefixStructuredMaterializerRouteContracts

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters
end Computability
end FoC

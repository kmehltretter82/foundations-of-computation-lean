import FoC.Computability.Compiler.ClosedCfg.TerminalCore.Core
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterTheory.Iteration
import FoC.Computability.Compiler.Core.CommonGround.Identity
import FoC.Computability.Compiler.Core.CommonGround.SeqComposition

set_option doc.verso true

/-!
# Exact target-specific run-config closeout

The fixed-description loop computes four semantic fields: the preserved input
word, the preserved stage, the final configuration, and the accumulated hit
bit.  This module packages those fields independently of their eventual
physical representation and identifies their exact scratch-padded target.

The construction adapter at the end deliberately starts from a serializer
that already reaches the right-shifted scratch target.  It parks that target
exactly with a single composition handoff.  Consequently the remaining #18
obligation is an honest target-specific serializer; it does not import the
shared structured tape-2 projector and therefore does not inherit the open
selected-head ingress and cleanup leaves.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace RunConfigEmitterCore
namespace ExactCloseout

/-- Semantic fields that must survive the execution loop and be serialized at
the #18 endpoint.  The scratch width is kept separate because it describes the
physical blank reservoir, not a simulator-layout field. -/
structure Fields where
  input : Word Bool
  stage : Nat
  config : Configuration
  hit : Bool

/-- Reassemble the ordinary simulator layout represented by closeout fields. -/
def Fields.asLayout (F : Fields) : SimulatorLayout where
  input := F.input
  stage := F.stage
  config := F.config
  hit := F.hit

/-- Read closeout fields from an ordinary simulator layout. -/
def Fields.ofLayout (L : SimulatorLayout) : Fields where
  input := L.input
  stage := L.stage
  config := L.config
  hit := L.hit

@[simp] theorem Fields.asLayout_ofLayout (L : SimulatorLayout) :
    (Fields.ofLayout L).asLayout = L := by
  cases L
  rfl

@[simp] theorem Fields.ofLayout_asLayout (F : Fields) :
    Fields.ofLayout F.asLayout = F := by
  cases F
  rfl

/-- Canonical encoded Boolean word determined by the four closeout fields. -/
def Fields.outputBits (F : Fields) : Word Bool :=
  SimulatorLayout.asBoolInput F.asLayout

theorem Fields.outputBits_eq_fields (F : Fields) :
    F.outputBits =
      encodeCodeWordAsInput
        (MachineCodeSymbol.header ::
          encodeBoolWordAppend F.input
            (encodeNatAppend F.stage
              (encodeConfigurationAppend F.config
                (encodeBoolAppend F.hit [])))) := by
  rfl

theorem Fields.outputBits_length_ge_two (F : Fields) :
    2 <= F.outputBits.length := by
  rw [Fields.outputBits, SimulatorLayout.asBoolInput,
    SimulatorLayout.encode, SimulatorLayout.encodeAppend]
  simp [encodeCodeWordAsInput, encodeCodeSymbolAsInput]

theorem Fields.outputBits_injective :
    Function.Injective Fields.outputBits := by
  intro F G hbits
  have hcode :
      SimulatorLayout.encode F.asLayout =
        SimulatorLayout.encode G.asLayout :=
    encodeCodeWordAsInput_injective hbits
  have hdecode := congrArg SimulatorLayout.decodeComplete hcode
  rw [SimulatorLayout.decodeComplete_encode,
    SimulatorLayout.decodeComplete_encode] at hdecode
  have hlayout : F.asLayout = G.asLayout := Option.some.inj hdecode
  simpa using congrArg Fields.ofLayout hlayout

/-- Exact scratch-padded output with a caller-supplied blank reservoir. -/
def Fields.scratchTape (scratchWidth : Nat) (F : Fields) : Tape Bool :=
  inputWithTrailingBlankPadding F.outputBits scratchWidth

/-- The convenient one-cell-right serializer target used before final
parking. -/
def Fields.rightScratchTape (scratchWidth : Nat) (F : Fields) : Tape Bool :=
  Tape.move Direction.right (F.scratchTape scratchWidth)

theorem Fields.scratchTape_normalizedOutput
    (scratchWidth : Nat) (F : Fields) :
    Tape.normalizedOutput (F.scratchTape scratchWidth) = F.outputBits := by
  exact inputWithTrailingBlankPadding_normalizedOutput
    F.outputBits scratchWidth

theorem Fields.scratchTape_equiv_input
    (scratchWidth : Nat) (F : Fields) :
    Tape.Equiv (F.scratchTape scratchWidth) (Tape.input F.outputBits) := by
  exact inputWithTrailingBlankPadding_equiv_input
    F.outputBits scratchWidth

theorem Fields.scratchTape_cells
    (scratchWidth : Nat) (F : Fields) :
    Tape.cells (F.scratchTape scratchWidth) =
      List.append (F.outputBits.map some)
        (List.replicate scratchWidth none) := by
  have hlen := F.outputBits_length_ge_two
  cases houtput : F.outputBits with
  | nil =>
      simp [houtput] at hlen
  | cons first rest =>
      cases first <;>
        simp [Fields.scratchTape, inputWithTrailingBlankPadding,
          Tape.cells, houtput]

theorem Fields.eq_of_scratchTape_eq
    {scratchWidthF scratchWidthG : Nat} {F G : Fields}
    (h : F.scratchTape scratchWidthF = G.scratchTape scratchWidthG) :
    F = G := by
  apply Fields.outputBits_injective
  have hnorm := congrArg Tape.normalizedOutput h
  simpa only [Fields.scratchTape_normalizedOutput] using hnorm

theorem Fields.scratchWidth_eq_of_scratchTape_eq
    {scratchWidthF scratchWidthG : Nat} {F G : Fields}
    (h : F.scratchTape scratchWidthF = G.scratchTape scratchWidthG) :
    scratchWidthF = scratchWidthG := by
  have hfields : F = G := Fields.eq_of_scratchTape_eq h
  subst G
  have hcells := congrArg (fun T : Tape Bool => (Tape.cells T).length) h
  rw [Fields.scratchTape_cells, Fields.scratchTape_cells] at hcells
  have hadd :
      F.outputBits.length + scratchWidthF =
        F.outputBits.length + scratchWidthG := by
    simpa using hcells
  exact Nat.add_left_cancel hadd

theorem Fields.rightScratchTape_move_left
    (scratchWidth : Nat) (F : Fields) :
    Tape.move Direction.left (F.rightScratchTape scratchWidth) =
      F.scratchTape scratchWidth := by
  have hlen := F.outputBits_length_ge_two
  cases houtput : F.outputBits with
  | nil =>
      simp [houtput] at hlen
  | cons first rest =>
      cases rest with
      | nil =>
          simp [houtput] at hlen
      | cons second tail =>
          cases first <;> cases second <;>
            simp [Fields.rightScratchTape, Fields.scratchTape,
              inputWithTrailingBlankPadding, houtput,
              Tape.move, Tape.moveLeft, Tape.moveRight]

theorem Fields.eq_of_rightScratchTape_eq
    {scratchWidthF scratchWidthG : Nat} {F G : Fields}
    (h : F.rightScratchTape scratchWidthF =
      G.rightScratchTape scratchWidthG) :
    F = G := by
  apply Fields.eq_of_scratchTape_eq
    (scratchWidthF := scratchWidthF)
    (scratchWidthG := scratchWidthG)
  have hleft := congrArg (Tape.move Direction.left) h
  simpa only [Fields.rightScratchTape_move_left] using hleft

theorem Fields.scratchWidth_eq_of_rightScratchTape_eq
    {scratchWidthF scratchWidthG : Nat} {F G : Fields}
    (h : F.rightScratchTape scratchWidthF =
      G.rightScratchTape scratchWidthG) :
    scratchWidthF = scratchWidthG := by
  apply Fields.scratchWidth_eq_of_scratchTape_eq
    (F := F) (G := G)
  have hleft := congrArg (Tape.move Direction.left) h
  simpa only [Fields.rightScratchTape_move_left] using hleft

/-- Semantic fields required by the fixed-description bounded run. -/
def semanticFields
    (D : MachineDescription) (L : SimulatorLayout) : Fields :=
  Fields.ofLayout (SimulatorLayout.run D L.stage L)

theorem semanticFields_asLayout
    (D : MachineDescription) (L : SimulatorLayout) :
    (semanticFields D L).asLayout = SimulatorLayout.run D L.stage L := by
  exact Fields.asLayout_ofLayout _

theorem semanticFields_eq_iterateStep
    (D : MachineDescription) (L : SimulatorLayout) :
    semanticFields D L =
      Fields.ofLayout
        (RunConfigEmitterTheory.iterateStep D L.stage
          (RunConfigEmitterTheory.seedHit D L)) := by
  rw [RunConfigEmitterTheory.iterateStep_seedHit_eq_run]
  rfl

theorem semanticFields_outputBits_eq
    (D : MachineDescription) (L : SimulatorLayout) :
    (semanticFields D L).outputBits =
      FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
        D L := by
  rfl

theorem semanticFields_scratchTape_eq
    (D : MachineDescription) (L : SimulatorLayout) :
    (semanticFields D L).scratchTape
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
          L) =
      FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
        D L := by
  rfl

theorem semanticFields_rightScratchTape_eq
    (D : MachineDescription) (L : SimulatorLayout) :
    (semanticFields D L).rightScratchTape
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
          L) =
      FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner
        D L := by
  rfl

/-!
## Honest serializer and exact-closeout contracts
-/

/-- A serializer has done all substantive work when it reaches the
right-shifted scratch-padded encoding of the indexed fields. -/
def SerializerSpec {ι : Type}
    (source : ι -> Tape Bool)
    (fields : ι -> Fields)
    (scratchWidth : ι -> Nat)
    (serializer : MachineDescription) : Prop :=
  serializer.SubroutineReady ∧
    forall i : ι,
      serializer.HaltsFromTape
        (source i)
        ((fields i).rightScratchTape (scratchWidth i))

/-- Exact closeout parks the head on the first output bit while retaining the
entire prescribed blank reservoir. -/
def Spec {ι : Type}
    (source : ι -> Tape Bool)
    (fields : ι -> Fields)
    (scratchWidth : ι -> Nat)
    (closeout : MachineDescription) : Prop :=
  closeout.SubroutineReady ∧
    forall i : ι,
      closeout.HaltsFromTape
        (source i)
        ((fields i).scratchTape (scratchWidth i))

def SerializerConstruction {ι : Type}
    (source : ι -> Tape Bool)
    (fields : ι -> Fields)
    (scratchWidth : ι -> Nat) : Prop :=
  exists serializer : MachineDescription,
    SerializerSpec source fields scratchWidth serializer

def Construction {ι : Type}
    (source : ι -> Tape Bool)
    (fields : ι -> Fields)
    (scratchWidth : ι -> Nat) : Prop :=
  exists closeout : MachineDescription,
    Spec source fields scratchWidth closeout

/-- Exact target functionality for two indices sharing one physical source. -/
theorem SerializerSpec.target_eq_of_source_eq {ι : Type}
    {source : ι -> Tape Bool}
    {fields : ι -> Fields}
    {scratchWidth : ι -> Nat}
    {serializer : MachineDescription}
    (hserializer : SerializerSpec source fields scratchWidth serializer)
    {i j : ι}
    (hsource : source i = source j) :
    (fields i).rightScratchTape (scratchWidth i) =
      (fields j).rightScratchTape (scratchWidth j) := by
  rcases hserializer with ⟨hready, hrun⟩
  have hrunj :
      serializer.HaltsFromTape (source i)
        ((fields j).rightScratchTape (scratchWidth j)) := by
    rw [hsource]
    exact hrun j
  exact MachineDescription.haltsFromTape_functional_of_haltTransitionFree
    hready.right (hrun i) hrunj

/-- Functionality guardrail: a deterministic serializer cannot map one exact
physical source to two distinct four-field outputs.  Any proposed loop endpoint
must therefore retain enough information to distinguish all indexed fields. -/
theorem SerializerSpec.fields_eq_of_source_eq {ι : Type}
    {source : ι -> Tape Bool}
    {fields : ι -> Fields}
    {scratchWidth : ι -> Nat}
    {serializer : MachineDescription}
    (hserializer : SerializerSpec source fields scratchWidth serializer)
    {i j : ι}
    (hsource : source i = source j) :
    fields i = fields j := by
  exact Fields.eq_of_rightScratchTape_eq
    (hserializer.target_eq_of_source_eq hsource)

theorem SerializerSpec.scratchWidth_eq_of_source_eq {ι : Type}
    {source : ι -> Tape Bool}
    {fields : ι -> Fields}
    {scratchWidth : ι -> Nat}
    {serializer : MachineDescription}
    (hserializer : SerializerSpec source fields scratchWidth serializer)
    {i j : ι}
    (hsource : source i = source j) :
    scratchWidth i = scratchWidth j := by
  exact Fields.scratchWidth_eq_of_rightScratchTape_eq
    (hserializer.target_eq_of_source_eq hsource)

theorem Spec.target_eq_of_source_eq {ι : Type}
    {source : ι -> Tape Bool}
    {fields : ι -> Fields}
    {scratchWidth : ι -> Nat}
    {closeout : MachineDescription}
    (hcloseout : Spec source fields scratchWidth closeout)
    {i j : ι}
    (hsource : source i = source j) :
    (fields i).scratchTape (scratchWidth i) =
      (fields j).scratchTape (scratchWidth j) := by
  rcases hcloseout with ⟨hready, hrun⟩
  have hrunj :
      closeout.HaltsFromTape (source i)
        ((fields j).scratchTape (scratchWidth j)) := by
    rw [hsource]
    exact hrun j
  exact MachineDescription.haltsFromTape_functional_of_haltTransitionFree
    hready.right (hrun i) hrunj

theorem Spec.fields_eq_of_source_eq {ι : Type}
    {source : ι -> Tape Bool}
    {fields : ι -> Fields}
    {scratchWidth : ι -> Nat}
    {closeout : MachineDescription}
    (hcloseout : Spec source fields scratchWidth closeout)
    {i j : ι}
    (hsource : source i = source j) :
    fields i = fields j := by
  exact Fields.eq_of_scratchTape_eq
    (hcloseout.target_eq_of_source_eq hsource)

theorem Spec.scratchWidth_eq_of_source_eq {ι : Type}
    {source : ι -> Tape Bool}
    {fields : ι -> Fields}
    {scratchWidth : ι -> Nat}
    {closeout : MachineDescription}
    (hcloseout : Spec source fields scratchWidth closeout)
    {i j : ι}
    (hsource : source i = source j) :
    scratchWidth i = scratchWidth j := by
  exact Fields.scratchWidth_eq_of_scratchTape_eq
    (hcloseout.target_eq_of_source_eq hsource)

/-- Use the sequential-composition handoff itself for the final one-cell left
move, then halt through the exact identity machine. -/
def parkSerializer (serializer : MachineDescription) : MachineDescription :=
  seqSubroutine serializer ExactIdentityDescription Direction.left

theorem parkSerializer_spec {ι : Type}
    {source : ι -> Tape Bool}
    {fields : ι -> Fields}
    {scratchWidth : ι -> Nat}
    {serializer : MachineDescription}
    (hserializer :
      SerializerSpec source fields scratchWidth serializer) :
    Spec source fields scratchWidth (parkSerializer serializer) := by
  rcases hserializer with ⟨hready, hrun⟩
  constructor
  · exact seqSubroutine_subroutineReady hready
      CommonGround.Identity.exactIdentityDescription_subroutineReady
  · intro i
    unfold parkSerializer
    exact
      CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
        hready
        CommonGround.Identity.exactIdentityDescription_subroutineReady
        (hrun i)
        ((fields i).rightScratchTape_move_left (scratchWidth i))
        (CommonGround.Identity.exactIdentityDescription_haltsFromTape
          ((fields i).scratchTape (scratchWidth i)))

theorem construction_of_serializerConstruction {ι : Type}
    {source : ι -> Tape Bool}
    {fields : ι -> Fields}
    {scratchWidth : ι -> Nat}
    (hserializer :
      SerializerConstruction source fields scratchWidth) :
    Construction source fields scratchWidth := by
  rcases hserializer with ⟨serializer, hserializer⟩
  exact ⟨parkSerializer serializer, parkSerializer_spec hserializer⟩

theorem exactIdentity_serializerSpec {ι : Type}
    (fields : ι -> Fields)
    (scratchWidth : ι -> Nat) :
    SerializerSpec
      (fun i => (fields i).rightScratchTape (scratchWidth i))
      fields scratchWidth ExactIdentityDescription := by
  constructor
  · exact CommonGround.Identity.exactIdentityDescription_subroutineReady
  · intro i
    exact CommonGround.Identity.exactIdentityDescription_haltsFromTape _

/-- Once the field serializer has reached the named right-scratch boundary,
the exact parking phase is a concrete, index-independent machine. -/
theorem rightScratchSource_spec {ι : Type}
    (fields : ι -> Fields)
    (scratchWidth : ι -> Nat) :
    Spec
      (fun i => (fields i).rightScratchTape (scratchWidth i))
      fields scratchWidth
      (parkSerializer ExactIdentityDescription) := by
  exact parkSerializer_spec
    (exactIdentity_serializerSpec fields scratchWidth)

theorem rightScratchSource_construction {ι : Type}
    (fields : ι -> Fields)
    (scratchWidth : ι -> Nat) :
    Construction
      (fun i => (fields i).rightScratchTape (scratchWidth i))
      fields scratchWidth := by
  exact ⟨parkSerializer ExactIdentityDescription,
    rightScratchSource_spec fields scratchWidth⟩

/-!
## Specialization to the #18 semantic target
-/

def SemanticSerializerSpec
    (D : MachineDescription)
    (source : SimulatorLayout -> Tape Bool)
    (serializer : MachineDescription) : Prop :=
  SerializerSpec source (semanticFields D)
    FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
    serializer

def SemanticSpec
    (D : MachineDescription)
    (source : SimulatorLayout -> Tape Bool)
    (closeout : MachineDescription) : Prop :=
  Spec source (semanticFields D)
    FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
    closeout

def SemanticSerializerConstruction
    (D : MachineDescription)
    (source : SimulatorLayout -> Tape Bool) : Prop :=
  exists serializer : MachineDescription,
    SemanticSerializerSpec D source serializer

def SemanticConstruction
    (D : MachineDescription)
    (source : SimulatorLayout -> Tape Bool) : Prop :=
  exists closeout : MachineDescription,
    SemanticSpec D source closeout

theorem semanticRightScratchSource_spec
    (D : MachineDescription) :
    SemanticSpec D
      (fun L =>
        FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner
          D L)
      (parkSerializer ExactIdentityDescription) := by
  change
    Spec
      (fun L =>
        (semanticFields D L).rightScratchTape
          (FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
            L))
      (semanticFields D)
      FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
      (parkSerializer ExactIdentityDescription)
  exact rightScratchSource_spec _ _

theorem semanticRightScratchSource_construction
    (D : MachineDescription) :
    SemanticConstruction D
      (fun L =>
        FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner
          D L) := by
  exact ⟨parkSerializer ExactIdentityDescription,
    semanticRightScratchSource_spec D⟩

theorem semanticSpec_iff_target
    (D : MachineDescription)
    (source : SimulatorLayout -> Tape Bool)
    (closeout : MachineDescription) :
    SemanticSpec D source closeout <->
      closeout.SubroutineReady ∧
        forall L : SimulatorLayout,
          closeout.HaltsFromTape
            (source L)
            (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
              D L) := by
  simp only [SemanticSpec, Spec, semanticFields_scratchTape_eq]

theorem semanticSerializerSpec_iff_rightTarget
    (D : MachineDescription)
    (source : SimulatorLayout -> Tape Bool)
    (serializer : MachineDescription) :
    SemanticSerializerSpec D source serializer <->
      serializer.SubroutineReady ∧
        forall L : SimulatorLayout,
          serializer.HaltsFromTape
            (source L)
            (FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner
              D L) := by
  simp only [SemanticSerializerSpec, SerializerSpec,
    semanticFields_rightScratchTape_eq]

theorem semanticConstruction_of_serializerConstruction
    {D : MachineDescription}
    {source : SimulatorLayout -> Tape Bool}
    (hserializer : SemanticSerializerConstruction D source) :
    SemanticConstruction D source := by
  rcases hserializer with ⟨serializer, hserializer⟩
  refine ⟨parkSerializer serializer, ?_⟩
  exact parkSerializer_spec hserializer

end ExactCloseout
end RunConfigEmitterCore
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC

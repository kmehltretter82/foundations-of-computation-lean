import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.GuardedEgress.WitnessBridge
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.GuardedEgress.PostCopyCloseout

set_option doc.verso true

/-!
# Guarded-egress assembly

This module composes the checked tape-field serializer, the witness-sensitive
metadata bridge, the token copier, and the final header/parking closeout.  The
two remaining finite leaves are explicit components so their proofs can be
completed independently without changing the integration theorem.
-/

namespace FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
namespace GuardedEgress.Assembly

open Languages MachineDescription
open CommonGround.FiniteTransducers

/-- Contract required from the metadata token copier at the semantic #18
index.  Its generic finite-machine run discharges this specialization. -/
def CopierSpec (copier : MachineDescription) : Prop :=
  copier.SubroutineReady ∧
    forall (i : GuardedEgress.Index)
      (layout : MetadataWitnessBridge.ReadyLayout),
      copier.HaltsFromTapeEquiv
        (MetadataWitnessBridge.readyTape i layout)
        (PostCopyCloseout.sourceTape ⟨i, layout⟩)

def CopierConstruction : Prop :=
  exists copier : MachineDescription, CopierSpec copier

structure Components where
  bridge : MachineDescription
  bridgeSpec : MetadataWitnessBridge.Spec bridge
  copier : MachineDescription
  copierSpec : CopierSpec copier

def description (C : Components) : MachineDescription :=
  SeqViaCanonical
    (SeqViaCanonical
      (SeqViaCanonical TapeFieldPipeline.description C.bridge)
      C.copier)
    PostCopyCloseout.description

theorem description_subroutineReady (C : Components) :
    (description C).SubroutineReady := by
  exact
    SeqViaCanonical_subroutineReady
      (SeqViaCanonical_subroutineReady
        (SeqViaCanonical_subroutineReady
          TapeFieldPipeline.description_subroutineReady
          C.bridgeSpec.subroutineReady)
        C.copierSpec.left)
      PostCopyCloseout.description_subroutineReady

theorem description_haltsFrom_source
    (C : Components) (i : GuardedEgress.Index) :
    (description C).HaltsFromTapeEquiv i.source i.target := by
  rcases
      C.bridgeSpec.haltsFromTapeEquiv i
        (TapeFieldSerializer.correctedSerializedTapeFieldTarget i)
        (Tape.Equiv.refl _) with
    ⟨layout, hbridge⟩
  let j : PostCopyCloseout.PostCopyIndex := ⟨i, layout⟩
  have hfieldBridge :=
    SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
      TapeFieldPipeline.description_subroutineReady
      C.bridgeSpec.subroutineReady
      (TapeFieldPipeline.description_haltsFrom_source i)
      (moveLeft_moveRight_equiv_self
        (TapeFieldSerializer.correctedSerializedTapeFieldTarget i))
      hbridge
  have hcopy := C.copierSpec.right i layout
  have hthroughCopy :=
    SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
      (SeqViaCanonical_subroutineReady
        TapeFieldPipeline.description_subroutineReady
        C.bridgeSpec.subroutineReady)
      C.copierSpec.left
      hfieldBridge
      (moveLeft_moveRight_equiv_self
        (MetadataWitnessBridge.readyTape i layout))
      hcopy
  have hcloseout := PostCopyCloseout.description_haltsFrom_source j
  have hcloseout' :
      PostCopyCloseout.description.HaltsFromTapeEquiv
        (PostCopyCloseout.sourceTape ⟨i, layout⟩) i.target := by
    simpa [j] using hcloseout
  unfold description
  exact
    SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
      (SeqViaCanonical_subroutineReady
        (SeqViaCanonical_subroutineReady
          TapeFieldPipeline.description_subroutineReady
          C.bridgeSpec.subroutineReady)
        C.copierSpec.left)
      PostCopyCloseout.description_subroutineReady
      hthroughCopy
      (moveLeft_moveRight_equiv_self
        (PostCopyCloseout.sourceTape ⟨i, layout⟩))
      hcloseout'

theorem spec (C : Components) : GuardedEgress.Spec (description C) := by
  constructor
  · exact description_subroutineReady C
  intro i actual hactual
  rcases description_haltsFrom_source C i with
    ⟨canonicalOutput, hcanonical, hcanonicalEquiv⟩
  rcases
      HaltsFromTapeEquiv_of_input_equiv
        (Tape.Equiv.symm hactual) hcanonical with
    ⟨actualOutput, hrun, hactualEquiv⟩
  exact
    ⟨actualOutput, hrun,
      Tape.Equiv.trans hactualEquiv hcanonicalEquiv⟩

theorem construction_of_component (C : Components) :
    GuardedEgress.Construction := by
  exact ⟨description C, spec C⟩

theorem construction_of_leaves
    (hbridge : MetadataWitnessBridge.Construction)
    (hcopier : CopierConstruction) : GuardedEgress.Construction := by
  rcases hbridge with ⟨bridge, hbridge⟩
  rcases hcopier with ⟨copier, hcopier⟩
  exact construction_of_component ⟨bridge, hbridge, copier, hcopier⟩

theorem metadataTokenCopySpec : CopierSpec MetadataTokenCopy.description := by
  constructor
  · exact MetadataTokenCopy.description_subroutineReady
  intro i layout
  cases hhit : i.finalHit
  · simpa [MetadataWitnessBridge.readyTape,
      PostCopyCloseout.sourceTape,
      MetadataWitnessBridge.ReadyLayout.gap,
      MetadataWitnessBridge.hitBits, MetadataWitnessBridge.hitToken,
      hhit, MetadataTokenCopy.TokenKind.bits] using
      MetadataTokenCopy.description_haltsFromTapeEquiv
        (List.append
          (List.replicate 4 (none : Option Bool))
          (List.replicate layout.basePadding none))
        (LengthAssembly.exactTapeFieldBits i.finalTape [])
        false true false true layout.gapTail
        (MetadataWitnessBridge.sourceMetadataTokens i)
        (List.replicate layout.rightPadding none)
  · simpa [MetadataWitnessBridge.readyTape,
      PostCopyCloseout.sourceTape,
      MetadataWitnessBridge.ReadyLayout.gap,
      MetadataWitnessBridge.hitBits, MetadataWitnessBridge.hitToken,
      hhit, MetadataTokenCopy.TokenKind.bits] using
      MetadataTokenCopy.description_haltsFromTapeEquiv
        (List.append
          (List.replicate 4 (none : Option Bool))
          (List.replicate layout.basePadding none))
        (LengthAssembly.exactTapeFieldBits i.finalTape [])
        false true true false layout.gapTail
        (MetadataWitnessBridge.sourceMetadataTokens i)
        (List.replicate layout.rightPadding none)

theorem metadataTokenCopyConstruction : CopierConstruction := by
  exact ⟨MetadataTokenCopy.description, metadataTokenCopySpec⟩

theorem construction_of_metadataWitnessBridge
    (hbridge : MetadataWitnessBridge.Construction) :
    GuardedEgress.Construction := by
  exact construction_of_leaves hbridge metadataTokenCopyConstruction

end GuardedEgress.Assembly
end FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore

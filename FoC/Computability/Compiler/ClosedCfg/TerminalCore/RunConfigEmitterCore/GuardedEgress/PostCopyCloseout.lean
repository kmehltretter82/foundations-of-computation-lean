import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.GuardedEgress.MetadataWitnessBridge
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.PaddedIdentity
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.PrependFixedFourBits

set_option doc.verso true

/-!
# Guarded-egress closeout after metadata copying

The metadata copier leaves the exact field body to the left of the four-bit
hit field and reserves four blank cells for the fixed header token.  This
module checks the remaining generic route: prepend that header, rewind to the
first output bit, and park one cell to its right.  Blank reservoirs are
retained only up to tape equivalence, matching the viable #18 contract.
-/

namespace FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
namespace GuardedEgress.PostCopyCloseout

open Languages MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.CountWindowRawSourceEncoder.RawBoundaryRightEdgeEmitter
open CanonicalLayouts.SimulatorLayoutScanner
open MetadataTokenCopy MetadataWitnessBridge

/-- One copier endpoint together with the padding choices made by its bridge. -/
structure PostCopyIndex where
  index : GuardedEgress.Index
  layout : MetadataWitnessBridge.ReadyLayout

/-- Serialized body before the fixed header and hit field are joined. -/
def bodyBits (j : PostCopyIndex) : Word Bool :=
  List.append
    (MetadataTokenCopy.tokenBits
      (MetadataWitnessBridge.sourceMetadataTokens j.index))
    (LengthAssembly.exactTapeFieldBits j.index.finalTape [])

/-- Complete semantic output word assembled by the closeout. -/
def prefixBits (j : PostCopyIndex) : Word Bool :=
  List.append headerPrefixBits
    (bodyBits j)

/-- Complete semantic output word assembled by the closeout. -/
def assembledBits (j : PostCopyIndex) : Word Bool :=
  List.append (prefixBits j) (MetadataWitnessBridge.hitBits j.index)

/-- The token copier, tape-field serializer, and hit tail concatenate to the
semantic field word before its checked output-word rewrite. -/
theorem assembledBits_eq_exactFieldsBits (j : PostCopyIndex) :
    assembledBits j = LengthAssembly.exactFieldsBits j.index.fields := by
  rw [assembledBits, prefixBits, bodyBits]
  rw [MetadataWitnessBridge.sourceMetadataTokenBits_eq_fields]
  rw [MetadataWitnessBridge.hitBits_eq_boolFieldBits]
  rw [LengthAssembly.exactFieldsBits_eq_fields]
  have htape : j.index.fields.config.tape = j.index.finalTape := by
    rfl
  rw [htape]
  simp [LengthAssembly.exactTapeFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.cellListFieldBits,
    List.append_assoc]

/-- The assembled word is the exact normalized output demanded by #18. -/
theorem assembledBits_eq_outputBits (j : PostCopyIndex) :
    assembledBits j = j.index.fields.outputBits := by
  rw [assembledBits_eq_exactFieldsBits]
  exact LengthAssembly.exactFieldsBits_eq_outputBits j.index.fields

/-- The three hit bits remaining to the right of the copier head. -/
def hitTailBits (j : PostCopyIndex) : Word Bool :=
  if j.index.finalHit then [true, true, false] else [true, false, true]

/-- Every encoded Boolean hit field starts with the copier's false head bit. -/
theorem hitBits_eq_false_cons (j : PostCopyIndex) :
    MetadataWitnessBridge.hitBits j.index = false :: hitTailBits j := by
  cases hhit : j.index.finalHit <;>
    simp [MetadataWitnessBridge.hitBits, MetadataWitnessBridge.hitToken,
      hitTailBits, hhit, MetadataTokenCopy.TokenKind.bits]

/-- Blanks retained to the right of the hit field after metadata copying. -/
def rightBlankTail (j : PostCopyIndex) : List (Option Bool) :=
  List.append
    (List.replicate
      (j.layout.gap +
        8 * (MetadataWitnessBridge.sourceMetadataTokens j.index).length + 3)
      (none : Option Bool))
    (List.replicate j.layout.rightPadding none)

/-- Total blank reservoir retained to the right of the serialized word. -/
def rightBlankCount (j : PostCopyIndex) : Nat :=
  (j.layout.gap +
      8 * (MetadataWitnessBridge.sourceMetadataTokens j.index).length + 3) +
    j.layout.rightPadding

theorem rightBlankTail_eq_replicate (j : PostCopyIndex) :
    rightBlankTail j =
      List.replicate (rightBlankCount j) (none : Option Bool) := by
  unfold rightBlankTail rightBlankCount
  symm
  calc
    List.replicate
          ((j.layout.gap +
              8 * (MetadataWitnessBridge.sourceMetadataTokens j.index).length + 3) +
            j.layout.rightPadding)
          (none : Option Bool) =
        List.replicate
            ((j.layout.gap +
                8 * (MetadataWitnessBridge.sourceMetadataTokens j.index).length + 3) +
              j.layout.rightPadding)
            none ++ [] := by
      simp
    _ =
        List.replicate
            (j.layout.gap +
              8 * (MetadataWitnessBridge.sourceMetadataTokens j.index).length + 3)
            none ++
          (List.replicate j.layout.rightPadding none ++ []) := by
      exact
        FoC.Computability.list_replicate_add_append
          (none : Option Bool)
          (j.layout.gap +
            8 * (MetadataWitnessBridge.sourceMetadataTokens j.index).length + 3)
          j.layout.rightPadding []
    _ =
        List.replicate
            (j.layout.gap +
              8 * (MetadataWitnessBridge.sourceMetadataTokens j.index).length + 3)
            none ++
          List.replicate j.layout.rightPadding none := by
      simp

/-- Exact copier endpoint, independent of the still-open copier run theorem. -/
def sourceTape (j : PostCopyIndex) : Tape Bool :=
  MetadataTokenCopy.targetTape
    (List.append
      (List.replicate 4 (none : Option Bool))
      (List.replicate j.layout.basePadding none))
    (LengthAssembly.exactTapeFieldBits j.index.finalTape [])
    (MetadataWitnessBridge.hitBits j.index)
    j.layout.gap
    (MetadataWitnessBridge.sourceMetadataTokens j.index)
    (List.replicate j.layout.rightPadding none)

/-- The same copier endpoint in the exact source shape of the fixed prepender. -/
def headerSourceTape (j : PostCopyIndex) : Tape Bool :=
  tapeAtCells
    (List.append ((bodyBits j).reverse.map some)
      (List.append (List.replicate 4 (none : Option Bool))
        (List.replicate j.layout.basePadding none)))
    (some false ::
      List.append ((hitTailBits j).map some) (rightBlankTail j))

/-- Tape immediately after the fixed header token has been prepended. -/
def headerTargetTape (j : PostCopyIndex) : Tape Bool :=
  tapeAtCells
    (List.append ((prefixBits j).reverse.map some)
      (List.replicate j.layout.basePadding none))
    (some false ::
      List.append ((hitTailBits j).map some) (rightBlankTail j))

/-- Unfolding the copier target exposes exactly the four reserved prepender
blanks and the false-led hit tail. -/
theorem sourceTape_eq_headerSourceTape (j : PostCopyIndex) :
    sourceTape j = headerSourceTape j := by
  rw [sourceTape, headerSourceTape, MetadataTokenCopy.targetTape]
  rw [hitBits_eq_false_cons]
  unfold bodyBits rightBlankTail
  rfl

/-- The shared fixed-four-bit primitive consumes exactly the reserved header
workspace and restores the first hit bit. -/
theorem prependHeader_haltsFrom_source (j : PostCopyIndex) :
    prependHeaderChunkLeftOfHeadDescription.HaltsFromTape
      (sourceTape j) (headerTargetTape j) := by
  rw [sourceTape_eq_headerSourceTape]
  simpa [headerSourceTape, headerTargetTape, prefixBits,
    CanonicalLayouts.SimulatorLayoutScanner.headerPrefixBits] using
    prependHeaderChunkLeftOfHeadDescription_haltsFrom_prepend_withScratch
      (bodyBits j)
      (List.replicate j.layout.basePadding (none : Option Bool))
      false
      (List.append ((hitTailBits j).map some) (rightBlankTail j))

/-- Header endpoint with invisible far-left padding removed. -/
def rewindSourceTape (j : PostCopyIndex) : Tape Bool :=
  tapeAtCells ((prefixBits j).reverse.map some)
    (some false ::
      List.append ((hitTailBits j).map some) (rightBlankTail j))

/-- Exact output of the generic right-edge rewinder. -/
def rewindTargetTape (j : PostCopyIndex) : Tape Bool :=
  tapeAtCells [none]
    (List.append ((assembledBits j).map some) (rightBlankTail j))

/-- The rewinder's retained blank reservoirs do not change the represented
normalized output tape. -/
theorem rewindTargetTape_equiv_input (j : PostCopyIndex) :
    Tape.Equiv (rewindTargetTape j) (Tape.input (assembledBits j)) := by
  rw [rewindTargetTape, rightBlankTail_eq_replicate]
  cases hbits : assembledBits j with
  | nil =>
      cases hcount : rightBlankCount j with
      | zero =>
          simp [tapeAtCells, Tape.input, Tape.blank, Tape.Equiv,
            Tape.dropTrailingNone]
      | succ count =>
          simp [tapeAtCells, Tape.input, Tape.blank, Tape.Equiv,
            Tape.dropTrailingNone, List.replicate_succ,
            FoC.Computability.dropTrailingNone_replicate_none]
  | cons bit rest =>
      simp [tapeAtCells, Tape.input, Tape.Equiv, Tape.dropTrailingNone,
        FoC.Computability.dropTrailingNone_append_replicate_none]

/-- The rewinder output represents the established scratch-padded closeout
tape, regardless of the copier's larger right blank reservoir. -/
theorem rewindTargetTape_equiv_scratchTape (j : PostCopyIndex) :
    Tape.Equiv (rewindTargetTape j)
      (j.index.fields.scratchTape j.index.scratchWidth) := by
  have hinput := rewindTargetTape_equiv_input j
  rw [assembledBits_eq_outputBits] at hinput
  exact
    Tape.Equiv.trans hinput
      (Tape.Equiv.symm
        (ExactCloseout.Fields.scratchTape_equiv_input
          j.index.scratchWidth j.index.fields))

/-- Moving right from the rewinder output lands on the exact target layout up
to invisible far-end blank padding. -/
theorem move_right_rewindTargetTape_equiv_target (j : PostCopyIndex) :
    Tape.Equiv (Tape.move Direction.right (rewindTargetTape j))
      j.index.target := by
  simpa [GuardedEgress.Index.target,
    ExactCloseout.Fields.rightScratchTape] using
    Tape.Equiv.move (rewindTargetTape_equiv_scratchTape j) Direction.right

/-- The prepender may retain far-left blanks, but they are invisible in the
logical tape relation consumed by the rewind phase. -/
theorem headerTargetTape_equiv_rewindSourceTape (j : PostCopyIndex) :
    Tape.Equiv (headerTargetTape j) (rewindSourceTape j) := by
  refine ⟨?_, rfl, rfl⟩
  exact
    FoC.Computability.dropTrailingNone_append_replicate_none
      ((prefixBits j).reverse.map some) j.layout.basePadding

/-- The generic rewinder preserves the three remaining hit bits and all right
blank padding while returning to the output word's first bit. -/
theorem rightEdgeRewind_haltsFrom_rewindSource (j : PostCopyIndex) :
    rightEdgeRewindDescription.HaltsFromTape
      (rewindSourceTape j) (rewindTargetTape j) := by
  simpa [rewindSourceTape, rewindTargetTape, assembledBits,
    hitBits_eq_false_cons, List.map_append, List.append_assoc] using
    rightEdgeRewindDescription_haltsFrom_rightEdge_noDelimiter
      (prefixBits j) false
      (List.append ((hitTailBits j).map some) (rightBlankTail j))

/-- Rewind from every far-left-padded prepender endpoint, with an output
representative equivalent to the named canonical rewind target. -/
theorem rightEdgeRewind_haltsFrom_headerTarget (j : PostCopyIndex) :
    rightEdgeRewindDescription.HaltsFromTapeEquiv
      (headerTargetTape j) (rewindTargetTape j) := by
  exact
    HaltsFromTapeEquiv_of_input_equiv
      (Tape.Equiv.symm (headerTargetTape_equiv_rewindSourceTape j))
      (rightEdgeRewind_haltsFrom_rewindSource j)

/-- Rewind to the first output bit and then park one cell to its right. -/
def rewindAndParkDescription : MachineDescription :=
  seqSubroutine rightEdgeRewindDescription ExactIdentityDescription
    Direction.right

theorem rewindAndParkDescription_subroutineReady :
    rewindAndParkDescription.SubroutineReady := by
  exact
    seqSubroutine_subroutineReady
      rightEdgeRewindDescription_subroutineReady
      CommonGround.Identity.exactIdentityDescription_subroutineReady

/-- Checked closeout from the header endpoint to the repaired #18 target
currency. -/
theorem rewindAndPark_haltsFrom_headerTarget (j : PostCopyIndex) :
    rewindAndParkDescription.HaltsFromTapeEquiv
      (headerTargetTape j) j.index.target := by
  rcases rightEdgeRewind_haltsFrom_headerTarget j with
    ⟨actual, hactual, hactualEquiv⟩
  have hseq :
      (seqSubroutine rightEdgeRewindDescription ExactIdentityDescription
          Direction.right).HaltsFromTape
        (headerTargetTape j) (Tape.move Direction.right actual) := by
    exact
      CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
        rightEdgeRewindDescription_subroutineReady
        CommonGround.Identity.exactIdentityDescription_subroutineReady
        hactual rfl
        (CommonGround.Identity.exactIdentityDescription_haltsFromTape
          (Tape.move Direction.right actual))
  refine ⟨Tape.move Direction.right actual, ?_, ?_⟩
  · simpa [rewindAndParkDescription] using hseq
  · exact
      Tape.Equiv.trans
        (Tape.Equiv.move hactualEquiv Direction.right)
        (move_right_rewindTargetTape_equiv_target j)

/-- Complete checked machine from the named copier endpoint to the final
right-parked output representative. -/
def description : MachineDescription :=
  SeqViaCanonical prependHeaderChunkLeftOfHeadDescription
    rewindAndParkDescription

theorem description_subroutineReady : description.SubroutineReady := by
  exact
    SeqViaCanonical_subroutineReady
      prependHeaderChunkLeftOfHeadDescription_subroutineReady
      rewindAndParkDescription_subroutineReady

theorem description_haltsFrom_source (j : PostCopyIndex) :
    description.HaltsFromTapeEquiv (sourceTape j) j.index.target := by
  unfold description
  exact
    SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
      prependHeaderChunkLeftOfHeadDescription_subroutineReady
      rewindAndParkDescription_subroutineReady
      (prependHeader_haltsFrom_source j).toEquiv
      (moveLeft_moveRight_equiv_self (headerTargetTape j))
      (rewindAndPark_haltsFrom_headerTarget j)

/-- The closeout accepts any blank-padding-equivalent copier endpoint and
preserves the repaired #18 target currency. -/
theorem spec :
    PipelineContracts.EquivInputEquivOutputSpec
      sourceTape (fun j => j.index.target) description := by
  constructor
  · exact description_subroutineReady
  · intro j actual hactual
    rcases description_haltsFrom_source j with
      ⟨canonicalOutput, hcanonical, hcanonicalEquiv⟩
    rcases
        HaltsFromTapeEquiv_of_input_equiv
          (Tape.Equiv.symm hactual) hcanonical with
      ⟨actualOutput, hrun, hactualEquiv⟩
    exact
      ⟨actualOutput, hrun,
        Tape.Equiv.trans hactualEquiv hcanonicalEquiv⟩

theorem construction :
    PipelineContracts.EquivInputEquivOutputConstruction
      sourceTape (fun j => j.index.target) := by
  exact ⟨description, spec⟩

end GuardedEgress.PostCopyCloseout
end FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore

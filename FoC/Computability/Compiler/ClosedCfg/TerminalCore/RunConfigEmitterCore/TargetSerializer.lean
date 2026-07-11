import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.ExactCloseout
import FoC.Computability.Compiler.Core.CommonGround.SameHeadComposition
import FoC.Computability.Compiler.Structured.Lowering.Projection

set_option doc.verso true

/-!
# Target-specific structured egress for #18

This module isolates the clean part of the physical egress when logical tape 2
already contains the fully serialized right-scratch closeout target.  The
concrete seeker and pair decoder reach an exact sparse intermediate tape.  The
remaining obligation is only to erase the two preceding encoded logical tapes,
compact the sparse decoded cells, retain the exact scratch width, and park on
the named right-scratch tape.

No declaration here imports the shared selected-head endpoint construction or
its open ingress/representative-cleanup leaves.

This is intentionally a conditional egress slice, not an adapter from the
current committed {lit}`FieldDecomposition.lean` boundary.  That boundary
stores the exact configuration on logical tape 0, the raw stage on logical
tape 1, and compact input/stage/state metadata followed by the separator,
scratch markers, and live hit cell on logical tape 2.  It does not yet place a
serialized
{name (full := FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore.ExactCloseout.Fields)}`ExactCloseout.Fields`
value on logical tape 2.  Exact
configuration encoding records the stored left/right tape lengths and blank
cells, which cannot be recovered from
{name (full := FoC.Computability.Tape.normalizedOutput)}`Tape.normalizedOutput`.
An earlier serializer must therefore consume the exact tape-0 boundaries and
the preserved metadata before this tape-2 extractor applies.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace RunConfigEmitterCore
namespace TargetSerializer

open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

/-- Complete index of the target-specific structured egress. -/
structure Index where
  tape0 : Tape Bool
  tape1 : Tape Bool
  fields : ExactCloseout.Fields
  scratchWidth : Nat

/-- Logical tape 2 already carries the fully serialized right-scratch target. -/
def Index.target (i : Index) : Tape Bool :=
  i.fields.rightScratchTape i.scratchWidth

/-- Physical lowered endpoint before target extraction. -/
def Index.source (i : Index) : Tape Bool :=
  encodedGuardedStructured3Tapes i.tape0 i.tape1 i.target

/-- Exact representative seen when lowering leaves one visited blank in the
far-left window.  It is equivalent, but not equal, to the canonical source. -/
def Index.sourceWithExplicitLeftPadding (i : Index) : Tape Bool :=
  { i.source with left := [none] }

/-- Exact encoded prefix preceding logical tape 2. -/
def Index.encodedPrefix (i : Index) : List (Option Bool) :=
  encodedPrefixBeforeTape
    (guardLogicalTapes [i.tape0, i.tape1, i.target]) 2

/-- The seeker leaves precisely the two guarded predecessor segments before
the selected decoder footprint. -/
theorem Index.encodedPrefix_eq (i : Index) :
    i.encodedPrefix =
      encodedStructuredTapeCellsPrefix
        [guardLogicalTape i.tape0, guardLogicalTape i.tape1] := by
  simp [Index.encodedPrefix, encodedPrefixBeforeTape, guardLogicalTapes]

/-- Exact sparse tape produced after seeking and decoding logical tape 2. -/
def Index.decoded (i : Index) : Tape Bool :=
  selectedSegmentLogicalTapeDecoderTargetTape
    i.target i.encodedPrefix

theorem Index.target_normalizedOutput (i : Index) :
    Tape.normalizedOutput i.target = i.fields.outputBits := by
  rw [Index.target, ExactCloseout.Fields.rightScratchTape,
    Tape.normalizedOutput_move]
  exact i.fields.scratchTape_normalizedOutput i.scratchWidth

theorem Index.target_read_eq_some (i : Index) :
    exists bit : Bool, Tape.read i.target = some bit := by
  have hlen := i.fields.outputBits_length_ge_two
  cases houtput : i.fields.outputBits with
  | nil =>
      simp [houtput] at hlen
  | cons first rest =>
      cases rest with
      | nil =>
          simp [houtput] at hlen
      | cons second tail =>
          refine ⟨second, ?_⟩
          cases first <;> cases second <;>
            simp [Index.target, ExactCloseout.Fields.rightScratchTape,
              ExactCloseout.Fields.scratchTape,
              inputWithTrailingBlankPadding, houtput,
              Tape.read, Tape.move, Tape.moveRight]

theorem Index.target_left_eq_singleton (i : Index) :
    exists first : Bool, i.target.left = [some first] := by
  have hlen := i.fields.outputBits_length_ge_two
  cases houtput : i.fields.outputBits with
  | nil =>
      simp [houtput] at hlen
  | cons first rest =>
      cases rest with
      | nil =>
          simp [houtput] at hlen
      | cons second tail =>
          refine ⟨first, ?_⟩
          cases first <;> cases second <;>
            simp [Index.target, ExactCloseout.Fields.rightScratchTape,
              ExactCloseout.Fields.scratchTape,
              inputWithTrailingBlankPadding, houtput,
              Tape.move, Tape.moveRight]

/-- The exact right-scratch target is not itself the canonical payload tape
expected by the older selected-footprint densifier route. -/
theorem Index.target_ne_canonicalDecoderPayload (i : Index) :
    i.target ≠
      rightEdgeScanSourceTapeFromLeft [none]
        i.fields.outputBits (List.replicate i.scratchWidth none) := by
  intro htarget
  rcases i.target_left_eq_singleton with ⟨first, hleft⟩
  have hleftEq := congrArg Tape.left htarget
  rw [hleft] at hleftEq
  have hlen := i.fields.outputBits_length_ge_two
  cases houtput : i.fields.outputBits with
  | nil =>
      simp [houtput] at hlen
  | cons bit rest =>
      simp [rightEdgeScanSourceTapeFromLeft, tapeAtCells, houtput] at hleftEq

theorem Index.source_cells (i : Index) :
    Tape.cells i.source =
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode (guardLogicalTape i.tape0))
          (List.append tapeSeparatorCells
            (List.append (logicalTapeCode (guardLogicalTape i.tape1))
              (List.append tapeSeparatorCells
                (List.append (logicalTapeCode (guardLogicalTape i.target))
                  tapeSeparatorCells))))) := by
  exact encodedGuardedStructured3Tapes_cells
    i.tape0 i.tape1 i.target

theorem Index.source_left (i : Index) : i.source.left = [] := by
  rfl

theorem Index.sourceWithExplicitLeftPadding_cells (i : Index) :
    Tape.cells i.sourceWithExplicitLeftPadding =
      none :: Tape.cells i.source := by
  simp [Index.sourceWithExplicitLeftPadding, Tape.cells, i.source_left]

theorem Index.sourceWithExplicitLeftPadding_equiv (i : Index) :
    Tape.Equiv i.sourceWithExplicitLeftPadding i.source := by
  constructor
  · rfl
  · exact ⟨rfl, rfl⟩

theorem Index.source_read (i : Index) :
    Tape.read i.source = none := by
  rfl

theorem Index.target_cells (i : Index) :
    Tape.cells i.target =
      List.append (i.fields.outputBits.map some)
        (List.replicate i.scratchWidth none) := by
  have hlen := i.fields.outputBits_length_ge_two
  cases houtput : i.fields.outputBits with
  | nil =>
      simp [houtput] at hlen
  | cons first rest =>
      cases rest with
      | nil =>
          simp [houtput] at hlen
      | cons second tail =>
          cases first <;> cases second <;>
            simp [Index.target, ExactCloseout.Fields.rightScratchTape,
              ExactCloseout.Fields.scratchTape,
              inputWithTrailingBlankPadding, houtput,
              Tape.cells, Tape.move, Tape.moveRight]

theorem Index.decoded_cells (i : Index) :
    Tape.cells i.decoded =
      List.append i.encodedPrefix
        (none ::
          List.append
            (statefulOptionCellsFrom selectedSegmentLogicalTapeDecoderNext
              selectedSegmentLogicalTapeDecoderEmit
              selectedSegmentLogicalTapeDecoderStart
              (logicalTapeBits (guardLogicalTape i.target)))
            [none, none]) := by
  exact selectedSegmentLogicalTapeDecoderTargetTape_cells
    i.target i.encodedPrefix

theorem Index.decoded_normalizedOutput (i : Index) :
    Tape.normalizedOutput i.decoded =
      List.append
        (i.encodedPrefix.filterMap (fun cell => cell))
        i.fields.outputBits := by
  rw [Index.decoded,
    selectedSegmentLogicalTapeDecoderTargetTape_normalizedOutput,
    i.target_normalizedOutput]

theorem Index.decoded_read (i : Index) :
    Tape.read i.decoded = none := by
  change i.decoded.head = none
  exact selectedSegmentLogicalTapeDecoderTargetTape_head
    i.target i.encodedPrefix

theorem Index.decoded_ne_target (i : Index) :
    i.decoded ≠ i.target := by
  intro h
  have hread := congrArg Tape.read h
  rw [i.decoded_read] at hread
  rcases i.target_read_eq_some with ⟨bit, htarget⟩
  rw [htarget] at hread
  cases hread

theorem Index.decoded_left_cons (i : Index) :
    exists rest : List (Option Bool), i.decoded.left = none :: rest := by
  rw [Index.decoded, selectedSegmentLogicalTapeDecoderTargetTape_left]
  exact ⟨_, rfl⟩

theorem Index.decoded_move_right_move_left (i : Index) :
    Tape.move Direction.right (Tape.move Direction.left i.decoded) =
      i.decoded := by
  rcases i.decoded_left_cons with ⟨rest, hleft⟩
  cases hdecoded : i.decoded with
  | mk left head right =>
      cases left with
      | nil =>
          simp [hdecoded] at hleft
      | cons cell tail =>
          simp [Tape.move, Tape.moveLeft, Tape.moveRight]

/-!
## Concrete seek-and-decode prefix
-/

def seekDecodeDescription : MachineDescription :=
  seqSubroutine seekTape2Description
    selectedSegmentLogicalTapeDecoderDescription Direction.right

theorem seekDecodeDescription_subroutineReady :
    seekDecodeDescription.SubroutineReady := by
  exact seqSubroutine_subroutineReady
    seekTape2Description_subroutineReady
    selectedSegmentLogicalTapeDecoderDescription_subroutineReady

theorem seekDecodeDescription_haltsFromTape (i : Index) :
    seekDecodeDescription.HaltsFromTape i.source i.decoded := by
  let logical : List (Tape Bool) :=
    guardLogicalTapes [i.tape0, i.tape1, i.target]
  have hsource :
      exists T : Tape Bool, exists U : Tape Bool, exists V : Tape Bool,
        logical = [T, U, V] ∧ AtEncodedBlockStart logical i.source := by
    refine ⟨guardLogicalTape i.tape0, guardLogicalTape i.tape1,
      guardLogicalTape i.target, ?_, ?_⟩
    · rfl
    · exact atEncodedBlockStart_self logical
  rcases seekTape2Description_contract_three.realizes
      logical i.source hsource with
    ⟨physical, hseek, hseparator⟩
  rcases hseparator with ⟨_hindex, hphysical⟩
  have hdecode :
      selectedSegmentLogicalTapeDecoderDescription.HaltsFromTape
        (Tape.move Direction.right physical) i.decoded := by
    rw [hphysical]
    simpa [logical, Index.decoded, Index.encodedPrefix,
      encodedSuffixFromTape, guardLogicalTapes] using
      selectedSegmentLogicalTapeDecoderDescription_haltsFrom_selectedSingletonPayload
        i.target i.encodedPrefix
  unfold seekDecodeDescription
  exact CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
    seekTape2Description_subroutineReady
    selectedSegmentLogicalTapeDecoderDescription_subroutineReady
    hseek rfl hdecode

/-!
## Exact target-specific cleanup frontier
-/

def Spec (extractor : MachineDescription) : Prop :=
  extractor.SubroutineReady ∧
    forall i : Index,
      extractor.HaltsFromTape i.source i.target

def Construction : Prop :=
  exists extractor : MachineDescription, Spec extractor

theorem Spec.haltsFromExplicitLeftPaddingEquiv
    {extractor : MachineDescription}
    (hextractor : Spec extractor) (i : Index) :
    extractor.HaltsFromTapeEquiv
      i.sourceWithExplicitLeftPadding i.target := by
  exact MachineDescription.HaltsFromTapeEquiv_of_input_equiv
    (Tape.Equiv.symm i.sourceWithExplicitLeftPadding_equiv)
    (hextractor.right i)

/-- Narrow remaining machine obligation after the checked seek/decode prefix. -/
def DecodedCleanupSpec (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall i : Index,
      cleanup.HaltsFromTape i.decoded i.target

def DecodedCleanupConstruction : Prop :=
  exists cleanup : MachineDescription, DecodedCleanupSpec cleanup

def extractorOfCleanup (cleanup : MachineDescription) : MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    seekDecodeDescription cleanup

theorem extractorOfCleanup_spec
    {cleanup : MachineDescription}
    (hcleanup : DecodedCleanupSpec cleanup) :
    Spec (extractorOfCleanup cleanup) := by
  rcases hcleanup with ⟨hready, hrun⟩
  constructor
  · exact CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
      seekDecodeDescription_subroutineReady hready
  · intro i
    unfold extractorOfCleanup
    exact CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
      seekDecodeDescription_subroutineReady hready
      (seekDecodeDescription_haltsFromTape i)
      i.decoded_move_right_move_left
      (hrun i)

theorem construction_of_decodedCleanupConstruction
    (hcleanup : DecodedCleanupConstruction) : Construction := by
  rcases hcleanup with ⟨cleanup, hcleanup⟩
  exact ⟨extractorOfCleanup cleanup, extractorOfCleanup_spec hcleanup⟩

def identityCounterexampleIndex : Index where
  tape0 := Tape.blank
  tape1 := Tape.blank
  fields :=
    { input := []
      stage := 0
      config := { state := 0, tape := Tape.blank }
      hit := false }
  scratchWidth := 0

/-- The sparse decoded tape is never already the exact right-scratch target,
so the cleanup frontier cannot be discharged by identity. -/
theorem exactIdentityDescription_not_decodedCleanupSpec :
    ¬ DecodedCleanupSpec ExactIdentityDescription := by
  intro hcleanup
  have htarget := hcleanup.right identityCounterexampleIndex
  have hself :=
    CommonGround.Identity.exactIdentityDescription_haltsFromTape
      identityCounterexampleIndex.decoded
  apply identityCounterexampleIndex.decoded_ne_target
  exact MachineDescription.haltsFromTape_functional_of_haltTransitionFree
    CommonGround.Identity.exactIdentityDescription_subroutineReady.right
    hself htarget

end TargetSerializer
end RunConfigEmitterCore
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC

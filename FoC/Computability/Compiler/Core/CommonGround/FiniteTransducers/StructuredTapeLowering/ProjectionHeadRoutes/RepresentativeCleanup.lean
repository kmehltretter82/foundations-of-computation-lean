import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.ProjectionHeadRoutes.ExactCleanup

set_option doc.verso true

/-!
# Representative selected-head cleanup contracts

The legacy exact padded-cleanup contract targeted an arbitrary public tape
literally.  That is too strong when the public tape has less visible context
than the scanner handoff source.  This module records the replacement
contract: exact finite-machine behavior targets a canonical padded
representative, and the public route is exposed through tape equivalence.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

/--
The number of explicit blank cells retained on the public target representative.

The size is chosen from the exact handoff source so the representative is large
enough to be a legal exact endpoint for the cleanup machine.
-/
def selectedSegmentLogicalTapeDecoderPaddedCleanupOutputPaddingLength
    (target : Tape Bool) (padding : List (Option Bool))
    (encodedPrefix : List (Option Bool)) : Nat :=
  Tape.contextLength
    (canonicalPrimitiveSeqHandoffTape
      (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
        target padding encodedPrefix))

/--
Canonical padded representative for selected-head cleanup output.

It is the public target with enough explicit blank right context to cover the
scanner handoff source footprint.  The extra cells are trailing blanks, so the
representative remains equivalent to the public target.
-/
def selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape
    (target : Tape Bool) (padding : List (Option Bool))
    (encodedPrefix : List (Option Bool)) : Tape Bool :=
  { left := target.left
    head := target.head
    right :=
      target.right ++
        List.replicate
          (selectedSegmentLogicalTapeDecoderPaddedCleanupOutputPaddingLength
            target padding encodedPrefix)
          (none : Option Bool) }

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape_left
    (target : Tape Bool) (padding : List (Option Bool))
    (encodedPrefix : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape
      target padding encodedPrefix).left =
      target.left := by
  rfl

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape_head
    (target : Tape Bool) (padding : List (Option Bool))
    (encodedPrefix : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape
      target padding encodedPrefix).head =
      target.head := by
  rfl

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape_right
    (target : Tape Bool) (padding : List (Option Bool))
    (encodedPrefix : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape
      target padding encodedPrefix).right =
      target.right ++
        List.replicate
          (selectedSegmentLogicalTapeDecoderPaddedCleanupOutputPaddingLength
            target padding encodedPrefix)
          (none : Option Bool) := by
  rfl

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape_cells
    (target : Tape Bool) (padding : List (Option Bool))
    (encodedPrefix : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape
          target padding encodedPrefix) =
      Tape.cells target ++
        List.replicate
          (selectedSegmentLogicalTapeDecoderPaddedCleanupOutputPaddingLength
            target padding encodedPrefix)
          (none : Option Bool) := by
  simp [selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape,
    Tape.cells, List.append_assoc]

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape_normalizedOutput
    (target : Tape Bool) (padding : List (Option Bool))
    (encodedPrefix : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape
          target padding encodedPrefix) =
      Tape.normalizedOutput target := by
  change
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape
          target padding encodedPrefix)).filterMap (fun cell => cell) =
      (Tape.cells target).filterMap (fun cell => cell)
  rw [selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape_cells]
  simp [List.filterMap_append]

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape_contextLength
    (target : Tape Bool) (padding : List (Option Bool))
    (encodedPrefix : List (Option Bool)) :
    Tape.contextLength
        (selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape
          target padding encodedPrefix) =
      Tape.contextLength target +
        selectedSegmentLogicalTapeDecoderPaddedCleanupOutputPaddingLength
          target padding encodedPrefix := by
  simp [selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape,
    Tape.contextLength, List.length_append]
  lia

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape_equiv
    (target : Tape Bool) (padding : List (Option Bool))
    (encodedPrefix : List (Option Bool)) :
    Tape.Equiv
      (selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape
        target padding encodedPrefix)
      target := by
  constructor
  · rfl
  constructor
  · rfl
  · exact
      FoC.Computability.dropTrailingNone_append_replicate_none
        target.right
        (selectedSegmentLogicalTapeDecoderPaddedCleanupOutputPaddingLength
          target padding encodedPrefix)

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape_contextLength_ge_handoff
    (target : Tape Bool) (padding : List (Option Bool))
    (encodedPrefix : List (Option Bool)) :
    Tape.contextLength
        (canonicalPrimitiveSeqHandoffTape
          (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
            target padding encodedPrefix)) <=
      Tape.contextLength
        (selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape
          target padding encodedPrefix) := by
  simp [
    selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape,
    selectedSegmentLogicalTapeDecoderPaddedCleanupOutputPaddingLength,
    Tape.contextLength,
    List.length_append]
  lia

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape_contextLength_ge_handoff_nil
    (target : Tape Bool) (encodedPrefix : List (Option Bool)) :
    Tape.contextLength
        (tapeAtCells
          (selectedSegmentLogicalTapeDecoderPaddedCleanupLeftStack
            target encodedPrefix)
          [none, none]) <=
      Tape.contextLength
        (selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape
          target [] encodedPrefix) := by
  simpa [
    selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape_handoff_nil] using
    selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape_contextLength_ge_handoff
      target [] encodedPrefix

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape_contextLength_ge_handoff_singleton
    (target : Tape Bool) (pad : Option Bool)
    (encodedPrefix : List (Option Bool)) :
    Tape.contextLength
        (tapeAtCells
          (selectedSegmentLogicalTapeDecoderPaddedCleanupLeftStack
            target encodedPrefix)
          [pad, none]) <=
      Tape.contextLength
        (selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape
          target [pad] encodedPrefix) := by
  simpa [
    selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape_handoff_singleton] using
    selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape_contextLength_ge_handoff
      target [pad] encodedPrefix

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape_contextLength_ge_handoff_cons_cons
    (target : Tape Bool) (pad next : Option Bool)
    (padding encodedPrefix : List (Option Bool)) :
    Tape.contextLength
        (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
          target (pad :: next :: padding) encodedPrefix) <=
      Tape.contextLength
        (selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape
          target (pad :: next :: padding) encodedPrefix) := by
  simpa [
    selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape_handoff_cons_cons] using
    selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape_contextLength_ge_handoff
      target (pad :: next :: padding) encodedPrefix

/--
Exact cleanup to the padded representative, plus the public equivalence proof.
-/
structure SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupSpec
    (cleanup : MachineDescription) : Prop where
  subroutineReady : cleanup.SubroutineReady
  forward :
    forall (target : Tape Bool) (padding : List (Option Bool))
      (encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape
          (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
            target padding encodedPrefix))
        (selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape
          target padding encodedPrefix)
  closedRepresentative :
    forall (target : Tape Bool) (padding : List (Option Bool))
      (encodedPrefix : List (Option Bool)),
      ExactClosedFromTape cleanup
        (canonicalPrimitiveSeqHandoffTape
          (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
            target padding encodedPrefix))
        (selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape
          target padding encodedPrefix)
  outputEquiv :
    forall (target : Tape Bool) (padding : List (Option Bool))
      (encodedPrefix : List (Option Bool)),
      Tape.Equiv
        (selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape
          target padding encodedPrefix)
        target

def SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupConstruction :
    Prop :=
  exists cleanup : MachineDescription,
    SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupSpec cleanup

namespace SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupSpec

theorem toCleanupSpec
    {cleanup : MachineDescription}
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupSpec
        cleanup) :
    SelectedSegmentLogicalTapeDecoderPaddedCleanupSpec cleanup := by
  constructor
  · exact hcleanup.subroutineReady
  · intro target padding encodedPrefix
    let source :=
      selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
        target padding encodedPrefix
    let output :=
      selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape
        target padding encodedPrefix
    have hrun :
        cleanup.HaltsFromTapeEquiv source output :=
      HaltsFromTapeEquiv_of_input_equiv
        (D := cleanup)
        (Tin := canonicalPrimitiveSeqHandoffTape source)
        (Tin' := source)
        (Tout := output)
        (canonicalPrimitiveSeqHandoffTape_equiv source)
        (by
          simpa [source, output] using
            hcleanup.forward target padding encodedPrefix)
    rcases hrun with ⟨actual, hhalts, hequiv⟩
    exact
      ⟨actual, hhalts,
        Tape.Equiv.trans hequiv
          (by
            simpa [output] using
              hcleanup.outputEquiv target padding encodedPrefix)⟩

end SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupSpec

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupSpec_of_representativeSpec
    {cleanup : MachineDescription}
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupSpec
        cleanup) :
    SelectedSegmentLogicalTapeDecoderPaddedCleanupSpec cleanup :=
  hcleanup.toCleanupSpec

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupConstruction_of_representative
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupConstruction) :
    SelectedSegmentLogicalTapeDecoderPaddedCleanupConstruction := by
  rcases hcleanup with ⟨cleanup, hcleanupSpec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderPaddedCleanupSpec_of_representativeSpec
        hcleanupSpec⟩

/-- Forward-only representative cleanup contract. -/
def SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSpec
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (target : Tape Bool) (padding : List (Option Bool))
      (encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape
          (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
            target padding encodedPrefix))
        (selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape
          target padding encodedPrefix)

def SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardConstruction :
    Prop :=
  exists cleanup : MachineDescription,
    SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSpec
      cleanup

theorem selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupSpec_of_forwardSpec
    {cleanup : MachineDescription}
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSpec
        cleanup) :
    SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupSpec cleanup where
  subroutineReady := hcleanup.left
  forward := hcleanup.right
  closedRepresentative := by
    intro target padding encodedPrefix
    exact
      exactClosedFromTape_of_haltsFromTape_of_subroutineReady
        hcleanup.left
        (hcleanup.right target padding encodedPrefix)
  outputEquiv :=
    selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape_equiv

theorem selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupConstruction_of_forward
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardConstruction) :
    SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupConstruction := by
  rcases hcleanup with ⟨cleanup, hcleanupSpec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupSpec_of_forwardSpec
        hcleanupSpec⟩

def SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupNilPaddingSpec
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (target : Tape Bool) (encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape
          (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
            target [] encodedPrefix))
        (selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape
          target [] encodedPrefix)

def SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupSingletonPaddingSpec
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (target : Tape Bool) (pad : Option Bool)
      (encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape
          (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
            target [pad] encodedPrefix))
        (selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape
          target [pad] encodedPrefix)

def SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupConsConsPaddingSpec
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (target : Tape Bool) (pad next : Option Bool)
      (padding encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape
          (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
            target (pad :: next :: padding) encodedPrefix))
        (selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape
          target (pad :: next :: padding) encodedPrefix)

def SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupHandoffSplitSpec
    (cleanup : MachineDescription) : Prop :=
  SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupNilPaddingSpec
      cleanup ∧
    SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupSingletonPaddingSpec
      cleanup ∧
    SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupConsConsPaddingSpec
      cleanup

def SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupHandoffSplitConstruction :
    Prop :=
  exists cleanup : MachineDescription,
    SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupHandoffSplitSpec
      cleanup

def SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSplitSpec
    (cleanup : MachineDescription) : Prop :=
  SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupNilPaddingSpec
      cleanup ∧
    (cleanup.SubroutineReady ∧
      forall (target : Tape Bool) (pad : Option Bool)
        (padding encodedPrefix : List (Option Bool)),
        cleanup.HaltsFromTape
          (canonicalPrimitiveSeqHandoffTape
            (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
              target (pad :: padding) encodedPrefix))
          (selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape
            target (pad :: padding) encodedPrefix))

def SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSplitConstruction :
    Prop :=
  exists cleanup : MachineDescription,
    SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSplitSpec
      cleanup

theorem selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSplitSpec_of_handoffSplitSpec
    {cleanup : MachineDescription}
    (hsplit :
      SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupHandoffSplitSpec
        cleanup) :
    SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSplitSpec
      cleanup := by
  rcases hsplit with ⟨hnil, hsingle, hlong⟩
  rcases hnil with ⟨hready, hnilRun⟩
  rcases hsingle with ⟨_hreadySingle, hsingleRun⟩
  rcases hlong with ⟨_hreadyLong, hlongRun⟩
  constructor
  · exact ⟨hready, hnilRun⟩
  · refine ⟨hready, ?_⟩
    intro target pad padding encodedPrefix
    cases padding with
    | nil =>
        exact hsingleRun target pad encodedPrefix
    | cons next padding =>
        exact hlongRun target pad next padding encodedPrefix

theorem selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupHandoffSplitSpec_of_forwardSplitSpec
    {cleanup : MachineDescription}
    (hsplit :
      SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSplitSpec
        cleanup) :
    SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupHandoffSplitSpec
      cleanup := by
  rcases hsplit with ⟨hnil, hcons⟩
  rcases hnil with ⟨hready, hnilRun⟩
  rcases hcons with ⟨_hreadyCons, hconsRun⟩
  exact
    ⟨⟨hready, hnilRun⟩,
      ⟨hready, fun target pad encodedPrefix =>
        hconsRun target pad [] encodedPrefix⟩,
      ⟨hready, fun target pad next padding encodedPrefix =>
        hconsRun target pad (next :: padding) encodedPrefix⟩⟩

theorem selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSplitConstruction_of_handoffSplit
    (hsplit :
      SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupHandoffSplitConstruction) :
    SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSplitConstruction := by
  rcases hsplit with ⟨cleanup, hsplitSpec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSplitSpec_of_handoffSplitSpec
        hsplitSpec⟩

theorem selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupHandoffSplitConstruction_of_forwardSplit
    (hsplit :
      SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSplitConstruction) :
    SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupHandoffSplitConstruction := by
  rcases hsplit with ⟨cleanup, hsplitSpec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupHandoffSplitSpec_of_forwardSplitSpec
        hsplitSpec⟩

theorem selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSplitConstruction_iff_handoffSplit :
    SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSplitConstruction <->
      SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupHandoffSplitConstruction := by
  constructor
  · exact
      selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupHandoffSplitConstruction_of_forwardSplit
  · exact
      selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSplitConstruction_of_handoffSplit

theorem selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSpec_of_handoffSplitSpec
    {cleanup : MachineDescription}
    (hsplit :
      SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupHandoffSplitSpec
        cleanup) :
    SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSpec
      cleanup := by
  rcases hsplit with ⟨hnil, hsingle, hlong⟩
  rcases hnil with ⟨hready, hnilRun⟩
  rcases hsingle with ⟨_hreadySingle, hsingleRun⟩
  rcases hlong with ⟨_hreadyLong, hlongRun⟩
  refine ⟨hready, ?_⟩
  intro target padding encodedPrefix
  cases padding with
  | nil =>
      exact hnilRun target encodedPrefix
  | cons pad padding =>
      cases padding with
      | nil =>
          exact hsingleRun target pad encodedPrefix
      | cons next padding =>
          exact hlongRun target pad next padding encodedPrefix

theorem selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSpec_of_forwardSplitSpec
    {cleanup : MachineDescription}
    (hsplit :
      SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSplitSpec
        cleanup) :
    SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSpec
      cleanup := by
  rcases hsplit with ⟨hnil, hcons⟩
  rcases hnil with ⟨hready, hnilRun⟩
  rcases hcons with ⟨_hreadyCons, hconsRun⟩
  refine ⟨hready, ?_⟩
  intro target padding encodedPrefix
  cases padding with
  | nil =>
      exact hnilRun target encodedPrefix
  | cons pad padding =>
      exact hconsRun target pad padding encodedPrefix

theorem selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSplitSpec_of_forwardSpec
    {cleanup : MachineDescription}
    (hforward :
      SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSpec
        cleanup) :
    SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSplitSpec
      cleanup := by
  rcases hforward with ⟨hready, hrun⟩
  exact
    ⟨⟨hready, fun target encodedPrefix =>
        hrun target [] encodedPrefix⟩,
      ⟨hready, fun target pad padding encodedPrefix =>
        hrun target (pad :: padding) encodedPrefix⟩⟩

theorem selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSpec_iff_forwardSplitSpec
    (cleanup : MachineDescription) :
    SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSpec
        cleanup <->
      SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSplitSpec
        cleanup := by
  constructor
  · exact
      selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSplitSpec_of_forwardSpec
  · exact
      selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSpec_of_forwardSplitSpec

theorem selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardConstruction_of_handoffSplit
    (hsplit :
      SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupHandoffSplitConstruction) :
    SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardConstruction := by
  rcases hsplit with ⟨cleanup, hsplitSpec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSpec_of_handoffSplitSpec
        hsplitSpec⟩

theorem selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardConstruction_of_forwardSplit
    (hsplit :
      SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSplitConstruction) :
    SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardConstruction := by
  rcases hsplit with ⟨cleanup, hsplitSpec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSpec_of_forwardSplitSpec
        hsplitSpec⟩

theorem selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSplitConstruction_of_forward
    (hforward :
      SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardConstruction) :
    SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSplitConstruction := by
  rcases hforward with ⟨cleanup, hforwardSpec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSplitSpec_of_forwardSpec
        hforwardSpec⟩

theorem selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardConstruction_iff_forwardSplit :
    SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardConstruction <->
      SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSplitConstruction := by
  constructor
  · exact
      selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSplitConstruction_of_forward
  · exact
      selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardConstruction_of_forwardSplit

theorem selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupConstruction_of_handoffSplit
    (hsplit :
      SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupHandoffSplitConstruction) :
    SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupConstruction :=
  selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupConstruction_of_forward
    (selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardConstruction_of_handoffSplit
      hsplit)

theorem selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupConstruction_of_forwardSplit
    (hsplit :
      SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSplitConstruction) :
    SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupConstruction :=
  selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupConstruction_of_forward
    (selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardConstruction_of_forwardSplit
      hsplit)

theorem selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardConstruction_of_construction
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupConstruction) :
    SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardConstruction := by
  rcases hcleanup with ⟨cleanup, hcleanupSpec⟩
  exact
    ⟨cleanup,
      ⟨hcleanupSpec.subroutineReady, hcleanupSpec.forward⟩⟩

theorem selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSplitConstruction_of_construction
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupConstruction) :
    SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSplitConstruction :=
  selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSplitConstruction_of_forward
    (selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardConstruction_of_construction
      hcleanup)

theorem selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupConstruction_iff_forward :
    SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupConstruction <->
      SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardConstruction := by
  constructor
  · exact
      selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardConstruction_of_construction
  · exact
      selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupConstruction_of_forward

theorem selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupConstruction_iff_forwardSplit :
    SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupConstruction <->
      SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSplitConstruction := by
  constructor
  · exact
      selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSplitConstruction_of_construction
  · exact
      selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupConstruction_of_forwardSplit

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC

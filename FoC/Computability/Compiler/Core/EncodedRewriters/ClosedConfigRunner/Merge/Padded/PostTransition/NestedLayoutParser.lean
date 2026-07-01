import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Merge.Padded.PostTransition.Specs

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

/-!
# Merge post-transition nested layout parser
-/

def SelectedMergePaddedEmitterNestedLayoutRawSourceTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells []
    ((CanonicalLayouts.DovetailLayoutScanner.dovetailLayoutFieldBits
      p.L []).map some)

def SelectedMergePaddedEmitterNestedLayoutRawParsedTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  CanonicalLayouts.DovetailLayoutScanner.restoredCheckedHandoffTapeFromTail
    (CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyRestoredBitsRev
      p.L).reverse

theorem SelectedMergePaddedEmitterNestedLayoutRawSourceTape_move_left_move_right
    (p : SelectedMergeEmitterPayload) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (SelectedMergePaddedEmitterNestedLayoutRawSourceTape p)) =
      SelectedMergePaddedEmitterNestedLayoutRawSourceTape p := by
  rw [SelectedMergePaddedEmitterNestedLayoutRawSourceTape,
    CanonicalLayouts.DovetailLayoutScanner.dovetailLayoutFieldBits_nil_eq_first_body]
  rcases
      CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyBits_cons_false
        p.L with
    ⟨tail, htail⟩
  rw [htail]
  simp [DovetailInitialLayoutInitializer.tapeAtCells,
    Tape.move, Tape.moveLeft, Tape.moveRight]

theorem
    SelectedMergePaddedEmitterNestedLayoutRawParsedTape_move_left_move_right
    (p : SelectedMergeEmitterPayload) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (SelectedMergePaddedEmitterNestedLayoutRawParsedTape p)) =
      SelectedMergePaddedEmitterNestedLayoutRawParsedTape p := by
  rw [SelectedMergePaddedEmitterNestedLayoutRawParsedTape]
  rw [
    CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyRestoredBitsRev_reverse]
  rcases
      CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyBits_cons_false
        p.L with
    ⟨tail, htail⟩
  rw [htail]
  cases tail <;>
    simp [
      CanonicalLayouts.DovetailLayoutScanner.restoredCheckedHandoffTapeFromTail,
      Tape.move, Tape.moveLeft, Tape.moveRight]

theorem checkedDovetailLayoutScannerDescription_haltsFrom_raw_nestedLayout
    (L : DovetailLayout) :
    CanonicalLayouts.DovetailLayoutScanner.CheckedDovetailLayoutScannerDescription.HaltsFromTape
      (DovetailInitialLayoutInitializer.tapeAtCells []
        ((CanonicalLayouts.DovetailLayoutScanner.dovetailLayoutFieldBits
          L []).map some))
      (CanonicalLayouts.DovetailLayoutScanner.restoredCheckedHandoffTapeFromTail
        (CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyRestoredBitsRev
          L).reverse) := by
  rcases
      CanonicalLayouts.DovetailLayoutScanner.run_checkedDovetailLayoutScanner_raw_to_checkedHandoff
        L with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  constructor
  · simpa [MachineDescription.HaltsFromTapeIn] using
      congrArg MachineDescription.Configuration.state hsteps
  · simpa [MachineDescription.HaltsFromTapeIn] using
      congrArg MachineDescription.Configuration.tape hsteps

theorem
    checkedDovetailLayoutScannerDescription_haltsFrom_mergeNestedLayoutRawSource
    (p : SelectedMergeEmitterPayload) :
    CanonicalLayouts.DovetailLayoutScanner.CheckedDovetailLayoutScannerDescription.HaltsFromTape
      (SelectedMergePaddedEmitterNestedLayoutRawSourceTape p)
      (SelectedMergePaddedEmitterNestedLayoutRawParsedTape p) := by
  exact checkedDovetailLayoutScannerDescription_haltsFrom_raw_nestedLayout
    p.L

def SelectedMergePaddedEmitterNestedLayoutWindowMaterializerSpec
    (materializer : MachineDescription) : Prop :=
  materializer.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      materializer.HaltsFromTape
        (SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape p)
        (SelectedMergePaddedEmitterNestedLayoutRawSourceTape p)

def SelectedMergePaddedEmitterNestedLayoutWindowRestorerSpec
    (restorer : MachineDescription) : Prop :=
  restorer.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      restorer.HaltsFromTape
        (SelectedMergePaddedEmitterNestedLayoutRawParsedTape p)
        (SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape p)

def SelectedMergePaddedEmitterNestedLayoutWindowMaterializerAndRestorerConstruction :
    Prop :=
  exists materializer : MachineDescription,
  exists restorer : MachineDescription,
    SelectedMergePaddedEmitterNestedLayoutWindowMaterializerSpec
      materializer ∧
    SelectedMergePaddedEmitterNestedLayoutWindowRestorerSpec restorer

def SelectedMergePaddedEmitterNestedLayoutWindowParser
    (materializer restorer : MachineDescription) : MachineDescription :=
  SeqViaCanonical
    (SeqViaCanonical materializer
      CanonicalLayouts.DovetailLayoutScanner.CheckedDovetailLayoutScannerDescription)
    restorer

theorem SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedSpec_of_windowMaterializerAndRestorer
    {materializer restorer : MachineDescription}
    (hmaterializer :
      SelectedMergePaddedEmitterNestedLayoutWindowMaterializerSpec
        materializer)
    (hrestorer :
      SelectedMergePaddedEmitterNestedLayoutWindowRestorerSpec restorer) :
    SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedSpec
      (SelectedMergePaddedEmitterNestedLayoutWindowParser
        materializer restorer) := by
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        (SeqViaCanonical_subroutineReady
          hmaterializer.left
          CanonicalLayouts.DovetailLayoutScanner.checkedDovetailLayoutScannerDescription_subroutineReady)
        hrestorer.left
  · intro p
    have hscannerSeq :
        (SeqViaCanonical materializer
          CanonicalLayouts.DovetailLayoutScanner.CheckedDovetailLayoutScannerDescription).HaltsFromTape
          (SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape p)
          (SelectedMergePaddedEmitterNestedLayoutRawParsedTape p) := by
      exact
        SeqViaCanonical_haltsFromTape_of_haltsFromTape
          hmaterializer.left
          CanonicalLayouts.DovetailLayoutScanner.checkedDovetailLayoutScannerDescription_subroutineReady
          (hmaterializer.right p)
          (SelectedMergePaddedEmitterNestedLayoutRawSourceTape_move_left_move_right
            p)
          (checkedDovetailLayoutScannerDescription_haltsFrom_mergeNestedLayoutRawSource
            p)
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        (SeqViaCanonical_subroutineReady
          hmaterializer.left
          CanonicalLayouts.DovetailLayoutScanner.checkedDovetailLayoutScannerDescription_subroutineReady)
        hrestorer.left
        hscannerSeq
        (SelectedMergePaddedEmitterNestedLayoutRawParsedTape_move_left_move_right
          p)
        (hrestorer.right p)

theorem selectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedConstruction_of_windowMaterializerAndRestorer
    (h :
      SelectedMergePaddedEmitterNestedLayoutWindowMaterializerAndRestorerConstruction) :
    SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedConstruction := by
  rcases h with ⟨materializer, restorer, hmaterializer, hrestorer⟩
  exact
    ⟨SelectedMergePaddedEmitterNestedLayoutWindowParser
        materializer restorer,
      SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedSpec_of_windowMaterializerAndRestorer
        hmaterializer hrestorer⟩

/--
Finite-machine leaf that exposes the nested raw layout field from the restored
outer source fields and restores the checked scanner result to the parsed
source-fields shape.
-/
theorem selectedMergePaddedEmitterNestedLayoutWindowMaterializerAndRestorerConstruction :
    SelectedMergePaddedEmitterNestedLayoutWindowMaterializerAndRestorerConstruction := by
  sorry

/--
Common finite-machine leaf that parses the nested layout code word after the
outer source fields have been restored.
-/
theorem selectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedConstruction :
    SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedConstruction := by
  exact
    selectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedConstruction_of_windowMaterializerAndRestorer
      selectedMergePaddedEmitterNestedLayoutWindowMaterializerAndRestorerConstruction

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC

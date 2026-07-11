import FoC.Computability.Compiler.Core.StructuredConstructionTargets.TwoStageEndpoints
import FoC.Computability.Compiler.Dovetail.Scanner.Simulator.Recognizer

set_option doc.verso true

/-!
# Simulator-layout word-start input materializer

The word-start simulator-layout recognizer followed by the shared structured
embedding emitter materializes the guarded three-logical-tape input for
exactly the encoded simulator-layout word family.  This closes the
materializer obligation of the fuel-output endpoint.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace StructuredConstructionTargets

open CommonGround.FiniteTransducers
open EncRewriters.CanonicalLayouts.SimulatorLayoutScanner

/-- Public input-bits family of encoded simulator layouts. -/
def simulatorLayoutWordStartInputBits (L : SimulatorLayout) : Word Bool :=
  encodeCodeWordAsInput (SimulatorLayout.encode L)

/-- Canonical guarded three-logical-tape target of the family. -/
def simulatorLayoutWordStartInitializedTape
    (L : SimulatorLayout) : Tape Bool :=
  structured3InputMaterializerTargetTape
    (Tape.input (simulatorLayoutWordStartInputBits L))
    Tape.blank

def simulatorLayoutWordStartMaterializerDescription : MachineDescription :=
  seqSubroutine
    SimulatorLayoutWordStartRecognizerDescription
    structured3InputEmbeddingEmitterDescription
    tapeCodePrimitiveCodeWordHandoffMove

private abbrev MAT := simulatorLayoutWordStartMaterializerDescription
private abbrev REC := SimulatorLayoutWordStartRecognizerDescription
private abbrev EMIT := structured3InputEmbeddingEmitterDescription

theorem structured3InputEmbeddingEmitterDescription_subroutineReady :
    EMIT.SubroutineReady :=
  structured3InputEmbeddingEmitterDescription_targetCellsRunSpec.left

theorem simulatorLayoutWordStartMaterializerDescription_subroutineReady :
    MAT.SubroutineReady :=
  seqSubroutine_subroutineReady
    simulatorLayoutWordStartRecognizerDescription_subroutineReady
    structured3InputEmbeddingEmitterDescription_subroutineReady

theorem move_left_checkedSimulatorHandoffTape
    (L : SimulatorLayout) :
    Tape.move Direction.left (checkedSimulatorHandoffTape L) =
      checkedSimulatorPaddedStartTape L := by
  rw [checkedSimulatorHandoffTape, checkedSimulatorPaddedStartTape,
    simulatorLayoutFieldBits_nil_eq_first_body L]
  cases hbody : markedSimulatorLayoutBodyBits L with
  | nil =>
      simp [DovetailInitialLayoutInitializer.tapeAtCells,
        Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons b rest =>
      simp [DovetailInitialLayoutInitializer.tapeAtCells,
        Tape.move, Tape.moveLeft, Tape.moveRight]

/--
Forward equivalence behavior of the composed word-start materializer.
-/
theorem simulatorLayoutWordStartMaterializer_forward
    (L : SimulatorLayout) :
    MAT.HaltsFromTapeEquiv
      (Tape.input (simulatorLayoutWordStartInputBits L))
      (simulatorLayoutWordStartInitializedTape L) := by
  have hbits :
      simulatorLayoutWordStartInputBits L =
        simulatorLayoutInputBits L := rfl
  have hrec :
      REC.HaltsFromTape
        (Tape.input (simulatorLayoutWordStartInputBits L))
        (checkedSimulatorHandoffTape L) := by
    rw [hbits]
    exact simulatorLayoutWordStartRecognizerDescription_forward L
  have hhandoff :
      Tape.move tapeCodePrimitiveCodeWordHandoffMove
          (checkedSimulatorHandoffTape L) =
        checkedSimulatorPaddedStartTape L :=
    move_left_checkedSimulatorHandoffTape L
  have hemitExact :
      EMIT.HaltsFromTape
        (Tape.input (simulatorLayoutWordStartInputBits L))
        (structured3InputEmbeddingEmitterTargetTape
          (simulatorLayoutWordStartInputBits L)) :=
    structured3InputEmbeddingEmitterDescription_targetCellsRunSpec.right
      (simulatorLayoutWordStartInputBits L)
  have hpaddedEq :
      checkedSimulatorPaddedStartTape L =
        DovetailInitialLayoutInitializer.tapeAtCells [none]
          (List.append
            ((simulatorLayoutWordStartInputBits L).map some) [none]) := by
    rw [checkedSimulatorPaddedStartTape, hbits,
      ← simulatorLayoutInputBits_eq_fieldBits]
  have hemitEquiv :
      EMIT.HaltsFromTapeEquiv
        (checkedSimulatorPaddedStartTape L)
        (structured3InputEmbeddingEmitterTargetTape
          (simulatorLayoutWordStartInputBits L)) := by
    rw [hpaddedEq]
    exact
      HaltsFromTapeEquiv_of_input_equiv
        (Tape.Equiv.symm
          (paddedStartTape_equiv_input
            (simulatorLayoutWordStartInputBits L)))
        hemitExact
  have hcomposed :
      MAT.HaltsFromTapeEquiv
        (Tape.input (simulatorLayoutWordStartInputBits L))
        (structured3InputEmbeddingEmitterTargetTape
          (simulatorLayoutWordStartInputBits L)) := by
    simpa [simulatorLayoutWordStartMaterializerDescription] using
      CommonGround.SeqComposition.seqSubroutine_haltsFromTapeEquiv_of_haltsFromTape_eq
        simulatorLayoutWordStartRecognizerDescription_subroutineReady
        structured3InputEmbeddingEmitterDescription_subroutineReady
        hrec hhandoff hemitEquiv
  rw [show
      simulatorLayoutWordStartInitializedTape L =
        structured3InputEmbeddingEmitterTargetTape
          (simulatorLayoutWordStartInputBits L) by
    rw [simulatorLayoutWordStartInitializedTape,
      structured3InputEmbeddingEmitterTargetTape_eq_materializerTarget]]
  exact hcomposed

/--
Word-start closedness of the composed materializer.
-/
theorem simulatorLayoutWordStartMaterializer_closedIndex :
    EquivClosedIndexedFromWordStart
      MAT
      simulatorLayoutWordStartInputBits
      simulatorLayoutWordStartInitializedTape := by
  intro w T hhalt
  rcases
      seqSubroutine_haltsFromTape_inv
        (A := REC) (B := EMIT)
        (handoffMove := tapeCodePrimitiveCodeWordHandoffMove)
        simulatorLayoutWordStartRecognizerDescription_subroutineReady
        structured3InputEmbeddingEmitterDescription_subroutineReady
        (by
          simpa [simulatorLayoutWordStartMaterializerDescription] using
            hhalt) with
    ⟨Tpre, hpre, nB, hemitRun⟩
  rcases
      simulatorLayoutWordStartRecognizerDescription_closed hpre with
    ⟨L, hwL, hTpre⟩
  have hmoveEquiv :
      Tape.Equiv
        (Tape.move tapeCodePrimitiveCodeWordHandoffMove Tpre)
        (Tape.input (simulatorLayoutWordStartInputBits L)) := by
    have hmove :
        Tape.Equiv
          (Tape.move tapeCodePrimitiveCodeWordHandoffMove Tpre)
          (Tape.move Direction.left
            (checkedSimulatorHandoffTape L)) :=
      Tape.Equiv.move hTpre Direction.left
    rw [move_left_checkedSimulatorHandoffTape L] at hmove
    refine Tape.Equiv.trans hmove ?_
    rw [show
        checkedSimulatorPaddedStartTape L =
          DovetailInitialLayoutInitializer.tapeAtCells [none]
            (List.append
              ((simulatorLayoutWordStartInputBits L).map some)
              [none]) by
      rw [checkedSimulatorPaddedStartTape,
        ← simulatorLayoutInputBits_eq_fieldBits]
      rfl]
    exact
      paddedStartTape_equiv_input (simulatorLayoutWordStartInputBits L)
  have hemitFrom :
      EMIT.HaltsFromTape
        (Tape.move tapeCodePrimitiveCodeWordHandoffMove Tpre) T := by
    refine ⟨nB, ?_, ?_⟩
    · simpa using congrArg Configuration.state hemitRun
    · simpa using congrArg Configuration.tape hemitRun
  rcases
      HaltsFromTapeEquiv_of_input_equiv
        (D := EMIT)
        (Tin := Tape.move tapeCodePrimitiveCodeWordHandoffMove Tpre)
        (Tin' := Tape.input (simulatorLayoutWordStartInputBits L))
        (Tout := T)
        hmoveEquiv
        hemitFrom with
    ⟨Tclean, hcleanRun, hTclean⟩
  have hcleanTarget :
      Tclean =
        structured3InputEmbeddingEmitterTargetTape
          (simulatorLayoutWordStartInputBits L) :=
    haltsFromTape_functional_of_haltTransitionFree
      structured3InputEmbeddingEmitterDescription_subroutineReady.right
      hcleanRun
      (structured3InputEmbeddingEmitterDescription_targetCellsRunSpec.right
        (simulatorLayoutWordStartInputBits L))
  refine ⟨L, hwL, ?_⟩
  have hTargetEq :
      structured3InputEmbeddingEmitterTargetTape
          (simulatorLayoutWordStartInputBits L) =
        simulatorLayoutWordStartInitializedTape L := by
    rw [simulatorLayoutWordStartInitializedTape,
      structured3InputEmbeddingEmitterTargetTape_eq_materializerTarget]
  rw [← hTargetEq, ← hcleanTarget]
  exact Tape.Equiv.symm hTclean

/--
Word-start equivalence materializer construction for the simulator-layout
family: recognizer plus shared embedding emitter.
-/
theorem simulatorLayoutWordStartEquivMaterializerConstruction_core :
    Structured3EndpointWordStartEquivMaterializerConstruction
      simulatorLayoutWordStartInputBits
      simulatorLayoutWordStartInitializedTape := by
  refine
    ⟨simulatorLayoutWordStartMaterializerDescription,
      simulatorLayoutWordStartMaterializerDescription_subroutineReady, ?_, ?_⟩
  · exact simulatorLayoutWordStartMaterializer_forward
  · exact simulatorLayoutWordStartMaterializer_closedIndex

end StructuredConstructionTargets

end Computability
end FoC

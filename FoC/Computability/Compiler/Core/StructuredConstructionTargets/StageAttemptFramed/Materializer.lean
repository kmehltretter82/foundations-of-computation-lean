import FoC.Computability.Compiler.Core.StructuredConstructionTargets.StageAttemptFramed.RecognizerClosed

/-! Word-start materializer for framed stage-attempt controller layouts. -/

namespace FoC.Computability.StructuredConstructionTargets.StageAttemptFramedMaterializer
open Languages
open MachineDescription
open CommonGround.SeqComposition
open EncRewriters.CanonicalLayouts.DovetailLayoutScanner
open Internal

private def StageAttemptFramedWordStartMaterializerDescription :
    MachineDescription :=
  seqSubroutine
    ControllerWordStartRecognizerDescription
    structured3InputEmbeddingEmitterDescription
    tapeCodePrimitiveCodeWordHandoffMove

private abbrev MAT := StageAttemptFramedWordStartMaterializerDescription
private abbrev EMIT := structured3InputEmbeddingEmitterDescription

private theorem stageAttemptFramedEmbeddingEmitter_subroutineReady :
    EMIT.SubroutineReady :=
  structured3InputEmbeddingEmitterDescription_targetCellsRunSpec.left

private theorem stageAttemptFramedWordStartMaterializerDescription_subroutineReady :
    MAT.SubroutineReady := by
  exact seqSubroutine_subroutineReady
    controllerWordStartRecognizerDescription_subroutineReady
    stageAttemptFramedEmbeddingEmitter_subroutineReady

private theorem stageAttemptFramedWordStartMaterializer_forward
    (C : DovetailControllerLayout) :
    MAT.HaltsFromTapeEquiv
      (Tape.input (stageAttemptFramedStructuredInputBits C))
      (stageAttemptFramedStructuredInitializedTape C) := by
  have hrecognizer := controllerWordStartRecognizerDescription_forward C
  have hemitterExact :
      EMIT.HaltsFromTape
        (Tape.input (stageAttemptFramedStructuredInputBits C))
        (structured3InputEmbeddingEmitterTargetTape
          (stageAttemptFramedStructuredInputBits C)) :=
    structured3InputEmbeddingEmitterDescription_targetCellsRunSpec.right
      (stageAttemptFramedStructuredInputBits C)
  have hemitter :
      EMIT.HaltsFromTapeEquiv
        (Tape.move tapeCodePrimitiveCodeWordHandoffMove
          (restoredCheckedHandoffTapeFromTail
            (markedControllerBodyBits C)))
        (structured3InputEmbeddingEmitterTargetTape
          (stageAttemptFramedStructuredInputBits C)) := by
    simpa [tapeCodePrimitiveCodeWordHandoffMove] using
      HaltsFromTapeEquiv_of_input_equiv
        (Tape.Equiv.symm
          (move_left_restoredCheckedHandoffTape_equiv_input C))
        hemitterExact
  have hcomposed :
      MAT.HaltsFromTapeEquiv
        (Tape.input (stageAttemptFramedStructuredInputBits C))
        (structured3InputEmbeddingEmitterTargetTape
          (stageAttemptFramedStructuredInputBits C)) := by
    simpa [StageAttemptFramedWordStartMaterializerDescription] using
      CommonGround.SeqComposition.seqSubroutine_haltsFromTapeEquiv_of_haltsFromTapeEquiv_eq
        controllerWordStartRecognizerDescription_subroutineReady
        stageAttemptFramedEmbeddingEmitter_subroutineReady
        hrecognizer rfl hemitter
  rw [show
      stageAttemptFramedStructuredInitializedTape C =
        structured3InputEmbeddingEmitterTargetTape
          (stageAttemptFramedStructuredInputBits C) by
    rw [stageAttemptFramedStructuredInitializedTape,
      structured3InputEmbeddingEmitterTargetTape_eq_materializerTarget]]
  exact hcomposed

private theorem stageAttemptFramedWordStartMaterializer_closedIndex :
    EquivClosedIndexedFromWordStart
      MAT
      stageAttemptFramedStructuredInputBits
      stageAttemptFramedStructuredInitializedTape := by
  intro w T hhalt
  rcases
      seqSubroutine_haltsFromTape_inv
        (A := REC) (B := EMIT)
        (handoffMove := tapeCodePrimitiveCodeWordHandoffMove)
        controllerWordStartRecognizerDescription_subroutineReady
        stageAttemptFramedEmbeddingEmitter_subroutineReady
        (by
          simpa [StageAttemptFramedWordStartMaterializerDescription]
            using hhalt) with
    ⟨Tpre, hpre, nEmitter, hemitterRun⟩
  rcases controllerWordStartRecognizerDescription_closed hpre with
    ⟨C, hwC, hTpre⟩
  have hmoveEquiv :
      Tape.Equiv
        (Tape.move tapeCodePrimitiveCodeWordHandoffMove Tpre)
        (Tape.input (stageAttemptFramedStructuredInputBits C)) := by
    exact Tape.Equiv.trans
      (Tape.Equiv.move hTpre Direction.left)
      (move_left_restoredCheckedHandoffTape_equiv_input C)
  have hemitterFrom :
      EMIT.HaltsFromTape
        (Tape.move tapeCodePrimitiveCodeWordHandoffMove Tpre) T := by
    refine ⟨nEmitter, ?_, ?_⟩
    · simpa using congrArg Configuration.state hemitterRun
    · simpa using congrArg Configuration.tape hemitterRun
  rcases
      HaltsFromTapeEquiv_of_input_equiv
        (D := EMIT)
        (Tin := Tape.move tapeCodePrimitiveCodeWordHandoffMove Tpre)
        (Tin' := Tape.input (stageAttemptFramedStructuredInputBits C))
        (Tout := T)
        hmoveEquiv hemitterFrom with
    ⟨Tclean, hcleanRun, hTclean⟩
  have hcleanTarget :
      Tclean =
        structured3InputEmbeddingEmitterTargetTape
          (stageAttemptFramedStructuredInputBits C) :=
    haltsFromTape_functional_of_haltTransitionFree
      stageAttemptFramedEmbeddingEmitter_subroutineReady.2
      hcleanRun
      (structured3InputEmbeddingEmitterDescription_targetCellsRunSpec.right
        (stageAttemptFramedStructuredInputBits C))
  refine ⟨C, hwC, ?_⟩
  have hTargetEq :
      structured3InputEmbeddingEmitterTargetTape
          (stageAttemptFramedStructuredInputBits C) =
        stageAttemptFramedStructuredInitializedTape C := by
    rw [stageAttemptFramedStructuredInitializedTape,
      structured3InputEmbeddingEmitterTargetTape_eq_materializerTarget]
  rw [← hTargetEq, ← hcleanTarget]
  exact Tape.Equiv.symm hTclean

theorem stageAttemptFramedWordStartEquivMaterializerConstruction_core :
    Structured3EndpointWordStartEquivMaterializerConstruction
      (fun C : DovetailControllerLayout =>
        encodeCodeWordAsInput (DovetailControllerLayout.encode C))
      (fun C : DovetailControllerLayout =>
        CommonGround.FiniteTransducers.structured3InputMaterializerTargetTape
          (Tape.input
            (encodeCodeWordAsInput (DovetailControllerLayout.encode C)))
          Tape.blank) := by
  change Structured3EndpointWordStartEquivMaterializerConstruction
    stageAttemptFramedStructuredInputBits
    stageAttemptFramedStructuredInitializedTape
  refine
    ⟨StageAttemptFramedWordStartMaterializerDescription,
      stageAttemptFramedWordStartMaterializerDescription_subroutineReady,
      ?_, ?_⟩
  · exact stageAttemptFramedWordStartMaterializer_forward
  · exact stageAttemptFramedWordStartMaterializer_closedIndex

end FoC.Computability.StructuredConstructionTargets.StageAttemptFramedMaterializer

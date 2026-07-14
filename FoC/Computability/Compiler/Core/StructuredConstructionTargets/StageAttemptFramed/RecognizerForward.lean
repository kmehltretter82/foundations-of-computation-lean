import FoC.Computability.Compiler.Core.StructuredConstructionTargets.FuelSimulator
import FoC.Computability.Compiler.Core.StructuredConstructionTargets.TwoStageEndpoints
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.AppendWord
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.BoundaryEraser
import FoC.Computability.Compiler.Core.CommonGround.SameHeadComposition
import FoC.Computability.Compiler.Dovetail.Scanner.Simulator.Recognizer
/-! Forward recognizer proof for framed stage-attempt controller layouts. -/
namespace FoC.Computability.StructuredConstructionTargets.StageAttemptFramedMaterializer.Internal
open Languages
open MachineDescription
open FoC.Computability.DovetailInitialLayoutInitializer
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner
open CommonGround.SeqComposition
open EncRewriters.CanonicalLayouts.DovetailLayoutScanner
open EncRewriters.CanonicalLayouts.SimulatorLayoutScanner
def stageAttemptFramedStructuredInputBits
    (C : DovetailControllerLayout) : Word Bool :=
  encodeCodeWordAsInput (DovetailControllerLayout.encode C)

def stageAttemptFramedStructuredInitializedTape
    (C : DovetailControllerLayout) : Tape Bool :=
  CommonGround.FiniteTransducers.structured3InputMaterializerTargetTape
    (Tape.input (stageAttemptFramedStructuredInputBits C))
    Tape.blank

def sentinelCode : Word MachineCodeSymbol :=
  MachineCodeSymbol.header :: encodeBoolAppend false []

def sentinelBits : Word Bool :=
  encodeCodeWordAsInput sentinelCode

abbrev CWA := CodeWordAlignedPreScannerDescription
private abbrev APP :=
  CommonGround.FiniteTransducers.generatedAppendWordDescription sentinelBits
private abbrev REW := CommonGround.FiniteTransducers.rightEdgeRewindDescription
abbrev MFTB := MarkFirstTransitionBitDescription
abbrev HRP := HeaderRemainderPrefixScannerDescription
abbrev BWSS := BoolWordSuffixScannerDescription
abbrev NNSS :=
  EncRewriters.CanonicalLayouts.DovetailStagePrefix.NonemptyNatSuffixScannerDescription
abbrev BFS := BoolFinalScannerDescription
abbrev ERASE :=
  CommonGround.FiniteTransducers.leftBoundaryEraserDescription
abbrev RFM := ReturnToFirstMarkerDescription

def FinalSentinelCleanupDescription : MachineDescription :=
  seqSubroutine
    (CommonGround.SameHeadComposition.leftRightSeqDescription BFS ERASE)
    RFM Direction.left

def SentinelScannerDescription : MachineDescription :=
  seqSubroutine MFTB
    (seqSubroutine HRP FinalSentinelCleanupDescription Direction.right)
    Direction.right

def ResultSentinelScannerDescription : MachineDescription :=
  seqSubroutine BWSS SentinelScannerDescription Direction.right

def StageResultSentinelScannerDescription : MachineDescription :=
  seqSubroutine NNSS ResultSentinelScannerDescription Direction.right

def InputStageResultSentinelScannerDescription : MachineDescription :=
  seqSubroutine BWSS StageResultSentinelScannerDescription Direction.right

def MarkedControllerBodyScannerDescription : MachineDescription :=
  seqSubroutine HRP InputStageResultSentinelScannerDescription Direction.right

def CheckedControllerSentinelScannerDescription : MachineDescription :=
  seqSubroutine MFTB MarkedControllerBodyScannerDescription Direction.right

def AppendSentinelRewindDescription : MachineDescription :=
  seqSubroutine APP REW Direction.left

def AlignedAppendRewindDescription : MachineDescription :=
  seqSubroutine CWA AppendSentinelRewindDescription Direction.left

def ControllerWordStartRecognizerDescription : MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    AlignedAppendRewindDescription CheckedControllerSentinelScannerDescription

abbrev FINAL := FinalSentinelCleanupDescription
abbrev SENT := SentinelScannerDescription
abbrev RSL := ResultSentinelScannerDescription
abbrev SRSL := StageResultSentinelScannerDescription
abbrev ISRSL := InputStageResultSentinelScannerDescription
abbrev BODY := MarkedControllerBodyScannerDescription
abbrev CHECK := CheckedControllerSentinelScannerDescription
abbrev AR := AppendSentinelRewindDescription
abbrev PRE := AlignedAppendRewindDescription
abbrev REC := ControllerWordStartRecognizerDescription

theorem finalSentinelCleanupDescription_subroutineReady :
    FINAL.SubroutineReady := by
  exact seqSubroutine_subroutineReady
    (CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
      boolFinalScannerDescription_subroutineReady
      CommonGround.FiniteTransducers.leftBoundaryEraserDescription_subroutineReady)
    returnToFirstMarkerDescription_subroutineReady

theorem sentinelScannerDescription_subroutineReady : SENT.SubroutineReady := by
  exact seqSubroutine_subroutineReady
    markFirstTransitionBitDescription_subroutineReady
    (seqSubroutine_subroutineReady
      headerRemainderPrefixScannerDescription_subroutineReady
      finalSentinelCleanupDescription_subroutineReady)

theorem resultSentinelScannerDescription_subroutineReady :
    RSL.SubroutineReady := by
  exact seqSubroutine_subroutineReady
    boolWordSuffixScannerDescription_subroutineReady
    sentinelScannerDescription_subroutineReady

theorem stageResultSentinelScannerDescription_subroutineReady :
    SRSL.SubroutineReady := by
  exact seqSubroutine_subroutineReady
    EncRewriters.CanonicalLayouts.DovetailStagePrefix.nonemptyNatSuffixScannerDescription_subroutineReady
    resultSentinelScannerDescription_subroutineReady

theorem inputStageResultSentinelScannerDescription_subroutineReady :
    ISRSL.SubroutineReady := by
  exact seqSubroutine_subroutineReady
    boolWordSuffixScannerDescription_subroutineReady
    stageResultSentinelScannerDescription_subroutineReady

theorem markedControllerBodyScannerDescription_subroutineReady :
    BODY.SubroutineReady := by
  exact seqSubroutine_subroutineReady
    headerRemainderPrefixScannerDescription_subroutineReady
    inputStageResultSentinelScannerDescription_subroutineReady

theorem checkedControllerSentinelScannerDescription_subroutineReady :
    CHECK.SubroutineReady := by
  exact seqSubroutine_subroutineReady
    markFirstTransitionBitDescription_subroutineReady
    markedControllerBodyScannerDescription_subroutineReady

theorem appendSentinelRewindDescription_subroutineReady : AR.SubroutineReady := by
  exact seqSubroutine_subroutineReady
    (CommonGround.FiniteTransducers.generatedAppendWordDescription_subroutineReady
      sentinelBits)
    CommonGround.FiniteTransducers.rightEdgeRewindDescription_subroutineReady

theorem alignedAppendRewindDescription_subroutineReady : PRE.SubroutineReady := by
  exact seqSubroutine_subroutineReady
    codeWordAlignedPreScannerDescription_subroutineReady
    appendSentinelRewindDescription_subroutineReady

theorem controllerWordStartRecognizerDescription_subroutineReady :
    REC.SubroutineReady := by
  exact CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
    alignedAppendRewindDescription_subroutineReady
    checkedControllerSentinelScannerDescription_subroutineReady

theorem dovetailControllerLayout_encodeAppend_eq_append
    (C : DovetailControllerLayout) (suffix : Word MachineCodeSymbol) :
    DovetailControllerLayout.encodeAppend C suffix =
      List.append (DovetailControllerLayout.encode C) suffix := by
  cases C with
  | mk input stage result =>
      change
        MachineCodeSymbol.header ::
            encodeBoolWordAppend input
              (encodeNatAppend stage
                (encodeBoolWordAppend result suffix)) =
          List.append
            (MachineCodeSymbol.header ::
              encodeBoolWordAppend input
                (encodeNatAppend stage
                  (encodeBoolWordAppend result [])))
            suffix
      rw [show encodeBoolWordAppend result suffix =
          List.append (encodeBoolWordAppend result []) suffix by
        simpa using encodeBoolWordAppend_append result [] suffix]
      rw [encodeNatAppend_append, encodeBoolWordAppend_append]
      rfl

private def augmentedControllerBits (C : DovetailControllerLayout) : Word Bool :=
  encodeCodeWordAsInput (DovetailControllerLayout.encodeAppend C sentinelCode)

private theorem augmentedControllerBits_eq_fields (C : DovetailControllerLayout) :
    augmentedControllerBits C =
      List.append headerPrefixBits
        (boolWordFieldBits C.input
          (List.append
            (stageNatBits C.stage)
            (boolWordFieldBits C.result sentinelBits))) := by
  rw [augmentedControllerBits, DovetailControllerLayout.encodeAppend]
  change
    List.append headerPrefixBits
      (encodeCodeWordAsInput
        (encodeBoolWordAppend C.input
          (encodeNatAppend C.stage
            (encodeBoolWordAppend C.result sentinelCode)))) = _
  rw [boolWordBits_eq_encodeBoolWordAppend]
  rw [EncRewriters.CanonicalLayouts.DovetailStagePrefix.natBits_eq_encodeNatAppend]
  rw [boolWordBits_eq_encodeBoolWordAppend]
  simp [boolWordFieldBits, cellListFieldBits, sentinelBits]

theorem augmentedControllerBits_eq_original_append (C : DovetailControllerLayout) :
    augmentedControllerBits C =
      List.append (stageAttemptFramedStructuredInputBits C) sentinelBits := by
  rw [augmentedControllerBits, stageAttemptFramedStructuredInputBits,
    dovetailControllerLayout_encodeAppend_eq_append,
    encodeCodeWordAsInput_append]
  rfl

theorem haltsFromTape_of_runConfig_eq
    {D : MachineDescription} {Tin Tout : Tape Bool} {n : Nat}
    (h :
      D.runConfig n { state := D.start, tape := Tin } =
        { state := D.halt, tape := Tout }) :
    D.HaltsFromTape Tin Tout := by
  exact ⟨n, congrArg Configuration.state h, congrArg Configuration.tape h⟩

private theorem sentinelScannerDescription_forward
    (prefixRev : Word Bool) :
    SENT.HaltsFromTapeEquiv
      (tapeAtCells
        (List.append (prefixRev.map some) [none, none])
        (List.append (sentinelBits.map some) [none]))
      (restoredCheckedHandoffTapeFromTail prefixRev.reverse) := by
  let baseLeft : List (Option Bool) :=
    List.append (prefixRev.map some) [none, none]
  let Tmark : Tape Bool :=
    tapeAtCells baseLeft
      [none, some false, some false, some false,
        some false, some true, some false, some true, none]
  have hmark :
      MFTB.HaltsFromTape
        (tapeAtCells baseLeft
          [some false, some false, some false, some false,
            some false, some true, some false, some true, none])
        Tmark := by
    apply haltsFromTape_of_runConfig_eq (n := 2)
    simp [Tmark, baseLeft, MarkFirstTransitionBitDescription,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      keepMove, writeMove, tapeAtCells, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft, Tape.moveRight]
  let headerBase : List (Option Bool) := none :: baseLeft
  let Theader : Tape Bool :=
    (headerRemainderHandoffConfigWithBaseAndRight
      headerBase [false, true, false, true] [none]).tape
  have hheader :
      HRP.HaltsFromTape
        (tapeAtCells headerBase
          [some false, some false, some false,
            some false, some true, some false, some true, none])
        Theader := by
    rcases run_headerRemainderPrefix_raw_to_handoff_withBaseAndRight
      headerBase false [true, false, true] [none] with ⟨n, hn⟩
    refine ⟨n, ?_, ?_⟩
    · simpa [Theader, config, HRP,
        HeaderRemainderPrefixScannerDescription,
        headerRemainderHandoffConfigWithBaseAndRight] using
        congrArg Configuration.state hn
    · simpa [Theader, config, HRP,
        HeaderRemainderPrefixScannerDescription,
        headerRemainderHandoffConfigWithBaseAndRight] using
        congrArg Configuration.tape hn
  let boolBase : List (Option Bool) :=
    List.append (headerRemainderBits.reverse.map some) headerBase
  let Tbool : Tape Bool :=
    (boolFinalHandoffConfigWithBaseAndRight false boolBase [none]).tape
  have hbool :
      BFS.HaltsFromTape
        (tapeAtCells boolBase
          [some false, some true, some false, some true, none])
        Tbool := by
    rcases run_boolFinal_raw_to_handoff_withBaseAndRight
      false boolBase [] with ⟨n, hn⟩
    refine ⟨n, ?_, ?_⟩
    · simpa [Tbool, config, BFS, BoolFinalScannerDescription,
        boolFinalHandoffConfigWithBaseAndRight,
        cellCodeBits, encodeCell, encodeCodeWordAsInput,
        encodeCodeSymbolAsInput] using
        congrArg Configuration.state hn
    · simpa [Tbool, config, BFS, BoolFinalScannerDescription,
        boolFinalHandoffConfigWithBaseAndRight,
        cellCodeBits, encodeCell, encodeCodeWordAsInput,
        encodeCodeSymbolAsInput] using
        congrArg Configuration.tape hn
  let field : Word Bool :=
    [false, false, false, false, true, false, true]
  let Terased : Tape Bool :=
    CommonGround.FiniteTransducers.leftBoundaryEraserTargetTape
      baseLeft field none []
  have herase :
      ERASE.HaltsFromTape Tbool Terased := by
    have hsource :
        Tbool = CommonGround.FiniteTransducers.leftBoundaryEraserSourceTape
          baseLeft field none [] := by
      simp [Tbool, boolBase, headerBase, field,
        boolFinalHandoffConfigWithBaseAndRight,
        CommonGround.FiniteTransducers.leftBoundaryEraserSourceTape,
        CommonGround.FiniteTransducers.tapeAtCells,
        DovetailInitialLayoutInitializer.tapeAtCells,
        headerRemainderBits,
        cellCodeBits, encodeCell, encodeCodeWordAsInput,
        encodeCodeSymbolAsInput]
    rw [hsource]
    exact
      CommonGround.FiniteTransducers.leftBoundaryEraserDescription_haltsFromTape
        baseLeft field none []
  have hboolErase :
      (CommonGround.SameHeadComposition.leftRightSeqDescription BFS ERASE).HaltsFromTape
          (tapeAtCells boolBase
            [some false, some true, some false, some true, none])
          Terased := by
    exact
      CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
        boolFinalScannerDescription_subroutineReady
        CommonGround.FiniteTransducers.leftBoundaryEraserDescription_subroutineReady
        hbool
        (by
          have hTbool :
              Tbool = Tape.move Direction.left
                (tapeAtCells
                  ([some true, some false, some true, some false] ++ boolBase)
                  [none]) := by
            simp [Tbool, boolFinalHandoffConfigWithBaseAndRight,
              cellCodeBits, encodeCell, encodeCodeWordAsInput,
              encodeCodeSymbolAsInput]
          rw [hTbool]
          simp [
            DovetailInitialLayoutInitializer.tapeAtCells,
            Tape.move, Tape.moveLeft, Tape.moveRight])
        herase
  let TreturnClean : Tape Bool :=
    (config RFM.start
      (List.append (prefixRev.map some) [none]) [none]).tape
  have hreturnClean :
      RFM.HaltsFromTape TreturnClean
        (restoredCheckedHandoffTapeFromTail prefixRev.reverse) := by
    have hr := run_returnToFirstMarker_from_reversedBits prefixRev
    refine ⟨prefixRev.length + 2, ?_, ?_⟩
    · simpa [TreturnClean, config, RFM,
        ReturnToFirstMarkerDescription] using congrArg Configuration.state hr
    · simpa [TreturnClean, config, RFM,
        ReturnToFirstMarkerDescription] using congrArg Configuration.tape hr
  have hreturn :
      RFM.HaltsFromTapeEquiv (Tape.move Direction.left Terased)
        (restoredCheckedHandoffTapeFromTail prefixRev.reverse) := by
    apply HaltsFromTapeEquiv_of_input_equiv
      (Tin := TreturnClean) (Tin' := Tape.move Direction.left Terased)
      (Tout := restoredCheckedHandoffTapeFromTail prefixRev.reverse)
    · simp only [TreturnClean, Terased,
        CommonGround.FiniteTransducers.leftBoundaryEraserTargetTape,
        CommonGround.FiniteTransducers.tapeAtCells,
        baseLeft, field, config,
        DovetailInitialLayoutInitializer.tapeAtCells,
        Tape.Equiv, Tape.move, Tape.moveLeft,
        List.replicate_succ, List.length_cons, List.length_nil,
        Nat.reduceAdd]
      constructor
      · calc
          Tape.dropTrailingNone (prefixRev.map some ++ [none]) =
              Tape.dropTrailingNone (prefixRev.map some) :=
            dropTrailingNone_append_none (prefixRev.map some)
          _ = Tape.dropTrailingNone (prefixRev.map some ++ [none, none]) := by
            rw [show prefixRev.map some ++ [none, none] =
                (prefixRev.map some ++ [none]) ++ [none] by
              simp [List.append_assoc]]
            rw [dropTrailingNone_append_none,
              dropTrailingNone_append_none]
      · simp [Tape.dropTrailingNone]
    · exact hreturnClean
  have hfinal :
      FINAL.HaltsFromTapeEquiv
        (tapeAtCells boolBase
          [some false, some true, some false, some true, none])
        (restoredCheckedHandoffTapeFromTail prefixRev.reverse) := by
    exact seqSubroutine_haltsFromTapeEquiv_of_haltsFromTape_eq
      (CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
        boolFinalScannerDescription_subroutineReady
        CommonGround.FiniteTransducers.leftBoundaryEraserDescription_subroutineReady)
      returnToFirstMarkerDescription_subroutineReady
      hboolErase rfl hreturn
  have hheaderFinal :
      (seqSubroutine HRP FINAL Direction.right).HaltsFromTapeEquiv
        (tapeAtCells headerBase
          [some false, some false, some false,
            some false, some true, some false, some true, none])
        (restoredCheckedHandoffTapeFromTail prefixRev.reverse) := by
    exact seqSubroutine_haltsFromTapeEquiv_of_haltsFromTape_eq
      headerRemainderPrefixScannerDescription_subroutineReady
      finalSentinelCleanupDescription_subroutineReady
      hheader
      (by
        simpa [Theader, boolBase] using
          headerRemainderHandoffConfigWithBaseAndRight_move_right
            headerBase false [true, false, true] [none])
      hfinal
  have hsent :
      SENT.HaltsFromTapeEquiv
        (tapeAtCells baseLeft
          [some false, some false, some false, some false,
            some false, some true, some false, some true, none])
        (restoredCheckedHandoffTapeFromTail prefixRev.reverse) := by
    exact seqSubroutine_haltsFromTapeEquiv_of_haltsFromTape_eq
      markFirstTransitionBitDescription_subroutineReady
      (seqSubroutine_subroutineReady
        headerRemainderPrefixScannerDescription_subroutineReady
        finalSentinelCleanupDescription_subroutineReady)
      hmark
      (by
        simp [Tmark, headerBase, tapeAtCells,
          Tape.move, Tape.moveRight])
      hheaderFinal
  simpa [baseLeft, sentinelBits, sentinelCode,
    encodeBoolAppend, encodeCellAppend, encodeCell,
    encodeCodeWordAsInput, encodeCodeSymbolAsInput] using hsent

def markedControllerBodyBits
    (C : DovetailControllerLayout) : Word Bool :=
  List.append headerRemainderBits
    (boolWordFieldBits C.input
      (List.append (stageNatBits C.stage)
        (boolWordFieldBits C.result [])))

private def markedControllerBodyRestoredBitsRev
    (C : DovetailControllerLayout) : Word Bool :=
  List.append (cellListCanonicalRestoredBitsRev (C.result.map some))
    (List.append (stageNatBits C.stage).reverse
      (List.append
        (cellListCanonicalRestoredBitsRev (C.input.map some))
        headerRemainderBits.reverse))

private theorem markedControllerBodyRestoredBitsRev_reverse
    (C : DovetailControllerLayout) :
    (markedControllerBodyRestoredBitsRev C).reverse =
      markedControllerBodyBits C := by
  simp [markedControllerBodyRestoredBitsRev, markedControllerBodyBits,
    boolWordFieldBits, cellListFieldBits,
    cellListCanonicalRestoredBitsRev_reverse,
    List.reverse_append, List.append_assoc]

private theorem markedControllerBodyRestoredBitsRev_map_some_withBase
    (C : DovetailControllerLayout) (base : List (Option Bool)) :
    List.append ((markedControllerBodyRestoredBitsRev C).map some) base =
      cellListCanonicalRestoredLeftWithBase (C.result.map some)
        (List.append ((stageNatBits C.stage).reverse.map some)
          (cellListCanonicalRestoredLeftWithBase (C.input.map some)
            (List.append (headerRemainderBits.reverse.map some) base))) := by
  let baseAfterHeader :=
    List.append (headerRemainderBits.reverse.map some) base
  let baseAfterInput :=
    cellListCanonicalRestoredLeftWithBase (C.input.map some)
      baseAfterHeader
  let baseAfterStage :=
    List.append ((stageNatBits C.stage).reverse.map some) baseAfterInput
  have hinput :
      List.append
          ((cellListCanonicalRestoredBitsRev (C.input.map some)).map some)
          baseAfterHeader =
        baseAfterInput := by
    simpa [baseAfterInput] using
      cellListCanonicalRestoredBitsRev_map_some_withBase
        (C.input.map some) baseAfterHeader
  have hresult :
      List.append
          ((cellListCanonicalRestoredBitsRev (C.result.map some)).map some)
          baseAfterStage =
        cellListCanonicalRestoredLeftWithBase (C.result.map some)
          baseAfterStage :=
    cellListCanonicalRestoredBitsRev_map_some_withBase
      (C.result.map some) baseAfterStage
  calc
    List.append ((markedControllerBodyRestoredBitsRev C).map some) base =
        List.append
          ((cellListCanonicalRestoredBitsRev (C.result.map some)).map some)
          (List.append ((stageNatBits C.stage).reverse.map some)
            (List.append
              ((cellListCanonicalRestoredBitsRev
                (C.input.map some)).map some)
              baseAfterHeader)) := by
            simp [markedControllerBodyRestoredBitsRev,
              baseAfterHeader, List.map_append, List.map_reverse,
              List.append_assoc]
    _ = List.append
          ((cellListCanonicalRestoredBitsRev (C.result.map some)).map some)
          baseAfterStage := by rw [hinput]
    _ = cellListCanonicalRestoredLeftWithBase (C.result.map some)
          baseAfterStage := hresult
    _ = cellListCanonicalRestoredLeftWithBase (C.result.map some)
          (List.append ((stageNatBits C.stage).reverse.map some)
            (cellListCanonicalRestoredLeftWithBase (C.input.map some)
              (List.append (headerRemainderBits.reverse.map some)
                base))) := by
          simp [baseAfterStage, baseAfterInput, baseAfterHeader]

theorem augmentedControllerBits_eq_first_body_append_sentinel
    (C : DovetailControllerLayout) :
    augmentedControllerBits C =
      false :: List.append (markedControllerBodyBits C) sentinelBits := by
  rw [augmentedControllerBits_eq_fields]
  simp [headerPrefixBits, headerRemainderBits,
    markedControllerBodyBits, boolWordFieldBits, cellListFieldBits,
    encodeCodeSymbolAsInput, List.append_assoc]

private theorem markedControllerBodyBits_append_sentinel
    (C : DovetailControllerLayout) :
    List.append (markedControllerBodyBits C) sentinelBits =
      List.append headerRemainderBits
        (boolWordFieldBits C.input
          (List.append (stageNatBits C.stage)
            (boolWordFieldBits C.result sentinelBits))) := by
  simp [markedControllerBodyBits, boolWordFieldBits,
    cellListFieldBits, List.append_assoc]

private theorem resultSentinelScannerDescription_forward
    (C : DovetailControllerLayout) :
    let markerBase : List (Option Bool) := [none, none]
    let baseAfterHeader :=
      List.append (headerRemainderBits.reverse.map some) markerBase
    let baseAfterInput :=
      cellListCanonicalRestoredLeftWithBase (C.input.map some)
        baseAfterHeader
    let baseAfterStage :=
      List.append ((stageNatBits C.stage).reverse.map some) baseAfterInput
    RSL.HaltsFromTapeEquiv
      (tapeAtCells baseAfterStage
        (List.append
          ((boolWordFieldBits C.result sentinelBits).map some) [none]))
      (restoredCheckedHandoffTapeFromTail
        (markedControllerBodyBits C)) := by
  dsimp only
  let markerBase : List (Option Bool) := [none, none]
  let baseAfterHeader :=
    List.append (headerRemainderBits.reverse.map some) markerBase
  let baseAfterInput :=
    cellListCanonicalRestoredLeftWithBase (C.input.map some)
      baseAfterHeader
  let baseAfterStage :=
    List.append ((stageNatBits C.stage).reverse.map some) baseAfterInput
  let baseAfterResult :=
    cellListCanonicalRestoredLeftWithBase (C.result.map some)
      baseAfterStage
  let sentinelTail : Word Bool :=
    [false, false, false, false, true, false, true]
  have hsentinelBits : sentinelBits = false :: sentinelTail := by
    rfl
  let Tresult : Tape Bool :=
    (boolWordCanonicalHandoffConfigWithBaseAndRight C.result
      baseAfterStage (false :: sentinelTail) [none]).tape
  have hresult :
      BWSS.HaltsFromTape
        (tapeAtCells baseAfterStage
          (List.append
            ((boolWordFieldBits C.result sentinelBits).map some) [none]))
        Tresult := by
    rcases run_boolWordSuffix_raw_to_canonical_handoff_withBaseAndRight
        C.result baseAfterStage sentinelTail [none] with ⟨n, hn⟩
    apply haltsFromTape_of_runConfig_eq (n := n)
    simpa [Tresult, BWSS, BoolWordSuffixScannerDescription,
      boolWordCanonicalHandoffConfigWithBaseAndRight,
      hsentinelBits, boolWordFieldBits, cellListFieldBits,
      config, List.map_append, List.append_assoc] using hn
  have hsentinel :
      SENT.HaltsFromTapeEquiv
        (tapeAtCells baseAfterResult
          (List.append (sentinelBits.map some) [none]))
        (restoredCheckedHandoffTapeFromTail
          (markedControllerBodyBits C)) := by
    have hbase :=
      markedControllerBodyRestoredBitsRev_map_some_withBase C markerBase
    have hbase' :
        List.append
            ((markedControllerBodyRestoredBitsRev C).map some) markerBase =
          baseAfterResult := by
      simpa [baseAfterResult, baseAfterStage, baseAfterInput,
        baseAfterHeader] using hbase
    have hs := sentinelScannerDescription_forward
      (markedControllerBodyRestoredBitsRev C)
    rw [markedControllerBodyRestoredBitsRev_reverse] at hs
    rw [← hbase']
    simpa [markerBase] using hs
  exact seqSubroutine_haltsFromTapeEquiv_of_haltsFromTape_eq
    boolWordSuffixScannerDescription_subroutineReady
    sentinelScannerDescription_subroutineReady
    hresult
    (by
      simpa [Tresult, baseAfterResult, hsentinelBits,
        boolWordCanonicalHandoffConfigWithBaseAndRight] using
        cellListCanonicalHandoffConfigWithBaseAndRight_move_right
          (C.result.map some) baseAfterStage false sentinelTail [none])
    hsentinel

private theorem stageResultSentinelScannerDescription_forward
    (C : DovetailControllerLayout) :
    let markerBase : List (Option Bool) := [none, none]
    let baseAfterHeader :=
      List.append (headerRemainderBits.reverse.map some) markerBase
    let baseAfterInput :=
      cellListCanonicalRestoredLeftWithBase (C.input.map some)
        baseAfterHeader
    SRSL.HaltsFromTapeEquiv
      (tapeAtCells baseAfterInput
        (List.append
          ((List.append (stageNatBits C.stage)
            (boolWordFieldBits C.result sentinelBits)).map some) [none]))
      (restoredCheckedHandoffTapeFromTail
        (markedControllerBodyBits C)) := by
  dsimp only
  let markerBase : List (Option Bool) := [none, none]
  let baseAfterHeader :=
    List.append (headerRemainderBits.reverse.map some) markerBase
  let baseAfterInput :=
    cellListCanonicalRestoredLeftWithBase (C.input.map some)
      baseAfterHeader
  let baseAfterStage :=
    List.append ((stageNatBits C.stage).reverse.map some) baseAfterInput
  rcases cellListFieldBits_cons_false (C.result.map some) sentinelBits with
    ⟨resultTail, hresultTail⟩
  have hresultBits :
      boolWordFieldBits C.result sentinelBits = false :: resultTail := by
    simpa [boolWordFieldBits] using hresultTail
  let Tstage : Tape Bool :=
    (EncRewriters.CanonicalLayouts.DovetailStagePrefix.nonemptyNatSuffixHandoffConfigWithBaseAndRight
      C.stage baseAfterInput (false :: resultTail) [none]).tape
  have hstage :
      NNSS.HaltsFromTape
        (tapeAtCells baseAfterInput
          (List.append
            ((List.append (stageNatBits C.stage)
              (boolWordFieldBits C.result sentinelBits)).map some) [none]))
        Tstage := by
    rcases
        EncRewriters.CanonicalLayouts.DovetailStagePrefix.run_nonemptyNatSuffix_raw_to_handoff_withBaseAndRight
          C.stage baseAfterInput false resultTail [none] with ⟨n, hn⟩
    apply haltsFromTape_of_runConfig_eq (n := n)
    simpa [Tstage, NNSS,
      EncRewriters.CanonicalLayouts.DovetailStagePrefix.NonemptyNatSuffixScannerDescription,
      EncRewriters.CanonicalLayouts.DovetailStagePrefix.nonemptyNatSuffixHandoffConfigWithBaseAndRight,
      hresultBits, config,
      List.map_append, List.append_assoc] using hn
  have hresult :
      RSL.HaltsFromTapeEquiv
        (tapeAtCells baseAfterStage
          (List.append
            ((boolWordFieldBits C.result sentinelBits).map some) [none]))
        (restoredCheckedHandoffTapeFromTail
          (markedControllerBodyBits C)) := by
    simpa [baseAfterStage, baseAfterInput, baseAfterHeader,
      markerBase] using resultSentinelScannerDescription_forward C
  exact seqSubroutine_haltsFromTapeEquiv_of_haltsFromTape_eq
    EncRewriters.CanonicalLayouts.DovetailStagePrefix.nonemptyNatSuffixScannerDescription_subroutineReady
    resultSentinelScannerDescription_subroutineReady
    hstage
    (by
      simpa [Tstage, baseAfterStage, hresultBits] using
        EncRewriters.CanonicalLayouts.DovetailStagePrefix.nonemptyNatSuffixHandoffConfigWithBaseAndRight_move_right
          C.stage baseAfterInput false resultTail [none])
    hresult

private theorem inputStageResultSentinelScannerDescription_forward
    (C : DovetailControllerLayout) :
    let markerBase : List (Option Bool) := [none, none]
    let baseAfterHeader :=
      List.append (headerRemainderBits.reverse.map some) markerBase
    ISRSL.HaltsFromTapeEquiv
      (tapeAtCells baseAfterHeader
        (List.append
          ((boolWordFieldBits C.input
            (List.append (stageNatBits C.stage)
              (boolWordFieldBits C.result sentinelBits))).map some) [none]))
      (restoredCheckedHandoffTapeFromTail
        (markedControllerBodyBits C)) := by
  dsimp only
  let markerBase : List (Option Bool) := [none, none]
  let baseAfterHeader :=
    List.append (headerRemainderBits.reverse.map some) markerBase
  let baseAfterInput :=
    cellListCanonicalRestoredLeftWithBase (C.input.map some)
      baseAfterHeader
  rcases stageNatBits_cons_false C.stage with ⟨stageTail, hstageTail⟩
  let inputSuffixTail : Word Bool :=
    List.append stageTail (boolWordFieldBits C.result sentinelBits)
  have hinputSuffix :
      List.append (stageNatBits C.stage)
          (boolWordFieldBits C.result sentinelBits) =
        false :: inputSuffixTail := by
    simp [inputSuffixTail, hstageTail]
  let Tinput : Tape Bool :=
    (boolWordCanonicalHandoffConfigWithBaseAndRight C.input
      baseAfterHeader (false :: inputSuffixTail) [none]).tape
  have hinput :
      BWSS.HaltsFromTape
        (tapeAtCells baseAfterHeader
          (List.append
            ((boolWordFieldBits C.input
              (List.append (stageNatBits C.stage)
                (boolWordFieldBits C.result sentinelBits))).map some) [none]))
        Tinput := by
    rcases run_boolWordSuffix_raw_to_canonical_handoff_withBaseAndRight
        C.input baseAfterHeader inputSuffixTail [none] with ⟨n, hn⟩
    rw [show
        boolWordFieldBits C.input
            (List.append (stageNatBits C.stage)
              (boolWordFieldBits C.result sentinelBits)) =
          List.append (stageNatBits C.input.length)
            (List.append (cellsCodeBits (C.input.map some))
              (false :: inputSuffixTail)) by
      simp [boolWordFieldBits, cellListFieldBits,
        inputSuffixTail, hstageTail]]
    apply haltsFromTape_of_runConfig_eq (n := n)
    simpa [Tinput, BWSS, BoolWordSuffixScannerDescription,
      boolWordCanonicalHandoffConfigWithBaseAndRight,
      config, List.map_append, List.append_assoc] using hn
  have hstageResult :
      SRSL.HaltsFromTapeEquiv
        (tapeAtCells baseAfterInput
          (List.append
            ((List.append (stageNatBits C.stage)
              (boolWordFieldBits C.result sentinelBits)).map some) [none]))
        (restoredCheckedHandoffTapeFromTail
          (markedControllerBodyBits C)) := by
    simpa [baseAfterInput, baseAfterHeader, markerBase] using
      stageResultSentinelScannerDescription_forward C
  exact seqSubroutine_haltsFromTapeEquiv_of_haltsFromTape_eq
    boolWordSuffixScannerDescription_subroutineReady
    stageResultSentinelScannerDescription_subroutineReady
    hinput
    (by
      have hsuffixCells :
          (false :: inputSuffixTail).map some =
            (List.append (stageNatBits C.stage)
              (boolWordFieldBits C.result sentinelBits)).map some := by
        rw [← hinputSuffix]
      simpa [Tinput, baseAfterInput, hsuffixCells,
        boolWordCanonicalHandoffConfigWithBaseAndRight] using
        cellListCanonicalHandoffConfigWithBaseAndRight_move_right
          (C.input.map some) baseAfterHeader false inputSuffixTail [none])
    hstageResult

private theorem markedControllerBodyScannerDescription_forward
    (C : DovetailControllerLayout) :
    let markerBase : List (Option Bool) := [none, none]
    BODY.HaltsFromTapeEquiv
      (tapeAtCells markerBase
        (List.append
          ((List.append headerRemainderBits
            (boolWordFieldBits C.input
              (List.append (stageNatBits C.stage)
                (boolWordFieldBits C.result sentinelBits)))).map some)
          [none]))
      (restoredCheckedHandoffTapeFromTail
        (markedControllerBodyBits C)) := by
  dsimp only
  let markerBase : List (Option Bool) := [none, none]
  let baseAfterHeader :=
    List.append (headerRemainderBits.reverse.map some) markerBase
  let bodySuffix : Word Bool :=
    boolWordFieldBits C.input
      (List.append (stageNatBits C.stage)
        (boolWordFieldBits C.result sentinelBits))
  rcases cellListFieldBits_cons_false (C.input.map some)
      (List.append (stageNatBits C.stage)
        (boolWordFieldBits C.result sentinelBits)) with
    ⟨inputTail, hinputTail⟩
  have hbodySuffix : bodySuffix = false :: inputTail := by
    simpa [bodySuffix, boolWordFieldBits] using hinputTail
  let Theader : Tape Bool :=
    (headerRemainderHandoffConfigWithBaseAndRight markerBase
      (false :: inputTail) [none]).tape
  have hheader :
      HRP.HaltsFromTape
        (tapeAtCells markerBase
          (List.append
            ((List.append headerRemainderBits bodySuffix).map some)
            [none]))
        Theader := by
    rcases run_headerRemainderPrefix_raw_to_handoff_withBaseAndRight
        markerBase false inputTail [none] with ⟨n, hn⟩
    apply haltsFromTape_of_runConfig_eq (n := n)
    simpa [Theader, HRP, HeaderRemainderPrefixScannerDescription,
      headerRemainderHandoffConfigWithBaseAndRight,
      headerRemainderBits, hbodySuffix, config,
      List.map_append, List.append_assoc] using hn
  have hinputStage :
      ISRSL.HaltsFromTapeEquiv
        (tapeAtCells baseAfterHeader
          (List.append (bodySuffix.map some) [none]))
        (restoredCheckedHandoffTapeFromTail
          (markedControllerBodyBits C)) := by
    simpa [bodySuffix, baseAfterHeader, markerBase] using
      inputStageResultSentinelScannerDescription_forward C
  exact seqSubroutine_haltsFromTapeEquiv_of_haltsFromTape_eq
    headerRemainderPrefixScannerDescription_subroutineReady
    inputStageResultSentinelScannerDescription_subroutineReady
    hheader
    (by
      simpa [Theader, baseAfterHeader, hbodySuffix] using
        headerRemainderHandoffConfigWithBaseAndRight_move_right
          markerBase false inputTail [none])
    hinputStage

private theorem checkedControllerSentinelScannerDescription_forward
    (C : DovetailControllerLayout) :
    CHECK.HaltsFromTapeEquiv
      (CommonGround.FiniteTransducers.rightEdgeRewindTargetTape
        (augmentedControllerBits C) [])
      (restoredCheckedHandoffTapeFromTail
        (markedControllerBodyBits C)) := by
  let bodyWithSentinel : Word Bool :=
    List.append (markedControllerBodyBits C) sentinelBits
  let bodyTail : Word Bool :=
    false :: false ::
      (boolWordFieldBits C.input
        (List.append (stageNatBits C.stage)
          (boolWordFieldBits C.result sentinelBits)))
  have hbodyShape :
      bodyWithSentinel =
        List.append headerRemainderBits
          (boolWordFieldBits C.input
            (List.append (stageNatBits C.stage)
              (boolWordFieldBits C.result sentinelBits))) := by
    simpa only [bodyWithSentinel, Word] using
      markedControllerBodyBits_append_sentinel C
  have hbodyFirst : bodyWithSentinel = false :: bodyTail := by
    rw [hbodyShape]
    simp [bodyTail, headerRemainderBits]
  have haugmented :
      augmentedControllerBits C = false :: bodyWithSentinel := by
    simpa only [bodyWithSentinel, Word] using
      augmentedControllerBits_eq_first_body_append_sentinel C
  let Tmark : Tape Bool :=
    tapeAtCells [none]
      (none :: List.append (bodyWithSentinel.map some) [none])
  have hmark :
      MFTB.HaltsFromTape
        (CommonGround.FiniteTransducers.rightEdgeRewindTargetTape
          (augmentedControllerBits C) [])
        Tmark := by
    apply haltsFromTape_of_runConfig_eq (n := 2)
    rw [haugmented]
    simp [Tmark, hbodyFirst,
      CommonGround.FiniteTransducers.rightEdgeRewindTargetTape,
      CommonGround.FiniteTransducers.tapeAtCells,
      MarkFirstTransitionBitDescription,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      keepMove, writeMove, tapeAtCells, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft, Tape.moveRight]
  have hbody :
      BODY.HaltsFromTapeEquiv
        (tapeAtCells [none, none]
          (List.append (bodyWithSentinel.map some) [none]))
        (restoredCheckedHandoffTapeFromTail
          (markedControllerBodyBits C)) := by
    rw [hbodyShape]
    simpa using
      markedControllerBodyScannerDescription_forward C
  exact seqSubroutine_haltsFromTapeEquiv_of_haltsFromTape_eq
    markFirstTransitionBitDescription_subroutineReady
    markedControllerBodyScannerDescription_subroutineReady
    hmark
    (by
      simp [Tmark, hbodyFirst, tapeAtCells, Tape.move, Tape.moveRight])
    hbody

theorem appendSentinelRewindDescription_forward
    (bits : Word Bool) :
    AR.HaltsFromTape
      (CommonGround.FiniteTransducers.FSTSourceTape bits 1)
      (CommonGround.FiniteTransducers.rightEdgeRewindTargetTape
        (List.append bits sentinelBits) []) := by
  let sentinelInit : Word Bool :=
    [false, false, false, false, false, true, false]
  have hsentinel : sentinelBits = List.append sentinelInit [true] := by
    rfl
  have happ :
      APP.HaltsFromTape
        (CommonGround.FiniteTransducers.FSTSourceTape bits 1)
        (CommonGround.FiniteTransducers.FSTAppendFinalWordTargetTape
          bits sentinelBits 1) :=
    CommonGround.FiniteTransducers.generatedAppendWordDescription_haltsFrom_FSTSourceTape_of_writer
      sentinelBits bits 1
      (CommonGround.FiniteTransducers.generatedAppendWordDescription_writerRuns
        sentinelBits)
  let leftStack : Word Bool :=
    (List.append bits sentinelInit).reverse
  let TrewindSource : Tape Bool :=
    CommonGround.FiniteTransducers.tapeAtCells
      (List.append (leftStack.map some) [none]) [some true, none]
  have hrewind :
      REW.HaltsFromTape TrewindSource
        (CommonGround.FiniteTransducers.rightEdgeRewindTargetTape
          (List.append bits sentinelBits) []) := by
    have hr :=
      CommonGround.FiniteTransducers.rightEdgeRewindDescription_haltsFrom_lastBitBoundary
        leftStack true []
    simpa [TrewindSource, leftStack, hsentinel,
      List.reverse_append, List.append_assoc] using hr
  exact seqSubroutine_haltsFromTape_of_haltsFromTape_eq
    (CommonGround.FiniteTransducers.generatedAppendWordDescription_subroutineReady
      sentinelBits)
    CommonGround.FiniteTransducers.rightEdgeRewindDescription_subroutineReady
    happ
    (by
      simp [TrewindSource, leftStack, sentinelInit, hsentinel,
        CommonGround.FiniteTransducers.FSTAppendFinalWordTargetTape,
        CommonGround.FiniteTransducers.appendFinalWordWriteTargetTape,
        CommonGround.FiniteTransducers.tapeAtCells,
        Tape.move, Tape.moveLeft, List.reverse_append])
    hrewind

theorem move_left_codeWordAlignedHandoffTape_cons
    (b : Bool) (tailBits : Word Bool) :
    Tape.move Direction.left
        (codeWordAlignedHandoffTape (b :: tailBits)) =
      tapeAtCells [none]
        (List.append ((b :: tailBits).map some) [none]) := by
  cases tailBits <;>
    simp [codeWordAlignedHandoffTape, tapeAtCells,
      Tape.move, Tape.moveLeft, Tape.moveRight]

private theorem alignedAppendRewindDescription_forward
    (C : DovetailControllerLayout) :
    PRE.HaltsFromTape
      (Tape.input (stageAttemptFramedStructuredInputBits C))
      (CommonGround.FiniteTransducers.rightEdgeRewindTargetTape
        (augmentedControllerBits C) []) := by
  have hconsCode :
      exists rest : Word MachineCodeSymbol,
        DovetailControllerLayout.encode C =
          MachineCodeSymbol.header :: rest := by
    cases C
    exact ⟨_, rfl⟩
  rcases hconsCode with ⟨restCode, hcode⟩
  have hpre :
      CWA.HaltsFromTape
        (Tape.input (stageAttemptFramedStructuredInputBits C))
        (codeWordAlignedHandoffTape
          (stageAttemptFramedStructuredInputBits C)) := by
    rw [show stageAttemptFramedStructuredInputBits C =
        encodeCodeWordAsInput
          (MachineCodeSymbol.header :: restCode) by
      rw [stageAttemptFramedStructuredInputBits, hcode]]
    exact codeWordAlignedPreScannerDescription_haltsFromTape
      MachineCodeSymbol.header restCode
  rcases
      EncRewriters.CanonicalLayouts.DovetailLayoutScanner.encodeCodeWordAsInput_cons_bits
        MachineCodeSymbol.header restCode with
    ⟨b0, bitsTail, hbitsCons⟩
  have hbitsShape :
      stageAttemptFramedStructuredInputBits C = b0 :: bitsTail := by
    rw [stageAttemptFramedStructuredInputBits, hcode]
    exact hbitsCons
  have har :
      AR.HaltsFromTape
        (CommonGround.FiniteTransducers.FSTSourceTape
          (stageAttemptFramedStructuredInputBits C) 1)
        (CommonGround.FiniteTransducers.rightEdgeRewindTargetTape
          (augmentedControllerBits C) []) := by
    have ha := appendSentinelRewindDescription_forward
      (stageAttemptFramedStructuredInputBits C)
    rw [← augmentedControllerBits_eq_original_append] at ha
    exact ha
  exact seqSubroutine_haltsFromTape_of_haltsFromTape_eq
    codeWordAlignedPreScannerDescription_subroutineReady
    appendSentinelRewindDescription_subroutineReady
    hpre
    (by
      rw [hbitsShape, move_left_codeWordAlignedHandoffTape_cons]
      simp [CommonGround.FiniteTransducers.FSTSourceTape,
        CommonGround.FiniteTransducers.tapeAtCells, tapeAtCells])
    har

theorem controllerWordStartRecognizerDescription_forward
    (C : DovetailControllerLayout) :
    REC.HaltsFromTapeEquiv
      (Tape.input (stageAttemptFramedStructuredInputBits C))
      (restoredCheckedHandoffTapeFromTail
        (markedControllerBodyBits C)) := by
  have hpre := alignedAppendRewindDescription_forward C
  have hcheck := checkedControllerSentinelScannerDescription_forward C
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTapeEquiv_of_haltsFromTape
      alignedAppendRewindDescription_subroutineReady
      checkedControllerSentinelScannerDescription_subroutineReady
      hpre
      (by
        rw [augmentedControllerBits_eq_first_body_append_sentinel]
        simp [CommonGround.FiniteTransducers.rightEdgeRewindTargetTape,
          CommonGround.FiniteTransducers.tapeAtCells,
          Tape.move, Tape.moveLeft, Tape.moveRight])
      hcheck

end FoC.Computability.StructuredConstructionTargets.StageAttemptFramedMaterializer.Internal

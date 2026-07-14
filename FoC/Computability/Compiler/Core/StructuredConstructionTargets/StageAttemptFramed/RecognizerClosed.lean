import FoC.Computability.Compiler.Core.StructuredConstructionTargets.StageAttemptFramed.RecognizerForward
namespace FoC.Computability.StructuredConstructionTargets.StageAttemptFramedMaterializer.Internal
open Languages
open MachineDescription
open FoC.Computability.DovetailInitialLayoutInitializer
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner
open CommonGround.SeqComposition
open EncRewriters.CanonicalLayouts.DovetailLayoutScanner
open EncRewriters.CanonicalLayouts.SimulatorLayoutScanner
private theorem sentinelScannerDescription_runConfig_parts_inv
    {Tin Tout : Tape Bool} {n : Nat}
    (h :
      SENT.runConfig n { state := SENT.start, tape := Tin } =
        { state := SENT.halt, tape := Tout }) :
    exists Tmark Theader : Tape Bool,
    exists nMark nHeader nFinal : Nat,
      MFTB.runConfig nMark { state := MFTB.start, tape := Tin } =
          { state := MFTB.halt, tape := Tmark } ∧
        HRP.runConfig nHeader
            { state := HRP.start,
              tape := Tape.move Direction.right Tmark } =
          { state := HRP.halt, tape := Theader } ∧
        FINAL.runConfig nFinal
            { state := FINAL.start,
              tape := Tape.move Direction.right Theader } =
          { state := FINAL.halt, tape := Tout } := by
  rcases
      seqSubroutine_runConfig_inv
        (A := MFTB)
        (B := seqSubroutine HRP FINAL Direction.right)
        (handoffMove := Direction.right)
        markFirstTransitionBitDescription_subroutineReady
        (seqSubroutine_subroutineReady
          headerRemainderPrefixScannerDescription_subroutineReady
          finalSentinelCleanupDescription_subroutineReady)
        (by simpa [SentinelScannerDescription] using h) with
    ⟨Tmark, hmark, hrest⟩
  rcases hmark with ⟨nMark, hmarkRun, _⟩
  rcases hrest with ⟨nRest, hrestRun⟩
  rcases
      seqSubroutine_runConfig_inv
        (A := HRP) (B := FINAL)
        (handoffMove := Direction.right)
        headerRemainderPrefixScannerDescription_subroutineReady
        finalSentinelCleanupDescription_subroutineReady
        (by simpa using hrestRun) with
    ⟨Theader, hheader, hfinal⟩
  rcases hheader with ⟨nHeader, hheaderRun, _⟩
  rcases hfinal with ⟨nFinal, hfinalRun⟩
  exact ⟨Tmark, Theader, nMark, nHeader, nFinal,
    hmarkRun, hheaderRun, hfinalRun⟩

private theorem finalSentinelCleanupDescription_boolFinal_run_inv
    {Tin Tout : Tape Bool} {n : Nat}
    (h :
      FINAL.runConfig n { state := FINAL.start, tape := Tin } =
        { state := FINAL.halt, tape := Tout }) :
    exists Tbool : Tape Bool,
    exists nBool : Nat,
      BFS.runConfig nBool { state := BFS.start, tape := Tin } =
        { state := BFS.halt, tape := Tbool } := by
  rcases
      seqSubroutine_runConfig_inv
        (A := CommonGround.SameHeadComposition.leftRightSeqDescription
          BFS ERASE)
        (B := RFM) (handoffMove := Direction.left)
        (CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
          boolFinalScannerDescription_subroutineReady
          CommonGround.FiniteTransducers.leftBoundaryEraserDescription_subroutineReady)
        returnToFirstMarkerDescription_subroutineReady
        (by simpa [FinalSentinelCleanupDescription] using h) with
    ⟨Tcleanup, hcleanup, _hreturn⟩
  rcases hcleanup with ⟨nCleanup, hcleanupRun, _⟩
  rcases
      seqSubroutine_runConfig_inv
        (A := seqSubroutine BFS ExactIdentityDescription Direction.left)
        (B := ERASE) (handoffMove := Direction.right)
        (seqSubroutine_subroutineReady
          boolFinalScannerDescription_subroutineReady
          CommonGround.Identity.exactIdentityDescription_subroutineReady)
        CommonGround.FiniteTransducers.leftBoundaryEraserDescription_subroutineReady
        (by
          simpa [CommonGround.SameHeadComposition.leftRightSeqDescription]
            using hcleanupRun) with
    ⟨Tidentity, hidentity, _herase⟩
  rcases hidentity with ⟨nIdentity, hidentityRun, _⟩
  rcases
      seqSubroutine_runConfig_inv
        (A := BFS) (B := ExactIdentityDescription)
        (handoffMove := Direction.left)
        boolFinalScannerDescription_subroutineReady
        CommonGround.Identity.exactIdentityDescription_subroutineReady
        (by simpa using hidentityRun) with
    ⟨Tbool, hbool, _hid⟩
  rcases hbool with ⟨nBool, hboolRun, _⟩
  exact ⟨Tbool, nBool, hboolRun⟩

private theorem runConfig_halt_false_of_reaches_stuck
    {D : MachineDescription} (hD : D.HaltTransitionFree)
    {start stuck : Configuration} {k n : Nat} {Tout : Tape Bool}
    (hprefix : D.runConfig k start = stuck)
    (hstep : D.stepConfig stuck = none)
    (hstuck : stuck.state ≠ D.halt)
    (hrun : D.runConfig n start = { state := D.halt, tape := Tout }) :
    False := by
  exact
    (runConfig_state_ne_halt_of_reaches_stuck
      hD hprefix hstep hstuck)
      (by simpa using congrArg Configuration.state hrun)

private theorem markFirstTransitionBitDescription_runConfig_withBase_inv
    (base : List (Option Bool)) (bits : Word Bool)
    {Tout : Tape Bool} {n : Nat}
    (h :
      MFTB.runConfig n
          { state := MFTB.start,
            tape := tapeAtCells base (bits.map some) } =
        { state := MFTB.halt, tape := Tout }) :
    exists tail : Word Bool,
      bits = false :: false :: tail ∧
        Tout =
          (config MFTB.halt base
            (none :: some false :: tail.map some)).tape := by
  cases bits with
  | nil =>
      exact False.elim
        (runConfig_halt_false_of_reaches_stuck
          markFirstTransitionBitDescription_haltTransitionFree
          (k := 0) (stuck :=
            { state := MFTB.start,
              tape := tapeAtCells base [] })
          rfl
          (by simp [MarkFirstTransitionBitDescription, tapeAtCells,
            stepConfig, lookupTransition, Matches, transition,
            keepMove, writeMove, Tape.read])
          (by change (0 : Nat) ≠ 9; decide)
          h)
  | cons first rest =>
      cases first with
      | true =>
          exact False.elim
            (runConfig_halt_false_of_reaches_stuck
              markFirstTransitionBitDescription_haltTransitionFree
              (k := 0) (stuck :=
                { state := MFTB.start,
                  tape := tapeAtCells base (some true :: rest.map some) })
              rfl
              (by simp [MarkFirstTransitionBitDescription, tapeAtCells,
                stepConfig, lookupTransition, Matches, transition,
                keepMove, writeMove, Tape.read])
              (by change (0 : Nat) ≠ 9; decide)
              h)
      | false =>
          cases rest with
          | nil =>
              let stuck : Configuration :=
                { state := 1, tape := tapeAtCells (none :: base) [] }
              exact False.elim
                (runConfig_halt_false_of_reaches_stuck
                  markFirstTransitionBitDescription_haltTransitionFree
                  (k := 1) (stuck := stuck)
                  (by simp [stuck, MarkFirstTransitionBitDescription,
                    tapeAtCells, runConfig, stepConfig, lookupTransition,
                    Matches, transition, writeMove, Tape.read, Tape.write,
                    Tape.move, Tape.moveRight])
                  (by simp [stuck, MarkFirstTransitionBitDescription,
                    tapeAtCells, stepConfig, lookupTransition,
                    Matches, transition, keepMove, writeMove, Tape.read])
                  (by change (1 : Nat) ≠ 9; decide)
                  h)
          | cons second tail =>
              cases second with
              | true =>
                  let stuck : Configuration :=
                    { state := 1,
                      tape := tapeAtCells (none :: base)
                        (some true :: tail.map some) }
                  exact False.elim
                    (runConfig_halt_false_of_reaches_stuck
                      markFirstTransitionBitDescription_haltTransitionFree
                      (k := 1) (stuck := stuck)
                      (by simp [stuck, MarkFirstTransitionBitDescription,
                        tapeAtCells, runConfig, stepConfig,
                        lookupTransition, Matches, transition, writeMove,
                        Tape.read, Tape.write, Tape.move, Tape.moveRight])
                      (by simp [stuck, MarkFirstTransitionBitDescription,
                        tapeAtCells, stepConfig, lookupTransition,
                        Matches, transition, keepMove, writeMove, Tape.read])
                      (by change (1 : Nat) ≠ 9; decide)
                      h)
              | false =>
                  refine ⟨tail, rfl, ?_⟩
                  have hgood :
                      MFTB.runConfig 2
                          { state := MFTB.start,
                            tape := tapeAtCells base
                              ((false :: false :: tail).map some) } =
                        { state := MFTB.halt,
                          tape :=
                            (config MFTB.halt base
                              (none :: some false :: tail.map some)).tape } := by
                    simp [MarkFirstTransitionBitDescription,
                      config, tapeAtCells, runConfig, stepConfig,
                      lookupTransition, Matches, transition,
                      keepMove, writeMove, Tape.read, Tape.write,
                      Tape.move, Tape.moveLeft, Tape.moveRight]
                  exact
                    (MachineDescription.runConfig_halt_tape_functional_of_haltTransitionFree
                      markFirstTransitionBitDescription_haltTransitionFree
                      hgood h).symm

private theorem headerRemainderPrefixScannerDescription_runConfig_withBase_inv
    (base : List (Option Bool)) (bits : Word Bool)
    {Tout : Tape Bool} {n : Nat}
    (h :
      HRP.runConfig n
          { state := HRP.start,
            tape := tapeAtCells base (bits.map some) } =
        { state := HRP.halt, tape := Tout }) :
    exists b : Bool, exists suffix : Word Bool,
      bits = false :: false :: false :: b :: suffix ∧
        Tout =
          (headerRemainderHandoffConfigWithBase base
            (b :: suffix)).tape := by
  let start : Configuration :=
    { state := HRP.start, tape := tapeAtCells base (bits.map some) }
  cases bits with
  | nil =>
      exact False.elim
        (runConfig_halt_false_of_reaches_stuck
          headerRemainderPrefixScannerDescription_haltTransitionFree
          (k := 0) (stuck := start) rfl
          (by simp [start, HeaderRemainderPrefixScannerDescription,
            tapeAtCells, stepConfig, lookupTransition, Matches,
            transition, keepMove, Tape.read])
          (by change (30 : Nat) ≠ 99; decide)
          (by simpa [start] using h))
  | cons first rest =>
      cases first with
      | true =>
          exact False.elim
            (runConfig_halt_false_of_reaches_stuck
              headerRemainderPrefixScannerDescription_haltTransitionFree
              (k := 0) (stuck := start) rfl
              (by simp [start, HeaderRemainderPrefixScannerDescription,
                tapeAtCells, stepConfig, lookupTransition, Matches,
                transition, keepMove, Tape.read])
              (by change (30 : Nat) ≠ 99; decide)
              (by simpa [start] using h))
      | false =>
          cases rest with
          | nil =>
              let stuck := HRP.runConfig 1 start
              exact False.elim
                (runConfig_halt_false_of_reaches_stuck
                  headerRemainderPrefixScannerDescription_haltTransitionFree
                  (k := 1) (stuck := stuck) rfl
                  (by simp [stuck, start,
                    HeaderRemainderPrefixScannerDescription,
                    tapeAtCells, runConfig, stepConfig, lookupTransition,
                    Matches, transition, keepMove, Tape.read,
                    Tape.write, Tape.move, Tape.moveRight])
                  (by
                    simp [stuck, start,
                      HeaderRemainderPrefixScannerDescription,
                      tapeAtCells, runConfig, stepConfig, lookupTransition,
                      Matches, transition, keepMove, Tape.read,
                      Tape.write, Tape.move, Tape.moveRight])
                  (by simpa [start] using h))
          | cons second restTail =>
              cases second with
              | true =>
                  let stuck := HRP.runConfig 1 start
                  exact False.elim
                    (runConfig_halt_false_of_reaches_stuck
                      headerRemainderPrefixScannerDescription_haltTransitionFree
                      (k := 1) (stuck := stuck) rfl
                      (by simp [stuck, start,
                        HeaderRemainderPrefixScannerDescription,
                        tapeAtCells, runConfig, stepConfig,
                        lookupTransition, Matches, transition, keepMove,
                        Tape.read, Tape.write, Tape.move, Tape.moveRight])
                      (by
                        simp [stuck, start,
                          HeaderRemainderPrefixScannerDescription,
                          tapeAtCells, runConfig, stepConfig,
                          lookupTransition, Matches, transition, keepMove,
                          Tape.read, Tape.write, Tape.move, Tape.moveRight])
                      (by simpa [start] using h))
              | false =>
                  cases restTail with
                  | nil =>
                      let stuck := HRP.runConfig 2 start
                      exact False.elim
                        (runConfig_halt_false_of_reaches_stuck
                          headerRemainderPrefixScannerDescription_haltTransitionFree
                          (k := 2) (stuck := stuck) rfl
                          (by simp [stuck, start,
                            HeaderRemainderPrefixScannerDescription,
                            tapeAtCells, runConfig, stepConfig,
                            lookupTransition, Matches, transition, keepMove,
                            Tape.read, Tape.write, Tape.move, Tape.moveRight])
                          (by
                            simp [stuck, start,
                              HeaderRemainderPrefixScannerDescription,
                              tapeAtCells, runConfig, stepConfig,
                              lookupTransition, Matches, transition, keepMove,
                              Tape.read, Tape.write, Tape.move, Tape.moveRight])
                          (by simpa [start] using h))
                  | cons third afterThird =>
                      cases third with
                      | true =>
                          let stuck := HRP.runConfig 2 start
                          exact False.elim
                            (runConfig_halt_false_of_reaches_stuck
                              headerRemainderPrefixScannerDescription_haltTransitionFree
                              (k := 2) (stuck := stuck) rfl
                              (by simp [stuck, start,
                                HeaderRemainderPrefixScannerDescription,
                                tapeAtCells, runConfig, stepConfig,
                                lookupTransition, Matches, transition,
                                keepMove, Tape.read, Tape.write,
                                Tape.move, Tape.moveRight])
                              (by
                                simp [stuck, start,
                                  HeaderRemainderPrefixScannerDescription,
                                  tapeAtCells, runConfig, stepConfig,
                                  lookupTransition, Matches, transition,
                                  keepMove, Tape.read, Tape.write,
                                  Tape.move, Tape.moveRight])
                              (by simpa [start] using h))
                      | false =>
                          cases afterThird with
                          | nil =>
                              let stuck := HRP.runConfig 3 start
                              exact False.elim
                                (runConfig_halt_false_of_reaches_stuck
                                  headerRemainderPrefixScannerDescription_haltTransitionFree
                                  (k := 3) (stuck := stuck) rfl
                                  (by simp [stuck, start,
                                    HeaderRemainderPrefixScannerDescription,
                                    tapeAtCells, runConfig, stepConfig,
                                    lookupTransition, Matches, transition,
                                    keepMove, Tape.read, Tape.write,
                                    Tape.move, Tape.moveRight])
                                  (by
                                    simp [stuck, start,
                                      HeaderRemainderPrefixScannerDescription,
                                      tapeAtCells, runConfig, stepConfig,
                                      lookupTransition, Matches, transition,
                                      keepMove, Tape.read, Tape.write,
                                      Tape.move, Tape.moveRight])
                                  (by simpa [start] using h))
                          | cons b suffix =>
                              refine ⟨b, suffix, rfl, ?_⟩
                              rcases
                                  run_headerRemainderPrefix_raw_to_handoff_withBase
                                    base b suffix with ⟨steps, hgood⟩
                              exact
                                (MachineDescription.runConfig_halt_tape_functional_of_haltTransitionFree
                                  headerRemainderPrefixScannerDescription_haltTransitionFree
                                  (by simpa [HRP,
                                    HeaderRemainderPrefixScannerDescription,
                                    headerRemainderHandoffConfigWithBase,
                                    start, config] using hgood)
                                  (by simpa [HRP,
                                    HeaderRemainderPrefixScannerDescription,
                                    start] using h)).symm

private theorem sentinelScannerDescription_runConfig_code_inv
    (base : List (Option Bool)) (code : Word MachineCodeSymbol)
    {Tout : Tape Bool} {n : Nat}
    (h :
      SENT.runConfig n
          { state := SENT.start,
            tape := tapeAtCells base
              ((encodeCodeWordAsInput code).map some) } =
        { state := SENT.halt, tape := Tout }) :
    exists flag : Bool,
      code = MachineCodeSymbol.header :: encodeBoolAppend flag [] := by
  rcases sentinelScannerDescription_runConfig_parts_inv h with
    ⟨Tmark, Theader, nMark, nHeader, nFinal,
      hmark, hheader, hfinal⟩
  rcases
      markFirstTransitionBitDescription_runConfig_withBase_inv
        base (encodeCodeWordAsInput code) hmark with
    ⟨tail, hbits, hTmark⟩
  have hheaderCode :
      HRP.runConfig nHeader
          { state := HRP.start,
            tape := tapeAtCells (none :: base)
              ((false :: tail).map some) } =
        { state := HRP.halt, tape := Theader } := by
    rw [hTmark] at hheader
    simpa [config, tapeAtCells, Tape.move, Tape.moveRight] using hheader
  rcases
      headerRemainderPrefixScannerDescription_runConfig_withBase_inv
        (none :: base) (false :: tail) hheaderCode with
    ⟨b, suffix, htail, hTheader⟩
  have hfullBits :
      encodeCodeWordAsInput code =
        false :: false :: false :: false :: b :: suffix := by
    rw [hbits, htail]
  rcases encodeCodeWordAsInput_header_prefix_inv hfullBits with
    ⟨rest, hcode, hrestBits⟩
  let baseAfterHeader : List (Option Bool) :=
    List.append (headerRemainderBits.reverse.map some) (none :: base)
  have hfinalCode :
      FINAL.runConfig nFinal
          { state := FINAL.start,
            tape := tapeAtCells baseAfterHeader
              ((encodeCodeWordAsInput rest).map some) } =
        { state := FINAL.halt, tape := Tout } := by
    rw [hTheader] at hfinal
    rw [headerRemainderHandoffConfigWithBase_move_right] at hfinal
    simpa [baseAfterHeader, hrestBits] using hfinal
  rcases finalSentinelCleanupDescription_boolFinal_run_inv hfinalCode with
    ⟨Tbool, nBool, hbool⟩
  have hboolCode :
      BFS.runConfig nBool
          (config BFS.start baseAfterHeader
            ((encodeCodeWordAsInput rest).map some)) =
        { state := BFS.halt, tape := Tbool } := by
    simpa [config] using hbool
  rcases
      boolFinalScannerDescription_runConfig_code_terminal_inv
        baseAfterHeader rest hboolCode with
    ⟨flag, hflagCode, _hterminal⟩
  exact ⟨flag, by rw [hcode, hflagCode]⟩

private theorem checkedControllerSentinelScannerDescription_haltsWithTape_fields_inv
    {bits : Word Bool} {Tout : Tape Bool}
    (h : CHECK.HaltsWithTape bits Tout) :
    exists b : Bool, exists suffixTail : Word Bool,
    exists Tinput Tstage Tresult : Tape Bool,
    exists nInput nStage nResult nSentinel : Nat,
      bits = false :: false :: false :: false :: b :: suffixTail ∧
        BWSS.runConfig nInput
            (config BWSS.start
              (List.append (headerRemainderBits.reverse.map some) [none])
              ((b :: suffixTail).map some)) =
          { state := BWSS.halt, tape := Tinput } ∧
        NNSS.runConfig nStage
            { state := NNSS.start,
              tape := Tape.move Direction.right Tinput } =
          { state := NNSS.halt, tape := Tstage } ∧
        BWSS.runConfig nResult
            { state := BWSS.start,
              tape := Tape.move Direction.right Tstage } =
          { state := BWSS.halt, tape := Tresult } ∧
        SENT.runConfig nSentinel
            { state := SENT.start,
              tape := Tape.move Direction.right Tresult } =
          { state := SENT.halt, tape := Tout } := by
  rcases
      seqSubroutine_haltsWithTape_inv
        (A := MFTB) (B := BODY) (handoffMove := Direction.right)
        markFirstTransitionBitDescription_subroutineReady
        markedControllerBodyScannerDescription_subroutineReady
        (by simpa [CheckedControllerSentinelScannerDescription] using h) with
    ⟨Tmark, hmark, nBody, hbody⟩
  rcases markFirstTransitionBitDescription_haltsWithTape_inv hmark with
    ⟨tail, hbits, hTmark⟩
  have hbodyMarked :
      BODY.runConfig nBody
          { state := BODY.start,
            tape := tapeAtCells [none]
              (some false :: tail.map some) } =
        { state := BODY.halt, tape := Tout } := by
    rw [hTmark] at hbody
    simpa [config, tapeAtCells, Tape.move, Tape.moveRight] using hbody
  rcases
      seqSubroutine_runConfig_inv
        (A := HRP) (B := ISRSL) (handoffMove := Direction.right)
        headerRemainderPrefixScannerDescription_subroutineReady
        inputStageResultSentinelScannerDescription_subroutineReady
        (by simpa [MarkedControllerBodyScannerDescription] using hbodyMarked) with
    ⟨Theader, hheader, hrest⟩
  rcases hheader with ⟨nHeader, hheaderRun, _hheaderFirst⟩
  rcases hrest with ⟨nRest, hrestRun⟩
  rcases
      headerRemainderPrefixScannerDescription_markedTail_inv
        hheaderRun with
    ⟨b, suffixTail, htail, hTheader⟩
  have hrestHeader :
      ISRSL.runConfig nRest
          (config ISRSL.start
            (List.append (headerRemainderBits.reverse.map some) [none])
            ((b :: suffixTail).map some)) =
        { state := ISRSL.halt, tape := Tout } := by
    rw [hTheader] at hrestRun
    simpa [headerRemainderHandoffConfigWithBase_move_right, config]
      using hrestRun
  rcases
      seqSubroutine_runConfig_inv
        (A := BWSS) (B := SRSL) (handoffMove := Direction.right)
        boolWordSuffixScannerDescription_subroutineReady
        stageResultSentinelScannerDescription_subroutineReady
        (by simpa [ISRSL, SRSL,
          InputStageResultSentinelScannerDescription, config]
          using hrestHeader) with
    ⟨Tinput, hinput, hstageRest⟩
  rcases hinput with ⟨nInput, hinputRun, _hinputFirst⟩
  rcases hstageRest with ⟨nStageRest, hstageRestRun⟩
  rcases
      seqSubroutine_runConfig_inv
        (A := NNSS) (B := RSL) (handoffMove := Direction.right)
        EncRewriters.CanonicalLayouts.DovetailStagePrefix.nonemptyNatSuffixScannerDescription_subroutineReady
        resultSentinelScannerDescription_subroutineReady
        (by simpa [SRSL, RSL, StageResultSentinelScannerDescription]
          using hstageRestRun) with
    ⟨Tstage, hstage, hresultRest⟩
  rcases hstage with ⟨nStage, hstageRun, _hstageFirst⟩
  rcases hresultRest with ⟨nResultRest, hresultRestRun⟩
  rcases
      seqSubroutine_runConfig_inv
        (A := BWSS) (B := SENT) (handoffMove := Direction.right)
        boolWordSuffixScannerDescription_subroutineReady
        sentinelScannerDescription_subroutineReady
        (by simpa [RSL, SENT, ResultSentinelScannerDescription]
          using hresultRestRun) with
    ⟨Tresult, hresult, hsentinel⟩
  rcases hresult with ⟨nResult, hresultRun, _hresultFirst⟩
  rcases hsentinel with ⟨nSentinel, hsentinelRun⟩
  refine ⟨b, suffixTail, Tinput, Tstage, Tresult,
    nInput, nStage, nResult, nSentinel, ?_, hinputRun,
    hstageRun, hresultRun, hsentinelRun⟩
  rw [hbits, htail]

private theorem checkedControllerSentinelScannerDescription_haltsWithTape_code_inv
    (code : Word MachineCodeSymbol) {Tout : Tape Bool}
    (h : CHECK.HaltsWithTape (encodeCodeWordAsInput code) Tout) :
    exists C : DovetailControllerLayout, exists flag : Bool,
      code =
        DovetailControllerLayout.encodeAppend C
          (MachineCodeSymbol.header :: encodeBoolAppend flag []) := by
  rcases
      checkedControllerSentinelScannerDescription_haltsWithTape_fields_inv h with
    ⟨b, suffixTail, Tinput, Tstage, Tresult,
      nInput, nStage, nResult, nSentinel,
      hbits, hinputRun, hstageRun, hresultRun, hsentinelRun⟩
  rcases encodeCodeWordAsInput_header_prefix_inv hbits with
    ⟨rest, hcode, hrestBits⟩
  let baseAfterHeader : List (Option Bool) :=
    List.append (headerRemainderBits.reverse.map some) [none]
  have hinputCode :
      BWSS.runConfig nInput
          (config BWSS.start baseAfterHeader
            ((encodeCodeWordAsInput rest).map some)) =
        { state := BWSS.halt, tape := Tinput } := by
    simpa [baseAfterHeader, hrestBits] using hinputRun
  rcases
      boolWordSuffixScannerDescription_runConfig_code_inv
        baseAfterHeader rest hinputCode with
    ⟨inputWord, inputRest, hrest⟩
  rw [hrest] at hinputCode
  rcases
      EncRewriters.BoundedLayoutRunner.boolWordSuffixScannerDescription_runConfig_encodeBoolWordAppend_stage_handoff
        baseAfterHeader inputWord inputRest hinputCode hstageRun with
    ⟨baseAfterInput, hinputMove⟩
  have hstageCode :
      NNSS.runConfig nStage
          (config NNSS.start baseAfterInput
            ((encodeCodeWordAsInput inputRest).map some)) =
        { state := NNSS.halt, tape := Tstage } := by
    rw [hinputMove] at hstageRun
    exact hstageRun
  rcases
      EncRewriters.CanonicalLayouts.DovetailStagePrefix.nonemptyNatSuffixScannerDescription_runConfig_code_inv
        baseAfterInput inputRest hstageCode with
    ⟨stage, resultFirst, resultSuffix, hinputRest⟩
  rcases encodeCodeWordAsInput_cons_bits resultFirst resultSuffix with
    ⟨resultBit, resultBitsTail, hresultBits⟩
  rw [hinputRest] at hstageCode
  rcases
      EncRewriters.CanonicalLayouts.DovetailStagePrefix.nonemptyNatSuffixScannerDescription_runConfig_encodeNatAppend_handoff
        baseAfterInput stage (resultFirst :: resultSuffix)
        resultBit resultBitsTail hresultBits hstageCode with
    ⟨baseAfterStage, hstageMove⟩
  have hresultCode :
      BWSS.runConfig nResult
          (config BWSS.start baseAfterStage
            ((encodeCodeWordAsInput
              (resultFirst :: resultSuffix)).map some)) =
        { state := BWSS.halt, tape := Tresult } := by
    rw [hstageMove] at hresultRun
    exact hresultRun
  rcases
      boolWordSuffixScannerDescription_runConfig_code_inv
        baseAfterStage (resultFirst :: resultSuffix) hresultCode with
    ⟨resultWord, sentinelRest, hresultRest⟩
  rw [hresultRest] at hresultCode
  rcases
      boolWordSuffixScannerDescription_runConfig_encodeBoolWordAppend_handoff
        baseAfterStage resultWord sentinelRest hresultCode with
    ⟨sentinelTail, hsentinelBits, hTresult⟩
  have hsentinelCode :
      SENT.runConfig nSentinel
          (config SENT.start
            (cellListCanonicalRestoredLeftWithBase
              (resultWord.map some) baseAfterStage)
            ((encodeCodeWordAsInput sentinelRest).map some)) =
        { state := SENT.halt, tape := Tout } := by
    rw [hTresult] at hsentinelRun
    rw [boolWordCanonicalHandoffConfigWithBase_move_right_all]
      at hsentinelRun
    simpa [config, hsentinelBits] using hsentinelRun
  rcases
      sentinelScannerDescription_runConfig_code_inv
        (cellListCanonicalRestoredLeftWithBase
          (resultWord.map some) baseAfterStage)
        sentinelRest hsentinelCode with
    ⟨flag, hsentinelRest⟩
  refine
    ⟨{ input := inputWord, stage := stage, result := resultWord },
      flag, ?_⟩
  rw [hcode, hrest, hinputRest, hresultRest, hsentinelRest]
  rfl

theorem controllerWordStartRecognizerDescription_closed
    {w : Word Bool} {T : Tape Bool}
    (h : REC.HaltsFromTape (Tape.input w) T) :
    exists C : DovetailControllerLayout,
      w = stageAttemptFramedStructuredInputBits C ∧
        Tape.Equiv T
          (restoredCheckedHandoffTapeFromTail
            (markedControllerBodyBits C)) := by
  let ID := ExactIdentityDescription
  rcases
      seqSubroutine_haltsFromTape_inv
        (A := seqSubroutine PRE ID Direction.left)
        (B := CHECK) (handoffMove := Direction.right)
        (seqSubroutine_subroutineReady
          alignedAppendRewindDescription_subroutineReady
          CommonGround.Identity.exactIdentityDescription_subroutineReady)
        checkedControllerSentinelScannerDescription_subroutineReady
        (by simpa [REC, ControllerWordStartRecognizerDescription,
          CommonGround.SameHeadComposition.leftRightSeqDescription, ID]
          using h) with
    ⟨Tidentity, hpreIdentity, nCheck, hcheckRun⟩
  rcases
      seqSubroutine_haltsFromTape_inv
        (A := PRE) (B := ID) (handoffMove := Direction.left)
        alignedAppendRewindDescription_subroutineReady
        CommonGround.Identity.exactIdentityDescription_subroutineReady
        hpreIdentity with
    ⟨Tpre, hpre, nIdentity, hidentityRun⟩
  have hTidentity :
      Tidentity = Tape.move Direction.left Tpre := by
    have hidentityExact :=
      CommonGround.Identity.exactIdentityDescription_runConfig_from_start
        nIdentity (Tape.move Direction.left Tpre)
    rw [hidentityExact] at hidentityRun
    exact (congrArg Configuration.tape hidentityRun).symm
  rcases
      seqSubroutine_haltsFromTape_inv
        (A := CWA) (B := AR) (handoffMove := Direction.left)
        codeWordAlignedPreScannerDescription_subroutineReady
        appendSentinelRewindDescription_subroutineReady
        (by simpa [PRE, AlignedAppendRewindDescription] using hpre) with
    ⟨Taligned, haligned, nAppendRewind, happendRewindRun⟩
  rcases codeWordAlignedPreScannerDescription_haltsFromTape_inv haligned with
    ⟨symbol, restCode, hw, hTaligned⟩
  rcases encodeCodeWordAsInput_cons_bits symbol restCode with
    ⟨firstBit, tailBits, hbitsCons⟩
  have hwCons : w = firstBit :: tailBits := by
    rw [hw]
    exact hbitsCons
  have hAppendRewindSource :
      Tape.move Direction.left Taligned =
        CommonGround.FiniteTransducers.FSTSourceTape w 1 := by
    rw [hTaligned, hwCons, move_left_codeWordAlignedHandoffTape_cons]
    simp [CommonGround.FiniteTransducers.FSTSourceTape,
      CommonGround.FiniteTransducers.tapeAtCells, tapeAtCells]
  have happendRewind :
      AR.HaltsFromTape
        (CommonGround.FiniteTransducers.FSTSourceTape w 1) Tpre := by
    rw [hAppendRewindSource] at happendRewindRun
    exact haltsFromTape_of_runConfig_eq happendRewindRun
  have hTpre :
      Tpre =
        CommonGround.FiniteTransducers.rightEdgeRewindTargetTape
          (List.append w sentinelBits) [] := by
    exact
      haltsFromTape_functional_of_haltTransitionFree
        appendSentinelRewindDescription_subroutineReady.2
        happendRewind
        (appendSentinelRewindDescription_forward w)
  have hcheckSource :
      Tape.move Direction.right Tidentity =
        CommonGround.FiniteTransducers.rightEdgeRewindTargetTape
          (List.append w sentinelBits) [] := by
    rw [hTidentity, hTpre]
    cases w <;>
      simp [CommonGround.FiniteTransducers.rightEdgeRewindTargetTape,
        sentinelBits, sentinelCode, encodeBoolAppend, encodeCellAppend,
        encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
        CommonGround.FiniteTransducers.tapeAtCells,
        Tape.move, Tape.moveLeft, Tape.moveRight]
  have hcheckFromPadded :
      CHECK.HaltsFromTape
        (CommonGround.FiniteTransducers.rightEdgeRewindTargetTape
          (List.append w sentinelBits) []) T := by
    rw [hcheckSource] at hcheckRun
    exact haltsFromTape_of_runConfig_eq hcheckRun
  have hpaddedEquiv :
      Tape.Equiv
        (CommonGround.FiniteTransducers.rightEdgeRewindTargetTape
          (List.append w sentinelBits) [])
        (Tape.input (List.append w sentinelBits)) := by
    have hstart :
        CommonGround.FiniteTransducers.rightEdgeRewindTargetTape
            (List.append w sentinelBits) [] =
          tapeAtCells [none]
            (List.append ((List.append w sentinelBits).map some) [none]) := by
      cases w <;>
        simp [CommonGround.FiniteTransducers.rightEdgeRewindTargetTape,
          CommonGround.FiniteTransducers.tapeAtCells, tapeAtCells,
          sentinelBits, sentinelCode, encodeBoolAppend, encodeCellAppend,
          encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput]
    rw [hstart]
    exact paddedStartTape_equiv_input (List.append w sentinelBits)
  rcases
      HaltsFromTapeEquiv_of_input_equiv
        (D := CHECK)
        (Tin := CommonGround.FiniteTransducers.rightEdgeRewindTargetTape
          (List.append w sentinelBits) [])
        (Tin' := Tape.input (List.append w sentinelBits))
        (Tout := T)
        hpaddedEquiv hcheckFromPadded with
    ⟨Tclean, hcleanRun, _hTclean⟩
  have hcleanWith :
      CHECK.HaltsWithTape (List.append w sentinelBits) Tclean := by
    rcases hcleanRun with ⟨n, hn⟩
    exact
      ⟨n, by
        simpa [HaltsWithTapeIn, HaltsFromTapeIn, initial] using hn⟩
  have hcombinedBits :
      List.append w sentinelBits =
        encodeCodeWordAsInput
          (List.append (symbol :: restCode) sentinelCode) := by
    rw [hw, sentinelBits, encodeCodeWordAsInput_append]
  have hcleanCode :
      CHECK.HaltsWithTape
        (encodeCodeWordAsInput
          (List.append (symbol :: restCode) sentinelCode)) Tclean := by
    rw [← hcombinedBits]
    exact hcleanWith
  rcases
      checkedControllerSentinelScannerDescription_haltsWithTape_code_inv
        (List.append (symbol :: restCode) sentinelCode) hcleanCode with
    ⟨C, flag, hcombinedCode⟩
  rw [dovetailControllerLayout_encodeAppend_eq_append] at hcombinedCode
  have hsuffixLength :
      sentinelCode.length =
        (MachineCodeSymbol.header :: encodeBoolAppend flag []).length := by
    cases flag <;> rfl
  have hcodeEq :
      symbol :: restCode = DovetailControllerLayout.encode C :=
    (List.append_inj' hcombinedCode hsuffixLength).left
  have hwC : w = stageAttemptFramedStructuredInputBits C := by
    rw [hw, hcodeEq]
    rfl
  refine ⟨C, hwC, ?_⟩
  rcases controllerWordStartRecognizerDescription_forward C with
    ⟨Tforward, hforward, hTforward⟩
  have hforwardFromW : REC.HaltsFromTape (Tape.input w) Tforward := by
    rw [hwC]
    exact hforward
  have hsame : T = Tforward :=
    haltsFromTape_functional_of_haltTransitionFree
      controllerWordStartRecognizerDescription_subroutineReady.2
      h hforwardFromW
  rw [hsame]
  exact hTforward

private theorem stageAttemptFramedStructuredInputBits_eq_first_body
    (C : DovetailControllerLayout) :
    stageAttemptFramedStructuredInputBits C =
      false :: markedControllerBodyBits C := by
  have h := augmentedControllerBits_eq_first_body_append_sentinel C
  rw [augmentedControllerBits_eq_original_append] at h
  exact (List.append_inj' h rfl).left

theorem move_left_restoredCheckedHandoffTape_equiv_input
    (C : DovetailControllerLayout) :
    Tape.Equiv
      (Tape.move Direction.left
        (restoredCheckedHandoffTapeFromTail
          (markedControllerBodyBits C)))
      (Tape.input (stageAttemptFramedStructuredInputBits C)) := by
  rw [stageAttemptFramedStructuredInputBits_eq_first_body]
  let tail : Word Bool :=
    false :: false ::
      boolWordFieldBits C.input
        (List.append (stageNatBits C.stage)
          (boolWordFieldBits C.result []))
  have hbody : markedControllerBodyBits C = false :: tail := by
    simp [markedControllerBodyBits, headerRemainderBits, tail]
  rw [hbody]
  change Tape.Equiv
    { left := [], head := some false,
      right := List.append ((false :: tail).map some) [none] }
    { left := [], head := some false,
      right := (false :: tail).map some }
  exact ⟨rfl, rfl, dropTrailingNone_append_none _⟩

end FoC.Computability.StructuredConstructionTargets.StageAttemptFramedMaterializer.Internal

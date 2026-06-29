import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.Composition.Definitions

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace CanonicalLayouts
namespace DovetailLayoutScanner

open FoC.Computability.DovetailInitialLayoutInitializer
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner
open CommonGround.SeqComposition
theorem rightHandoffSequential_runConfig_exists
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {nA : Nat} {Tin Tmid Tout : Tape Bool}
    (hArun :
      A.runConfig nA { state := A.start, tape := Tin } =
        { state := A.halt, tape := Tmid })
    (hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start, tape := Tape.move Direction.right Tmid } =
          { state := B.halt, tape := Tout }) :
    exists steps : Nat,
      (seqSubroutine A B Direction.right).runConfig
          steps
          { state := (seqSubroutine A B
              Direction.right).start
            tape := Tin } =
        { state :=
            (seqSubroutine A B Direction.right).halt
          tape := Tout } :=
  seqSubroutine_runConfig_exists
    (A := A) (B := B) (handoffMove := Direction.right)
    hA hB hArun hBReach

private abbrev CLSS := CellListSuffixScannerDescription
private abbrev CSS := CellSuffixScannerDescription
private abbrev TSS := TapeSuffixScannerDescription
private abbrev CFS := ConfigurationSuffixScannerDescription
private abbrev FHFS := FinalHitFlagsScannerDescription
private abbrev RCF := RejectConfigAndFinalFlagsScannerDescription
private abbrev CFFS := ConfigurationsAndFinalFlagsScannerDescription
private abbrev SCFFS := StageConfigurationsAndFinalFlagsScannerDescription
private abbrev ISCFFS := InputStageConfigurationsAndFinalFlagsScannerDescription
private abbrev MDBS := MarkedDovetailLayoutBodyScannerDescription
private abbrev CDL := CheckedDovetailLayoutScannerDescription
private abbrev TRP := TransitionRemainderPrefixScannerDescription
private abbrev RFM := ReturnToFirstMarkerDescription
private abbrev MFTB := MarkFirstTransitionBitDescription
private abbrev BWSS := BoolWordSuffixScannerDescription
private abbrev BSS := BoolSuffixScannerDescription
private abbrev BFS := BoolFinalScannerDescription
private abbrev NNSS := DovetailStagePrefix.NonemptyNatSuffixScannerDescription

theorem run_finalHitFlags_raw_to_handoff_withBase
    (acceptHit rejectHit : Bool)
    (baseLeft : List (Option Bool)) :
    exists steps : Nat,
      FHFS.runConfig steps
          { state := FHFS.start
            tape :=
              tapeAtCells baseLeft
                ((boolFieldBits acceptHit
                  (boolFieldBits rejectHit [])).map some) } =
        { state := FHFS.halt
          tape :=
            (boolFinalHandoffConfigWithBase rejectHit
              (List.append
                ((cellCodeBits (some acceptHit)).reverse.map some)
                baseLeft)).tape } := by
  rcases cellCodeBits_cons_false (some rejectHit) with
    ⟨tail, htail⟩
  rcases run_boolOnlySuffix_raw_to_handoff_withBase
      acceptHit baseLeft false tail with
    ⟨acceptSteps, haccept⟩
  let baseAfterAccept :=
    List.append ((cellCodeBits (some acceptHit)).reverse.map some)
      baseLeft
  let Tmid :=
    boolOnlySuffixHandoffConfigWithBase acceptHit baseLeft
      (false :: tail)
  have hArun :
      BSS.runConfig acceptSteps
          { state := BSS.start
            tape :=
              tapeAtCells baseLeft
                ((boolFieldBits acceptHit
                  (boolFieldBits rejectHit [])).map some) } =
        { state := BSS.halt
          tape := Tmid.tape } := by
    change
      BSS.runConfig acceptSteps
          (config 10 baseLeft
            ((boolFieldBits acceptHit
              (boolFieldBits rejectHit [])).map some)) =
        Tmid
    rw [show
        ((boolFieldBits acceptHit
          (boolFieldBits rejectHit [])).map some) =
          List.append ((cellCodeBits (some acceptHit)).map some)
            (some false :: tail.map some) by
      change
        (cellFieldBits (some acceptHit)
          (cellFieldBits (some rejectHit) [])).map some =
          List.append ((cellCodeBits (some acceptHit)).map some)
            (some false :: tail.map some)
      simp [cellFieldBits, htail, List.map_append]]
    simpa [Tmid] using haccept
  have hBReach :
      exists nB : Nat,
        BFS.runConfig nB
            { state := BFS.start
              tape := Tape.move Direction.right Tmid.tape } =
          { state := BFS.halt
            tape :=
              (boolFinalHandoffConfigWithBase rejectHit
                baseAfterAccept).tape } := by
    rcases run_boolFinal_raw_to_handoff_withBase
        rejectHit baseAfterAccept with
      ⟨finalSteps, hfinal⟩
    have hmove :
        Tape.move Direction.right Tmid.tape =
          tapeAtCells baseAfterAccept
            ((cellCodeBits (some rejectHit)).map some) := by
      simpa [Tmid, baseAfterAccept, htail] using
        boolOnlySuffixHandoffConfigWithBase_move_right
          acceptHit baseLeft false tail
    exact
      runConfig_reaches_from_move_eq
        (B := BFS)
        (handoffMove := Direction.right)
        hmove
        (by simpa [config] using hfinal)
  simpa [FinalHitFlagsScannerDescription, Tmid, baseAfterAccept]
    using
      seqSubroutine_runConfig_exists
        (A := BSS)
        (B := BFS)
        (handoffMove := Direction.right)
        boolSuffixScannerDescription_subroutineReady
        boolFinalScannerDescription_subroutineReady
        hArun hBReach

theorem run_cellThenCellList_raw_to_handoff_withBase
    (head : Option Bool) (right baseLeft : List (Option Bool))
    (suffixTail : Word Bool) :
    exists steps : Nat,
      (seqSubroutine
          CSS
          CLSS
          Direction.right).runConfig steps
          { state :=
              (seqSubroutine
                CSS
                CLSS
                Direction.right).start
            tape :=
              tapeAtCells baseLeft
                ((cellFieldBits head
                  (cellListFieldBits right
                    (false :: suffixTail))).map some) } =
        { state :=
            (seqSubroutine
              CSS
              CLSS
              Direction.right).halt
          tape :=
            (cellListCanonicalHandoffConfigWithBase right
              (List.append ((cellCodeBits head).reverse.map some)
                baseLeft)
              (false :: suffixTail)).tape } := by
  rcases cellListFieldBits_cons_false right (false :: suffixTail) with
    ⟨fieldTail, hfieldTail⟩
  rcases run_cellSuffix_raw_to_handoff_withBase
      head baseLeft false fieldTail with
    ⟨headSteps, hhead⟩
  let baseAfterHead :=
    List.append ((cellCodeBits head).reverse.map some) baseLeft
  let Tmid := cellSuffixHandoffConfigWithBase head baseLeft
    (false :: fieldTail)
  have hArun :
      CSS.runConfig headSteps
          { state := CSS.start
            tape :=
              tapeAtCells baseLeft
                ((cellFieldBits head
                  (cellListFieldBits right
                    (false :: suffixTail))).map some) } =
        { state := CSS.halt
          tape := Tmid.tape } := by
    simpa [Tmid, cellFieldBits, hfieldTail, List.map_append] using
      hhead
  have hBReach :
      exists nB : Nat,
        CLSS.runConfig nB
            { state := CLSS.start
              tape := Tape.move Direction.right Tmid.tape } =
          { state := CLSS.halt
            tape :=
              (cellListCanonicalHandoffConfigWithBase right
                baseAfterHead (false :: suffixTail)).tape } := by
    rcases run_cellList_raw_to_canonical_handoff_withBase
        right baseAfterHead suffixTail with
      ⟨rightSteps, hright⟩
    have hmove :
        Tape.move Direction.right Tmid.tape =
          tapeAtCells baseAfterHead
            ((cellListFieldBits right
              (false :: suffixTail)).map some) := by
      simpa [Tmid, baseAfterHead, hfieldTail] using
        cellSuffixHandoffConfigWithBase_move_right
          head baseLeft false fieldTail
    exact
      runConfig_reaches_from_move_eq
        (B := CLSS)
        (handoffMove := Direction.right)
        hmove
        (by
          simpa [CellListSuffixScannerDescription, config,
            cellListFieldBits, List.map_append, baseAfterHead] using
            hright)
  simpa [Tmid, baseAfterHead, cellFieldBits, hfieldTail,
    List.map_append] using
      seqSubroutine_runConfig_exists
        (A := CSS)
        (B := CLSS)
        (handoffMove := Direction.right)
        cellSuffixScannerDescription_subroutineReady
        cellListSuffixScannerDescription_subroutineReady
        hArun hBReach

theorem run_tapeSuffix_raw_to_handoff_withBase
    (T : Tape Bool) (baseLeft : List (Option Bool))
    (suffixTail : Word Bool) :
    exists steps : Nat,
      TSS.runConfig steps
          { state := TSS.start
            tape :=
              tapeAtCells baseLeft
                ((tapeFieldBits T (false :: suffixTail)).map some) } =
        { state := TSS.halt
          tape :=
            (cellListCanonicalHandoffConfigWithBase T.right
              (List.append ((cellCodeBits T.head).reverse.map some)
                (cellListCanonicalRestoredLeftWithBase T.left baseLeft))
              (false :: suffixTail)).tape } := by
  rcases cellFieldBits_cons_false T.head
      (cellListFieldBits T.right (false :: suffixTail)) with
    ⟨headTail, hheadTail⟩
  rcases run_cellList_raw_to_canonical_handoff_withBase
      T.left baseLeft headTail with
    ⟨leftSteps, hleft⟩
  let baseAfterLeft := cellListCanonicalRestoredLeftWithBase T.left baseLeft
  let Tmid := cellListCanonicalHandoffConfigWithBase T.left baseLeft
    (false :: headTail)
  have hArun :
      CLSS.runConfig leftSteps
          { state := CLSS.start
            tape :=
              tapeAtCells baseLeft
                ((tapeFieldBits T (false :: suffixTail)).map some) } =
        { state := CLSS.halt
          tape := Tmid.tape } := by
    change
      CLSS.runConfig leftSteps
          (config 100 baseLeft
            ((tapeFieldBits T (false :: suffixTail)).map some)) =
        Tmid
    rw [show
        ((tapeFieldBits T (false :: suffixTail)).map some) =
          List.append ((stageNatBits T.left.length).map some)
            (List.append ((cellsCodeBits T.left).map some)
              (some false :: headTail.map some)) by
      change
        (cellListFieldBits T.left
          (cellFieldBits T.head
            (cellListFieldBits T.right (false :: suffixTail)))).map
            some =
          List.append ((stageNatBits T.left.length).map some)
            (List.append ((cellsCodeBits T.left).map some)
              (some false :: headTail.map some))
      rw [hheadTail]
      simp [cellListFieldBits, List.map_append]]
    simpa [Tmid] using hleft
  have hBReach :
      exists nB : Nat,
        (seqSubroutine
          CSS
          CLSS
          Direction.right).runConfig nB
            { state :=
                (seqSubroutine
                  CSS
                  CLSS
                  Direction.right).start
              tape := Tape.move Direction.right Tmid.tape } =
          { state :=
              (seqSubroutine
                CSS
                CLSS
                Direction.right).halt
            tape :=
              (cellListCanonicalHandoffConfigWithBase T.right
                (List.append ((cellCodeBits T.head).reverse.map some)
                  baseAfterLeft)
                (false :: suffixTail)).tape } := by
    rcases run_cellThenCellList_raw_to_handoff_withBase
        T.head T.right baseAfterLeft suffixTail with
      ⟨innerSteps, hinner⟩
    have hmove :
        Tape.move Direction.right Tmid.tape =
          tapeAtCells baseAfterLeft
            ((cellFieldBits T.head
              (cellListFieldBits T.right
                (false :: suffixTail))).map some) := by
      simpa [Tmid, baseAfterLeft, hheadTail] using
        cellListCanonicalHandoffConfigWithBase_move_right
          T.left baseLeft false headTail
    exact
      runConfig_reaches_from_move_eq
        (B :=
          seqSubroutine
            CSS
            CLSS
            Direction.right)
        (handoffMove := Direction.right)
        hmove
        (by simpa [baseAfterLeft] using hinner)
  simpa [TapeSuffixScannerDescription, Tmid, baseAfterLeft,
    tapeFieldBits, hheadTail, List.map_append] using
    seqSubroutine_runConfig_exists
      (A := CLSS)
      (B :=
        seqSubroutine
          CSS
          CLSS
          Direction.right)
      (handoffMove := Direction.right)
      cellListSuffixScannerDescription_subroutineReady
      (seqSubroutine_subroutineReady
        cellSuffixScannerDescription_subroutineReady
        cellListSuffixScannerDescription_subroutineReady)
      hArun hBReach

theorem run_configurationSuffix_raw_to_handoff_withBase
    (cfg : Configuration)
    (baseLeft : List (Option Bool)) (suffixTail : Word Bool) :
    exists steps : Nat,
      CFS.runConfig steps
          { state := CFS.start
            tape :=
              tapeAtCells baseLeft
                ((configurationFieldBits cfg
                  (false :: suffixTail)).map some) } =
        { state := CFS.halt
          tape :=
            (cellListCanonicalHandoffConfigWithBase cfg.tape.right
              (List.append ((cellCodeBits cfg.tape.head).reverse.map some)
                (cellListCanonicalRestoredLeftWithBase cfg.tape.left
                  (List.append ((stageNatBits cfg.state).reverse.map some)
                    baseLeft)))
              (false :: suffixTail)).tape } := by
  rcases tapeFieldBits_cons_false cfg.tape (false :: suffixTail) with
    ⟨tapeTail, htapeTail⟩
  rcases
      DovetailStagePrefix.run_nonemptyNatSuffix_raw_to_handoff_withBase
        cfg.state baseLeft false tapeTail with
    ⟨stateSteps, hstate⟩
  let baseAfterState :=
    List.append ((stageNatBits cfg.state).reverse.map some) baseLeft
  let Tmid :=
    DovetailStagePrefix.nonemptyNatSuffixHandoffConfigWithBase
      cfg.state baseLeft (false :: tapeTail)
  have hArun :
      NNSS.runConfig
          stateSteps
          { state :=
              NNSS.start
            tape :=
              tapeAtCells baseLeft
                ((configurationFieldBits cfg
                  (false :: suffixTail)).map some) } =
        { state := NNSS.halt
          tape := Tmid.tape } := by
    change
      NNSS.runConfig
          stateSteps
          (config 200 baseLeft
            ((configurationFieldBits cfg
              (false :: suffixTail)).map some)) =
        Tmid
    rw [show
        ((configurationFieldBits cfg
          (false :: suffixTail)).map some) =
          List.append ((stageNatBits cfg.state).map some)
            (some false :: tapeTail.map some) by
      change
        (List.append (stageNatBits cfg.state)
          (tapeFieldBits cfg.tape (false :: suffixTail))).map some =
          List.append ((stageNatBits cfg.state).map some)
            (some false :: tapeTail.map some)
      rw [htapeTail]
      simp [List.map_append]]
    simpa [Tmid] using hstate
  have hBReach :
      exists nB : Nat,
        TSS.runConfig nB
            { state := TSS.start
              tape := Tape.move Direction.right Tmid.tape } =
          { state := TSS.halt
            tape :=
              (cellListCanonicalHandoffConfigWithBase cfg.tape.right
                (List.append
                  ((cellCodeBits cfg.tape.head).reverse.map some)
                  (cellListCanonicalRestoredLeftWithBase cfg.tape.left
                    baseAfterState))
                (false :: suffixTail)).tape } := by
    rcases run_tapeSuffix_raw_to_handoff_withBase
        cfg.tape baseAfterState suffixTail with
      ⟨tapeSteps, htape⟩
    have hmove :
        Tape.move Direction.right Tmid.tape =
          tapeAtCells baseAfterState
            ((tapeFieldBits cfg.tape
              (false :: suffixTail)).map some) := by
      simpa [Tmid, baseAfterState, htapeTail] using
        DovetailStagePrefix.nonemptyNatSuffixHandoffConfigWithBase_move_right
          cfg.state baseLeft false tapeTail
    exact
      runConfig_reaches_from_move_eq
        (B := TSS)
        (handoffMove := Direction.right)
        hmove
        (by simpa [baseAfterState] using htape)
  simpa [ConfigurationSuffixScannerDescription, Tmid, baseAfterState,
    configurationFieldBits, htapeTail, List.map_append] using
      seqSubroutine_runConfig_exists
        (A := NNSS)
        (B := TSS)
        (handoffMove := Direction.right)
        DovetailStagePrefix.nonemptyNatSuffixScannerDescription_subroutineReady
        tapeSuffixScannerDescription_subroutineReady
        hArun hBReach

theorem run_rejectConfigAndFinalFlags_raw_to_handoff_withBase
    (rejectConfig : Configuration)
    (acceptHit rejectHit : Bool)
    (baseLeft : List (Option Bool)) :
    exists steps : Nat,
      RCF.runConfig steps
          { state := RCF.start
            tape :=
              tapeAtCells baseLeft
                ((configurationFieldBits rejectConfig
                  (boolFieldBits acceptHit
                    (boolFieldBits rejectHit []))).map some) } =
        { state := RCF.halt
          tape :=
            (boolFinalHandoffConfigWithBase rejectHit
              (List.append
                ((cellCodeBits (some acceptHit)).reverse.map some)
                (configurationRestoredLeftWithBase rejectConfig
                  baseLeft))).tape } := by
  rcases cellFieldBits_cons_false (some acceptHit)
      (boolFieldBits rejectHit []) with
    ⟨flagsTail, hflagsTail⟩
  rcases run_configurationSuffix_raw_to_handoff_withBase
      rejectConfig baseLeft flagsTail with
    ⟨configSteps, hconfig⟩
  let TmidTape : Tape Bool :=
    (cellListCanonicalHandoffConfigWithBase rejectConfig.tape.right
      (List.append ((cellCodeBits rejectConfig.tape.head).reverse.map some)
        (cellListCanonicalRestoredLeftWithBase rejectConfig.tape.left
          (List.append ((stageNatBits rejectConfig.state).reverse.map some)
            baseLeft)))
      (false :: flagsTail)).tape
  have hArun :
      CFS.runConfig configSteps
          { state := CFS.start
            tape :=
            tapeAtCells baseLeft
                ((configurationFieldBits rejectConfig
                  (boolFieldBits acceptHit
                    (boolFieldBits rejectHit []))).map some) } =
        { state := CFS.halt
          tape := TmidTape } := by
    rw [show
        ((configurationFieldBits rejectConfig
          (boolFieldBits acceptHit
            (boolFieldBits rejectHit []))).map some) =
          (configurationFieldBits rejectConfig
            (false :: flagsTail)).map some by
      have hflagsBits :
          boolFieldBits acceptHit (boolFieldBits rejectHit []) =
            false :: flagsTail := by
        simpa [boolFieldBits] using hflagsTail
      rw [hflagsBits]]
    simpa [TmidTape] using hconfig
  have hBReach :
      exists nB : Nat,
        FHFS.runConfig nB
            { state := FHFS.start
              tape := Tape.move Direction.right TmidTape } =
          { state := FHFS.halt
            tape :=
              (boolFinalHandoffConfigWithBase rejectHit
                (List.append
                  ((cellCodeBits (some acceptHit)).reverse.map some)
                  (configurationRestoredLeftWithBase rejectConfig
                    baseLeft))).tape } := by
    rcases run_finalHitFlags_raw_to_handoff_withBase
        acceptHit rejectHit
        (configurationRestoredLeftWithBase rejectConfig baseLeft) with
      ⟨flagSteps, hflags⟩
    have hmove :
        Tape.move Direction.right TmidTape =
          tapeAtCells
            (configurationRestoredLeftWithBase rejectConfig baseLeft)
            ((boolFieldBits acceptHit
              (boolFieldBits rejectHit [])).map some) := by
      have hraw :
          Tape.move Direction.right TmidTape =
            tapeAtCells
              (configurationRestoredLeftWithBase rejectConfig baseLeft)
              ((false :: flagsTail).map some) := by
        simpa [TmidTape, configurationRestoredLeftWithBase] using
          cellListCanonicalHandoffConfigWithBase_move_right
            rejectConfig.tape.right
            (List.append
              ((cellCodeBits rejectConfig.tape.head).reverse.map some)
              (cellListCanonicalRestoredLeftWithBase rejectConfig.tape.left
                (List.append
                  ((stageNatBits rejectConfig.state).reverse.map some)
                  baseLeft)))
            false flagsTail
      rw [hraw]
      have hflagsCells :
          (false :: flagsTail).map some =
            (boolFieldBits acceptHit
              (boolFieldBits rejectHit [])).map some := by
        simpa [boolFieldBits] using
          congrArg (fun bits => bits.map some) hflagsTail.symm
      simp [hflagsCells]
    exact
      runConfig_reaches_from_move_eq
        (B := FHFS)
        (handoffMove := Direction.right)
        hmove
        (by simpa using hflags)
  simpa [RejectConfigAndFinalFlagsScannerDescription, TmidTape] using
    seqSubroutine_runConfig_exists
      (A := CFS)
      (B := FHFS)
      (handoffMove := Direction.right)
      configurationSuffixScannerDescription_subroutineReady
      finalHitFlagsScannerDescription_subroutineReady
      hArun hBReach

theorem run_configurationsAndFinalFlags_raw_to_handoff_withBase
    (acceptConfig rejectConfig : Configuration)
    (acceptHit rejectHit : Bool)
    (baseLeft : List (Option Bool)) :
    exists steps : Nat,
      CFFS.runConfig steps
          { state := CFFS.start
            tape :=
              tapeAtCells baseLeft
                ((configurationFieldBits acceptConfig
                  (configurationFieldBits rejectConfig
                    (boolFieldBits acceptHit
                      (boolFieldBits rejectHit [])))).map some) } =
        { state := CFFS.halt
          tape :=
            (boolFinalHandoffConfigWithBase rejectHit
              (List.append
                ((cellCodeBits (some acceptHit)).reverse.map some)
                (configurationRestoredLeftWithBase rejectConfig
                  (configurationRestoredLeftWithBase acceptConfig
                    baseLeft)))).tape } := by
  rcases configurationFieldBits_cons_false rejectConfig
      (boolFieldBits acceptHit (boolFieldBits rejectHit [])) with
    ⟨rejectTail, hrejectTail⟩
  rcases run_configurationSuffix_raw_to_handoff_withBase
      acceptConfig baseLeft rejectTail with
    ⟨acceptSteps, haccept⟩
  let TmidTape : Tape Bool :=
    (cellListCanonicalHandoffConfigWithBase acceptConfig.tape.right
      (List.append ((cellCodeBits acceptConfig.tape.head).reverse.map some)
        (cellListCanonicalRestoredLeftWithBase acceptConfig.tape.left
          (List.append ((stageNatBits acceptConfig.state).reverse.map some)
            baseLeft)))
      (false :: rejectTail)).tape
  have hArun :
      CFS.runConfig acceptSteps
          { state := CFS.start
            tape :=
              tapeAtCells baseLeft
                ((configurationFieldBits acceptConfig
                  (configurationFieldBits rejectConfig
                    (boolFieldBits acceptHit
                      (boolFieldBits rejectHit [])))).map some) } =
        { state := CFS.halt
          tape := TmidTape } := by
    rw [show
        ((configurationFieldBits acceptConfig
          (configurationFieldBits rejectConfig
            (boolFieldBits acceptHit
              (boolFieldBits rejectHit [])))).map some) =
          (configurationFieldBits acceptConfig
            (false :: rejectTail)).map some by
      rw [hrejectTail]]
    simpa [TmidTape] using haccept
  have hBReach :
      exists nB : Nat,
        RCF.runConfig nB
            { state := RCF.start
              tape := Tape.move Direction.right TmidTape } =
          { state := RCF.halt
            tape :=
              (boolFinalHandoffConfigWithBase rejectHit
                (List.append
                  ((cellCodeBits (some acceptHit)).reverse.map some)
                  (configurationRestoredLeftWithBase rejectConfig
                    (configurationRestoredLeftWithBase acceptConfig
                      baseLeft)))).tape } := by
    rcases run_rejectConfigAndFinalFlags_raw_to_handoff_withBase
        rejectConfig acceptHit rejectHit
        (configurationRestoredLeftWithBase acceptConfig baseLeft) with
      ⟨rejectSteps, hreject⟩
    have hmove :
        Tape.move Direction.right TmidTape =
          tapeAtCells
            (configurationRestoredLeftWithBase acceptConfig baseLeft)
            ((configurationFieldBits rejectConfig
              (boolFieldBits acceptHit
                (boolFieldBits rejectHit []))).map some) := by
      have hraw :
          Tape.move Direction.right TmidTape =
            tapeAtCells
              (configurationRestoredLeftWithBase acceptConfig baseLeft)
              ((false :: rejectTail).map some) := by
        simpa [TmidTape, configurationRestoredLeftWithBase] using
          cellListCanonicalHandoffConfigWithBase_move_right
            acceptConfig.tape.right
            (List.append
              ((cellCodeBits acceptConfig.tape.head).reverse.map some)
              (cellListCanonicalRestoredLeftWithBase acceptConfig.tape.left
                (List.append
                  ((stageNatBits acceptConfig.state).reverse.map some)
                  baseLeft)))
            false rejectTail
      rw [hraw]
      have hrejectCells :
          (false :: rejectTail).map some =
            (configurationFieldBits rejectConfig
              (boolFieldBits acceptHit
                (boolFieldBits rejectHit []))).map some := by
        simpa using
          congrArg (fun bits => bits.map some) hrejectTail.symm
      simp [hrejectCells]
    exact
      runConfig_reaches_from_move_eq
        (B := RCF)
        (handoffMove := Direction.right)
        hmove
        (by simpa using hreject)
  simpa [ConfigurationsAndFinalFlagsScannerDescription, TmidTape] using
    seqSubroutine_runConfig_exists
      (A := CFS)
      (B := RCF)
      (handoffMove := Direction.right)
      configurationSuffixScannerDescription_subroutineReady
      rejectConfigAndFinalFlagsScannerDescription_subroutineReady
      hArun hBReach

theorem run_stageConfigurationsAndFinalFlags_raw_to_handoff_withBase
    (stage : Nat)
    (acceptConfig rejectConfig : Configuration)
    (acceptHit rejectHit : Bool)
    (baseLeft : List (Option Bool)) :
    exists steps : Nat,
      SCFFS.runConfig steps
          { state := SCFFS.start
            tape :=
              tapeAtCells baseLeft
                ((List.append (stageNatBits stage)
                  (configurationFieldBits acceptConfig
                    (configurationFieldBits rejectConfig
                      (boolFieldBits acceptHit
                        (boolFieldBits rejectHit []))))).map some) } =
        { state := SCFFS.halt
          tape :=
            (boolFinalHandoffConfigWithBase rejectHit
              (List.append
                ((cellCodeBits (some acceptHit)).reverse.map some)
                (configurationRestoredLeftWithBase rejectConfig
                  (configurationRestoredLeftWithBase acceptConfig
                    (List.append ((stageNatBits stage).reverse.map some)
                      baseLeft))))).tape } := by
  rcases configurationFieldBits_cons_false acceptConfig
      (configurationFieldBits rejectConfig
        (boolFieldBits acceptHit (boolFieldBits rejectHit []))) with
    ⟨acceptTail, hacceptTail⟩
  rcases DovetailStagePrefix.run_nonemptyNatSuffix_raw_to_handoff_withBase
      stage baseLeft false acceptTail with
    ⟨stageSteps, hstage⟩
  let TmidTape : Tape Bool :=
    (DovetailStagePrefix.nonemptyNatSuffixHandoffConfigWithBase
      stage baseLeft (false :: acceptTail)).tape
  let baseAfterStage : List (Option Bool) :=
    List.append ((stageNatBits stage).reverse.map some) baseLeft
  have hArun :
      NNSS.runConfig
          stageSteps
          { state :=
              NNSS.start
            tape :=
              tapeAtCells baseLeft
                ((List.append (stageNatBits stage)
                  (configurationFieldBits acceptConfig
                    (configurationFieldBits rejectConfig
                      (boolFieldBits acceptHit
                        (boolFieldBits rejectHit []))))).map some) } =
        { state := NNSS.halt
          tape := TmidTape } := by
    rw [show
        (List.append (stageNatBits stage)
          (configurationFieldBits acceptConfig
            (configurationFieldBits rejectConfig
              (boolFieldBits acceptHit
                (boolFieldBits rejectHit []))))).map some =
          (List.append (stageNatBits stage)
            (false :: acceptTail)).map some by
      rw [hacceptTail]]
    simpa [TmidTape] using hstage
  have hBReach :
      exists nB : Nat,
        CFFS.runConfig nB
            { state := CFFS.start
              tape := Tape.move Direction.right TmidTape } =
          { state := CFFS.halt
            tape :=
              (boolFinalHandoffConfigWithBase rejectHit
                (List.append
                  ((cellCodeBits (some acceptHit)).reverse.map some)
                  (configurationRestoredLeftWithBase rejectConfig
                    (configurationRestoredLeftWithBase acceptConfig
                      baseAfterStage)))).tape } := by
    rcases run_configurationsAndFinalFlags_raw_to_handoff_withBase
        acceptConfig rejectConfig acceptHit rejectHit baseAfterStage with
      ⟨configSteps, hconfigs⟩
    have hmove :
        Tape.move Direction.right TmidTape =
          tapeAtCells baseAfterStage
            ((configurationFieldBits acceptConfig
              (configurationFieldBits rejectConfig
                (boolFieldBits acceptHit
                  (boolFieldBits rejectHit [])))).map some) := by
      have hraw :
          Tape.move Direction.right TmidTape =
            tapeAtCells baseAfterStage
              ((false :: acceptTail).map some) := by
        simpa [TmidTape, baseAfterStage] using
          DovetailStagePrefix.nonemptyNatSuffixHandoffConfigWithBase_move_right
            stage baseLeft false acceptTail
      rw [hraw]
      have hacceptCells :
          (false :: acceptTail).map some =
            (configurationFieldBits acceptConfig
              (configurationFieldBits rejectConfig
                (boolFieldBits acceptHit
                  (boolFieldBits rejectHit [])))).map some := by
        simpa using
          congrArg (fun bits => bits.map some) hacceptTail.symm
      simp [hacceptCells]
    exact
      runConfig_reaches_from_move_eq
        (B := CFFS)
        (handoffMove := Direction.right)
        hmove
        (by simpa [baseAfterStage] using hconfigs)
  simpa [SCFFS, TmidTape,
    baseAfterStage] using
      seqSubroutine_runConfig_exists
        (A := NNSS)
        (B := CFFS)
        (handoffMove := Direction.right)
        DovetailStagePrefix.nonemptyNatSuffixScannerDescription_subroutineReady
        configurationsAndFinalFlagsScannerDescription_subroutineReady
        hArun hBReach

theorem run_inputStageConfigurationsAndFinalFlags_raw_to_handoff_withBase
    (input : Word Bool) (stage : Nat)
    (acceptConfig rejectConfig : Configuration)
    (acceptHit rejectHit : Bool)
    (baseLeft : List (Option Bool)) :
    exists steps : Nat,
      ISCFFS.runConfig
          steps
          { state :=
              ISCFFS.start
            tape :=
              tapeAtCells baseLeft
                ((boolWordFieldBits input
                  (List.append (stageNatBits stage)
                    (configurationFieldBits acceptConfig
                      (configurationFieldBits rejectConfig
                        (boolFieldBits acceptHit
                          (boolFieldBits rejectHit [])))))).map some) } =
        { state :=
            ISCFFS.halt
          tape :=
            (boolFinalHandoffConfigWithBase rejectHit
              (List.append
                ((cellCodeBits (some acceptHit)).reverse.map some)
                (configurationRestoredLeftWithBase rejectConfig
                  (configurationRestoredLeftWithBase acceptConfig
                    (List.append ((stageNatBits stage).reverse.map some)
                      (cellListCanonicalRestoredLeftWithBase
                        (input.map some) baseLeft)))))).tape } := by
  let stageSuffix : Word Bool :=
    configurationFieldBits acceptConfig
      (configurationFieldBits rejectConfig
        (boolFieldBits acceptHit (boolFieldBits rejectHit [])))
  rcases stageNatBits_cons_false stage with ⟨stageTail, hstageTail⟩
  let inputSuffixTail : Word Bool :=
    List.append stageTail stageSuffix
  rcases run_boolWordSuffix_raw_to_canonical_handoff_withBase
      input baseLeft inputSuffixTail with
    ⟨inputSteps, hinput⟩
  let TmidTape : Tape Bool :=
    (boolWordCanonicalHandoffConfigWithBase input baseLeft
      (false :: inputSuffixTail)).tape
  let baseAfterInput : List (Option Bool) :=
    cellListCanonicalRestoredLeftWithBase (input.map some) baseLeft
  have hArun :
      BWSS.runConfig inputSteps
          { state := BWSS.start
            tape :=
              tapeAtCells baseLeft
                ((boolWordFieldBits input
                  (List.append (stageNatBits stage)
                    (configurationFieldBits acceptConfig
                      (configurationFieldBits rejectConfig
                        (boolFieldBits acceptHit
                          (boolFieldBits rejectHit [])))))).map some) } =
        { state := BWSS.halt
          tape := TmidTape } := by
    change
      BWSS.runConfig inputSteps
          (config 100 baseLeft
            ((boolWordFieldBits input
              (List.append (stageNatBits stage)
                stageSuffix)).map some)) =
        { state := BWSS.halt
          tape := TmidTape }
    rw [show
        ((boolWordFieldBits input
          (List.append (stageNatBits stage) stageSuffix)).map some) =
          List.append ((stageNatBits input.length).map some)
            (List.append ((cellsCodeBits (input.map some)).map some)
              (some false :: inputSuffixTail.map some)) by
      rw [hstageTail]
      simp [boolWordFieldBits, cellListFieldBits, inputSuffixTail,
        stageSuffix, List.map_append]]
    simpa [TmidTape, boolWordCanonicalHandoffConfigWithBase] using
      hinput
  have hBReach :
      exists nB : Nat,
        SCFFS.runConfig nB
            { state :=
                SCFFS.start
              tape := Tape.move Direction.right TmidTape } =
          { state := SCFFS.halt
            tape :=
              (boolFinalHandoffConfigWithBase rejectHit
                (List.append
                  ((cellCodeBits (some acceptHit)).reverse.map some)
                  (configurationRestoredLeftWithBase rejectConfig
                    (configurationRestoredLeftWithBase acceptConfig
                      (List.append ((stageNatBits stage).reverse.map some)
                        baseAfterInput))))).tape } := by
    rcases run_stageConfigurationsAndFinalFlags_raw_to_handoff_withBase
        stage acceptConfig rejectConfig acceptHit rejectHit baseAfterInput with
      ⟨stageSteps, hstage⟩
    have hmove :
        Tape.move Direction.right TmidTape =
          tapeAtCells baseAfterInput
            ((List.append (stageNatBits stage) stageSuffix).map some) := by
      have hraw :
          Tape.move Direction.right TmidTape =
            tapeAtCells baseAfterInput
              ((false :: inputSuffixTail).map some) := by
        simpa [TmidTape, baseAfterInput,
          boolWordCanonicalHandoffConfigWithBase] using
          cellListCanonicalHandoffConfigWithBase_move_right
            (input.map some) baseLeft false inputSuffixTail
      rw [hraw]
      have hsuffixCells :
          (false :: inputSuffixTail).map some =
            (List.append (stageNatBits stage) stageSuffix).map some := by
        rw [hstageTail]
        simp [inputSuffixTail, List.map_append]
      simp [hsuffixCells]
    exact
      runConfig_reaches_from_move_eq
        (B := SCFFS)
        (handoffMove := Direction.right)
        hmove
        (by simpa [baseAfterInput, stageSuffix] using hstage)
  simpa [ISCFFS,
    TmidTape, baseAfterInput] using
      seqSubroutine_runConfig_exists
        (A := BWSS)
        (B := SCFFS)
        (handoffMove := Direction.right)
        boolWordSuffixScannerDescription_subroutineReady
        stageConfigurationsAndFinalFlagsScannerDescription_subroutineReady
        hArun hBReach

theorem run_markedDovetailLayoutBody_raw_to_handoff_withBase_phaseChain
    (L : DovetailLayout)
    (baseLeft : List (Option Bool)) :
    exists steps : Nat,
      MDBS.runConfig steps
          { state := MDBS.start
            tape :=
              tapeAtCells baseLeft
                ((List.append transitionRemainderBits
                  (boolWordFieldBits L.input
                    (List.append (stageNatBits L.stage)
                      (configurationFieldBits L.acceptConfig
                        (configurationFieldBits L.rejectConfig
                          (boolFieldBits L.acceptHit
                            (boolFieldBits L.rejectHit []))))))).map
                  some) } =
        { state := MDBS.halt
          tape :=
            (boolFinalHandoffConfigWithBase L.rejectHit
              (List.append
                ((cellCodeBits (some L.acceptHit)).reverse.map some)
                (configurationRestoredLeftWithBase L.rejectConfig
                  (configurationRestoredLeftWithBase L.acceptConfig
                    (List.append ((stageNatBits L.stage).reverse.map some)
                      (cellListCanonicalRestoredLeftWithBase
                        (L.input.map some)
                        (List.append
                          (transitionRemainderBits.reverse.map some)
                          baseLeft))))))).tape } := by
  let inputSuffix : Word Bool :=
    List.append (stageNatBits L.stage)
      (configurationFieldBits L.acceptConfig
        (configurationFieldBits L.rejectConfig
          (boolFieldBits L.acceptHit
            (boolFieldBits L.rejectHit []))))
  rcases cellListFieldBits_cons_false (L.input.map some)
      inputSuffix with
    ⟨inputTail, hinputTail⟩
  rcases run_transitionRemainderPrefix_raw_to_handoff_withBase
      baseLeft false inputTail with
    ⟨transitionSteps, htransition⟩
  let TmidTape : Tape Bool :=
    (transitionRemainderHandoffConfigWithBase baseLeft
      (false :: inputTail)).tape
  let baseAfterTransition : List (Option Bool) :=
    List.append (transitionRemainderBits.reverse.map some) baseLeft
  have hArun :
      TRP.runConfig
          transitionSteps
          { state := TRP.start
            tape :=
              tapeAtCells baseLeft
                ((List.append transitionRemainderBits
                  (boolWordFieldBits L.input inputSuffix)).map some) } =
        { state := TRP.halt
          tape := TmidTape } := by
    rw [show
        (List.append transitionRemainderBits
          (boolWordFieldBits L.input inputSuffix)).map some =
          (some false :: some false :: some true ::
            some false :: inputTail.map some) by
      have hinputBits :
          boolWordFieldBits L.input inputSuffix = false :: inputTail := by
        simpa [boolWordFieldBits] using hinputTail
      rw [hinputBits]
      simp [transitionRemainderBits]]
    simpa [TmidTape] using htransition
  have hBReach :
      exists nB : Nat,
        ISCFFS.runConfig nB
            { state :=
                ISCFFS.start
              tape := Tape.move Direction.right TmidTape } =
          { state :=
              ISCFFS.halt
            tape :=
              (boolFinalHandoffConfigWithBase L.rejectHit
                (List.append
                  ((cellCodeBits (some L.acceptHit)).reverse.map some)
                  (configurationRestoredLeftWithBase L.rejectConfig
                    (configurationRestoredLeftWithBase L.acceptConfig
                      (List.append ((stageNatBits L.stage).reverse.map some)
                        (cellListCanonicalRestoredLeftWithBase
                          (L.input.map some)
                          baseAfterTransition)))))).tape } := by
    rcases
        run_inputStageConfigurationsAndFinalFlags_raw_to_handoff_withBase
          L.input L.stage L.acceptConfig L.rejectConfig
          L.acceptHit L.rejectHit baseAfterTransition with
      ⟨inputSteps, hinput⟩
    have hmove :
        Tape.move Direction.right TmidTape =
          tapeAtCells baseAfterTransition
            ((boolWordFieldBits L.input inputSuffix).map some) := by
      have hraw :
          Tape.move Direction.right TmidTape =
            tapeAtCells baseAfterTransition
              ((false :: inputTail).map some) := by
        simpa [TmidTape, baseAfterTransition] using
          transitionRemainderHandoffConfigWithBase_move_right
            baseLeft false inputTail
      rw [hraw]
      have hinputCells :
          (false :: inputTail).map some =
            (boolWordFieldBits L.input inputSuffix).map some := by
        simpa using
          congrArg (fun bits => bits.map some) hinputTail.symm
      simp [hinputCells]
    exact
      runConfig_reaches_from_move_eq
        (B := ISCFFS)
        (handoffMove := Direction.right)
        hmove
        (by simpa [baseAfterTransition, inputSuffix] using hinput)
  simpa [MarkedDovetailLayoutBodyScannerDescription, TmidTape,
    baseAfterTransition] using
      rightHandoffSequential_runConfig_exists
        (A := TRP)
        (B := ISCFFS)
        transitionRemainderPrefixScannerDescription_subroutineReady
        inputStageConfigurationsAndFinalFlagsScannerDescription_subroutineReady
        hArun hBReach

theorem run_markedDovetailLayoutBody_raw_to_handoff_withBase
    (L : DovetailLayout)
    (baseLeft : List (Option Bool)) :
    exists steps : Nat,
      MDBS.runConfig steps
          { state := MDBS.start
            tape :=
              tapeAtCells baseLeft
                ((List.append transitionRemainderBits
                  (boolWordFieldBits L.input
                    (List.append (stageNatBits L.stage)
                      (configurationFieldBits L.acceptConfig
                        (configurationFieldBits L.rejectConfig
                          (boolFieldBits L.acceptHit
                            (boolFieldBits L.rejectHit []))))))).map
                  some) } =
        { state := MDBS.halt
          tape :=
            (boolFinalHandoffConfigWithBase L.rejectHit
              (List.append
                ((cellCodeBits (some L.acceptHit)).reverse.map some)
                (configurationRestoredLeftWithBase L.rejectConfig
                  (configurationRestoredLeftWithBase L.acceptConfig
                    (List.append ((stageNatBits L.stage).reverse.map some)
                      (cellListCanonicalRestoredLeftWithBase
                        (L.input.map some)
                        (List.append
                          (transitionRemainderBits.reverse.map some)
                          baseLeft))))))).tape } :=
  run_markedDovetailLayoutBody_raw_to_handoff_withBase_phaseChain
    L baseLeft

theorem run_markedDovetailLayoutBody_return_to_checkedHandoff
    (L : DovetailLayout) :
    exists steps : Nat,
      (seqSubroutine
          MDBS
          RFM
          Direction.right).runConfig steps
          { state :=
              (seqSubroutine
                MDBS
                RFM
                Direction.right).start
            tape :=
              tapeAtCells [none]
                ((markedDovetailLayoutBodyBits L).map some) } =
        { state :=
            (seqSubroutine
              MDBS
              RFM
              Direction.right).halt
          tape :=
            restoredCheckedHandoffTapeFromTail
              (markedDovetailLayoutBodyRestoredBitsRev L).reverse } := by
  rcases run_markedDovetailLayoutBody_raw_to_handoff_withBase
      L [none] with
    ⟨bodySteps, hbody⟩
  let TmidTape : Tape Bool :=
    (boolFinalHandoffConfigWithBase L.rejectHit
      (List.append
        ((cellCodeBits (some L.acceptHit)).reverse.map some)
        (configurationRestoredLeftWithBase L.rejectConfig
          (configurationRestoredLeftWithBase L.acceptConfig
            (List.append ((stageNatBits L.stage).reverse.map some)
              (cellListCanonicalRestoredLeftWithBase
                (L.input.map some)
                (List.append (transitionRemainderBits.reverse.map some)
                  [none]))))))).tape
  have hArun :
      MDBS.runConfig bodySteps
          { state := MDBS.start
            tape :=
              tapeAtCells [none]
                ((markedDovetailLayoutBodyBits L).map some) } =
        { state := MDBS.halt
          tape := TmidTape } := by
    simpa [markedDovetailLayoutBodyBits, TmidTape] using hbody
  have hBReach :
      exists nB : Nat,
        RFM.runConfig nB
            { state := RFM.start
              tape := Tape.move Direction.right TmidTape } =
          { state := RFM.halt
            tape :=
              restoredCheckedHandoffTapeFromTail
                (markedDovetailLayoutBodyRestoredBitsRev L).reverse } := by
    have hmove :
        Tape.move Direction.right TmidTape =
          tapeAtCells
            (List.append
              ((markedDovetailLayoutBodyRestoredBitsRev L).map some)
              [none])
            [none] := by
      have hraw :
          Tape.move Direction.right TmidTape =
            tapeAtCells
              (finalHitFlagsRestoredLeftWithBase L.acceptHit L.rejectHit
                (configurationRestoredLeftWithBase L.rejectConfig
                  (configurationRestoredLeftWithBase L.acceptConfig
                    (List.append
                      ((stageNatBits L.stage).reverse.map some)
                      (cellListCanonicalRestoredLeftWithBase
                        (L.input.map some)
                        (List.append
                          (transitionRemainderBits.reverse.map some)
                          [none]))))))
              [] := by
        simpa [TmidTape, finalHitFlagsRestoredLeftWithBase] using
          boolFinalHandoffConfigWithBase_move_right
            L.rejectHit
            (List.append
              ((cellCodeBits (some L.acceptHit)).reverse.map some)
              (configurationRestoredLeftWithBase L.rejectConfig
                (configurationRestoredLeftWithBase L.acceptConfig
                  (List.append
                    ((stageNatBits L.stage).reverse.map some)
                    (cellListCanonicalRestoredLeftWithBase
                      (L.input.map some)
                      (List.append
                        (transitionRemainderBits.reverse.map some)
                        [none]))))))
      rw [hraw]
      rw [← markedDovetailLayoutBodyRestoredBitsRev_map_some_withMarker L]
      rfl
    exact
      runConfig_reaches_from_move_eq
        (B := RFM)
        (handoffMove := Direction.right)
        hmove
        (by
          simpa [ReturnToFirstMarkerDescription, config] using
            run_returnToFirstMarker_from_reversedBits
              (markedDovetailLayoutBodyRestoredBitsRev L))
  simpa [TmidTape] using
    seqSubroutine_runConfig_exists
      (A := MDBS)
      (B := RFM)
      (handoffMove := Direction.right)
      markedDovetailLayoutBodyScannerDescription_subroutineReady
      returnToFirstMarkerDescription_subroutineReady
      hArun hBReach

theorem run_checkedDovetailLayoutScanner_raw_to_checkedHandoff_phaseChain
    (L : DovetailLayout) :
    exists steps : Nat,
      CDL.runConfig steps
          { state := CDL.start
            tape := tapeAtCells [] ((dovetailLayoutFieldBits L []).map some) } =
        { state := CDL.halt
          tape :=
            restoredCheckedHandoffTapeFromTail
              (markedDovetailLayoutBodyRestoredBitsRev L).reverse } := by
  rcases markedDovetailLayoutBodyBits_cons_false L with
    ⟨bodyTail, hbodyTail⟩
  let TmidTape : Tape Bool :=
    (config MFTB.halt []
      (none :: some false :: bodyTail.map some)).tape
  have hArun :
      MFTB.runConfig 2
          { state := MFTB.start
            tape :=
              tapeAtCells []
                ((dovetailLayoutFieldBits L []).map some) } =
        { state := MFTB.halt
          tape := TmidTape } := by
    rw [dovetailLayoutFieldBits_nil_eq_first_body L]
    rw [hbodyTail]
    simpa [TmidTape] using
      run_markFirstTransitionBit_raw bodyTail
  have hBReach :
      exists nB : Nat,
        (seqSubroutine
          MDBS
          RFM
          Direction.right).runConfig nB
            { state :=
                (seqSubroutine
                  MDBS
                  RFM
                  Direction.right).start
              tape := Tape.move Direction.right TmidTape } =
          { state :=
              (seqSubroutine
                MDBS
                RFM
                Direction.right).halt
            tape :=
              restoredCheckedHandoffTapeFromTail
                (markedDovetailLayoutBodyRestoredBitsRev L).reverse } := by
    rcases run_markedDovetailLayoutBody_return_to_checkedHandoff L with
      ⟨bodyReturnSteps, hbodyReturn⟩
    have hmove :
        Tape.move Direction.right TmidTape =
          tapeAtCells [none]
            ((markedDovetailLayoutBodyBits L).map some) := by
      simp [TmidTape, hbodyTail, config, tapeAtCells, Tape.move,
        Tape.moveRight]
    exact
      runConfig_reaches_from_move_eq
        (B :=
          seqSubroutine
            MDBS
            RFM
            Direction.right)
        (handoffMove := Direction.right)
        hmove
        hbodyReturn
  simpa [CheckedDovetailLayoutScannerDescription, TmidTape] using
    rightHandoffSequential_runConfig_exists
      (A := MFTB)
      (B :=
        seqSubroutine
          MDBS
          RFM
          Direction.right)
      markFirstTransitionBitDescription_subroutineReady
      (seqSubroutine_subroutineReady
        markedDovetailLayoutBodyScannerDescription_subroutineReady
        returnToFirstMarkerDescription_subroutineReady)
      hArun hBReach

theorem run_checkedDovetailLayoutScanner_raw_to_checkedHandoff
    (L : DovetailLayout) :
    exists steps : Nat,
      CDL.runConfig steps
          { state := CDL.start
            tape := tapeAtCells [] ((dovetailLayoutFieldBits L []).map some) } =
        { state := CDL.halt
          tape :=
            restoredCheckedHandoffTapeFromTail
              (markedDovetailLayoutBodyRestoredBitsRev L).reverse } :=
  run_checkedDovetailLayoutScanner_raw_to_checkedHandoff_phaseChain L


end DovetailLayoutScanner
end CanonicalLayouts
end EncodedRewriters

end Computability
end FoC

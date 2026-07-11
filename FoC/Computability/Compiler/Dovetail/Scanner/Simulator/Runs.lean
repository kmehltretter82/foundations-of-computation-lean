import FoC.Computability.Compiler.Dovetail.Scanner.Simulator.Definitions
import FoC.Computability.Compiler.Dovetail.Scanner.Composition.Runs

set_option doc.verso true

/-!
# Simulator-layout scanner runs

Forward run lemmas for the composed checked simulator-layout scanner.  The
scanner is entered from a window-padded start (one visited blank on each
side), because the token-alignment pre-scanner runs first; all phases are
therefore threaded in their {lit}`withBaseAndRight` forms.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace CanonicalLayouts
namespace SimulatorLayoutScanner

open FoC.Computability.DovetailInitialLayoutInitializer
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner
open CommonGround.SeqComposition
open DovetailLayoutScanner

private abbrev CFS := ConfigurationSuffixScannerDescription
private abbrev BFS := BoolFinalScannerDescription
private abbrev NNSS := DovetailStagePrefix.NonemptyNatSuffixScannerDescription
private abbrev BWSS := BoolWordSuffixScannerDescription
private abbrev HRP := HeaderRemainderPrefixScannerDescription
private abbrev CFF := ConfigurationAndFinalFlagScannerDescription
private abbrev SCFF := StageConfigurationAndFinalFlagScannerDescription
private abbrev ISCFF := InputStageConfigurationAndFinalFlagScannerDescription
private abbrev MSBS := MarkedSimulatorLayoutBodyScannerDescription
private abbrev CSL := CheckedSimulatorLayoutScannerDescription
private abbrev RFM := ReturnToFirstMarkerDescription
private abbrev MFTB := MarkFirstTransitionBitDescription

private theorem rightHandoffSequential_runConfig_exists
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

theorem boolFinalHandoffConfigWithBaseAndRight_move_right
    (flag : Bool) (baseLeft rightPadding : List (Option Bool)) :
    Tape.move Direction.right
        (boolFinalHandoffConfigWithBaseAndRight flag baseLeft
          rightPadding).tape =
      tapeAtCells
        (List.append ((cellCodeBits (some flag)).reverse.map some)
          baseLeft)
        rightPadding := by
  cases flag <;> cases rightPadding <;>
    simp [boolFinalHandoffConfigWithBaseAndRight, cellCodeBits,
      tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight,
      encodeCell,
      encodeCodeWordAsInput,
      encodeCodeSymbolAsInput]

/-!
## Body-field phase chain
-/

theorem run_configurationAndFinalFlag_raw_to_handoff_withBaseAndRight
    (cfg : Configuration) (hit : Bool)
    (baseLeft rightPadding : List (Option Bool)) :
    exists steps : Nat,
      CFF.runConfig steps
          { state := CFF.start
            tape :=
              tapeAtCells baseLeft
                (List.append
                  ((configurationFieldBits cfg
                    (boolFieldBits hit [])).map some)
                  (none :: rightPadding)) } =
        { state := CFF.halt
          tape :=
            (boolFinalHandoffConfigWithBaseAndRight hit
              (configurationRestoredLeftWithBase cfg baseLeft)
              (none :: rightPadding)).tape } := by
  rcases cellCodeBits_cons_false (some hit) with ⟨hitTail, hhitTail⟩
  have hhitBits :
      boolFieldBits hit [] = false :: hitTail := by
    simpa [boolFieldBits, cellFieldBits] using hhitTail
  rcases run_configurationSuffix_raw_to_handoff_withBaseAndRight
      cfg baseLeft hitTail (none :: rightPadding) with
    ⟨configSteps, hconfig⟩
  let Tmid : Tape Bool :=
    (cellListCanonicalHandoffConfigWithBaseAndRight
      cfg.tape.right
      (List.append ((cellCodeBits cfg.tape.head).reverse.map some)
        (cellListCanonicalRestoredLeftWithBase cfg.tape.left
          (List.append ((stageNatBits cfg.state).reverse.map some)
            baseLeft)))
      (false :: hitTail) (none :: rightPadding)).tape
  have hArun :
      CFS.runConfig configSteps
          { state := CFS.start
            tape :=
              tapeAtCells baseLeft
                (List.append
                  ((configurationFieldBits cfg
                    (boolFieldBits hit [])).map some)
                  (none :: rightPadding)) } =
        { state := CFS.halt
          tape := Tmid } := by
    rw [hhitBits]
    simpa [Tmid, config] using hconfig
  have hBReach :
      exists nB : Nat,
        BFS.runConfig nB
            { state := BFS.start
              tape := Tape.move Direction.right Tmid } =
          { state := BFS.halt
            tape :=
              (boolFinalHandoffConfigWithBaseAndRight hit
                (configurationRestoredLeftWithBase cfg baseLeft)
                (none :: rightPadding)).tape } := by
    rcases run_boolFinal_raw_to_handoff_withBaseAndRight
        hit (configurationRestoredLeftWithBase cfg baseLeft)
        rightPadding with
      ⟨finalSteps, hfinal⟩
    have hmove :
        Tape.move Direction.right Tmid =
          tapeAtCells
            (configurationRestoredLeftWithBase cfg baseLeft)
            (List.append ((cellCodeBits (some hit)).map some)
              (none :: rightPadding)) := by
      have hraw :
          Tape.move Direction.right Tmid =
            tapeAtCells
              (cellListCanonicalRestoredLeftWithBase cfg.tape.right
                (List.append
                  ((cellCodeBits cfg.tape.head).reverse.map some)
                  (cellListCanonicalRestoredLeftWithBase cfg.tape.left
                    (List.append
                      ((stageNatBits cfg.state).reverse.map some)
                      baseLeft))))
              (List.append ((false :: hitTail).map some)
                (none :: rightPadding)) := by
        simpa [Tmid] using
          cellListCanonicalHandoffConfigWithBaseAndRight_move_right
            cfg.tape.right
            (List.append
              ((cellCodeBits cfg.tape.head).reverse.map some)
              (cellListCanonicalRestoredLeftWithBase cfg.tape.left
                (List.append
                  ((stageNatBits cfg.state).reverse.map some)
                  baseLeft)))
            false hitTail (none :: rightPadding)
      rw [hraw]
      have hcells :
          ((false :: hitTail).map some :
              List (Option Bool)) =
            (cellCodeBits (some hit)).map some := by
        rw [hhitTail]
      rw [hcells]
      rfl
    exact
      runConfig_reaches_from_move_eq
        (B := BFS)
        (handoffMove := Direction.right)
        hmove
        (by exact hfinal)
  simpa [ConfigurationAndFinalFlagScannerDescription, Tmid] using
    rightHandoffSequential_runConfig_exists
      (A := CFS)
      (B := BFS)
      configurationSuffixScannerDescription_subroutineReady
      boolFinalScannerDescription_subroutineReady
      hArun hBReach

theorem run_stageConfigurationAndFinalFlag_raw_to_handoff_withBaseAndRight
    (stage : Nat) (cfg : Configuration) (hit : Bool)
    (baseLeft rightPadding : List (Option Bool)) :
    exists steps : Nat,
      SCFF.runConfig steps
          { state := SCFF.start
            tape :=
              tapeAtCells baseLeft
                (List.append
                  ((List.append (stageNatBits stage)
                    (configurationFieldBits cfg
                      (boolFieldBits hit []))).map some)
                  (none :: rightPadding)) } =
        { state := SCFF.halt
          tape :=
            (boolFinalHandoffConfigWithBaseAndRight hit
              (configurationRestoredLeftWithBase cfg
                (List.append ((stageNatBits stage).reverse.map some)
                  baseLeft))
              (none :: rightPadding)).tape } := by
  rcases configurationFieldBits_cons_false cfg
      (boolFieldBits hit []) with
    ⟨configTail, hconfigTail⟩
  rcases DovetailStagePrefix.run_nonemptyNatSuffix_raw_to_handoff_withBaseAndRight
      stage baseLeft false configTail (none :: rightPadding) with
    ⟨stageSteps, hstage⟩
  let Tmid : Tape Bool :=
    (DovetailStagePrefix.nonemptyNatSuffixHandoffConfigWithBaseAndRight
      stage baseLeft (false :: configTail) (none :: rightPadding)).tape
  let baseAfterStage : List (Option Bool) :=
    List.append ((stageNatBits stage).reverse.map some) baseLeft
  have hArun :
      NNSS.runConfig stageSteps
          { state := NNSS.start
            tape :=
              tapeAtCells baseLeft
                (List.append
                  ((List.append (stageNatBits stage)
                    (configurationFieldBits cfg
                      (boolFieldBits hit []))).map some)
                  (none :: rightPadding)) } =
        { state := NNSS.halt
          tape := Tmid } := by
    rw [show
        (List.append
          ((List.append (stageNatBits stage)
            (configurationFieldBits cfg
              (boolFieldBits hit []))).map some)
          (none :: rightPadding) :
            List (Option Bool)) =
          List.append ((stageNatBits stage).map some)
            (some false ::
              List.append (configTail.map some)
                (none :: rightPadding)) by
      rw [hconfigTail]
      simp [List.map_append, List.append_assoc]]
    exact hstage
  have hBReach :
      exists nB : Nat,
        CFF.runConfig nB
            { state := CFF.start
              tape := Tape.move Direction.right Tmid } =
          { state := CFF.halt
            tape :=
              (boolFinalHandoffConfigWithBaseAndRight hit
                (configurationRestoredLeftWithBase cfg baseAfterStage)
                (none :: rightPadding)).tape } := by
    rcases run_configurationAndFinalFlag_raw_to_handoff_withBaseAndRight
        cfg hit baseAfterStage rightPadding with
      ⟨configSteps, hconfig⟩
    have hmove :
        Tape.move Direction.right Tmid =
          tapeAtCells baseAfterStage
            (List.append
              ((configurationFieldBits cfg
                (boolFieldBits hit [])).map some)
              (none :: rightPadding)) := by
      have hraw :
          Tape.move Direction.right Tmid =
            tapeAtCells baseAfterStage
              (List.append ((false :: configTail).map some)
                (none :: rightPadding)) := by
        simpa [Tmid, baseAfterStage] using
          DovetailStagePrefix.nonemptyNatSuffixHandoffConfigWithBaseAndRight_move_right
            stage baseLeft false configTail (none :: rightPadding)
      rw [hraw]
      have hcells :
          ((false :: configTail).map some :
              List (Option Bool)) =
            (configurationFieldBits cfg
              (boolFieldBits hit [])).map some := by
        rw [hconfigTail]
      rw [hcells]
    exact
      runConfig_reaches_from_move_eq
        (B := CFF)
        (handoffMove := Direction.right)
        hmove
        (by simpa [baseAfterStage] using hconfig)
  simpa [StageConfigurationAndFinalFlagScannerDescription, Tmid,
    baseAfterStage] using
    rightHandoffSequential_runConfig_exists
      (A := NNSS)
      (B := CFF)
      DovetailStagePrefix.nonemptyNatSuffixScannerDescription_subroutineReady
      configurationAndFinalFlagScannerDescription_subroutineReady
      hArun hBReach

theorem run_inputStageConfigurationAndFinalFlag_raw_to_handoff_withBaseAndRight
    (input : Word Bool) (stage : Nat) (cfg : Configuration) (hit : Bool)
    (baseLeft rightPadding : List (Option Bool)) :
    exists steps : Nat,
      ISCFF.runConfig steps
          { state := ISCFF.start
            tape :=
              tapeAtCells baseLeft
                (List.append
                  ((boolWordFieldBits input
                    (List.append (stageNatBits stage)
                      (configurationFieldBits cfg
                        (boolFieldBits hit [])))).map some)
                  (none :: rightPadding)) } =
        { state := ISCFF.halt
          tape :=
            (boolFinalHandoffConfigWithBaseAndRight hit
              (configurationRestoredLeftWithBase cfg
                (List.append ((stageNatBits stage).reverse.map some)
                  (cellListCanonicalRestoredLeftWithBase
                    (input.map some) baseLeft)))
              (none :: rightPadding)).tape } := by
  let stageSuffix : Word Bool :=
    List.append (stageNatBits stage)
      (configurationFieldBits cfg (boolFieldBits hit []))
  rcases stageNatBits_cons_false stage with ⟨stageTail, hstageTail⟩
  let inputSuffixTail : Word Bool :=
    List.append stageTail
      (configurationFieldBits cfg (boolFieldBits hit []))
  rcases run_boolWordSuffix_raw_to_canonical_handoff_withBaseAndRight
      input baseLeft inputSuffixTail (none :: rightPadding) with
    ⟨inputSteps, hinput⟩
  let Tmid : Tape Bool :=
    (boolWordCanonicalHandoffConfigWithBaseAndRight input baseLeft
      (false :: inputSuffixTail) (none :: rightPadding)).tape
  let baseAfterInput : List (Option Bool) :=
    cellListCanonicalRestoredLeftWithBase (input.map some) baseLeft
  have hArun :
      BWSS.runConfig inputSteps
          { state := BWSS.start
            tape :=
              tapeAtCells baseLeft
                (List.append
                  ((boolWordFieldBits input stageSuffix).map some)
                  (none :: rightPadding)) } =
        { state := BWSS.halt
          tape := Tmid } := by
    rw [show
        (List.append
          ((boolWordFieldBits input stageSuffix).map some)
          (none :: rightPadding) :
            List (Option Bool)) =
          List.append ((stageNatBits input.length).map some)
            (List.append ((cellsCodeBits (input.map some)).map some)
              (some false ::
                List.append (inputSuffixTail.map some)
                  (none :: rightPadding))) by
      rw [show
          (boolWordFieldBits input stageSuffix :
              Word Bool) =
            List.append (stageNatBits input.length)
              (List.append (cellsCodeBits (input.map some))
                (false :: inputSuffixTail)) by
        rw [show
            (false :: inputSuffixTail : Word Bool) =
              stageSuffix by
          simp [inputSuffixTail, stageSuffix, hstageTail]]
        simp [boolWordFieldBits, cellListFieldBits]]
      simp [List.map_append, List.append_assoc]]
    exact hinput
  have hBReach :
      exists nB : Nat,
        SCFF.runConfig nB
            { state := SCFF.start
              tape := Tape.move Direction.right Tmid } =
          { state := SCFF.halt
            tape :=
              (boolFinalHandoffConfigWithBaseAndRight hit
                (configurationRestoredLeftWithBase cfg
                  (List.append ((stageNatBits stage).reverse.map some)
                    baseAfterInput))
                (none :: rightPadding)).tape } := by
    rcases run_stageConfigurationAndFinalFlag_raw_to_handoff_withBaseAndRight
        stage cfg hit baseAfterInput rightPadding with
      ⟨stageSteps, hstage⟩
    have hmove :
        Tape.move Direction.right Tmid =
          tapeAtCells baseAfterInput
            (List.append (stageSuffix.map some)
              (none :: rightPadding)) := by
      have hraw :
          Tape.move Direction.right Tmid =
            tapeAtCells baseAfterInput
              (List.append ((false :: inputSuffixTail).map some)
                (none :: rightPadding)) := by
        simpa [Tmid, baseAfterInput,
          boolWordCanonicalHandoffConfigWithBaseAndRight] using
          cellListCanonicalHandoffConfigWithBaseAndRight_move_right
            (input.map some) baseLeft false inputSuffixTail
            (none :: rightPadding)
      rw [hraw]
      have hcells :
          ((false :: inputSuffixTail).map some :
              List (Option Bool)) =
            stageSuffix.map some := by
        rw [show (false :: inputSuffixTail : Word Bool) = stageSuffix by
          simp [inputSuffixTail, stageSuffix, hstageTail]]
      rw [hcells]
    exact
      runConfig_reaches_from_move_eq
        (B := SCFF)
        (handoffMove := Direction.right)
        hmove
        (by simpa [baseAfterInput, stageSuffix] using hstage)
  simpa [InputStageConfigurationAndFinalFlagScannerDescription, Tmid,
    baseAfterInput, stageSuffix] using
    rightHandoffSequential_runConfig_exists
      (A := BWSS)
      (B := SCFF)
      boolWordSuffixScannerDescription_subroutineReady
      stageConfigurationAndFinalFlagScannerDescription_subroutineReady
      hArun hBReach

theorem run_markedSimulatorLayoutBody_raw_to_handoff_withBaseAndRight
    (L : SimulatorLayout)
    (baseLeft rightPadding : List (Option Bool)) :
    exists steps : Nat,
      MSBS.runConfig steps
          { state := MSBS.start
            tape :=
              tapeAtCells baseLeft
                (List.append
                  ((markedSimulatorLayoutBodyBits L).map some)
                  (none :: rightPadding)) } =
        { state := MSBS.halt
          tape :=
            (boolFinalHandoffConfigWithBaseAndRight L.hit
              (configurationRestoredLeftWithBase L.config
                (List.append ((stageNatBits L.stage).reverse.map some)
                  (cellListCanonicalRestoredLeftWithBase
                    (L.input.map some)
                    (List.append
                      (headerRemainderBits.reverse.map some)
                      baseLeft))))
              (none :: rightPadding)).tape } := by
  let inputSuffix : Word Bool :=
    List.append (stageNatBits L.stage)
      (configurationFieldBits L.config (boolFieldBits L.hit []))
  rcases cellListFieldBits_cons_false (L.input.map some)
      inputSuffix with
    ⟨inputTail, hinputTail⟩
  rcases run_headerRemainderPrefix_raw_to_handoff_withBaseAndRight
      baseLeft false inputTail (none :: rightPadding) with
    ⟨headerSteps, hheader⟩
  let Tmid : Tape Bool :=
    (headerRemainderHandoffConfigWithBaseAndRight baseLeft
      (false :: inputTail) (none :: rightPadding)).tape
  let baseAfterHeader : List (Option Bool) :=
    List.append (headerRemainderBits.reverse.map some) baseLeft
  have hArun :
      HRP.runConfig headerSteps
          { state := HRP.start
            tape :=
              tapeAtCells baseLeft
                (List.append
                  ((markedSimulatorLayoutBodyBits L).map some)
                  (none :: rightPadding)) } =
        { state := HRP.halt
          tape := Tmid } := by
    rw [show
        (List.append
          ((markedSimulatorLayoutBodyBits L).map some)
          (none :: rightPadding) :
            List (Option Bool)) =
          some false :: some false :: some false ::
            some false ::
              List.append (inputTail.map some)
                (none :: rightPadding) by
      have hinputBits :
          boolWordFieldBits L.input inputSuffix =
            false :: inputTail := by
        simpa [boolWordFieldBits] using hinputTail
      rw [show
          (markedSimulatorLayoutBodyBits L : Word Bool) =
            List.append headerRemainderBits
              (boolWordFieldBits L.input inputSuffix) by
        simp [markedSimulatorLayoutBodyBits, inputSuffix]]
      rw [hinputBits]
      simp [headerRemainderBits]]
    simpa [Tmid, config] using! hheader
  have hBReach :
      exists nB : Nat,
        ISCFF.runConfig nB
            { state := ISCFF.start
              tape := Tape.move Direction.right Tmid } =
          { state := ISCFF.halt
            tape :=
              (boolFinalHandoffConfigWithBaseAndRight L.hit
                (configurationRestoredLeftWithBase L.config
                  (List.append
                    ((stageNatBits L.stage).reverse.map some)
                    (cellListCanonicalRestoredLeftWithBase
                      (L.input.map some) baseAfterHeader)))
                (none :: rightPadding)).tape } := by
    rcases run_inputStageConfigurationAndFinalFlag_raw_to_handoff_withBaseAndRight
        L.input L.stage L.config L.hit baseAfterHeader rightPadding with
      ⟨inputSteps, hinput⟩
    have hmove :
        Tape.move Direction.right Tmid =
          tapeAtCells baseAfterHeader
            (List.append
              ((boolWordFieldBits L.input inputSuffix).map some)
              (none :: rightPadding)) := by
      have hraw :
          Tape.move Direction.right Tmid =
            tapeAtCells baseAfterHeader
              (List.append ((false :: inputTail).map some)
                (none :: rightPadding)) := by
        simpa [Tmid, baseAfterHeader] using
          headerRemainderHandoffConfigWithBaseAndRight_move_right
            baseLeft false inputTail (none :: rightPadding)
      rw [hraw]
      have hinputCells :
          ((false :: inputTail).map some :
              List (Option Bool)) =
            (boolWordFieldBits L.input inputSuffix).map some := by
        have hinputBits :
            boolWordFieldBits L.input inputSuffix =
              false :: inputTail := by
          simpa [boolWordFieldBits] using hinputTail
        rw [hinputBits]
      rw [hinputCells]
    exact
      runConfig_reaches_from_move_eq
        (B := ISCFF)
        (handoffMove := Direction.right)
        hmove
        (by simpa [baseAfterHeader, inputSuffix] using hinput)
  simpa [MarkedSimulatorLayoutBodyScannerDescription, Tmid,
    baseAfterHeader] using!
    rightHandoffSequential_runConfig_exists
      (A := HRP)
      (B := ISCFF)
      headerRemainderPrefixScannerDescription_subroutineReady
      inputStageConfigurationAndFinalFlagScannerDescription_subroutineReady
      hArun hBReach

/-!
## Checked complete-layout scanner from the padded start
-/

private theorem run_markFirstBit_withBase
    (baseLeft tailCells : List (Option Bool)) :
    MFTB.runConfig 2
        (config 0 baseLeft
          (some false :: some false :: tailCells)) =
      config MFTB.halt baseLeft
        (none :: some false :: tailCells) := by
  cases tailCells <;>
    simp [MarkFirstTransitionBitDescription, config, tapeAtCells,
      keepMove, writeMove, runConfig,
      stepConfig, lookupTransition,
      Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft,
      Tape.moveRight]

private def rfmScanConfig
    (remainingRev scanned : Word Bool)
    (base restTail : List (Option Bool)) : Configuration :=
  match remainingRev with
  | [] =>
      config 1 base
        (none :: List.append (scanned.map some) (none :: restTail))
  | bit :: rest =>
      config 1 (List.append (rest.map some) (none :: base))
        (some bit :: List.append (scanned.map some) (none :: restTail))

private theorem run_rfm_scan_withBase
    (remainingRev scanned : Word Bool)
    (base restTail : List (Option Bool)) :
    RFM.runConfig (remainingRev.length + 1)
        (rfmScanConfig remainingRev scanned base restTail) =
      { state := RFM.halt
        tape :=
          Tape.move Direction.right
            { left := base
              head := some false
              right :=
                List.append
                  ((List.append remainingRev.reverse scanned).map some)
                  (none :: restTail) } } := by
  induction remainingRev generalizing scanned with
  | nil =>
      simp [rfmScanConfig,
        ReturnToFirstMarkerDescription, config, tapeAtCells,
        keepMove, writeMove, runConfig,
        stepConfig, lookupTransition,
        Matches, transition,
        Tape.read, Tape.write, Tape.move, Tape.moveRight]
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 1 = 1 + (rest.length + 1) by
        simp [List.length_cons]
        lia]
      rw [runConfig_add]
      have hstep :
          RFM.runConfig 1
              (rfmScanConfig (bit :: rest) scanned base restTail) =
            rfmScanConfig rest (bit :: scanned) base restTail := by
        cases bit <;> cases rest <;>
          simp [rfmScanConfig,
            ReturnToFirstMarkerDescription, config, tapeAtCells,
            keepMove, writeMove, runConfig,
            stepConfig, lookupTransition,
            Matches, transition,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      rw [hstep]
      rw [ih (bit :: scanned)]
      simp [List.reverse_cons, List.append_assoc]

private theorem run_rfm_from_reversedBits_withBase
    (prefixRev : Word Bool) (base restTail : List (Option Bool)) :
    RFM.runConfig (prefixRev.length + 2)
        (config 0
          (List.append (prefixRev.map some) (none :: base))
          (none :: restTail)) =
      { state := RFM.halt
        tape :=
          Tape.move Direction.right
            { left := base
              head := some false
              right :=
                List.append (prefixRev.reverse.map some)
                  (none :: restTail) } } := by
  rw [show prefixRev.length + 2 = 1 + (prefixRev.length + 1) by lia]
  rw [runConfig_add]
  have hstep :
      RFM.runConfig 1
          (config 0
            (List.append (prefixRev.map some) (none :: base))
            (none :: restTail)) =
        rfmScanConfig prefixRev [] base restTail := by
    cases prefixRev <;> cases restTail <;>
      simp [rfmScanConfig,
        ReturnToFirstMarkerDescription, config, tapeAtCells,
        keepMove, writeMove, runConfig,
        stepConfig, lookupTransition,
        Matches, transition,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft]
  rw [hstep]
  rw [run_rfm_scan_withBase prefixRev [] base restTail]
  simp

/-- Padded start tape of the checked simulator-layout scanner: the canonical
input word with one visited blank on each side of the window. -/
def checkedSimulatorPaddedStartTape (L : SimulatorLayout) : Tape Bool :=
  tapeAtCells [none]
    (List.append ((simulatorLayoutFieldBits L []).map some) [none])

/-- Exact handoff tape of the checked scanner from the padded start: the
same window, with the head returned to bit 1. -/
def checkedSimulatorHandoffTape (L : SimulatorLayout) : Tape Bool :=
  Tape.move Direction.right (checkedSimulatorPaddedStartTape L)

theorem run_checkedSimulatorLayoutScanner_padded_to_checkedHandoff
    (L : SimulatorLayout) :
    exists steps : Nat,
      CSL.runConfig steps
          { state := CSL.start
            tape := checkedSimulatorPaddedStartTape L } =
        { state := CSL.halt
          tape := checkedSimulatorHandoffTape L } := by
  rcases markedSimulatorLayoutBodyBits_cons_false L with
    ⟨bodyTail, hbodyTail⟩
  let TmarkTape : Tape Bool :=
    (config MFTB.halt [none]
      (none :: some false ::
        List.append (bodyTail.map some) [none])).tape
  have hArun :
      MFTB.runConfig 2
          { state := MFTB.start
            tape := checkedSimulatorPaddedStartTape L } =
        { state := MFTB.halt
          tape := TmarkTape } := by
    have hcells :
        (List.append ((simulatorLayoutFieldBits L []).map some)
          [none] : List (Option Bool)) =
          some false :: some false ::
            List.append (bodyTail.map some) [none] := by
      rw [simulatorLayoutFieldBits_nil_eq_first_body L, hbodyTail]
      simp
    have hstart :
        checkedSimulatorPaddedStartTape L =
          (config 0 [none]
            (some false :: some false ::
              List.append (bodyTail.map some) [none])).tape :=
      congrArg (tapeAtCells [none]) hcells
    rw [hstart]
    simpa [TmarkTape] using!
      run_markFirstBit_withBase [none]
        (List.append (bodyTail.map some) [none])
  have hBReach :
      exists nB : Nat,
        (seqSubroutine MSBS RFM Direction.right).runConfig nB
            { state := (seqSubroutine MSBS RFM Direction.right).start
              tape := Tape.move Direction.right TmarkTape } =
          { state := (seqSubroutine MSBS RFM Direction.right).halt
            tape := checkedSimulatorHandoffTape L } := by
    rcases run_markedSimulatorLayoutBody_raw_to_handoff_withBaseAndRight
        L [none, none] [] with
      ⟨bodySteps, hbody⟩
    let TbodyTape : Tape Bool :=
      (boolFinalHandoffConfigWithBaseAndRight L.hit
        (configurationRestoredLeftWithBase L.config
          (List.append ((stageNatBits L.stage).reverse.map some)
            (cellListCanonicalRestoredLeftWithBase
              (L.input.map some)
              (List.append (headerRemainderBits.reverse.map some)
                [none, none]))))
        [none]).tape
    have hmove :
        Tape.move Direction.right TmarkTape =
          tapeAtCells [none, none]
            (List.append
              ((markedSimulatorLayoutBodyBits L).map some)
              (none :: [])) := by
      rw [hbodyTail]
      simp [TmarkTape, config, tapeAtCells, Tape.move, Tape.moveRight]
    have hbodyRun :
        MSBS.runConfig bodySteps
            { state := MSBS.start
              tape := Tape.move Direction.right TmarkTape } =
          { state := MSBS.halt
            tape := TbodyTape } := by
      rw [hmove]
      simpa [TbodyTape] using hbody
    have hRFMReach :
        exists nR : Nat,
          RFM.runConfig nR
              { state := RFM.start
                tape := Tape.move Direction.right TbodyTape } =
            { state := RFM.halt
              tape := checkedSimulatorHandoffTape L } := by
      refine ⟨(markedSimulatorLayoutBodyRestoredBitsRev L).length + 2, ?_⟩
      have hmoveBody :
          Tape.move Direction.right TbodyTape =
            tapeAtCells
              (List.append
                ((markedSimulatorLayoutBodyRestoredBitsRev L).map some)
                (none :: [none]))
              [none] := by
        have hraw :
            Tape.move Direction.right TbodyTape =
              tapeAtCells
                (List.append
                  ((cellCodeBits (some L.hit)).reverse.map some)
                  (configurationRestoredLeftWithBase L.config
                    (List.append
                      ((stageNatBits L.stage).reverse.map some)
                      (cellListCanonicalRestoredLeftWithBase
                        (L.input.map some)
                        (List.append
                          (headerRemainderBits.reverse.map some)
                          [none, none])))))
                [none] := by
          simpa [TbodyTape] using
            boolFinalHandoffConfigWithBaseAndRight_move_right L.hit
              (configurationRestoredLeftWithBase L.config
                (List.append ((stageNatBits L.stage).reverse.map some)
                  (cellListCanonicalRestoredLeftWithBase
                    (L.input.map some)
                    (List.append
                      (headerRemainderBits.reverse.map some)
                      [none, none]))))
              [none]
        rw [hraw]
        rw [← markedSimulatorLayoutBodyRestoredBitsRev_map_some_withBase
          L [none, none]]
      have hrfm :=
        run_rfm_from_reversedBits_withBase
          (markedSimulatorLayoutBodyRestoredBitsRev L) [none] []
      rw [hmoveBody]
      have hstartCfg :
          (config 0
            (List.append
              ((markedSimulatorLayoutBodyRestoredBitsRev L).map some)
              (none :: [none]))
            [none] : Configuration) =
            { state := RFM.start
              tape :=
                tapeAtCells
                  (List.append
                    ((markedSimulatorLayoutBodyRestoredBitsRev L).map
                      some)
                    (none :: [none]))
                  [none] } := rfl
      rw [← hstartCfg]
      rw [hrfm]
      have hhandoff :
          (Tape.move Direction.right
            { left := [none]
              head := some false
              right :=
                List.append
                  (((markedSimulatorLayoutBodyRestoredBitsRev
                    L).reverse).map some)
                  [none] } : Tape Bool) =
            checkedSimulatorHandoffTape L := by
        rw [markedSimulatorLayoutBodyRestoredBitsRev_reverse L]
        show _ =
          Tape.move Direction.right
            (tapeAtCells [none]
              (List.append ((simulatorLayoutFieldBits L []).map some)
                [none]))
        rw [show
            (List.append ((simulatorLayoutFieldBits L []).map some)
              [none] : List (Option Bool)) =
              some false ::
                List.append
                  ((markedSimulatorLayoutBodyBits L).map some)
                  [none] by
          rw [simulatorLayoutFieldBits_nil_eq_first_body L]
          rfl]
        rfl
      rw [hhandoff]
    exact
      rightHandoffSequential_runConfig_exists
        (A := MSBS)
        (B := RFM)
        markedSimulatorLayoutBodyScannerDescription_subroutineReady
        returnToFirstMarkerDescription_subroutineReady
        hbodyRun hRFMReach
  simpa [CheckedSimulatorLayoutScannerDescription, TmarkTape] using
    rightHandoffSequential_runConfig_exists
      (A := MFTB)
      (B := seqSubroutine MSBS RFM Direction.right)
      markFirstTransitionBitDescription_subroutineReady
      (seqSubroutine_subroutineReady
        markedSimulatorLayoutBodyScannerDescription_subroutineReady
        returnToFirstMarkerDescription_subroutineReady)
      hArun hBReach

end SimulatorLayoutScanner
end CanonicalLayouts
end EncRewriters

end Computability
end FoC

import FoC.Computability.Compiler.Dovetail.Scanner.Simulator.Runs
import FoC.Computability.Compiler.Dovetail.Scanner.Closed

set_option doc.verso true

/-!
# Closed simulator-layout scanner runs

Sequential inversions for the composed checked simulator-layout scanner: a
halting run from an ordinary word start splits into the marker phase, the
per-field scanner runs, and the return phase.  These are the simulator-family
mirrors of the dovetail-layout closed splits.
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

def MarkedSimulatorLayoutBodyReturnDescription : MachineDescription :=
  seqSubroutine
    MarkedSimulatorLayoutBodyScannerDescription
    ReturnToFirstMarkerDescription
    Direction.right

private abbrev MSBR := MarkedSimulatorLayoutBodyReturnDescription

theorem markedSimulatorLayoutBodyReturnDescription_subroutineReady :
    MSBR.SubroutineReady :=
  seqSubroutine_subroutineReady
    markedSimulatorLayoutBodyScannerDescription_subroutineReady
    returnToFirstMarkerDescription_subroutineReady

theorem checkedSimulatorLayoutScannerDescription_haltsWithTape_marker_inv
    {bits : Word Bool} {Tout : Tape Bool}
    (h : CSL.HaltsWithTape bits Tout) :
    exists tail : Word Bool,
    exists nB : Nat,
      bits = false :: false :: tail ∧
        MSBR.runConfig nB
            { state := MSBR.start
              tape :=
                Tape.move Direction.right
                  (config MFTB.halt []
                    (none :: some false :: tail.map some)).tape } =
          { state := MSBR.halt
            tape := Tout } := by
  rcases
      seqSubroutine_haltsWithTape_inv
        (A := MFTB)
        (B := MSBR)
        (handoffMove := Direction.right)
        markFirstTransitionBitDescription_subroutineReady
        markedSimulatorLayoutBodyReturnDescription_subroutineReady
        (by
          simpa [CheckedSimulatorLayoutScannerDescription,
            MSBR] using! h) with
    ⟨Tmid, hmark, nB, hbody⟩
  rcases markFirstTransitionBitDescription_haltsWithTape_inv hmark with
    ⟨tail, hbits, hTmid⟩
  refine ⟨tail, nB, hbits, ?_⟩
  rw [hTmid] at hbody
  exact hbody

theorem markedSimulatorLayoutBodyReturnDescription_runConfig_inv
    {Tin Tout : Tape Bool} {n : Nat}
    (h :
      MSBR.runConfig n
          { state := MSBR.start
            tape := Tin } =
        { state := MSBR.halt
          tape := Tout }) :
    exists Tbody : Tape Bool,
      (exists nBody : Nat,
        MSBS.runConfig nBody
            { state := MSBS.start
              tape := Tin } =
          { state := MSBS.halt
            tape := Tbody } ∧
          forall k : Nat,
            k < nBody ->
              (MSBS.runConfig k
                { state := MSBS.start
                  tape := Tin }).state ≠
                MSBS.halt) ∧
        exists nReturn : Nat,
          RFM.runConfig nReturn
              { state := RFM.start
                tape := Tape.move Direction.right Tbody } =
            { state := RFM.halt
              tape := Tout } := by
  simpa [MarkedSimulatorLayoutBodyReturnDescription] using
    seqSubroutine_runConfig_inv
      (A := MSBS)
      (B := RFM)
      (handoffMove := Direction.right)
      markedSimulatorLayoutBodyScannerDescription_subroutineReady
      returnToFirstMarkerDescription_subroutineReady
      (by simpa [MarkedSimulatorLayoutBodyReturnDescription] using h)

theorem markedSimulatorLayoutBodyScannerDescription_runConfig_inv
    {Tin Tout : Tape Bool} {n : Nat}
    (h :
      MSBS.runConfig n
          { state := MSBS.start
            tape := Tin } =
        { state := MSBS.halt
          tape := Tout }) :
    exists Theader : Tape Bool,
      (exists nHeader : Nat,
        HRP.runConfig nHeader
            { state := HRP.start
              tape := Tin } =
          { state := HRP.halt
            tape := Theader } ∧
          forall k : Nat,
            k < nHeader ->
              (HRP.runConfig k
                { state := HRP.start
                  tape := Tin }).state ≠
                HRP.halt) ∧
        exists nRest : Nat,
          ISCFF.runConfig nRest
              { state :=
                  ISCFF.start
                tape := Tape.move Direction.right Theader } =
            { state :=
                ISCFF.halt
              tape := Tout } := by
  simpa [MarkedSimulatorLayoutBodyScannerDescription] using
    seqSubroutine_runConfig_inv
      (A := HRP)
      (B := ISCFF)
      (handoffMove := Direction.right)
      headerRemainderPrefixScannerDescription_subroutineReady
      inputStageConfigurationAndFinalFlagScannerDescription_subroutineReady
      (by simpa [MarkedSimulatorLayoutBodyScannerDescription] using h)

theorem checkedSimulatorLayoutScannerDescription_haltsWithTape_body_return_inv
    {bits : Word Bool} {Tout : Tape Bool}
    (h : CSL.HaltsWithTape bits Tout) :
    exists tail : Word Bool,
    exists Tbody : Tape Bool,
    exists nBody : Nat,
    exists nReturn : Nat,
      bits = false :: false :: tail ∧
        MSBS.runConfig nBody
            { state := MSBS.start
              tape := tapeAtCells [none] (some false :: tail.map some) } =
          { state := MSBS.halt
            tape := Tbody } ∧
        RFM.runConfig nReturn
            { state := RFM.start
              tape := Tape.move Direction.right Tbody } =
          { state := RFM.halt
            tape := Tout } := by
  rcases checkedSimulatorLayoutScannerDescription_haltsWithTape_marker_inv h with
    ⟨tail, nBodyReturn, hbits, hrun⟩
  rcases
      markedSimulatorLayoutBodyReturnDescription_runConfig_inv hrun with
    ⟨Tbody, hbody, hreturn⟩
  rcases hbody with ⟨nBody, hbodyRun, _hbodyFirst⟩
  rcases hreturn with ⟨nReturn, hreturnRun⟩
  refine ⟨tail, Tbody, nBody, nReturn, hbits, ?_, hreturnRun⟩
  have hmove :
      Tape.move Direction.right
          (config MFTB.halt []
            (none :: some false :: tail.map some)).tape =
        tapeAtCells [none] (some false :: tail.map some) := by
    simp [config, tapeAtCells, Tape.move, Tape.moveRight]
  simpa [hmove] using hbodyRun

theorem headerRemainderPrefixScannerDescription_markedTail_inv
    {tail : Word Bool} {T : Tape Bool} {n : Nat}
    (h :
      HRP.runConfig n
          { state := HRP.start
            tape := tapeAtCells [none] (some false :: tail.map some) } =
        { state := HRP.halt
          tape := T }) :
    exists b : Bool,
    exists suffixTail : Word Bool,
      tail = false :: false :: b :: suffixTail ∧
        T =
          (headerRemainderHandoffConfigWithBase [none]
            (b :: suffixTail)).tape := by
  let start : Configuration :=
    { state := HRP.start
      tape := tapeAtCells [none] (some false :: tail.map some) }
  have hhaltState :
      (HRP.runConfig n start).state =
        HRP.halt := by
    simpa [start] using
      congrArg Configuration.state h
  cases tail with
  | nil =>
      let stuck :=
        HRP.runConfig 1 start
      have hstep :
          HRP.stepConfig stuck =
            none := by
        simp [stuck, start, HeaderRemainderPrefixScannerDescription,
          tapeAtCells, keepMove, runConfig,
          stepConfig,
          lookupTransition,
          Matches, transition,
          Tape.read, Tape.write, Tape.move, Tape.moveRight]
      have hstuck :
          stuck.state ≠
            HRP.halt := by
        simp [stuck, start, HeaderRemainderPrefixScannerDescription,
          tapeAtCells, keepMove, runConfig,
          stepConfig,
          lookupTransition,
          Matches, transition,
          Tape.read, Tape.write, Tape.move, Tape.moveRight]
      exact False.elim
        (CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
          headerRemainderPrefixScannerDescription_haltTransitionFree
          (D := HRP)
          (c := start) (stuck := stuck) (k := 1) (n := n)
          rfl hstep hstuck hhaltState)
  | cons first rest =>
      cases first
      · cases rest with
        | nil =>
            let stuck :=
              HRP.runConfig 2 start
            have hstep :
                HRP.stepConfig
                    stuck = none := by
              simp [stuck, start,
                HeaderRemainderPrefixScannerDescription,
                tapeAtCells, keepMove, runConfig,
                stepConfig,
                lookupTransition,
                Matches, transition,
                Tape.read, Tape.write, Tape.move, Tape.moveRight]
            have hstuck :
                stuck.state ≠
                  HRP.halt := by
              simp [stuck, start,
                HeaderRemainderPrefixScannerDescription,
                tapeAtCells, keepMove, runConfig,
                stepConfig,
                lookupTransition,
                Matches, transition,
                Tape.read, Tape.write, Tape.move, Tape.moveRight]
            exact False.elim
              (CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
                headerRemainderPrefixScannerDescription_haltTransitionFree
                (D := HRP)
                (c := start) (stuck := stuck) (k := 2) (n := n)
                rfl hstep hstuck hhaltState)
        | cons second restTail =>
            cases second
            · cases restTail with
              | nil =>
                  let stuck :=
                    HRP.runConfig 3
                      start
                  have hstep :
                      HRP.stepConfig
                          stuck = none := by
                    simp [stuck, start,
                      HeaderRemainderPrefixScannerDescription,
                      tapeAtCells, keepMove, runConfig,
                      stepConfig,
                      lookupTransition,
                      Matches,
                      transition, Tape.read, Tape.write,
                      Tape.move, Tape.moveRight]
                  have hstuck :
                      stuck.state ≠
                        HRP.halt := by
                    simp [stuck, start,
                      HeaderRemainderPrefixScannerDescription,
                      tapeAtCells, keepMove, runConfig,
                      stepConfig,
                      lookupTransition,
                      Matches,
                      transition, Tape.read, Tape.write,
                      Tape.move, Tape.moveRight]
                  exact False.elim
                    (CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
                      headerRemainderPrefixScannerDescription_haltTransitionFree
                      (D := HRP)
                      (c := start) (stuck := stuck) (k := 3) (n := n)
                      rfl hstep hstuck hhaltState)
              | cons b suffixTail =>
                  refine ⟨b, suffixTail, rfl, ?_⟩
                  rcases
                      run_headerRemainderPrefix_raw_to_handoff_withBase
                        [none] b suffixTail with
                    ⟨steps, hsteps⟩
                  have hstepsHalt :
                      HRP.runConfig
                          steps start =
                        { state :=
                            HRP.halt
                          tape :=
                            (headerRemainderHandoffConfigWithBase [none]
                              (b :: suffixTail)).tape } := by
                    simpa [start, config,
                      headerRemainderHandoffConfigWithBase] using! hsteps
                  exact
                    (MachineDescription.runConfig_halt_tape_functional_of_haltTransitionFree
                      headerRemainderPrefixScannerDescription_haltTransitionFree
                      hstepsHalt
                      (by simpa [start] using h)).symm
            · let stuck :=
                HRP.runConfig 2
                  start
              have hstep :
                  HRP.stepConfig
                      stuck = none := by
                cases restTail <;>
                  simp [stuck, start,
                    HeaderRemainderPrefixScannerDescription,
                    tapeAtCells, keepMove, runConfig,
                    stepConfig,
                    lookupTransition,
                    Matches, transition,
                    Tape.read, Tape.write, Tape.move, Tape.moveRight]
              have hstuck :
                  stuck.state ≠
                    HRP.halt := by
                cases restTail <;>
                  simp [stuck, start,
                    HeaderRemainderPrefixScannerDescription,
                    tapeAtCells, keepMove, runConfig,
                    stepConfig,
                    lookupTransition,
                    Matches, transition,
                    Tape.read, Tape.write, Tape.move, Tape.moveRight]
              exact False.elim
                (CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
                  headerRemainderPrefixScannerDescription_haltTransitionFree
                  (D := HRP)
                  (c := start) (stuck := stuck) (k := 2) (n := n)
                  rfl hstep hstuck hhaltState)
      · let stuck :=
          HRP.runConfig 1 start
        have hstep :
            HRP.stepConfig stuck =
              none := by
          cases rest <;>
            simp [stuck, start, HeaderRemainderPrefixScannerDescription,
              tapeAtCells, keepMove, runConfig,
              stepConfig,
              lookupTransition,
              Matches, transition,
              Tape.read, Tape.write, Tape.move, Tape.moveRight]
        have hstuck :
            stuck.state ≠
              HRP.halt := by
          cases rest <;>
            simp [stuck, start, HeaderRemainderPrefixScannerDescription,
              tapeAtCells, keepMove, runConfig,
              stepConfig,
              lookupTransition,
              Matches, transition,
              Tape.read, Tape.write, Tape.move, Tape.moveRight]
        exact False.elim
          (CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
            headerRemainderPrefixScannerDescription_haltTransitionFree
            (D := HRP)
            (c := start) (stuck := stuck) (k := 1) (n := n)
            rfl hstep hstuck hhaltState)

theorem checkedSimulatorLayoutScannerDescription_haltsWithTape_header_inv
    {bits : Word Bool} {Tout : Tape Bool}
    (h : CSL.HaltsWithTape bits Tout) :
    exists tail : Word Bool,
    exists Theader : Tape Bool,
    exists Tbody : Tape Bool,
    exists nHeader : Nat,
    exists nRest : Nat,
    exists nReturn : Nat,
      bits = false :: false :: tail ∧
        HRP.runConfig nHeader
            { state := HRP.start
              tape := tapeAtCells [none] (some false :: tail.map some) } =
          { state := HRP.halt
            tape := Theader } ∧
        ISCFF.runConfig nRest
            { state :=
                ISCFF.start
              tape := Tape.move Direction.right Theader } =
          { state :=
              ISCFF.halt
            tape := Tbody } ∧
        RFM.runConfig nReturn
            { state := RFM.start
              tape := Tape.move Direction.right Tbody } =
          { state := RFM.halt
            tape := Tout } := by
  rcases
      checkedSimulatorLayoutScannerDescription_haltsWithTape_body_return_inv
        h with
    ⟨tail, Tbody, nBody, nReturn, hbits, hbodyRun, hreturnRun⟩
  rcases
      markedSimulatorLayoutBodyScannerDescription_runConfig_inv
        hbodyRun with
    ⟨Theader, hheader, hrest⟩
  rcases hheader with ⟨nHeader, hheaderRun, _hfirst⟩
  rcases hrest with ⟨nRest, hrestRun⟩
  exact
    ⟨tail, Theader, Tbody, nHeader, nRest, nReturn,
      hbits, hheaderRun, hrestRun, hreturnRun⟩

theorem checkedSimulatorLayoutScannerDescription_haltsWithTape_afterHeader_inv
    {bits : Word Bool} {Tout : Tape Bool}
    (h : CSL.HaltsWithTape bits Tout) :
    exists b : Bool,
    exists suffixTail : Word Bool,
    exists Tbody : Tape Bool,
    exists nRest : Nat,
    exists nReturn : Nat,
      bits = false :: false :: false :: false :: b :: suffixTail ∧
        ISCFF.runConfig nRest
            { state :=
                ISCFF.start
              tape :=
                tapeAtCells
                  (List.append (headerRemainderBits.reverse.map some)
                    [none])
                  ((b :: suffixTail).map some) } =
          { state :=
              ISCFF.halt
            tape := Tbody } ∧
        RFM.runConfig nReturn
            { state := RFM.start
              tape := Tape.move Direction.right Tbody } =
          { state := RFM.halt
            tape := Tout } := by
  rcases
      checkedSimulatorLayoutScannerDescription_haltsWithTape_header_inv h with
    ⟨tail, Theader, Tbody, _nHeader, nRest, nReturn,
      hbits, hheaderRun, hrestRun, hreturnRun⟩
  rcases
      headerRemainderPrefixScannerDescription_markedTail_inv
        hheaderRun with
    ⟨b, suffixTail, htail, hTheader⟩
  refine ⟨b, suffixTail, Tbody, nRest, nReturn, ?_, ?_, hreturnRun⟩
  · rw [hbits, htail]
  · rw [hTheader] at hrestRun
    simpa [headerRemainderHandoffConfigWithBase_move_right] using
      hrestRun

theorem inputStageConfigurationAndFinalFlagScannerDescription_runConfig_inv
    {Tin Tout : Tape Bool} {n : Nat}
    (h :
      ISCFF.runConfig n
          { state :=
              ISCFF.start
            tape := Tin } =
        { state :=
            ISCFF.halt
          tape := Tout }) :
    exists Tinput : Tape Bool,
      (exists nInput : Nat,
        BWSS.runConfig nInput
            { state := BWSS.start
              tape := Tin } =
          { state := BWSS.halt
            tape := Tinput } ∧
          forall k : Nat,
            k < nInput ->
              (BWSS.runConfig k
                { state := BWSS.start
                  tape := Tin }).state ≠
                BWSS.halt) ∧
        exists nStage : Nat,
          SCFF.runConfig nStage
              { state :=
                  SCFF.start
                tape := Tape.move Direction.right Tinput } =
            { state := SCFF.halt
              tape := Tout } := by
  simpa [InputStageConfigurationAndFinalFlagScannerDescription] using
    seqSubroutine_runConfig_inv
      (A := BWSS)
      (B := SCFF)
      (handoffMove := Direction.right)
      boolWordSuffixScannerDescription_subroutineReady
      stageConfigurationAndFinalFlagScannerDescription_subroutineReady
      (by
        simpa [InputStageConfigurationAndFinalFlagScannerDescription] using
          h)

theorem stageConfigurationAndFinalFlagScannerDescription_runConfig_inv
    {Tin Tout : Tape Bool} {n : Nat}
    (h :
      SCFF.runConfig n
          { state :=
              SCFF.start
            tape := Tin } =
        { state :=
            SCFF.halt
          tape := Tout }) :
    exists Tstage : Tape Bool,
      (exists nStage : Nat,
        NNSS.runConfig nStage
            { state := NNSS.start
              tape := Tin } =
          { state := NNSS.halt
            tape := Tstage } ∧
          forall k : Nat,
            k < nStage ->
              (NNSS.runConfig k
                { state :=
                    NNSS.start
                  tape := Tin }).state ≠
                NNSS.halt) ∧
        exists nConfig : Nat,
          CFF.runConfig nConfig
              { state :=
                  CFF.start
                tape := Tape.move Direction.right Tstage } =
            { state := CFF.halt
              tape := Tout } := by
  simpa [StageConfigurationAndFinalFlagScannerDescription] using
    seqSubroutine_runConfig_inv
      (A := NNSS)
      (B := CFF)
      (handoffMove := Direction.right)
      DovetailStagePrefix.nonemptyNatSuffixScannerDescription_subroutineReady
      configurationAndFinalFlagScannerDescription_subroutineReady
      (by
        simpa [StageConfigurationAndFinalFlagScannerDescription] using h)

theorem configurationAndFinalFlagScannerDescription_runConfig_inv
    {Tin Tout : Tape Bool} {n : Nat}
    (h :
      CFF.runConfig n
          { state :=
              CFF.start
            tape := Tin } =
        { state :=
            CFF.halt
          tape := Tout }) :
    exists Tconfig : Tape Bool,
      (exists nConfig : Nat,
        CFS.runConfig nConfig
            { state := CFS.start
              tape := Tin } =
          { state := CFS.halt
            tape := Tconfig } ∧
          forall k : Nat,
            k < nConfig ->
              (CFS.runConfig k
                { state := CFS.start
                  tape := Tin }).state ≠
                CFS.halt) ∧
        exists nFlag : Nat,
          BFS.runConfig nFlag
              { state := BFS.start
                tape := Tape.move Direction.right Tconfig } =
            { state := BFS.halt
              tape := Tout } := by
  simpa [ConfigurationAndFinalFlagScannerDescription] using
    seqSubroutine_runConfig_inv
      (A := CFS)
      (B := BFS)
      (handoffMove := Direction.right)
      configurationSuffixScannerDescription_subroutineReady
      boolFinalScannerDescription_subroutineReady
      (by
        simpa [ConfigurationAndFinalFlagScannerDescription] using h)

theorem checkedSimulatorLayoutScannerDescription_haltsWithTape_fields_inv
    {bits : Word Bool} {Tout : Tape Bool}
    (h : CSL.HaltsWithTape bits Tout) :
    exists b : Bool,
    exists suffixTail : Word Bool,
    exists Tinput : Tape Bool,
    exists Tstage : Tape Bool,
    exists Tconfig : Tape Bool,
    exists Tbody : Tape Bool,
    exists nInput : Nat,
    exists nStage : Nat,
    exists nConfig : Nat,
    exists nFlag : Nat,
    exists nReturn : Nat,
      bits = false :: false :: false :: false :: b :: suffixTail ∧
        BWSS.runConfig nInput
            { state := BWSS.start
              tape :=
                tapeAtCells
                  (List.append (headerRemainderBits.reverse.map some)
                    [none])
                  ((b :: suffixTail).map some) } =
          { state := BWSS.halt
            tape := Tinput } ∧
        NNSS.runConfig nStage
            { state := NNSS.start
              tape := Tape.move Direction.right Tinput } =
          { state := NNSS.halt
            tape := Tstage } ∧
        CFS.runConfig nConfig
            { state := CFS.start
              tape := Tape.move Direction.right Tstage } =
          { state := CFS.halt
            tape := Tconfig } ∧
        BFS.runConfig nFlag
            { state := BFS.start
              tape := Tape.move Direction.right Tconfig } =
          { state := BFS.halt
            tape := Tbody } ∧
        RFM.runConfig nReturn
            { state := RFM.start
              tape := Tape.move Direction.right Tbody } =
          { state := RFM.halt
            tape := Tout } := by
  rcases
      checkedSimulatorLayoutScannerDescription_haltsWithTape_afterHeader_inv
        h with
    ⟨b, suffixTail, Tbody, nRest, nReturn, hbits, hrestRun, hreturnRun⟩
  rcases
      inputStageConfigurationAndFinalFlagScannerDescription_runConfig_inv
        hrestRun with
    ⟨Tinput, hinput, hstage⟩
  rcases hinput with ⟨nInput, hinputRun, _hinputFirst⟩
  rcases hstage with ⟨nStage, hstageRun⟩
  rcases
      stageConfigurationAndFinalFlagScannerDescription_runConfig_inv
        hstageRun with
    ⟨Tstage, hstage', hconfig⟩
  rcases hstage' with ⟨nStage', hstageRun', _hstageFirst⟩
  rcases hconfig with ⟨nConfig, hconfigRun⟩
  rcases
      configurationAndFinalFlagScannerDescription_runConfig_inv
        hconfigRun with
    ⟨Tconfig, hconfig', hflag⟩
  rcases hconfig' with ⟨nConfig', hconfigRun', _hconfigFirst⟩
  rcases hflag with ⟨nFlag, hflagRun⟩
  exact
    ⟨b, suffixTail, Tinput, Tstage, Tconfig, Tbody,
      nInput, nStage', nConfig', nFlag, nReturn,
      hbits, hinputRun, hstageRun', hconfigRun', hflagRun, hreturnRun⟩

end SimulatorLayoutScanner
end CanonicalLayouts
end EncRewriters

end Computability
end FoC

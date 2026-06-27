import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.Composition

set_option doc.verso true

/-!
# Closed facts for the dovetail-layout scanner

This module starts the closed-direction proof stack for the checked complete
layout scanner.  The first lemma inverts the initial marker writer: any halting
run of the marker writer must have started on the two leading transition bits
and must halt with the first bit replaced by the internal blank marker.
-/

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

def MarkedDovetailLayoutBodyReturnDescription : MachineDescription :=
  seqSubroutine
    MarkedDovetailLayoutBodyScannerDescription
    ReturnToFirstMarkerDescription
    Direction.right

theorem markedDovetailLayoutBodyReturnDescription_subroutineReady :
    MarkedDovetailLayoutBodyReturnDescription.SubroutineReady :=
  seqSubroutine_subroutineReady
    markedDovetailLayoutBodyScannerDescription_subroutineReady
    returnToFirstMarkerDescription_subroutineReady

private abbrev MDBR := MarkedDovetailLayoutBodyReturnDescription
private abbrev MFTB := MarkFirstTransitionBitDescription
private abbrev CDL := CheckedDovetailLayoutScannerDescription
private abbrev MDBS := MarkedDovetailLayoutBodyScannerDescription
private abbrev RFM := ReturnToFirstMarkerDescription
private abbrev TRP := TransitionRemainderPrefixScannerDescription
private abbrev ISCFFS := InputStageConfigurationsAndFinalFlagsScannerDescription
private abbrev SCFFS := StageConfigurationsAndFinalFlagsScannerDescription
private abbrev BWSS := BoolWordSuffixScannerDescription
private abbrev NNSS := DovetailStagePrefix.NonemptyNatSuffixScannerDescription
private abbrev CFFS := ConfigurationsAndFinalFlagsScannerDescription
private abbrev CFS := ConfigurationSuffixScannerDescription
private abbrev RCF := RejectConfigAndFinalFlagsScannerDescription
private abbrev FHFS := FinalHitFlagsScannerDescription
private abbrev BSS := BoolSuffixScannerDescription
private abbrev BFS := BoolFinalScannerDescription

theorem markFirstTransitionBitDescription_haltsWithTape_inv
    {bits : Word Bool} {T : Tape Bool}
    (h : MFTB.HaltsWithTape bits T) :
    exists tail : Word Bool,
      bits = false :: false :: tail ∧
        T =
          (config MFTB.halt []
            (none :: some false :: tail.map some)).tape := by
  rcases runConfig_eq_halt_of_haltsWithTape h with
    ⟨n, hn⟩
  cases bits with
  | nil =>
      have hstep :
          MFTB.stepConfig
              (MFTB.initial []) = none := by
        decide
      have hrun :=
        runConfig_of_stepConfig_none hstep n
      have hstate : 0 = 9 := by
        simpa [MarkFirstTransitionBitDescription,
          initial] using
          congrArg Configuration.state
            (hrun.symm.trans hn)
      omega
  | cons b rest =>
      cases b
      · cases rest with
        | nil =>
            cases n with
            | zero =>
                simp [MarkFirstTransitionBitDescription,
                  runConfig] at hn
            | succ n =>
                let c1 : Configuration :=
                  { state := 1
                    tape := tapeAtCells [none] [] }
                have hstep0 :
                    MFTB.stepConfig
                        (MFTB.initial [false]) =
                      some c1 := by
                  simp [c1, MarkFirstTransitionBitDescription,
                    tapeAtCells, keepMove, writeMove,
                    initial,
                    stepConfig,
                    lookupTransition,
                    Matches,
                    transition, Tape.input, Tape.read,
                    Tape.write, Tape.move, Tape.moveRight]
                have hrun :
                    MFTB.runConfig (Nat.succ n)
                        (MFTB.initial [false]) =
                      MFTB.runConfig n c1 := by
                  simp [runConfig, hstep0]
                have hstep1 :
                    MFTB.stepConfig c1 = none := by
                  simp [c1, MarkFirstTransitionBitDescription, tapeAtCells,
                    keepMove, writeMove, stepConfig,
                    lookupTransition,
                    Matches,
                    transition, Tape.read]
                have hstay :=
                  runConfig_of_stepConfig_none hstep1 n
                have hrunFinal :
                    MFTB.runConfig (Nat.succ n)
                        (MFTB.initial [false]) =
                      c1 :=
                  hrun.trans hstay
                have hstate : 1 = 9 := by
                  simpa [c1, MarkFirstTransitionBitDescription] using
                    congrArg Configuration.state
                      (hrunFinal.symm.trans hn)
                omega
        | cons c tail =>
            cases c
            · refine ⟨tail, rfl, ?_⟩
              cases n with
              | zero =>
                  simp [MarkFirstTransitionBitDescription,
                    runConfig] at hn
              | succ n =>
                  cases n with
                  | zero =>
                      simp [MarkFirstTransitionBitDescription,
                        keepMove, writeMove,
                        runConfig,
                        stepConfig,
                        lookupTransition,
                        Matches,
                        transition, Tape.input,
                        Tape.read, Tape.write, Tape.move, Tape.moveRight]
                        at hn
                  | succ k =>
                      have hrun :
                          MFTB.runConfig
                              (Nat.succ (Nat.succ k))
                              (MFTB.initial
                                (false :: false :: tail)) =
                            config MFTB.halt []
                              (none :: some false :: tail.map some) := by
                        rw [show Nat.succ (Nat.succ k) = 2 + k by omega]
                        rw [runConfig_add]
                        have h2 :
                            MFTB.runConfig 2
                                (MFTB.initial
                                  (false :: false :: tail)) =
                              config MFTB.halt []
                                (none :: some false :: tail.map some) := by
                          simpa [initial, config,
                            tapeAtCells] using
                            run_markFirstTransitionBit_raw tail
                        rw [h2]
                        exact
                          runConfig_halt
                            markFirstTransitionBitDescription_haltTransitionFree
                            (config MFTB.halt []
                              (none :: some false :: tail.map some)).tape k
                      let cfgGood : Configuration :=
                        config MFTB.halt []
                          (none :: some false :: tail.map some)
                      have hcfg :
                          cfgGood =
                            { state := MFTB.halt
                              tape := T } := by
                        simpa [cfgGood] using hrun.symm.trans hn
                      exact
                        (congrArg Configuration.tape
                          hcfg).symm
            · cases n with
              | zero =>
                  simp [MarkFirstTransitionBitDescription,
                    runConfig] at hn
              | succ n =>
                  let c1 : Configuration :=
                    { state := 1
                      tape := tapeAtCells [none]
                        (some true :: tail.map some) }
                  have hstep0 :
                      MFTB.stepConfig
                          (MFTB.initial
                            (false :: true :: tail)) =
                        some c1 := by
                    simp [c1, MarkFirstTransitionBitDescription,
                      tapeAtCells, keepMove, writeMove,
                      initial,
                      stepConfig,
                      lookupTransition,
                      Matches,
                      transition, Tape.input, Tape.read,
                      Tape.write, Tape.move, Tape.moveRight]
                  have hrun :
                      MFTB.runConfig
                          (Nat.succ n)
                          (MFTB.initial
                            (false :: true :: tail)) =
                        MFTB.runConfig n c1 := by
                    simp [runConfig, hstep0]
                  have hstep1 :
                      MFTB.stepConfig c1 =
                        none := by
                    simp [c1, MarkFirstTransitionBitDescription, tapeAtCells,
                      keepMove, writeMove, stepConfig,
                      lookupTransition,
                      Matches,
                      transition, Tape.read]
                  have hstay :=
                    runConfig_of_stepConfig_none hstep1 n
                  have hrunFinal :
                      MFTB.runConfig
                          (Nat.succ n)
                          (MFTB.initial
                            (false :: true :: tail)) =
                        c1 :=
                    hrun.trans hstay
                  have hstate : 1 = 9 := by
                    simpa [c1, MarkFirstTransitionBitDescription] using
                      congrArg Configuration.state
                        (hrunFinal.symm.trans hn)
                  omega
      · have hstep :
            MFTB.stepConfig
                (MFTB.initial (true :: rest)) =
              none := by
          simp [MarkFirstTransitionBitDescription, keepMove, writeMove,
            initial, stepConfig,
            lookupTransition, Matches,
            transition, Tape.input, Tape.read]
        have hrun :=
          runConfig_of_stepConfig_none hstep n
        have hstate : 0 = 9 := by
          simpa [MarkFirstTransitionBitDescription,
            initial] using
            congrArg Configuration.state
              (hrun.symm.trans hn)
        omega

theorem checkedDovetailLayoutScannerDescription_haltsWithTape_marker_inv
    {bits : Word Bool} {Tout : Tape Bool}
    (h : CDL.HaltsWithTape bits Tout) :
    exists tail : Word Bool,
    exists nB : Nat,
      bits = false :: false :: tail ∧
        MDBR.runConfig nB
            { state := MDBR.start
              tape :=
                Tape.move Direction.right
                  (config MFTB.halt []
                    (none :: some false :: tail.map some)).tape } =
          { state := MDBR.halt
            tape := Tout } := by
  rcases
      seqSubroutine_haltsWithTape_inv
        (A := MFTB)
        (B := MDBR)
        (handoffMove := Direction.right)
        markFirstTransitionBitDescription_subroutineReady
        markedDovetailLayoutBodyReturnDescription_subroutineReady
        (by
          simpa [CheckedDovetailLayoutScannerDescription,
            MDBR] using h) with
    ⟨Tmid, hmark, nB, hbody⟩
  rcases markFirstTransitionBitDescription_haltsWithTape_inv hmark with
    ⟨tail, hbits, hTmid⟩
  refine ⟨tail, nB, hbits, ?_⟩
  rw [hTmid] at hbody
  exact hbody

theorem markedDovetailLayoutBodyReturnDescription_runConfig_inv
    {Tin Tout : Tape Bool} {n : Nat}
    (h :
      MDBR.runConfig n
          { state := MDBR.start
            tape := Tin } =
        { state := MDBR.halt
          tape := Tout }) :
    exists Tbody : Tape Bool,
      (exists nBody : Nat,
        MDBS.runConfig nBody
            { state := MDBS.start
              tape := Tin } =
          { state := MDBS.halt
            tape := Tbody } ∧
          forall k : Nat,
            k < nBody ->
              (MDBS.runConfig k
                { state := MDBS.start
                  tape := Tin }).state ≠
                MDBS.halt) ∧
        exists nReturn : Nat,
          RFM.runConfig nReturn
              { state := RFM.start
                tape := Tape.move Direction.right Tbody } =
            { state := RFM.halt
              tape := Tout } := by
  simpa [MarkedDovetailLayoutBodyReturnDescription] using
    seqSubroutine_runConfig_inv
      (A := MDBS)
      (B := RFM)
      (handoffMove := Direction.right)
      markedDovetailLayoutBodyScannerDescription_subroutineReady
      returnToFirstMarkerDescription_subroutineReady
      (by simpa [MarkedDovetailLayoutBodyReturnDescription] using h)

theorem markedDovetailLayoutBodyScannerDescription_runConfig_inv
    {Tin Tout : Tape Bool} {n : Nat}
    (h :
      MDBS.runConfig n
          { state := MDBS.start
            tape := Tin } =
        { state := MDBS.halt
          tape := Tout }) :
    exists Ttransition : Tape Bool,
      (exists nTransition : Nat,
        TRP.runConfig nTransition
            { state := TRP.start
              tape := Tin } =
          { state := TRP.halt
            tape := Ttransition } ∧
          forall k : Nat,
            k < nTransition ->
              (TRP.runConfig k
                { state := TRP.start
                  tape := Tin }).state ≠
                TRP.halt) ∧
        exists nRest : Nat,
          ISCFFS.runConfig nRest
              { state :=
                  ISCFFS.start
                tape := Tape.move Direction.right Ttransition } =
            { state :=
                ISCFFS.halt
              tape := Tout } := by
  simpa [MarkedDovetailLayoutBodyScannerDescription] using
    seqSubroutine_runConfig_inv
      (A := TRP)
      (B := ISCFFS)
        (handoffMove := Direction.right)
      transitionRemainderPrefixScannerDescription_subroutineReady
      inputStageConfigurationsAndFinalFlagsScannerDescription_subroutineReady
      (by simpa [MarkedDovetailLayoutBodyScannerDescription] using h)

theorem checkedDovetailLayoutScannerDescription_haltsWithTape_body_return_inv
    {bits : Word Bool} {Tout : Tape Bool}
    (h : CDL.HaltsWithTape bits Tout) :
    exists tail : Word Bool,
    exists Tbody : Tape Bool,
    exists nBody : Nat,
    exists nReturn : Nat,
      bits = false :: false :: tail ∧
        MDBS.runConfig nBody
            { state := MDBS.start
              tape := tapeAtCells [none] (some false :: tail.map some) } =
          { state := MDBS.halt
            tape := Tbody } ∧
        RFM.runConfig nReturn
            { state := RFM.start
              tape := Tape.move Direction.right Tbody } =
          { state := RFM.halt
            tape := Tout } := by
  rcases checkedDovetailLayoutScannerDescription_haltsWithTape_marker_inv h with
    ⟨tail, nBodyReturn, hbits, hrun⟩
  rcases
      markedDovetailLayoutBodyReturnDescription_runConfig_inv hrun with
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

theorem runConfig_state_ne_halt_of_reaches_stuck
    {D : MachineDescription}
    {c stuck : Configuration} {k n : Nat}
    (hD : D.HaltTransitionFree)
    (hprefix : D.runConfig k c = stuck)
    (hstep : D.stepConfig stuck = none)
    (hstuck : stuck.state ≠ D.halt) :
    (D.runConfig n c).state ≠ D.halt :=
  CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
    hD hprefix hstep hstuck

theorem transitionRemainderPrefixScannerDescription_markedTail_inv
    {tail : Word Bool} {T : Tape Bool} {n : Nat}
    (h :
      TRP.runConfig n
          { state := TRP.start
            tape := tapeAtCells [none] (some false :: tail.map some) } =
        { state := TRP.halt
          tape := T }) :
    exists b : Bool,
    exists suffixTail : Word Bool,
      tail = false :: true :: b :: suffixTail ∧
        T =
          (transitionRemainderHandoffConfigWithBase [none]
            (b :: suffixTail)).tape := by
  let start : Configuration :=
    { state := TRP.start
      tape := tapeAtCells [none] (some false :: tail.map some) }
  have hhaltState :
      (TRP.runConfig n start).state =
        TRP.halt := by
    simpa [start] using
      congrArg Configuration.state h
  cases tail with
  | nil =>
      let stuck :=
        TRP.runConfig 1 start
      have hstep :
          TRP.stepConfig stuck =
            none := by
        simp [stuck, start, TransitionRemainderPrefixScannerDescription,
          tapeAtCells, keepMove, runConfig,
          stepConfig,
          lookupTransition,
          Matches, transition,
          Tape.read, Tape.write, Tape.move, Tape.moveRight]
      have hstuck :
          stuck.state ≠
            TRP.halt := by
        simp [stuck, start, TransitionRemainderPrefixScannerDescription,
          tapeAtCells, keepMove, runConfig,
          stepConfig,
          lookupTransition,
          Matches, transition,
          Tape.read, Tape.write, Tape.move, Tape.moveRight]
      exact False.elim
        (runConfig_state_ne_halt_of_reaches_stuck
          transitionRemainderPrefixScannerDescription_haltTransitionFree
          (D := TRP)
          (c := start) (stuck := stuck) (k := 1) (n := n)
          rfl hstep hstuck hhaltState)
  | cons first rest =>
      cases first
      · cases rest with
        | nil =>
            let stuck :=
              TRP.runConfig 2 start
            have hstep :
                TRP.stepConfig
                    stuck = none := by
              simp [stuck, start,
                TransitionRemainderPrefixScannerDescription,
                tapeAtCells, keepMove, runConfig,
                stepConfig,
                lookupTransition,
                Matches, transition,
                Tape.read, Tape.write, Tape.move, Tape.moveRight]
            have hstuck :
                stuck.state ≠
                  TRP.halt := by
              simp [stuck, start,
                TransitionRemainderPrefixScannerDescription,
                tapeAtCells, keepMove, runConfig,
                stepConfig,
                lookupTransition,
                Matches, transition,
                Tape.read, Tape.write, Tape.move, Tape.moveRight]
            exact False.elim
              (runConfig_state_ne_halt_of_reaches_stuck
                transitionRemainderPrefixScannerDescription_haltTransitionFree
                (D := TRP)
                (c := start) (stuck := stuck) (k := 2) (n := n)
                rfl hstep hstuck hhaltState)
        | cons second restTail =>
            cases second
            · let stuck :=
                TRP.runConfig 2
                  start
              have hstep :
                  TRP.stepConfig
                      stuck = none := by
                cases restTail <;>
                  simp [stuck, start,
                    TransitionRemainderPrefixScannerDescription,
                    tapeAtCells, keepMove, runConfig,
                    stepConfig,
                    lookupTransition,
                    Matches, transition,
                    Tape.read, Tape.write, Tape.move, Tape.moveRight]
              have hstuck :
                  stuck.state ≠
                    TRP.halt := by
                cases restTail <;>
                  simp [stuck, start,
                    TransitionRemainderPrefixScannerDescription,
                    tapeAtCells, keepMove, runConfig,
                    stepConfig,
                    lookupTransition,
                    Matches, transition,
                    Tape.read, Tape.write, Tape.move, Tape.moveRight]
              exact False.elim
                (runConfig_state_ne_halt_of_reaches_stuck
                  transitionRemainderPrefixScannerDescription_haltTransitionFree
                  (D := TRP)
                  (c := start) (stuck := stuck) (k := 2) (n := n)
                  rfl hstep hstuck hhaltState)
            · cases restTail with
              | nil =>
                  let stuck :=
                    TRP.runConfig 3
                      start
                  have hstep :
                      TRP.stepConfig
                          stuck = none := by
                    simp [stuck, start,
                      TransitionRemainderPrefixScannerDescription,
                      tapeAtCells, keepMove, runConfig,
                      stepConfig,
                      lookupTransition,
                      Matches,
                      transition, Tape.read, Tape.write,
                      Tape.move, Tape.moveRight]
                  have hstuck :
                      stuck.state ≠
                        TRP.halt := by
                    simp [stuck, start,
                      TransitionRemainderPrefixScannerDescription,
                      tapeAtCells, keepMove, runConfig,
                      stepConfig,
                      lookupTransition,
                      Matches,
                      transition, Tape.read, Tape.write,
                      Tape.move, Tape.moveRight]
                  exact False.elim
                    (runConfig_state_ne_halt_of_reaches_stuck
                      transitionRemainderPrefixScannerDescription_haltTransitionFree
                      (D := TRP)
                      (c := start) (stuck := stuck) (k := 3) (n := n)
                      rfl hstep hstuck hhaltState)
              | cons b suffixTail =>
                  refine ⟨b, suffixTail, rfl, ?_⟩
                  rcases
                      run_transitionRemainderPrefix_raw_to_handoff_withBase
                        [none] b suffixTail with
                    ⟨steps, hsteps⟩
                  have hstepsHalt :
                      TRP.runConfig
                          steps start =
                        { state :=
                            TRP.halt
                          tape :=
                            (transitionRemainderHandoffConfigWithBase [none]
                              (b :: suffixTail)).tape } := by
                    simpa [start, config,
                      transitionRemainderHandoffConfigWithBase] using hsteps
                  exact
                    (MachineDescription.runConfig_halt_tape_functional_of_haltTransitionFree
                      transitionRemainderPrefixScannerDescription_haltTransitionFree
                      hstepsHalt
                      (by simpa [start] using h)).symm
      · let stuck :=
          TRP.runConfig 1 start
        have hstep :
            TRP.stepConfig stuck =
              none := by
          cases rest <;>
            simp [stuck, start, TransitionRemainderPrefixScannerDescription,
              tapeAtCells, keepMove, runConfig,
              stepConfig,
              lookupTransition,
              Matches, transition,
              Tape.read, Tape.write, Tape.move, Tape.moveRight]
        have hstuck :
            stuck.state ≠
              TRP.halt := by
          cases rest <;>
            simp [stuck, start, TransitionRemainderPrefixScannerDescription,
              tapeAtCells, keepMove, runConfig,
              stepConfig,
              lookupTransition,
              Matches, transition,
              Tape.read, Tape.write, Tape.move, Tape.moveRight]
        exact False.elim
          (runConfig_state_ne_halt_of_reaches_stuck
            transitionRemainderPrefixScannerDescription_haltTransitionFree
            (D := TRP)
            (c := start) (stuck := stuck) (k := 1) (n := n)
            rfl hstep hstuck hhaltState)

theorem checkedDovetailLayoutScannerDescription_haltsWithTape_transition_inv
    {bits : Word Bool} {Tout : Tape Bool}
    (h : CDL.HaltsWithTape bits Tout) :
    exists tail : Word Bool,
    exists Ttransition : Tape Bool,
    exists Tbody : Tape Bool,
    exists nTransition : Nat,
    exists nRest : Nat,
    exists nReturn : Nat,
      bits = false :: false :: tail ∧
        TRP.runConfig nTransition
            { state := TRP.start
              tape := tapeAtCells [none] (some false :: tail.map some) } =
          { state := TRP.halt
            tape := Ttransition } ∧
        ISCFFS.runConfig nRest
            { state :=
                ISCFFS.start
              tape := Tape.move Direction.right Ttransition } =
          { state :=
              ISCFFS.halt
            tape := Tbody } ∧
        RFM.runConfig nReturn
            { state := RFM.start
              tape := Tape.move Direction.right Tbody } =
          { state := RFM.halt
            tape := Tout } := by
  rcases
      checkedDovetailLayoutScannerDescription_haltsWithTape_body_return_inv
        h with
    ⟨tail, Tbody, nBody, nReturn, hbits, hbodyRun, hreturnRun⟩
  rcases
      markedDovetailLayoutBodyScannerDescription_runConfig_inv
        hbodyRun with
    ⟨Ttransition, htransition, hrest⟩
  rcases htransition with ⟨nTransition, htransitionRun, _hfirst⟩
  rcases hrest with ⟨nRest, hrestRun⟩
  exact
    ⟨tail, Ttransition, Tbody, nTransition, nRest, nReturn,
      hbits, htransitionRun, hrestRun, hreturnRun⟩

theorem checkedDovetailLayoutScannerDescription_haltsWithTape_afterTransition_inv
    {bits : Word Bool} {Tout : Tape Bool}
    (h : CDL.HaltsWithTape bits Tout) :
    exists b : Bool,
    exists suffixTail : Word Bool,
    exists Tbody : Tape Bool,
    exists nRest : Nat,
    exists nReturn : Nat,
      bits = false :: false :: false :: true :: b :: suffixTail ∧
        ISCFFS.runConfig nRest
            { state :=
                ISCFFS.start
              tape :=
                tapeAtCells
                  (List.append (transitionRemainderBits.reverse.map some)
                    [none])
                  ((b :: suffixTail).map some) } =
          { state :=
              ISCFFS.halt
            tape := Tbody } ∧
        RFM.runConfig nReturn
            { state := RFM.start
              tape := Tape.move Direction.right Tbody } =
          { state := RFM.halt
            tape := Tout } := by
  rcases
      checkedDovetailLayoutScannerDescription_haltsWithTape_transition_inv h with
    ⟨tail, Ttransition, Tbody, _nTransition, nRest, nReturn,
      hbits, htransitionRun, hrestRun, hreturnRun⟩
  rcases
      transitionRemainderPrefixScannerDescription_markedTail_inv
        htransitionRun with
    ⟨b, suffixTail, htail, hTtransition⟩
  refine ⟨b, suffixTail, Tbody, nRest, nReturn, ?_, ?_, hreturnRun⟩
  · rw [hbits, htail]
  · rw [hTtransition] at hrestRun
    simpa [transitionRemainderHandoffConfigWithBase_move_right] using
      hrestRun

theorem inputStageConfigurationsAndFinalFlagsScannerDescription_runConfig_inv
    {Tin Tout : Tape Bool} {n : Nat}
    (h :
      ISCFFS.runConfig n
          { state :=
              ISCFFS.start
            tape := Tin } =
        { state :=
            ISCFFS.halt
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
          SCFFS.runConfig nStage
              { state :=
                  SCFFS.start
                tape := Tape.move Direction.right Tinput } =
            { state := SCFFS.halt
              tape := Tout } := by
  simpa [InputStageConfigurationsAndFinalFlagsScannerDescription] using
    seqSubroutine_runConfig_inv
      (A := BWSS)
      (B := SCFFS)
      (handoffMove := Direction.right)
      boolWordSuffixScannerDescription_subroutineReady
      stageConfigurationsAndFinalFlagsScannerDescription_subroutineReady
      (by
        simpa [InputStageConfigurationsAndFinalFlagsScannerDescription] using
          h)

theorem checkedDovetailLayoutScannerDescription_haltsWithTape_inputField_inv
    {bits : Word Bool} {Tout : Tape Bool}
    (h : CDL.HaltsWithTape bits Tout) :
    exists b : Bool,
    exists suffixTail : Word Bool,
    exists Tinput : Tape Bool,
    exists Tbody : Tape Bool,
    exists nInput : Nat,
    exists nStage : Nat,
    exists nReturn : Nat,
      bits = false :: false :: false :: true :: b :: suffixTail ∧
        BWSS.runConfig nInput
            { state := BWSS.start
              tape :=
                tapeAtCells
                  (List.append (transitionRemainderBits.reverse.map some)
                    [none])
                  ((b :: suffixTail).map some) } =
          { state := BWSS.halt
            tape := Tinput } ∧
        SCFFS.runConfig nStage
            { state :=
                SCFFS.start
              tape := Tape.move Direction.right Tinput } =
          { state := SCFFS.halt
            tape := Tbody } ∧
        RFM.runConfig nReturn
            { state := RFM.start
              tape := Tape.move Direction.right Tbody } =
          { state := RFM.halt
            tape := Tout } := by
  rcases
      checkedDovetailLayoutScannerDescription_haltsWithTape_afterTransition_inv
        h with
    ⟨b, suffixTail, Tbody, nRest, nReturn,
      hbits, hrestRun, hreturnRun⟩
  rcases
      inputStageConfigurationsAndFinalFlagsScannerDescription_runConfig_inv
        hrestRun with
    ⟨Tinput, hinput, hstage⟩
  rcases hinput with ⟨nInput, hinputRun, _hinputFirst⟩
  rcases hstage with ⟨nStage, hstageRun⟩
  exact
    ⟨b, suffixTail, Tinput, Tbody, nInput, nStage, nReturn,
      hbits, hinputRun, hstageRun, hreturnRun⟩

theorem stageConfigurationsAndFinalFlagsScannerDescription_runConfig_inv
    {Tin Tout : Tape Bool} {n : Nat}
    (h :
      SCFFS.runConfig n
          { state :=
              SCFFS.start
            tape := Tin } =
        { state :=
            SCFFS.halt
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
        exists nConfigs : Nat,
          CFFS.runConfig nConfigs
              { state :=
                  CFFS.start
                tape := Tape.move Direction.right Tstage } =
            { state := CFFS.halt
              tape := Tout } := by
  simpa [StageConfigurationsAndFinalFlagsScannerDescription] using
    seqSubroutine_runConfig_inv
      (A := NNSS)
      (B := CFFS)
      (handoffMove := Direction.right)
      DovetailStagePrefix.nonemptyNatSuffixScannerDescription_subroutineReady
      configurationsAndFinalFlagsScannerDescription_subroutineReady
      (by
        simpa [StageConfigurationsAndFinalFlagsScannerDescription] using h)

theorem checkedDovetailLayoutScannerDescription_haltsWithTape_stageField_inv
    {bits : Word Bool} {Tout : Tape Bool}
    (h : CDL.HaltsWithTape bits Tout) :
    exists b : Bool,
    exists suffixTail : Word Bool,
    exists Tinput : Tape Bool,
    exists Tstage : Tape Bool,
    exists Tbody : Tape Bool,
    exists nInput : Nat,
    exists nStage : Nat,
    exists nConfigs : Nat,
    exists nReturn : Nat,
      bits = false :: false :: false :: true :: b :: suffixTail ∧
        BWSS.runConfig nInput
            { state := BWSS.start
              tape :=
                tapeAtCells
                  (List.append (transitionRemainderBits.reverse.map some)
                    [none])
                  ((b :: suffixTail).map some) } =
          { state := BWSS.halt
            tape := Tinput } ∧
        NNSS.runConfig nStage
            { state := NNSS.start
              tape := Tape.move Direction.right Tinput } =
          { state := NNSS.halt
            tape := Tstage } ∧
        CFFS.runConfig nConfigs
            { state := CFFS.start
              tape := Tape.move Direction.right Tstage } =
          { state := CFFS.halt
            tape := Tbody } ∧
        RFM.runConfig nReturn
            { state := RFM.start
              tape := Tape.move Direction.right Tbody } =
          { state := RFM.halt
            tape := Tout } := by
  rcases
      checkedDovetailLayoutScannerDescription_haltsWithTape_inputField_inv h with
    ⟨b, suffixTail, Tinput, Tbody, nInput, nStageAll, nReturn,
      hbits, hinputRun, hstageAllRun, hreturnRun⟩
  rcases
      stageConfigurationsAndFinalFlagsScannerDescription_runConfig_inv
        hstageAllRun with
    ⟨Tstage, hstage, hconfigs⟩
  rcases hstage with ⟨nStage, hstageRun, _hstageFirst⟩
  rcases hconfigs with ⟨nConfigs, hconfigsRun⟩
  exact
    ⟨b, suffixTail, Tinput, Tstage, Tbody, nInput, nStage,
      nConfigs, nReturn, hbits, hinputRun, hstageRun, hconfigsRun,
      hreturnRun⟩

theorem configurationsAndFinalFlagsScannerDescription_runConfig_inv
    {Tin Tout : Tape Bool} {n : Nat}
    (h :
      CFFS.runConfig n
          { state := CFFS.start
            tape := Tin } =
        { state := CFFS.halt
          tape := Tout }) :
    exists Taccept : Tape Bool,
      (exists nAccept : Nat,
        CFS.runConfig nAccept
            { state := CFS.start
              tape := Tin } =
          { state := CFS.halt
            tape := Taccept } ∧
          forall k : Nat,
            k < nAccept ->
              (CFS.runConfig k
                { state := CFS.start
                  tape := Tin }).state ≠
                CFS.halt) ∧
        exists nRejectFlags : Nat,
          RCF.runConfig
              nRejectFlags
              { state := RCF.start
                tape := Tape.move Direction.right Taccept } =
            { state := RCF.halt
              tape := Tout } := by
  simpa [ConfigurationsAndFinalFlagsScannerDescription] using
    seqSubroutine_runConfig_inv
      (A := CFS)
      (B := RCF)
      (handoffMove := Direction.right)
      configurationSuffixScannerDescription_subroutineReady
      rejectConfigAndFinalFlagsScannerDescription_subroutineReady
      (by
        simpa [ConfigurationsAndFinalFlagsScannerDescription] using h)

theorem checkedDovetailLayoutScannerDescription_haltsWithTape_acceptConfig_inv
    {bits : Word Bool} {Tout : Tape Bool}
    (h : CDL.HaltsWithTape bits Tout) :
    exists b : Bool,
    exists suffixTail : Word Bool,
    exists Tinput : Tape Bool,
    exists Tstage : Tape Bool,
    exists Taccept : Tape Bool,
    exists Tbody : Tape Bool,
    exists nInput : Nat,
    exists nStage : Nat,
    exists nAccept : Nat,
    exists nRejectFlags : Nat,
    exists nReturn : Nat,
      bits = false :: false :: false :: true :: b :: suffixTail ∧
        BWSS.runConfig nInput
            { state := BWSS.start
              tape :=
                tapeAtCells
                  (List.append (transitionRemainderBits.reverse.map some)
                    [none])
                  ((b :: suffixTail).map some) } =
          { state := BWSS.halt
            tape := Tinput } ∧
        NNSS.runConfig nStage
            { state := NNSS.start
              tape := Tape.move Direction.right Tinput } =
          { state := NNSS.halt
            tape := Tstage } ∧
        CFS.runConfig nAccept
            { state := CFS.start
              tape := Tape.move Direction.right Tstage } =
          { state := CFS.halt
            tape := Taccept } ∧
        RCF.runConfig nRejectFlags
            { state := RCF.start
              tape := Tape.move Direction.right Taccept } =
          { state := RCF.halt
            tape := Tbody } ∧
        RFM.runConfig nReturn
            { state := RFM.start
              tape := Tape.move Direction.right Tbody } =
          { state := RFM.halt
            tape := Tout } := by
  rcases
      checkedDovetailLayoutScannerDescription_haltsWithTape_stageField_inv h with
    ⟨b, suffixTail, Tinput, Tstage, Tbody, nInput, nStage,
      nConfigs, nReturn, hbits, hinputRun, hstageRun, hconfigsRun,
      hreturnRun⟩
  rcases
      configurationsAndFinalFlagsScannerDescription_runConfig_inv
        hconfigsRun with
    ⟨Taccept, haccept, hrejectFlags⟩
  rcases haccept with ⟨nAccept, hacceptRun, _hacceptFirst⟩
  rcases hrejectFlags with ⟨nRejectFlags, hrejectFlagsRun⟩
  exact
    ⟨b, suffixTail, Tinput, Tstage, Taccept, Tbody, nInput, nStage,
      nAccept, nRejectFlags, nReturn, hbits, hinputRun, hstageRun,
      hacceptRun, hrejectFlagsRun, hreturnRun⟩

theorem rejectConfigAndFinalFlagsScannerDescription_runConfig_inv
    {Tin Tout : Tape Bool} {n : Nat}
    (h :
      RCF.runConfig n
          { state := RCF.start
            tape := Tin } =
        { state := RCF.halt
          tape := Tout }) :
    exists Treject : Tape Bool,
      (exists nReject : Nat,
        CFS.runConfig nReject
            { state := CFS.start
              tape := Tin } =
          { state := CFS.halt
            tape := Treject } ∧
          forall k : Nat,
            k < nReject ->
              (CFS.runConfig k
                { state := CFS.start
                  tape := Tin }).state ≠
                CFS.halt) ∧
        exists nFinalFlags : Nat,
          FHFS.runConfig nFinalFlags
              { state := FHFS.start
                tape := Tape.move Direction.right Treject } =
            { state := FHFS.halt
              tape := Tout } := by
  simpa [RejectConfigAndFinalFlagsScannerDescription] using
    seqSubroutine_runConfig_inv
      (A := CFS)
      (B := FHFS)
      (handoffMove := Direction.right)
      configurationSuffixScannerDescription_subroutineReady
      finalHitFlagsScannerDescription_subroutineReady
      (by
        simpa [RejectConfigAndFinalFlagsScannerDescription] using h)

theorem checkedDovetailLayoutScannerDescription_haltsWithTape_rejectConfig_inv
    {bits : Word Bool} {Tout : Tape Bool}
    (h : CDL.HaltsWithTape bits Tout) :
    exists b : Bool,
    exists suffixTail : Word Bool,
    exists Tinput : Tape Bool,
    exists Tstage : Tape Bool,
    exists Taccept : Tape Bool,
    exists Treject : Tape Bool,
    exists Tbody : Tape Bool,
    exists nInput : Nat,
    exists nStage : Nat,
    exists nAccept : Nat,
    exists nReject : Nat,
    exists nFinalFlags : Nat,
    exists nReturn : Nat,
      bits = false :: false :: false :: true :: b :: suffixTail ∧
        BWSS.runConfig nInput
            { state := BWSS.start
              tape :=
                tapeAtCells
                  (List.append (transitionRemainderBits.reverse.map some)
                    [none])
                  ((b :: suffixTail).map some) } =
          { state := BWSS.halt
            tape := Tinput } ∧
        NNSS.runConfig nStage
            { state := NNSS.start
              tape := Tape.move Direction.right Tinput } =
          { state := NNSS.halt
            tape := Tstage } ∧
        CFS.runConfig nAccept
            { state := CFS.start
              tape := Tape.move Direction.right Tstage } =
          { state := CFS.halt
            tape := Taccept } ∧
        CFS.runConfig nReject
            { state := CFS.start
              tape := Tape.move Direction.right Taccept } =
          { state := CFS.halt
            tape := Treject } ∧
        FHFS.runConfig nFinalFlags
            { state := FHFS.start
              tape := Tape.move Direction.right Treject } =
          { state := FHFS.halt
            tape := Tbody } ∧
        RFM.runConfig nReturn
            { state := RFM.start
              tape := Tape.move Direction.right Tbody } =
          { state := RFM.halt
            tape := Tout } := by
  rcases
      checkedDovetailLayoutScannerDescription_haltsWithTape_acceptConfig_inv h with
    ⟨b, suffixTail, Tinput, Tstage, Taccept, Tbody, nInput, nStage,
      nAccept, nRejectFlags, nReturn, hbits, hinputRun, hstageRun,
      hacceptRun, hrejectFlagsRun, hreturnRun⟩
  rcases
      rejectConfigAndFinalFlagsScannerDescription_runConfig_inv
        hrejectFlagsRun with
    ⟨Treject, hreject, hfinalFlags⟩
  rcases hreject with ⟨nReject, hrejectRun, _hrejectFirst⟩
  rcases hfinalFlags with ⟨nFinalFlags, hfinalFlagsRun⟩
  exact
    ⟨b, suffixTail, Tinput, Tstage, Taccept, Treject, Tbody, nInput,
      nStage, nAccept, nReject, nFinalFlags, nReturn, hbits, hinputRun,
      hstageRun, hacceptRun, hrejectRun, hfinalFlagsRun, hreturnRun⟩

theorem finalHitFlagsScannerDescription_runConfig_inv
    {Tin Tout : Tape Bool} {n : Nat}
    (h :
      FHFS.runConfig n
          { state := FHFS.start
            tape := Tin } =
        { state := FHFS.halt
          tape := Tout }) :
    exists TacceptHit : Tape Bool,
      (exists nAcceptHit : Nat,
        BSS.runConfig nAcceptHit
            { state := BSS.start
              tape := Tin } =
          { state := BSS.halt
            tape := TacceptHit } ∧
          forall k : Nat,
            k < nAcceptHit ->
              (BSS.runConfig k
                { state := BSS.start
                  tape := Tin }).state ≠
                BSS.halt) ∧
        exists nRejectHit : Nat,
          BFS.runConfig nRejectHit
              { state := BFS.start
                tape := Tape.move Direction.right TacceptHit } =
            { state := BFS.halt
              tape := Tout } := by
  simpa [FinalHitFlagsScannerDescription] using
    seqSubroutine_runConfig_inv
      (A := BSS)
      (B := BFS)
      (handoffMove := Direction.right)
      boolSuffixScannerDescription_subroutineReady
      boolFinalScannerDescription_subroutineReady
      (by
        simpa [FinalHitFlagsScannerDescription] using h)

theorem checkedDovetailLayoutScannerDescription_haltsWithTape_finalFlags_inv
    {bits : Word Bool} {Tout : Tape Bool}
    (h : CDL.HaltsWithTape bits Tout) :
    exists b : Bool,
    exists suffixTail : Word Bool,
    exists Tinput : Tape Bool,
    exists Tstage : Tape Bool,
    exists Taccept : Tape Bool,
    exists Treject : Tape Bool,
    exists TacceptHit : Tape Bool,
    exists Tbody : Tape Bool,
    exists nInput : Nat,
    exists nStage : Nat,
    exists nAccept : Nat,
    exists nReject : Nat,
    exists nAcceptHit : Nat,
    exists nRejectHit : Nat,
    exists nReturn : Nat,
      bits = false :: false :: false :: true :: b :: suffixTail ∧
        BWSS.runConfig nInput
            { state := BWSS.start
              tape :=
                tapeAtCells
                  (List.append (transitionRemainderBits.reverse.map some)
                    [none])
                  ((b :: suffixTail).map some) } =
          { state := BWSS.halt
            tape := Tinput } ∧
        NNSS.runConfig nStage
            { state := NNSS.start
              tape := Tape.move Direction.right Tinput } =
          { state := NNSS.halt
            tape := Tstage } ∧
        CFS.runConfig nAccept
            { state := CFS.start
              tape := Tape.move Direction.right Tstage } =
          { state := CFS.halt
            tape := Taccept } ∧
        CFS.runConfig nReject
            { state := CFS.start
              tape := Tape.move Direction.right Taccept } =
          { state := CFS.halt
            tape := Treject } ∧
        BSS.runConfig nAcceptHit
            { state := BSS.start
              tape := Tape.move Direction.right Treject } =
          { state := BSS.halt
            tape := TacceptHit } ∧
        BFS.runConfig nRejectHit
            { state := BFS.start
              tape := Tape.move Direction.right TacceptHit } =
          { state := BFS.halt
            tape := Tbody } ∧
        RFM.runConfig nReturn
            { state := RFM.start
              tape := Tape.move Direction.right Tbody } =
          { state := RFM.halt
            tape := Tout } := by
  rcases
      checkedDovetailLayoutScannerDescription_haltsWithTape_rejectConfig_inv h with
    ⟨b, suffixTail, Tinput, Tstage, Taccept, Treject, Tbody, nInput,
      nStage, nAccept, nReject, nFinalFlags, nReturn, hbits, hinputRun,
      hstageRun, hacceptRun, hrejectRun, hfinalFlagsRun, hreturnRun⟩
  rcases finalHitFlagsScannerDescription_runConfig_inv hfinalFlagsRun with
    ⟨TacceptHit, hacceptHit, hrejectHit⟩
  rcases hacceptHit with ⟨nAcceptHit, hacceptHitRun, _hacceptHitFirst⟩
  rcases hrejectHit with ⟨nRejectHit, hrejectHitRun⟩
  exact
    ⟨b, suffixTail, Tinput, Tstage, Taccept, Treject, TacceptHit, Tbody,
      nInput, nStage, nAccept, nReject, nAcceptHit, nRejectHit, nReturn,
      hbits, hinputRun, hstageRun, hacceptRun, hrejectRun, hacceptHitRun,
      hrejectHitRun, hreturnRun⟩

end DovetailLayoutScanner
end CanonicalLayouts
end EncodedRewriters

end Computability
end FoC

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

namespace EncodedRewriters
namespace CanonicalLayouts
namespace DovetailLayoutScanner

open FoC.Computability.DovetailInitialLayoutInitializer
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner

def MarkedDovetailLayoutBodyReturnDescription : MachineDescription :=
  MachineDescription.seqSubroutine
    MarkedDovetailLayoutBodyScannerDescription
    ReturnToFirstMarkerDescription
    Direction.right

theorem markedDovetailLayoutBodyReturnDescription_subroutineReady :
    MarkedDovetailLayoutBodyReturnDescription.SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    markedDovetailLayoutBodyScannerDescription_subroutineReady
    returnToFirstMarkerDescription_subroutineReady

theorem markFirstTransitionBitDescription_haltsWithTape_inv
    {bits : Word Bool} {T : Tape Bool}
    (h : MarkFirstTransitionBitDescription.HaltsWithTape bits T) :
    exists tail : Word Bool,
      bits = false :: false :: tail ∧
        T =
          (config MarkFirstTransitionBitDescription.halt []
            (none :: some false :: tail.map some)).tape := by
  rcases MachineDescription.runConfig_eq_halt_of_haltsWithTape h with
    ⟨n, hn⟩
  cases bits with
  | nil =>
      have hstep :
          MarkFirstTransitionBitDescription.stepConfig
              (MarkFirstTransitionBitDescription.initial []) = none := by
        native_decide
      have hrun :=
        MachineDescription.runConfig_of_stepConfig_none hstep n
      have hstate : 0 = 9 := by
        simpa [MarkFirstTransitionBitDescription,
          MachineDescription.initial] using
          congrArg MachineDescription.Configuration.state
            (hrun.symm.trans hn)
      omega
  | cons b rest =>
      cases b
      · cases rest with
        | nil =>
            cases n with
            | zero =>
                simp [MarkFirstTransitionBitDescription,
                  MachineDescription.runConfig] at hn
            | succ n =>
                let c1 : MachineDescription.Configuration :=
                  { state := 1
                    tape := tapeAtCells [none] [] }
                have hstep0 :
                    MarkFirstTransitionBitDescription.stepConfig
                        (MarkFirstTransitionBitDescription.initial [false]) =
                      some c1 := by
                  simp [c1, MarkFirstTransitionBitDescription,
                    tapeAtCells, keepMove, writeMove,
                    MachineDescription.initial,
                    MachineDescription.stepConfig,
                    MachineDescription.lookupTransition,
                    MachineDescription.Matches,
                    MachineDescription.transition, Tape.input, Tape.read,
                    Tape.write, Tape.move, Tape.moveRight]
                have hrun :
                    MarkFirstTransitionBitDescription.runConfig (Nat.succ n)
                        (MarkFirstTransitionBitDescription.initial [false]) =
                      MarkFirstTransitionBitDescription.runConfig n c1 := by
                  simp [MachineDescription.runConfig, hstep0]
                have hstep1 :
                    MarkFirstTransitionBitDescription.stepConfig c1 = none := by
                  simp [c1, MarkFirstTransitionBitDescription, tapeAtCells,
                    keepMove, writeMove, MachineDescription.stepConfig,
                    MachineDescription.lookupTransition,
                    MachineDescription.Matches,
                    MachineDescription.transition, Tape.read]
                have hstay :=
                  MachineDescription.runConfig_of_stepConfig_none hstep1 n
                have hrunFinal :
                    MarkFirstTransitionBitDescription.runConfig (Nat.succ n)
                        (MarkFirstTransitionBitDescription.initial [false]) =
                      c1 :=
                  hrun.trans hstay
                have hstate : 1 = 9 := by
                  simpa [c1, MarkFirstTransitionBitDescription] using
                    congrArg MachineDescription.Configuration.state
                      (hrunFinal.symm.trans hn)
                omega
        | cons c tail =>
            cases c
            · refine ⟨tail, rfl, ?_⟩
              cases n with
              | zero =>
                  simp [MarkFirstTransitionBitDescription,
                    MachineDescription.runConfig] at hn
              | succ n =>
                  cases n with
                  | zero =>
                      simp [MarkFirstTransitionBitDescription,
                        keepMove, writeMove,
                        MachineDescription.runConfig,
                        MachineDescription.stepConfig,
                        MachineDescription.lookupTransition,
                        MachineDescription.Matches,
                        MachineDescription.transition, Tape.input,
                        Tape.read, Tape.write, Tape.move, Tape.moveRight]
                        at hn
                  | succ k =>
                      have hrun :
                          MarkFirstTransitionBitDescription.runConfig
                              (Nat.succ (Nat.succ k))
                              (MarkFirstTransitionBitDescription.initial
                                (false :: false :: tail)) =
                            config MarkFirstTransitionBitDescription.halt []
                              (none :: some false :: tail.map some) := by
                        rw [show Nat.succ (Nat.succ k) = 2 + k by omega]
                        rw [MachineDescription.runConfig_add]
                        have h2 :
                            MarkFirstTransitionBitDescription.runConfig 2
                                (MarkFirstTransitionBitDescription.initial
                                  (false :: false :: tail)) =
                              config MarkFirstTransitionBitDescription.halt []
                                (none :: some false :: tail.map some) := by
                          simpa [MachineDescription.initial, config,
                            tapeAtCells] using
                            run_markFirstTransitionBit_raw tail
                        rw [h2]
                        exact
                          MachineDescription.runConfig_halt
                            markFirstTransitionBitDescription_haltTransitionFree
                            (config MarkFirstTransitionBitDescription.halt []
                              (none :: some false :: tail.map some)).tape k
                      let cfgGood : MachineDescription.Configuration :=
                        config MarkFirstTransitionBitDescription.halt []
                          (none :: some false :: tail.map some)
                      have hcfg :
                          cfgGood =
                            { state := MarkFirstTransitionBitDescription.halt
                              tape := T } := by
                        simpa [cfgGood] using hrun.symm.trans hn
                      exact
                        (congrArg MachineDescription.Configuration.tape
                          hcfg).symm
            · cases n with
              | zero =>
                  simp [MarkFirstTransitionBitDescription,
                    MachineDescription.runConfig] at hn
              | succ n =>
                  let c1 : MachineDescription.Configuration :=
                    { state := 1
                      tape := tapeAtCells [none]
                        (some true :: tail.map some) }
                  have hstep0 :
                      MarkFirstTransitionBitDescription.stepConfig
                          (MarkFirstTransitionBitDescription.initial
                            (false :: true :: tail)) =
                        some c1 := by
                    simp [c1, MarkFirstTransitionBitDescription,
                      tapeAtCells, keepMove, writeMove,
                      MachineDescription.initial,
                      MachineDescription.stepConfig,
                      MachineDescription.lookupTransition,
                      MachineDescription.Matches,
                      MachineDescription.transition, Tape.input, Tape.read,
                      Tape.write, Tape.move, Tape.moveRight]
                  have hrun :
                      MarkFirstTransitionBitDescription.runConfig
                          (Nat.succ n)
                          (MarkFirstTransitionBitDescription.initial
                            (false :: true :: tail)) =
                        MarkFirstTransitionBitDescription.runConfig n c1 := by
                    simp [MachineDescription.runConfig, hstep0]
                  have hstep1 :
                      MarkFirstTransitionBitDescription.stepConfig c1 =
                        none := by
                    simp [c1, MarkFirstTransitionBitDescription, tapeAtCells,
                      keepMove, writeMove, MachineDescription.stepConfig,
                      MachineDescription.lookupTransition,
                      MachineDescription.Matches,
                      MachineDescription.transition, Tape.read]
                  have hstay :=
                    MachineDescription.runConfig_of_stepConfig_none hstep1 n
                  have hrunFinal :
                      MarkFirstTransitionBitDescription.runConfig
                          (Nat.succ n)
                          (MarkFirstTransitionBitDescription.initial
                            (false :: true :: tail)) =
                        c1 :=
                    hrun.trans hstay
                  have hstate : 1 = 9 := by
                    simpa [c1, MarkFirstTransitionBitDescription] using
                      congrArg MachineDescription.Configuration.state
                        (hrunFinal.symm.trans hn)
                  omega
      · have hstep :
            MarkFirstTransitionBitDescription.stepConfig
                (MarkFirstTransitionBitDescription.initial (true :: rest)) =
              none := by
          simp [MarkFirstTransitionBitDescription, keepMove, writeMove,
            MachineDescription.initial, MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.input, Tape.read]
        have hrun :=
          MachineDescription.runConfig_of_stepConfig_none hstep n
        have hstate : 0 = 9 := by
          simpa [MarkFirstTransitionBitDescription,
            MachineDescription.initial] using
            congrArg MachineDescription.Configuration.state
              (hrun.symm.trans hn)
        omega

theorem checkedDovetailLayoutScannerDescription_haltsWithTape_marker_inv
    {bits : Word Bool} {Tout : Tape Bool}
    (h : CheckedDovetailLayoutScannerDescription.HaltsWithTape bits Tout) :
    exists tail : Word Bool,
    exists nB : Nat,
      bits = false :: false :: tail ∧
        MarkedDovetailLayoutBodyReturnDescription.runConfig nB
            { state := MarkedDovetailLayoutBodyReturnDescription.start
              tape :=
                Tape.move Direction.right
                  (config MarkFirstTransitionBitDescription.halt []
                    (none :: some false :: tail.map some)).tape } =
          { state := MarkedDovetailLayoutBodyReturnDescription.halt
            tape := Tout } := by
  rcases
      MachineDescription.seqSubroutine_haltsWithTape_inv
        (A := MarkFirstTransitionBitDescription)
        (B := MarkedDovetailLayoutBodyReturnDescription)
        (handoffMove := Direction.right)
        markFirstTransitionBitDescription_subroutineReady
        markedDovetailLayoutBodyReturnDescription_subroutineReady
        (by
          simpa [CheckedDovetailLayoutScannerDescription,
            MarkedDovetailLayoutBodyReturnDescription] using h) with
    ⟨Tmid, hmark, nB, hbody⟩
  rcases markFirstTransitionBitDescription_haltsWithTape_inv hmark with
    ⟨tail, hbits, hTmid⟩
  refine ⟨tail, nB, hbits, ?_⟩
  rw [hTmid] at hbody
  exact hbody

theorem markedDovetailLayoutBodyReturnDescription_runConfig_inv
    {Tin Tout : Tape Bool} {n : Nat}
    (h :
      MarkedDovetailLayoutBodyReturnDescription.runConfig n
          { state := MarkedDovetailLayoutBodyReturnDescription.start
            tape := Tin } =
        { state := MarkedDovetailLayoutBodyReturnDescription.halt
          tape := Tout }) :
    exists Tbody : Tape Bool,
      (exists nBody : Nat,
        MarkedDovetailLayoutBodyScannerDescription.runConfig nBody
            { state := MarkedDovetailLayoutBodyScannerDescription.start
              tape := Tin } =
          { state := MarkedDovetailLayoutBodyScannerDescription.halt
            tape := Tbody } ∧
          forall k : Nat,
            k < nBody ->
              (MarkedDovetailLayoutBodyScannerDescription.runConfig k
                { state := MarkedDovetailLayoutBodyScannerDescription.start
                  tape := Tin }).state ≠
                MarkedDovetailLayoutBodyScannerDescription.halt) ∧
        exists nReturn : Nat,
          ReturnToFirstMarkerDescription.runConfig nReturn
              { state := ReturnToFirstMarkerDescription.start
                tape := Tape.move Direction.right Tbody } =
            { state := ReturnToFirstMarkerDescription.halt
              tape := Tout } := by
  simpa [MarkedDovetailLayoutBodyReturnDescription] using
    MachineDescription.seqSubroutine_runConfig_inv
      (A := MarkedDovetailLayoutBodyScannerDescription)
      (B := ReturnToFirstMarkerDescription)
      (handoffMove := Direction.right)
      markedDovetailLayoutBodyScannerDescription_subroutineReady
      returnToFirstMarkerDescription_subroutineReady
      (by simpa [MarkedDovetailLayoutBodyReturnDescription] using h)

theorem markedDovetailLayoutBodyScannerDescription_runConfig_inv
    {Tin Tout : Tape Bool} {n : Nat}
    (h :
      MarkedDovetailLayoutBodyScannerDescription.runConfig n
          { state := MarkedDovetailLayoutBodyScannerDescription.start
            tape := Tin } =
        { state := MarkedDovetailLayoutBodyScannerDescription.halt
          tape := Tout }) :
    exists Ttransition : Tape Bool,
      (exists nTransition : Nat,
        TransitionRemainderPrefixScannerDescription.runConfig nTransition
            { state := TransitionRemainderPrefixScannerDescription.start
              tape := Tin } =
          { state := TransitionRemainderPrefixScannerDescription.halt
            tape := Ttransition } ∧
          forall k : Nat,
            k < nTransition ->
              (TransitionRemainderPrefixScannerDescription.runConfig k
                { state := TransitionRemainderPrefixScannerDescription.start
                  tape := Tin }).state ≠
                TransitionRemainderPrefixScannerDescription.halt) ∧
        exists nRest : Nat,
          InputStageConfigurationsAndFinalFlagsScannerDescription.runConfig nRest
              { state :=
                  InputStageConfigurationsAndFinalFlagsScannerDescription.start
                tape := Tape.move Direction.right Ttransition } =
            { state :=
                InputStageConfigurationsAndFinalFlagsScannerDescription.halt
              tape := Tout } := by
  simpa [MarkedDovetailLayoutBodyScannerDescription] using
    MachineDescription.seqSubroutine_runConfig_inv
      (A := TransitionRemainderPrefixScannerDescription)
      (B := InputStageConfigurationsAndFinalFlagsScannerDescription)
        (handoffMove := Direction.right)
      transitionRemainderPrefixScannerDescription_subroutineReady
      inputStageConfigurationsAndFinalFlagsScannerDescription_subroutineReady
      (by simpa [MarkedDovetailLayoutBodyScannerDescription] using h)

theorem checkedDovetailLayoutScannerDescription_haltsWithTape_body_return_inv
    {bits : Word Bool} {Tout : Tape Bool}
    (h : CheckedDovetailLayoutScannerDescription.HaltsWithTape bits Tout) :
    exists tail : Word Bool,
    exists Tbody : Tape Bool,
    exists nBody : Nat,
    exists nReturn : Nat,
      bits = false :: false :: tail ∧
        MarkedDovetailLayoutBodyScannerDescription.runConfig nBody
            { state := MarkedDovetailLayoutBodyScannerDescription.start
              tape := tapeAtCells [none] (some false :: tail.map some) } =
          { state := MarkedDovetailLayoutBodyScannerDescription.halt
            tape := Tbody } ∧
        ReturnToFirstMarkerDescription.runConfig nReturn
            { state := ReturnToFirstMarkerDescription.start
              tape := Tape.move Direction.right Tbody } =
          { state := ReturnToFirstMarkerDescription.halt
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
          (config MarkFirstTransitionBitDescription.halt []
            (none :: some false :: tail.map some)).tape =
        tapeAtCells [none] (some false :: tail.map some) := by
    simp [config, tapeAtCells, Tape.move, Tape.moveRight]
  simpa [hmove] using hbodyRun

theorem runConfig_state_ne_halt_of_reaches_stuck
    {D : MachineDescription}
    {c stuck : MachineDescription.Configuration} {k n : Nat}
    (hD : D.HaltTransitionFree)
    (hprefix : D.runConfig k c = stuck)
    (hstep : D.stepConfig stuck = none)
    (hstuck : stuck.state ≠ D.halt) :
    (D.runConfig n c).state ≠ D.halt := by
  by_cases hle : k ≤ n
  · intro hhalt
    let rem := n - k
    have hn : n = k + rem := by omega
    have hrun :
        D.runConfig n c = D.runConfig rem stuck := by
      rw [hn, MachineDescription.runConfig_add, hprefix]
    have hstay :=
      MachineDescription.runConfig_of_stepConfig_none hstep rem
    have hstate : stuck.state = D.halt := by
      have hstateEq :
          (D.runConfig n c).state = stuck.state := by
        rw [hrun, hstay]
      exact hstateEq ▸ hhalt
    exact hstuck hstate
  · intro hhalt
    let rem := k - n
    have hk : k = n + rem := by omega
    have hrunHalt :
        D.runConfig n c =
          { state := D.halt, tape := (D.runConfig n c).tape } := by
      cases hcfg : D.runConfig n c with
      | mk state tape =>
          simp [hcfg] at hhalt ⊢
          exact hhalt
    have hstay :
        D.runConfig rem (D.runConfig n c) =
          D.runConfig n c := by
      rw [hrunHalt]
      exact MachineDescription.runConfig_halt hD
        (D.runConfig n c).tape rem
    have hstate : stuck.state = D.halt := by
      have hstuckEq :
          stuck = D.runConfig n c := by
        rw [← hprefix, hk, MachineDescription.runConfig_add, hstay]
      rw [hstuckEq]
      exact hhalt
    exact hstuck hstate

theorem transitionRemainderPrefixScannerDescription_markedTail_inv
    {tail : Word Bool} {T : Tape Bool} {n : Nat}
    (h :
      TransitionRemainderPrefixScannerDescription.runConfig n
          { state := TransitionRemainderPrefixScannerDescription.start
            tape := tapeAtCells [none] (some false :: tail.map some) } =
        { state := TransitionRemainderPrefixScannerDescription.halt
          tape := T }) :
    exists b : Bool,
    exists suffixTail : Word Bool,
      tail = false :: true :: b :: suffixTail ∧
        T =
          (transitionRemainderHandoffConfigWithBase [none]
            (b :: suffixTail)).tape := by
  let start : MachineDescription.Configuration :=
    { state := TransitionRemainderPrefixScannerDescription.start
      tape := tapeAtCells [none] (some false :: tail.map some) }
  have hhaltState :
      (TransitionRemainderPrefixScannerDescription.runConfig n start).state =
        TransitionRemainderPrefixScannerDescription.halt := by
    simpa [start] using
      congrArg MachineDescription.Configuration.state h
  cases tail with
  | nil =>
      let stuck :=
        TransitionRemainderPrefixScannerDescription.runConfig 1 start
      have hstep :
          TransitionRemainderPrefixScannerDescription.stepConfig stuck =
            none := by
        simp [stuck, start, TransitionRemainderPrefixScannerDescription,
          tapeAtCells, keepMove, MachineDescription.runConfig,
          MachineDescription.stepConfig,
          MachineDescription.lookupTransition,
          MachineDescription.Matches, MachineDescription.transition,
          Tape.read, Tape.write, Tape.move, Tape.moveRight]
      have hstuck :
          stuck.state ≠
            TransitionRemainderPrefixScannerDescription.halt := by
        simp [stuck, start, TransitionRemainderPrefixScannerDescription,
          tapeAtCells, keepMove, MachineDescription.runConfig,
          MachineDescription.stepConfig,
          MachineDescription.lookupTransition,
          MachineDescription.Matches, MachineDescription.transition,
          Tape.read, Tape.write, Tape.move, Tape.moveRight]
      exact False.elim
        (runConfig_state_ne_halt_of_reaches_stuck
          transitionRemainderPrefixScannerDescription_haltTransitionFree
          (D := TransitionRemainderPrefixScannerDescription)
          (c := start) (stuck := stuck) (k := 1) (n := n)
          rfl hstep hstuck hhaltState)
  | cons first rest =>
      cases first
      · cases rest with
        | nil =>
            let stuck :=
              TransitionRemainderPrefixScannerDescription.runConfig 2 start
            have hstep :
                TransitionRemainderPrefixScannerDescription.stepConfig
                    stuck = none := by
              simp [stuck, start,
                TransitionRemainderPrefixScannerDescription,
                tapeAtCells, keepMove, MachineDescription.runConfig,
                MachineDescription.stepConfig,
                MachineDescription.lookupTransition,
                MachineDescription.Matches, MachineDescription.transition,
                Tape.read, Tape.write, Tape.move, Tape.moveRight]
            have hstuck :
                stuck.state ≠
                  TransitionRemainderPrefixScannerDescription.halt := by
              simp [stuck, start,
                TransitionRemainderPrefixScannerDescription,
                tapeAtCells, keepMove, MachineDescription.runConfig,
                MachineDescription.stepConfig,
                MachineDescription.lookupTransition,
                MachineDescription.Matches, MachineDescription.transition,
                Tape.read, Tape.write, Tape.move, Tape.moveRight]
            exact False.elim
              (runConfig_state_ne_halt_of_reaches_stuck
                transitionRemainderPrefixScannerDescription_haltTransitionFree
                (D := TransitionRemainderPrefixScannerDescription)
                (c := start) (stuck := stuck) (k := 2) (n := n)
                rfl hstep hstuck hhaltState)
        | cons second restTail =>
            cases second
            · let stuck :=
                TransitionRemainderPrefixScannerDescription.runConfig 2
                  start
              have hstep :
                  TransitionRemainderPrefixScannerDescription.stepConfig
                      stuck = none := by
                cases restTail <;>
                  simp [stuck, start,
                    TransitionRemainderPrefixScannerDescription,
                    tapeAtCells, keepMove, MachineDescription.runConfig,
                    MachineDescription.stepConfig,
                    MachineDescription.lookupTransition,
                    MachineDescription.Matches, MachineDescription.transition,
                    Tape.read, Tape.write, Tape.move, Tape.moveRight]
              have hstuck :
                  stuck.state ≠
                    TransitionRemainderPrefixScannerDescription.halt := by
                cases restTail <;>
                  simp [stuck, start,
                    TransitionRemainderPrefixScannerDescription,
                    tapeAtCells, keepMove, MachineDescription.runConfig,
                    MachineDescription.stepConfig,
                    MachineDescription.lookupTransition,
                    MachineDescription.Matches, MachineDescription.transition,
                    Tape.read, Tape.write, Tape.move, Tape.moveRight]
              exact False.elim
                (runConfig_state_ne_halt_of_reaches_stuck
                  transitionRemainderPrefixScannerDescription_haltTransitionFree
                  (D := TransitionRemainderPrefixScannerDescription)
                  (c := start) (stuck := stuck) (k := 2) (n := n)
                  rfl hstep hstuck hhaltState)
            · cases restTail with
              | nil =>
                  let stuck :=
                    TransitionRemainderPrefixScannerDescription.runConfig 3
                      start
                  have hstep :
                      TransitionRemainderPrefixScannerDescription.stepConfig
                          stuck = none := by
                    simp [stuck, start,
                      TransitionRemainderPrefixScannerDescription,
                      tapeAtCells, keepMove, MachineDescription.runConfig,
                      MachineDescription.stepConfig,
                      MachineDescription.lookupTransition,
                      MachineDescription.Matches,
                      MachineDescription.transition, Tape.read, Tape.write,
                      Tape.move, Tape.moveRight]
                  have hstuck :
                      stuck.state ≠
                        TransitionRemainderPrefixScannerDescription.halt := by
                    simp [stuck, start,
                      TransitionRemainderPrefixScannerDescription,
                      tapeAtCells, keepMove, MachineDescription.runConfig,
                      MachineDescription.stepConfig,
                      MachineDescription.lookupTransition,
                      MachineDescription.Matches,
                      MachineDescription.transition, Tape.read, Tape.write,
                      Tape.move, Tape.moveRight]
                  exact False.elim
                    (runConfig_state_ne_halt_of_reaches_stuck
                      transitionRemainderPrefixScannerDescription_haltTransitionFree
                      (D := TransitionRemainderPrefixScannerDescription)
                      (c := start) (stuck := stuck) (k := 3) (n := n)
                      rfl hstep hstuck hhaltState)
              | cons b suffixTail =>
                  refine ⟨b, suffixTail, rfl, ?_⟩
                  rcases
                      run_transitionRemainderPrefix_raw_to_handoff_withBase
                        [none] b suffixTail with
                    ⟨steps, hsteps⟩
                  have hstepsHalt :
                      TransitionRemainderPrefixScannerDescription.runConfig
                          steps start =
                        { state :=
                            TransitionRemainderPrefixScannerDescription.halt
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
          TransitionRemainderPrefixScannerDescription.runConfig 1 start
        have hstep :
            TransitionRemainderPrefixScannerDescription.stepConfig stuck =
              none := by
          cases rest <;>
            simp [stuck, start, TransitionRemainderPrefixScannerDescription,
              tapeAtCells, keepMove, MachineDescription.runConfig,
              MachineDescription.stepConfig,
              MachineDescription.lookupTransition,
              MachineDescription.Matches, MachineDescription.transition,
              Tape.read, Tape.write, Tape.move, Tape.moveRight]
        have hstuck :
            stuck.state ≠
              TransitionRemainderPrefixScannerDescription.halt := by
          cases rest <;>
            simp [stuck, start, TransitionRemainderPrefixScannerDescription,
              tapeAtCells, keepMove, MachineDescription.runConfig,
              MachineDescription.stepConfig,
              MachineDescription.lookupTransition,
              MachineDescription.Matches, MachineDescription.transition,
              Tape.read, Tape.write, Tape.move, Tape.moveRight]
        exact False.elim
          (runConfig_state_ne_halt_of_reaches_stuck
            transitionRemainderPrefixScannerDescription_haltTransitionFree
            (D := TransitionRemainderPrefixScannerDescription)
            (c := start) (stuck := stuck) (k := 1) (n := n)
            rfl hstep hstuck hhaltState)

theorem checkedDovetailLayoutScannerDescription_haltsWithTape_transition_inv
    {bits : Word Bool} {Tout : Tape Bool}
    (h : CheckedDovetailLayoutScannerDescription.HaltsWithTape bits Tout) :
    exists tail : Word Bool,
    exists Ttransition : Tape Bool,
    exists Tbody : Tape Bool,
    exists nTransition : Nat,
    exists nRest : Nat,
    exists nReturn : Nat,
      bits = false :: false :: tail ∧
        TransitionRemainderPrefixScannerDescription.runConfig nTransition
            { state := TransitionRemainderPrefixScannerDescription.start
              tape := tapeAtCells [none] (some false :: tail.map some) } =
          { state := TransitionRemainderPrefixScannerDescription.halt
            tape := Ttransition } ∧
        InputStageConfigurationsAndFinalFlagsScannerDescription.runConfig nRest
            { state :=
                InputStageConfigurationsAndFinalFlagsScannerDescription.start
              tape := Tape.move Direction.right Ttransition } =
          { state :=
              InputStageConfigurationsAndFinalFlagsScannerDescription.halt
            tape := Tbody } ∧
        ReturnToFirstMarkerDescription.runConfig nReturn
            { state := ReturnToFirstMarkerDescription.start
              tape := Tape.move Direction.right Tbody } =
          { state := ReturnToFirstMarkerDescription.halt
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
    (h : CheckedDovetailLayoutScannerDescription.HaltsWithTape bits Tout) :
    exists b : Bool,
    exists suffixTail : Word Bool,
    exists Tbody : Tape Bool,
    exists nRest : Nat,
    exists nReturn : Nat,
      bits = false :: false :: false :: true :: b :: suffixTail ∧
        InputStageConfigurationsAndFinalFlagsScannerDescription.runConfig nRest
            { state :=
                InputStageConfigurationsAndFinalFlagsScannerDescription.start
              tape :=
                tapeAtCells
                  (List.append (transitionRemainderBits.reverse.map some)
                    [none])
                  ((b :: suffixTail).map some) } =
          { state :=
              InputStageConfigurationsAndFinalFlagsScannerDescription.halt
            tape := Tbody } ∧
        ReturnToFirstMarkerDescription.runConfig nReturn
            { state := ReturnToFirstMarkerDescription.start
              tape := Tape.move Direction.right Tbody } =
          { state := ReturnToFirstMarkerDescription.halt
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
      InputStageConfigurationsAndFinalFlagsScannerDescription.runConfig n
          { state :=
              InputStageConfigurationsAndFinalFlagsScannerDescription.start
            tape := Tin } =
        { state :=
            InputStageConfigurationsAndFinalFlagsScannerDescription.halt
          tape := Tout }) :
    exists Tinput : Tape Bool,
      (exists nInput : Nat,
        BoolWordSuffixScannerDescription.runConfig nInput
            { state := BoolWordSuffixScannerDescription.start
              tape := Tin } =
          { state := BoolWordSuffixScannerDescription.halt
            tape := Tinput } ∧
          forall k : Nat,
            k < nInput ->
              (BoolWordSuffixScannerDescription.runConfig k
                { state := BoolWordSuffixScannerDescription.start
                  tape := Tin }).state ≠
                BoolWordSuffixScannerDescription.halt) ∧
        exists nStage : Nat,
          StageConfigurationsAndFinalFlagsScannerDescription.runConfig nStage
              { state :=
                  StageConfigurationsAndFinalFlagsScannerDescription.start
                tape := Tape.move Direction.right Tinput } =
            { state := StageConfigurationsAndFinalFlagsScannerDescription.halt
              tape := Tout } := by
  simpa [InputStageConfigurationsAndFinalFlagsScannerDescription] using
    MachineDescription.seqSubroutine_runConfig_inv
      (A := BoolWordSuffixScannerDescription)
      (B := StageConfigurationsAndFinalFlagsScannerDescription)
      (handoffMove := Direction.right)
      boolWordSuffixScannerDescription_subroutineReady
      stageConfigurationsAndFinalFlagsScannerDescription_subroutineReady
      (by
        simpa [InputStageConfigurationsAndFinalFlagsScannerDescription] using
          h)

theorem checkedDovetailLayoutScannerDescription_haltsWithTape_inputField_inv
    {bits : Word Bool} {Tout : Tape Bool}
    (h : CheckedDovetailLayoutScannerDescription.HaltsWithTape bits Tout) :
    exists b : Bool,
    exists suffixTail : Word Bool,
    exists Tinput : Tape Bool,
    exists Tbody : Tape Bool,
    exists nInput : Nat,
    exists nStage : Nat,
    exists nReturn : Nat,
      bits = false :: false :: false :: true :: b :: suffixTail ∧
        BoolWordSuffixScannerDescription.runConfig nInput
            { state := BoolWordSuffixScannerDescription.start
              tape :=
                tapeAtCells
                  (List.append (transitionRemainderBits.reverse.map some)
                    [none])
                  ((b :: suffixTail).map some) } =
          { state := BoolWordSuffixScannerDescription.halt
            tape := Tinput } ∧
        StageConfigurationsAndFinalFlagsScannerDescription.runConfig nStage
            { state :=
                StageConfigurationsAndFinalFlagsScannerDescription.start
              tape := Tape.move Direction.right Tinput } =
          { state := StageConfigurationsAndFinalFlagsScannerDescription.halt
            tape := Tbody } ∧
        ReturnToFirstMarkerDescription.runConfig nReturn
            { state := ReturnToFirstMarkerDescription.start
              tape := Tape.move Direction.right Tbody } =
          { state := ReturnToFirstMarkerDescription.halt
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
      StageConfigurationsAndFinalFlagsScannerDescription.runConfig n
          { state :=
              StageConfigurationsAndFinalFlagsScannerDescription.start
            tape := Tin } =
        { state :=
            StageConfigurationsAndFinalFlagsScannerDescription.halt
          tape := Tout }) :
    exists Tstage : Tape Bool,
      (exists nStage : Nat,
        DovetailStagePrefix.NatSuffixScannerDescription.runConfig nStage
            { state := DovetailStagePrefix.NatSuffixScannerDescription.start
              tape := Tin } =
          { state := DovetailStagePrefix.NatSuffixScannerDescription.halt
            tape := Tstage } ∧
          forall k : Nat,
            k < nStage ->
              (DovetailStagePrefix.NatSuffixScannerDescription.runConfig k
                { state :=
                    DovetailStagePrefix.NatSuffixScannerDescription.start
                  tape := Tin }).state ≠
                DovetailStagePrefix.NatSuffixScannerDescription.halt) ∧
        exists nConfigs : Nat,
          ConfigurationsAndFinalFlagsScannerDescription.runConfig nConfigs
              { state :=
                  ConfigurationsAndFinalFlagsScannerDescription.start
                tape := Tape.move Direction.right Tstage } =
            { state := ConfigurationsAndFinalFlagsScannerDescription.halt
              tape := Tout } := by
  simpa [StageConfigurationsAndFinalFlagsScannerDescription] using
    MachineDescription.seqSubroutine_runConfig_inv
      (A := DovetailStagePrefix.NatSuffixScannerDescription)
      (B := ConfigurationsAndFinalFlagsScannerDescription)
      (handoffMove := Direction.right)
      DovetailStagePrefix.natSuffixScannerDescription_subroutineReady
      configurationsAndFinalFlagsScannerDescription_subroutineReady
      (by
        simpa [StageConfigurationsAndFinalFlagsScannerDescription] using h)

theorem checkedDovetailLayoutScannerDescription_haltsWithTape_stageField_inv
    {bits : Word Bool} {Tout : Tape Bool}
    (h : CheckedDovetailLayoutScannerDescription.HaltsWithTape bits Tout) :
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
        BoolWordSuffixScannerDescription.runConfig nInput
            { state := BoolWordSuffixScannerDescription.start
              tape :=
                tapeAtCells
                  (List.append (transitionRemainderBits.reverse.map some)
                    [none])
                  ((b :: suffixTail).map some) } =
          { state := BoolWordSuffixScannerDescription.halt
            tape := Tinput } ∧
        DovetailStagePrefix.NatSuffixScannerDescription.runConfig nStage
            { state := DovetailStagePrefix.NatSuffixScannerDescription.start
              tape := Tape.move Direction.right Tinput } =
          { state := DovetailStagePrefix.NatSuffixScannerDescription.halt
            tape := Tstage } ∧
        ConfigurationsAndFinalFlagsScannerDescription.runConfig nConfigs
            { state := ConfigurationsAndFinalFlagsScannerDescription.start
              tape := Tape.move Direction.right Tstage } =
          { state := ConfigurationsAndFinalFlagsScannerDescription.halt
            tape := Tbody } ∧
        ReturnToFirstMarkerDescription.runConfig nReturn
            { state := ReturnToFirstMarkerDescription.start
              tape := Tape.move Direction.right Tbody } =
          { state := ReturnToFirstMarkerDescription.halt
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
      ConfigurationsAndFinalFlagsScannerDescription.runConfig n
          { state := ConfigurationsAndFinalFlagsScannerDescription.start
            tape := Tin } =
        { state := ConfigurationsAndFinalFlagsScannerDescription.halt
          tape := Tout }) :
    exists Taccept : Tape Bool,
      (exists nAccept : Nat,
        ConfigurationSuffixScannerDescription.runConfig nAccept
            { state := ConfigurationSuffixScannerDescription.start
              tape := Tin } =
          { state := ConfigurationSuffixScannerDescription.halt
            tape := Taccept } ∧
          forall k : Nat,
            k < nAccept ->
              (ConfigurationSuffixScannerDescription.runConfig k
                { state := ConfigurationSuffixScannerDescription.start
                  tape := Tin }).state ≠
                ConfigurationSuffixScannerDescription.halt) ∧
        exists nRejectFlags : Nat,
          RejectConfigAndFinalFlagsScannerDescription.runConfig
              nRejectFlags
              { state := RejectConfigAndFinalFlagsScannerDescription.start
                tape := Tape.move Direction.right Taccept } =
            { state := RejectConfigAndFinalFlagsScannerDescription.halt
              tape := Tout } := by
  simpa [ConfigurationsAndFinalFlagsScannerDescription] using
    MachineDescription.seqSubroutine_runConfig_inv
      (A := ConfigurationSuffixScannerDescription)
      (B := RejectConfigAndFinalFlagsScannerDescription)
      (handoffMove := Direction.right)
      configurationSuffixScannerDescription_subroutineReady
      rejectConfigAndFinalFlagsScannerDescription_subroutineReady
      (by
        simpa [ConfigurationsAndFinalFlagsScannerDescription] using h)

theorem checkedDovetailLayoutScannerDescription_haltsWithTape_acceptConfig_inv
    {bits : Word Bool} {Tout : Tape Bool}
    (h : CheckedDovetailLayoutScannerDescription.HaltsWithTape bits Tout) :
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
        BoolWordSuffixScannerDescription.runConfig nInput
            { state := BoolWordSuffixScannerDescription.start
              tape :=
                tapeAtCells
                  (List.append (transitionRemainderBits.reverse.map some)
                    [none])
                  ((b :: suffixTail).map some) } =
          { state := BoolWordSuffixScannerDescription.halt
            tape := Tinput } ∧
        DovetailStagePrefix.NatSuffixScannerDescription.runConfig nStage
            { state := DovetailStagePrefix.NatSuffixScannerDescription.start
              tape := Tape.move Direction.right Tinput } =
          { state := DovetailStagePrefix.NatSuffixScannerDescription.halt
            tape := Tstage } ∧
        ConfigurationSuffixScannerDescription.runConfig nAccept
            { state := ConfigurationSuffixScannerDescription.start
              tape := Tape.move Direction.right Tstage } =
          { state := ConfigurationSuffixScannerDescription.halt
            tape := Taccept } ∧
        RejectConfigAndFinalFlagsScannerDescription.runConfig nRejectFlags
            { state := RejectConfigAndFinalFlagsScannerDescription.start
              tape := Tape.move Direction.right Taccept } =
          { state := RejectConfigAndFinalFlagsScannerDescription.halt
            tape := Tbody } ∧
        ReturnToFirstMarkerDescription.runConfig nReturn
            { state := ReturnToFirstMarkerDescription.start
              tape := Tape.move Direction.right Tbody } =
          { state := ReturnToFirstMarkerDescription.halt
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
      RejectConfigAndFinalFlagsScannerDescription.runConfig n
          { state := RejectConfigAndFinalFlagsScannerDescription.start
            tape := Tin } =
        { state := RejectConfigAndFinalFlagsScannerDescription.halt
          tape := Tout }) :
    exists Treject : Tape Bool,
      (exists nReject : Nat,
        ConfigurationSuffixScannerDescription.runConfig nReject
            { state := ConfigurationSuffixScannerDescription.start
              tape := Tin } =
          { state := ConfigurationSuffixScannerDescription.halt
            tape := Treject } ∧
          forall k : Nat,
            k < nReject ->
              (ConfigurationSuffixScannerDescription.runConfig k
                { state := ConfigurationSuffixScannerDescription.start
                  tape := Tin }).state ≠
                ConfigurationSuffixScannerDescription.halt) ∧
        exists nFinalFlags : Nat,
          FinalHitFlagsScannerDescription.runConfig nFinalFlags
              { state := FinalHitFlagsScannerDescription.start
                tape := Tape.move Direction.right Treject } =
            { state := FinalHitFlagsScannerDescription.halt
              tape := Tout } := by
  simpa [RejectConfigAndFinalFlagsScannerDescription] using
    MachineDescription.seqSubroutine_runConfig_inv
      (A := ConfigurationSuffixScannerDescription)
      (B := FinalHitFlagsScannerDescription)
      (handoffMove := Direction.right)
      configurationSuffixScannerDescription_subroutineReady
      finalHitFlagsScannerDescription_subroutineReady
      (by
        simpa [RejectConfigAndFinalFlagsScannerDescription] using h)

theorem checkedDovetailLayoutScannerDescription_haltsWithTape_rejectConfig_inv
    {bits : Word Bool} {Tout : Tape Bool}
    (h : CheckedDovetailLayoutScannerDescription.HaltsWithTape bits Tout) :
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
        BoolWordSuffixScannerDescription.runConfig nInput
            { state := BoolWordSuffixScannerDescription.start
              tape :=
                tapeAtCells
                  (List.append (transitionRemainderBits.reverse.map some)
                    [none])
                  ((b :: suffixTail).map some) } =
          { state := BoolWordSuffixScannerDescription.halt
            tape := Tinput } ∧
        DovetailStagePrefix.NatSuffixScannerDescription.runConfig nStage
            { state := DovetailStagePrefix.NatSuffixScannerDescription.start
              tape := Tape.move Direction.right Tinput } =
          { state := DovetailStagePrefix.NatSuffixScannerDescription.halt
            tape := Tstage } ∧
        ConfigurationSuffixScannerDescription.runConfig nAccept
            { state := ConfigurationSuffixScannerDescription.start
              tape := Tape.move Direction.right Tstage } =
          { state := ConfigurationSuffixScannerDescription.halt
            tape := Taccept } ∧
        ConfigurationSuffixScannerDescription.runConfig nReject
            { state := ConfigurationSuffixScannerDescription.start
              tape := Tape.move Direction.right Taccept } =
          { state := ConfigurationSuffixScannerDescription.halt
            tape := Treject } ∧
        FinalHitFlagsScannerDescription.runConfig nFinalFlags
            { state := FinalHitFlagsScannerDescription.start
              tape := Tape.move Direction.right Treject } =
          { state := FinalHitFlagsScannerDescription.halt
            tape := Tbody } ∧
        ReturnToFirstMarkerDescription.runConfig nReturn
            { state := ReturnToFirstMarkerDescription.start
              tape := Tape.move Direction.right Tbody } =
          { state := ReturnToFirstMarkerDescription.halt
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
      FinalHitFlagsScannerDescription.runConfig n
          { state := FinalHitFlagsScannerDescription.start
            tape := Tin } =
        { state := FinalHitFlagsScannerDescription.halt
          tape := Tout }) :
    exists TacceptHit : Tape Bool,
      (exists nAcceptHit : Nat,
        BoolSuffixScannerDescription.runConfig nAcceptHit
            { state := BoolSuffixScannerDescription.start
              tape := Tin } =
          { state := BoolSuffixScannerDescription.halt
            tape := TacceptHit } ∧
          forall k : Nat,
            k < nAcceptHit ->
              (BoolSuffixScannerDescription.runConfig k
                { state := BoolSuffixScannerDescription.start
                  tape := Tin }).state ≠
                BoolSuffixScannerDescription.halt) ∧
        exists nRejectHit : Nat,
          BoolFinalScannerDescription.runConfig nRejectHit
              { state := BoolFinalScannerDescription.start
                tape := Tape.move Direction.right TacceptHit } =
            { state := BoolFinalScannerDescription.halt
              tape := Tout } := by
  simpa [FinalHitFlagsScannerDescription] using
    MachineDescription.seqSubroutine_runConfig_inv
      (A := BoolSuffixScannerDescription)
      (B := BoolFinalScannerDescription)
      (handoffMove := Direction.right)
      boolSuffixScannerDescription_subroutineReady
      boolFinalScannerDescription_subroutineReady
      (by
        simpa [FinalHitFlagsScannerDescription] using h)

theorem checkedDovetailLayoutScannerDescription_haltsWithTape_finalFlags_inv
    {bits : Word Bool} {Tout : Tape Bool}
    (h : CheckedDovetailLayoutScannerDescription.HaltsWithTape bits Tout) :
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
        BoolWordSuffixScannerDescription.runConfig nInput
            { state := BoolWordSuffixScannerDescription.start
              tape :=
                tapeAtCells
                  (List.append (transitionRemainderBits.reverse.map some)
                    [none])
                  ((b :: suffixTail).map some) } =
          { state := BoolWordSuffixScannerDescription.halt
            tape := Tinput } ∧
        DovetailStagePrefix.NatSuffixScannerDescription.runConfig nStage
            { state := DovetailStagePrefix.NatSuffixScannerDescription.start
              tape := Tape.move Direction.right Tinput } =
          { state := DovetailStagePrefix.NatSuffixScannerDescription.halt
            tape := Tstage } ∧
        ConfigurationSuffixScannerDescription.runConfig nAccept
            { state := ConfigurationSuffixScannerDescription.start
              tape := Tape.move Direction.right Tstage } =
          { state := ConfigurationSuffixScannerDescription.halt
            tape := Taccept } ∧
        ConfigurationSuffixScannerDescription.runConfig nReject
            { state := ConfigurationSuffixScannerDescription.start
              tape := Tape.move Direction.right Taccept } =
          { state := ConfigurationSuffixScannerDescription.halt
            tape := Treject } ∧
        BoolSuffixScannerDescription.runConfig nAcceptHit
            { state := BoolSuffixScannerDescription.start
              tape := Tape.move Direction.right Treject } =
          { state := BoolSuffixScannerDescription.halt
            tape := TacceptHit } ∧
        BoolFinalScannerDescription.runConfig nRejectHit
            { state := BoolFinalScannerDescription.start
              tape := Tape.move Direction.right TacceptHit } =
          { state := BoolFinalScannerDescription.halt
            tape := Tbody } ∧
        ReturnToFirstMarkerDescription.runConfig nReturn
            { state := ReturnToFirstMarkerDescription.start
              tape := Tape.move Direction.right Tbody } =
          { state := ReturnToFirstMarkerDescription.halt
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

import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.Composition

set_option doc.verso true

/-!
# Primitive closed facts for dovetail-layout scanners

This module contains closed-direction facts for the primitive field scanners.
It is deliberately separate from the large composed closed proof so the
field-level inversions can be developed and reused one scanner at a time.
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

private abbrev CLSS := CellListSuffixScannerDescription
private abbrev BWSS := BoolWordSuffixScannerDescription
private abbrev NSS := DovetailStagePrefix.NatSuffixScannerDescription

theorem cellListSuffixScannerDescription_runConfig_start_cell_inv
    (baseLeft : List (Option Bool)) (first : Option Bool)
    (suffixTail : List (Option Bool))
    {Tout : Tape Bool} {n : Nat}
    (h :
      CLSS.runConfig n
          (config CLSS.start baseLeft
            (first :: suffixTail)) =
        { state := CLSS.halt
          tape := Tout }) :
      first = some false := by
  cases first with
  | none =>
      exfalso
      cases n with
      | zero =>
          simp [CellListSuffixScannerDescription, config, tapeAtCells,
            runConfig] at h
      | succ k =>
          let c0 : Configuration :=
            config CLSS.start baseLeft
              (none :: suffixTail)
          have hstep :
              CLSS.stepConfig c0 = none := by
            cases suffixTail <;>
              simp [c0, CellListSuffixScannerDescription, config,
                tapeAtCells, keep, keepMove, writeMove,
                scanLeftToSentinelRestart,
                stepConfig,
                lookupTransition,
                Matches,
                transition, Tape.read]
          have hstay :
              CLSS.runConfig (Nat.succ k) c0 =
                c0 := by
            exact runConfig_of_stepConfig_none hstep
              (Nat.succ k)
          have hstate :=
            congrArg Configuration.state
              (hstay.symm.trans (by simpa [c0] using h))
          simp [c0, config, CellListSuffixScannerDescription] at hstate
  | some bit =>
      cases bit with
      | false =>
          rfl
      | true =>
          exfalso
          cases n with
          | zero =>
              simp [CellListSuffixScannerDescription, config, tapeAtCells,
                runConfig] at h
          | succ k =>
              let c0 : Configuration :=
                config CLSS.start baseLeft
                  (some true :: suffixTail)
              have hstep :
                  CLSS.stepConfig c0 = none := by
                cases suffixTail <;>
                  simp [c0, CellListSuffixScannerDescription, config,
                    tapeAtCells, keep, keepMove, writeMove,
                    scanLeftToSentinelRestart,
                    stepConfig,
                    lookupTransition,
                    Matches,
                    transition, Tape.read]
              have hstay :
                  CLSS.runConfig (Nat.succ k)
                      c0 =
                    c0 := by
                exact runConfig_of_stepConfig_none hstep
                  (Nat.succ k)
              have hstate :=
                congrArg Configuration.state
                  (hstay.symm.trans (by simpa [c0] using h))
              simp [c0, config, CellListSuffixScannerDescription] at hstate

theorem cellListSuffixScannerDescription_runConfig_start_bit_inv
    (baseLeft : List (Option Bool)) (first : Bool)
    (suffixTail : List (Option Bool))
    {Tout : Tape Bool} {n : Nat}
    (h :
      CLSS.runConfig n
          (config CLSS.start baseLeft
            (some first :: suffixTail)) =
        { state := CLSS.halt
          tape := Tout }) :
      first = false := by
  have hcell :=
    cellListSuffixScannerDescription_runConfig_start_cell_inv
      baseLeft (some first) suffixTail h
  cases first <;> simp at hcell ⊢

theorem primitive_runConfig_state_ne_halt_of_reaches_stuck
    {D : MachineDescription}
    {c stuck : Configuration} {k n : Nat}
    (hD : D.HaltTransitionFree)
    (hprefix : D.runConfig k c = stuck)
    (hstep : D.stepConfig stuck = none)
    (hstuck : stuck.state ≠ D.halt) :
    (D.runConfig n c).state ≠ D.halt := by
  exact runConfig_state_ne_halt_of_reaches_stuck
    hD hprefix hstep hstuck

theorem cellListSuffixScannerDescription_runConfig_start_nat_prefix_inv
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    {Tout : Tape Bool} {n : Nat}
    (h :
      CLSS.runConfig n
          (config CLSS.start baseLeft
            (bits.map some)) =
        { state := CLSS.halt
          tape := Tout }) :
    exists doneBit : Bool,
    exists tail : Word Bool,
      bits = false :: false :: true :: doneBit :: tail := by
  let start : Configuration :=
    config CLSS.start baseLeft (bits.map some)
  have hhaltState :
      (CLSS.runConfig n start).state =
        CLSS.halt := by
    simpa [start] using
      congrArg Configuration.state h
  cases bits with
  | nil =>
      let stuck : Configuration := start
      have hstep :
          CLSS.stepConfig stuck = none := by
        simp [stuck, start, CellListSuffixScannerDescription, config,
          tapeAtCells, keep, keepMove, writeMove,
          scanLeftToSentinelRestart, stepConfig,
          lookupTransition, Matches,
          transition, Tape.read]
      have hstuck :
          stuck.state ≠ CLSS.halt := by
        simp [stuck, start, CellListSuffixScannerDescription, config]
      exact False.elim
        (primitive_runConfig_state_ne_halt_of_reaches_stuck
          cellListSuffixScannerDescription_haltTransitionFree
          (D := CLSS)
          (c := start) (stuck := stuck) (k := 0) (n := n)
          rfl hstep hstuck hhaltState)
  | cons first rest =>
      cases first
      · cases rest with
        | nil =>
            let stuck :=
              CLSS.runConfig 1 start
            have hstep :
                CLSS.stepConfig stuck = none := by
              simp [stuck, start, CellListSuffixScannerDescription, config,
                tapeAtCells, keep, keepMove, writeMove,
                scanLeftToSentinelRestart, runConfig,
                stepConfig,
                lookupTransition,
                Matches,
                transition, Tape.read, Tape.write,
                Tape.move, Tape.moveRight]
            have hstuck :
                stuck.state ≠ CLSS.halt := by
              simp [stuck, start, CellListSuffixScannerDescription, config,
                tapeAtCells, keep, keepMove, writeMove,
                scanLeftToSentinelRestart, runConfig,
                stepConfig,
                lookupTransition,
                Matches,
                transition, Tape.read, Tape.write,
                Tape.move, Tape.moveRight]
            exact False.elim
              (primitive_runConfig_state_ne_halt_of_reaches_stuck
                cellListSuffixScannerDescription_haltTransitionFree
                (D := CLSS)
                (c := start) (stuck := stuck) (k := 1) (n := n)
                rfl hstep hstuck hhaltState)
        | cons second restTail =>
            cases second
            · cases restTail with
              | nil =>
                  let stuck :=
                    CLSS.runConfig 2 start
                  have hstep :
                      CLSS.stepConfig stuck =
                        none := by
                    simp [stuck, start, CellListSuffixScannerDescription,
                      config, tapeAtCells, keep, keepMove, writeMove,
                      scanLeftToSentinelRestart,
                      runConfig,
                      stepConfig,
                      lookupTransition,
                      Matches,
                      transition, Tape.read, Tape.write,
                      Tape.move, Tape.moveRight]
                  have hstuck :
                      stuck.state ≠
                        CLSS.halt := by
                    simp [stuck, start, CellListSuffixScannerDescription,
                      config, tapeAtCells, keep, keepMove, writeMove,
                      scanLeftToSentinelRestart,
                      runConfig,
                      stepConfig,
                      lookupTransition,
                      Matches,
                      transition, Tape.read, Tape.write,
                      Tape.move, Tape.moveRight]
                  exact False.elim
                    (primitive_runConfig_state_ne_halt_of_reaches_stuck
                      cellListSuffixScannerDescription_haltTransitionFree
                      (D := CLSS)
                      (c := start) (stuck := stuck) (k := 2) (n := n)
                      rfl hstep hstuck hhaltState)
              | cons third tail =>
                  cases third
                  · let stuck :=
                      CLSS.runConfig 2 start
                    have hstep :
                        CLSS.stepConfig stuck =
                          none := by
                      cases tail <;>
                        simp [stuck, start,
                          CellListSuffixScannerDescription, config,
                          tapeAtCells, keep, keepMove, writeMove,
                          scanLeftToSentinelRestart,
                          runConfig,
                          stepConfig,
                          lookupTransition,
                          Matches,
                          transition, Tape.read,
                          Tape.write, Tape.move, Tape.moveRight]
                    have hstuck :
                        stuck.state ≠
                          CLSS.halt := by
                      cases tail <;>
                        simp [stuck, start,
                          CellListSuffixScannerDescription, config,
                          tapeAtCells, keep, keepMove, writeMove,
                          scanLeftToSentinelRestart,
                          runConfig,
                          stepConfig,
                          lookupTransition,
                          Matches,
                          transition, Tape.read,
                          Tape.write, Tape.move, Tape.moveRight]
                    exact False.elim
                      (primitive_runConfig_state_ne_halt_of_reaches_stuck
                        cellListSuffixScannerDescription_haltTransitionFree
                        (D := CLSS)
                        (c := start) (stuck := stuck) (k := 2) (n := n)
                        rfl hstep hstuck hhaltState)
                  · cases tail with
                    | nil =>
                        let stuck :=
                          CLSS.runConfig 4 start
                        have hstep :
                            CLSS.stepConfig
                                stuck = none := by
                          simp [stuck, start,
                            CellListSuffixScannerDescription, config,
                            tapeAtCells, keep, keepMove, writeMove,
                            scanLeftToSentinelRestart,
                            runConfig,
                            stepConfig,
                            lookupTransition,
                            Matches,
                            transition, Tape.read,
                            Tape.write, Tape.move, Tape.moveRight]
                        have hstuck :
                            stuck.state ≠
                              CLSS.halt := by
                          simp [stuck, start,
                            CellListSuffixScannerDescription, config,
                            tapeAtCells, keep, keepMove, writeMove,
                            scanLeftToSentinelRestart,
                            runConfig,
                            stepConfig,
                            lookupTransition,
                            Matches,
                            transition, Tape.read,
                            Tape.write, Tape.move, Tape.moveRight]
                        exact False.elim
                          (primitive_runConfig_state_ne_halt_of_reaches_stuck
                            cellListSuffixScannerDescription_haltTransitionFree
                            (D := CLSS)
                            (c := start) (stuck := stuck) (k := 4)
                            (n := n) rfl hstep hstuck hhaltState)
                    | cons doneBit tailRest =>
                        exact ⟨doneBit, tailRest, rfl⟩
            · let stuck :=
                CLSS.runConfig 1 start
              have hstep :
                  CLSS.stepConfig stuck = none := by
                cases restTail <;>
                  simp [stuck, start, CellListSuffixScannerDescription,
                    config, tapeAtCells, keep, keepMove, writeMove,
                    scanLeftToSentinelRestart,
                    runConfig,
                    stepConfig,
                    lookupTransition,
                    Matches,
                    transition, Tape.read, Tape.write,
                    Tape.move, Tape.moveRight]
              have hstuck :
                  stuck.state ≠ CLSS.halt := by
                cases restTail <;>
                  simp [stuck, start, CellListSuffixScannerDescription,
                    config, tapeAtCells, keep, keepMove, writeMove,
                    scanLeftToSentinelRestart,
                    runConfig,
                    stepConfig,
                    lookupTransition,
                    Matches,
                    transition, Tape.read, Tape.write,
                    Tape.move, Tape.moveRight]
              exact False.elim
                (primitive_runConfig_state_ne_halt_of_reaches_stuck
                  cellListSuffixScannerDescription_haltTransitionFree
                  (D := CLSS)
                  (c := start) (stuck := stuck) (k := 1) (n := n)
                  rfl hstep hstuck hhaltState)
      · have hfirstFalse :
            true = false := by
          exact
            cellListSuffixScannerDescription_runConfig_start_bit_inv
              baseLeft true (rest.map some)
              (by
                simpa [start] using h)
        cases hfirstFalse

theorem boolWordSuffixScannerDescription_runConfig_start_cell_inv
    (baseLeft : List (Option Bool)) (first : Option Bool)
    (suffixTail : List (Option Bool))
    {Tout : Tape Bool} {n : Nat}
    (h :
      BWSS.runConfig n
          (config BWSS.start baseLeft
            (first :: suffixTail)) =
        { state := BWSS.halt
          tape := Tout }) :
      first = some false := by
  cases first with
  | none =>
      exfalso
      cases n with
      | zero =>
          simp [BoolWordSuffixScannerDescription, config, tapeAtCells,
            runConfig] at h
      | succ k =>
          let c0 : Configuration :=
            config BWSS.start baseLeft
              (none :: suffixTail)
          have hstep :
              BWSS.stepConfig c0 = none := by
            cases suffixTail <;>
              simp [c0, BoolWordSuffixScannerDescription, config,
                tapeAtCells, keep, keepMove, writeMove,
                scanLeftToSentinelRestart,
                stepConfig,
                lookupTransition,
                Matches,
                transition, Tape.read]
          have hstay :
              BWSS.runConfig (Nat.succ k) c0 =
                c0 := by
            exact runConfig_of_stepConfig_none hstep
              (Nat.succ k)
          have hstate :=
            congrArg Configuration.state
              (hstay.symm.trans (by simpa [c0] using h))
          simp [c0, config, BoolWordSuffixScannerDescription] at hstate
  | some bit =>
      cases bit with
      | false =>
          rfl
      | true =>
          exfalso
          cases n with
          | zero =>
              simp [BoolWordSuffixScannerDescription, config, tapeAtCells,
                runConfig] at h
          | succ k =>
              let c0 : Configuration :=
                config BWSS.start baseLeft
                  (some true :: suffixTail)
              have hstep :
                  BWSS.stepConfig c0 = none := by
                cases suffixTail <;>
                  simp [c0, BoolWordSuffixScannerDescription, config,
                    tapeAtCells, keep, keepMove, writeMove,
                    scanLeftToSentinelRestart,
                    stepConfig,
                    lookupTransition,
                    Matches,
                    transition, Tape.read]
              have hstay :
                  BWSS.runConfig (Nat.succ k)
                      c0 =
                    c0 := by
                exact runConfig_of_stepConfig_none hstep
                  (Nat.succ k)
              have hstate :=
                congrArg Configuration.state
                  (hstay.symm.trans (by simpa [c0] using h))
              simp [c0, config, BoolWordSuffixScannerDescription] at hstate

theorem boolWordSuffixScannerDescription_runConfig_start_bit_inv
    (baseLeft : List (Option Bool)) (first : Bool)
    (suffixTail : List (Option Bool))
    {Tout : Tape Bool} {n : Nat}
    (h :
      BWSS.runConfig n
          (config BWSS.start baseLeft
            (some first :: suffixTail)) =
        { state := BWSS.halt
          tape := Tout }) :
      first = false := by
  have hcell :=
    boolWordSuffixScannerDescription_runConfig_start_cell_inv
      baseLeft (some first) suffixTail h
  cases first <;> simp at hcell ⊢

theorem boolWordSuffixScannerDescription_runConfig_start_nat_prefix_inv
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    {Tout : Tape Bool} {n : Nat}
    (h :
      BWSS.runConfig n
          (config BWSS.start baseLeft
            (bits.map some)) =
        { state := BWSS.halt
          tape := Tout }) :
    exists doneBit : Bool,
    exists tail : Word Bool,
      bits = false :: false :: true :: doneBit :: tail := by
  let start : Configuration :=
    config BWSS.start baseLeft (bits.map some)
  have hhaltState :
      (BWSS.runConfig n start).state =
        BWSS.halt := by
    simpa [start] using
      congrArg Configuration.state h
  cases bits with
  | nil =>
      let stuck : Configuration := start
      have hstep :
          BWSS.stepConfig stuck = none := by
        simp [stuck, start, BoolWordSuffixScannerDescription, config,
          tapeAtCells, keep, keepMove, writeMove,
          scanLeftToSentinelRestart, stepConfig,
          lookupTransition, Matches,
          transition, Tape.read]
      have hstuck :
          stuck.state ≠ BWSS.halt := by
        simp [stuck, start, BoolWordSuffixScannerDescription, config]
      exact False.elim
        (primitive_runConfig_state_ne_halt_of_reaches_stuck
          boolWordSuffixScannerDescription_haltTransitionFree
          (D := BWSS)
          (c := start) (stuck := stuck) (k := 0) (n := n)
          rfl hstep hstuck hhaltState)
  | cons first rest =>
      cases first
      · cases rest with
        | nil =>
            let stuck :=
              BWSS.runConfig 1 start
            have hstep :
                BWSS.stepConfig stuck = none := by
              simp [stuck, start, BoolWordSuffixScannerDescription, config,
                tapeAtCells, keep, keepMove, writeMove,
                scanLeftToSentinelRestart, runConfig,
                stepConfig,
                lookupTransition,
                Matches,
                transition, Tape.read, Tape.write,
                Tape.move, Tape.moveRight]
            have hstuck :
                stuck.state ≠ BWSS.halt := by
              simp [stuck, start, BoolWordSuffixScannerDescription, config,
                tapeAtCells, keep, keepMove, writeMove,
                scanLeftToSentinelRestart, runConfig,
                stepConfig,
                lookupTransition,
                Matches,
                transition, Tape.read, Tape.write,
                Tape.move, Tape.moveRight]
            exact False.elim
              (primitive_runConfig_state_ne_halt_of_reaches_stuck
                boolWordSuffixScannerDescription_haltTransitionFree
                (D := BWSS)
                (c := start) (stuck := stuck) (k := 1) (n := n)
                rfl hstep hstuck hhaltState)
        | cons second restTail =>
            cases second
            · cases restTail with
              | nil =>
                  let stuck :=
                    BWSS.runConfig 2 start
                  have hstep :
                      BWSS.stepConfig stuck =
                        none := by
                    simp [stuck, start, BoolWordSuffixScannerDescription,
                      config, tapeAtCells, keep, keepMove, writeMove,
                      scanLeftToSentinelRestart,
                      runConfig,
                      stepConfig,
                      lookupTransition,
                      Matches,
                      transition, Tape.read, Tape.write,
                      Tape.move, Tape.moveRight]
                  have hstuck :
                      stuck.state ≠
                        BWSS.halt := by
                    simp [stuck, start, BoolWordSuffixScannerDescription,
                      config, tapeAtCells, keep, keepMove, writeMove,
                      scanLeftToSentinelRestart,
                      runConfig,
                      stepConfig,
                      lookupTransition,
                      Matches,
                      transition, Tape.read, Tape.write,
                      Tape.move, Tape.moveRight]
                  exact False.elim
                    (primitive_runConfig_state_ne_halt_of_reaches_stuck
                      boolWordSuffixScannerDescription_haltTransitionFree
                      (D := BWSS)
                      (c := start) (stuck := stuck) (k := 2) (n := n)
                      rfl hstep hstuck hhaltState)
              | cons third tail =>
                  cases third
                  · let stuck :=
                      BWSS.runConfig 2 start
                    have hstep :
                        BWSS.stepConfig stuck =
                          none := by
                      cases tail <;>
                        simp [stuck, start,
                          BoolWordSuffixScannerDescription, config,
                          tapeAtCells, keep, keepMove, writeMove,
                          scanLeftToSentinelRestart,
                          runConfig,
                          stepConfig,
                          lookupTransition,
                          Matches,
                          transition, Tape.read,
                          Tape.write, Tape.move, Tape.moveRight]
                    have hstuck :
                        stuck.state ≠
                          BWSS.halt := by
                      cases tail <;>
                        simp [stuck, start,
                          BoolWordSuffixScannerDescription, config,
                          tapeAtCells, keep, keepMove, writeMove,
                          scanLeftToSentinelRestart,
                          runConfig,
                          stepConfig,
                          lookupTransition,
                          Matches,
                          transition, Tape.read,
                          Tape.write, Tape.move, Tape.moveRight]
                    exact False.elim
                      (primitive_runConfig_state_ne_halt_of_reaches_stuck
                        boolWordSuffixScannerDescription_haltTransitionFree
                        (D := BWSS)
                        (c := start) (stuck := stuck) (k := 2) (n := n)
                        rfl hstep hstuck hhaltState)
                  · cases tail with
                    | nil =>
                        let stuck :=
                          BWSS.runConfig 4 start
                        have hstep :
                            BWSS.stepConfig
                                stuck = none := by
                          simp [stuck, start,
                            BoolWordSuffixScannerDescription, config,
                            tapeAtCells, keep, keepMove, writeMove,
                            scanLeftToSentinelRestart,
                            runConfig,
                            stepConfig,
                            lookupTransition,
                            Matches,
                            transition, Tape.read,
                            Tape.write, Tape.move, Tape.moveRight]
                        have hstuck :
                            stuck.state ≠
                              BWSS.halt := by
                          simp [stuck, start,
                            BoolWordSuffixScannerDescription, config,
                            tapeAtCells, keep, keepMove, writeMove,
                            scanLeftToSentinelRestart,
                            runConfig,
                            stepConfig,
                            lookupTransition,
                            Matches,
                            transition, Tape.read,
                            Tape.write, Tape.move, Tape.moveRight]
                        exact False.elim
                          (primitive_runConfig_state_ne_halt_of_reaches_stuck
                            boolWordSuffixScannerDescription_haltTransitionFree
                            (D := BWSS)
                            (c := start) (stuck := stuck) (k := 4)
                            (n := n) rfl hstep hstuck hhaltState)
                    | cons doneBit tailRest =>
                        exact ⟨doneBit, tailRest, rfl⟩
            · let stuck :=
                BWSS.runConfig 1 start
              have hstep :
                  BWSS.stepConfig stuck = none := by
                cases restTail <;>
                  simp [stuck, start, BoolWordSuffixScannerDescription,
                    config, tapeAtCells, keep, keepMove, writeMove,
                    scanLeftToSentinelRestart,
                    runConfig,
                    stepConfig,
                    lookupTransition,
                    Matches,
                    transition, Tape.read, Tape.write,
                    Tape.move, Tape.moveRight]
              have hstuck :
                  stuck.state ≠ BWSS.halt := by
                cases restTail <;>
                  simp [stuck, start, BoolWordSuffixScannerDescription,
                    config, tapeAtCells, keep, keepMove, writeMove,
                    scanLeftToSentinelRestart,
                    runConfig,
                    stepConfig,
                    lookupTransition,
                    Matches,
                    transition, Tape.read, Tape.write,
                    Tape.move, Tape.moveRight]
              exact False.elim
                (primitive_runConfig_state_ne_halt_of_reaches_stuck
                  boolWordSuffixScannerDescription_haltTransitionFree
                  (D := BWSS)
                  (c := start) (stuck := stuck) (k := 1) (n := n)
                  rfl hstep hstuck hhaltState)
      · have hfirstFalse :
            true = false := by
          exact
            boolWordSuffixScannerDescription_runConfig_start_bit_inv
              baseLeft true (rest.map some)
              (by
                simpa [start] using h)
        cases hfirstFalse

theorem natSuffixScannerDescription_runConfig_nonblank_suffix_inv
    (stage : Nat) (baseLeft : List (Option Bool))
    (b : Bool) (suffixTail : List (Option Bool))
    {Tout : Tape Bool} {n : Nat}
    (h :
      NSS.runConfig n
          (config NSS.start
            baseLeft
            (List.append ((stageNatBits stage).map some)
              (some b :: suffixTail))) =
        { state := NSS.halt
          tape := Tout }) :
      Tout = Tape.move Direction.left
        (tapeAtCells
          (List.append ((stageNatBits stage).reverse.map some) baseLeft)
          (some b :: suffixTail)) := by
  let c0 : Configuration :=
    config NSS.start baseLeft
      (List.append ((stageNatBits stage).map some) (some b :: suffixTail))
  let Tfinal : Tape Bool :=
    Tape.move Direction.left
      (tapeAtCells
        (List.append ((stageNatBits stage).reverse.map some) baseLeft)
        (some b :: suffixTail))
  have hforward :
      NSS.runConfig
          (4 * stage + 5) c0 =
        { state := NSS.halt
          tape := Tfinal } := by
    rcases
        DovetailStagePrefix.stageNatBits_reverse_map_some_cons stage with
      ⟨tail, htail⟩
    rw [show 4 * stage + 5 = (4 * stage + 4) + 1 by omega]
    rw [runConfig_add]
    have hprefix :=
      DovetailStagePrefix.natSuffix_run_state200_stageNat_to_state210
        stage baseLeft (some b :: suffixTail)
    rw [show
        NSS.runConfig
            (4 * stage + 4) c0 =
          config 210
            (List.append ((stageNatBits stage).reverse.map some)
              baseLeft)
            (some b :: suffixTail) by
      simpa [c0] using hprefix]
    rw [htail]
    unfold Tfinal
    rw [htail]
    simpa [List.append_assoc] using
      DovetailStagePrefix.natSuffix_run_state210_handoff b (some true)
        (List.append tail baseLeft) suffixTail
  have htape :=
    runConfig_halt_tape_functional_from_config
      DovetailStagePrefix.natSuffixScannerDescription_haltTransitionFree
      hforward
      (by simpa [c0] using h)
  simpa [Tfinal] using htape.symm

theorem natSuffixScannerDescription_runConfig_stageNat_handoff
    (baseLeft : List (Option Bool)) (stage : Nat)
    (b : Bool) (suffixTail : Word Bool)
    {Tout : Tape Bool} {n : Nat}
    (h :
      NSS.runConfig n
          (config
            NSS.start
            baseLeft
            (List.append
              ((stageNatBits stage).map some)
              ((b :: suffixTail).map some))) =
        { state :=
            NSS.halt
          tape := Tout }) :
      Tape.move Direction.right Tout =
        tapeAtCells
          (List.append
            ((stageNatBits stage).reverse.map some)
            baseLeft)
          ((b :: suffixTail).map some) := by
  let c0 : Configuration :=
    config
      NSS.start
      baseLeft
      (List.append
        ((stageNatBits stage).map some)
        ((b :: suffixTail).map some))
  rcases
      DovetailStagePrefix.run_natSuffix_raw_to_handoff_withBase
        stage baseLeft b suffixTail with
    ⟨_steps, hforward⟩
  have hTout :
      Tout =
        (DovetailStagePrefix.natSuffixHandoffConfigWithBase
          stage baseLeft (b :: suffixTail)).tape := by
    exact
      (MachineDescription.runConfig_halt_tape_functional_of_haltTransitionFree
        DovetailStagePrefix.natSuffixScannerDescription_haltTransitionFree
        (by simpa [c0] using hforward)
        (by simpa [c0] using h)).symm
  rw [hTout]
  exact
    DovetailStagePrefix.natSuffixHandoffConfigWithBase_move_right
      stage baseLeft b suffixTail

theorem natSuffixScannerDescription_runConfig_stageNat_handoff_withRight
    (baseLeft : List (Option Bool)) (stage : Nat)
    (b : Bool) (suffixTail : Word Bool)
    (rightPadding : List (Option Bool))
    {Tout : Tape Bool} {n : Nat}
    (h :
      NSS.runConfig n
          (config
            NSS.start
            baseLeft
            (List.append
              ((stageNatBits stage).map some)
              (some b ::
                List.append (suffixTail.map some) rightPadding))) =
        { state :=
            NSS.halt
          tape := Tout }) :
      Tape.move Direction.right Tout =
        tapeAtCells
          (List.append
            ((stageNatBits stage).reverse.map some)
            baseLeft)
          (List.append ((b :: suffixTail).map some) rightPadding) := by
  let c0 : Configuration :=
    config
      NSS.start
      baseLeft
      (List.append
        ((stageNatBits stage).map some)
        (some b :: List.append (suffixTail.map some) rightPadding))
  rcases
      DovetailStagePrefix.run_natSuffix_raw_to_handoff_withBaseAndRight
        stage baseLeft b suffixTail rightPadding with
    ⟨_steps, hforward⟩
  have hTout :
      Tout =
        (DovetailStagePrefix.natSuffixHandoffConfigWithBaseAndRight
          stage baseLeft (b :: suffixTail) rightPadding).tape := by
    exact
      (MachineDescription.runConfig_halt_tape_functional_of_haltTransitionFree
        DovetailStagePrefix.natSuffixScannerDescription_haltTransitionFree
        (by simpa [c0] using hforward)
        (by simpa [c0] using h)).symm
  rw [hTout]
  exact
    DovetailStagePrefix.natSuffixHandoffConfigWithBaseAndRight_move_right
      stage baseLeft b suffixTail rightPadding

theorem natSuffixScannerDescription_runConfig_encodeNatAppend_handoff
    (baseLeft : List (Option Bool)) (stage : Nat)
    (suffix : Word MachineCodeSymbol) (b : Bool) (suffixTail : Word Bool)
    {Tout : Tape Bool} {n : Nat}
    (hsuffix :
      encodeCodeWordAsInput suffix = b :: suffixTail)
    (h :
      NSS.runConfig n
          (config
            NSS.start
            baseLeft
            ((encodeCodeWordAsInput
              (encodeNatAppend stage suffix)).map
              some)) =
        { state :=
            NSS.halt
          tape := Tout }) :
    exists baseAfter : List (Option Bool),
      Tape.move Direction.right Tout =
        tapeAtCells baseAfter
          ((encodeCodeWordAsInput suffix).map some) := by
  refine
    ⟨List.append ((stageNatBits stage).reverse.map some) baseLeft, ?_⟩
  have hrun :
      NSS.runConfig n
          (config
            NSS.start
            baseLeft
            (List.append ((stageNatBits stage).map some)
              ((b :: suffixTail).map some))) =
        { state :=
            NSS.halt
          tape := Tout } := by
    simpa [DovetailStagePrefix.natBits_eq_encodeNatAppend,
      hsuffix, List.map_append] using h
  simpa [hsuffix] using
    natSuffixScannerDescription_runConfig_stageNat_handoff
      baseLeft stage b suffixTail hrun

theorem natSuffixScannerDescription_runConfig_encodeNatAppend_handoff_withRight
    (baseLeft : List (Option Bool)) (stage : Nat)
    (suffix : Word MachineCodeSymbol) (b : Bool) (suffixTail : Word Bool)
    (rightPadding : List (Option Bool))
    {Tout : Tape Bool} {n : Nat}
    (hsuffix :
      encodeCodeWordAsInput suffix = b :: suffixTail)
    (h :
      NSS.runConfig n
          (config
            NSS.start
            baseLeft
            (List.append
              ((encodeCodeWordAsInput
                (encodeNatAppend stage suffix)).map some)
              rightPadding)) =
        { state :=
            NSS.halt
          tape := Tout }) :
    exists baseAfter : List (Option Bool),
      Tape.move Direction.right Tout =
        tapeAtCells baseAfter
          (List.append ((encodeCodeWordAsInput suffix).map some)
            rightPadding) := by
  refine
    ⟨List.append ((stageNatBits stage).reverse.map some) baseLeft, ?_⟩
  have hrun :
      NSS.runConfig n
          (config
            NSS.start
            baseLeft
            (List.append ((stageNatBits stage).map some)
              (some b ::
                List.append (suffixTail.map some) rightPadding))) =
        { state :=
            NSS.halt
          tape := Tout } := by
    simpa [DovetailStagePrefix.natBits_eq_encodeNatAppend,
      hsuffix, List.map_append, List.append_assoc] using h
  simpa [hsuffix, List.map_append, List.append_assoc] using
    natSuffixScannerDescription_runConfig_stageNat_handoff_withRight
      baseLeft stage b suffixTail rightPadding hrun

theorem boolWordSuffixScannerDescription_runConfig_canonical_false_suffix_inv
    (bits : Word Bool) (baseLeft : List (Option Bool)) (suffixTail : Word Bool)
    {Tout : Tape Bool} {n : Nat}
    (h :
      BWSS.runConfig n
          (config BWSS.start baseLeft
            (List.append ((stageNatBits bits.length).map some)
              (List.append ((cellsCodeBits (bits.map some)).map some)
                (some false :: suffixTail.map some)))) =
        { state := BWSS.halt
          tape := Tout }) :
      Tout =
        (boolWordCanonicalHandoffConfigWithBase bits baseLeft
          (false :: suffixTail)).tape := by
  let c0 : Configuration :=
    config BWSS.start baseLeft
      (List.append ((stageNatBits bits.length).map some)
        (List.append ((cellsCodeBits (bits.map some)).map some)
          (some false :: suffixTail.map some)))
  rcases run_boolWordSuffix_raw_to_canonical_handoff_withBase
      bits baseLeft suffixTail with
    ⟨_forwardSteps, hforward⟩
  have htape :=
    runConfig_halt_tape_functional_from_config
      boolWordSuffixScannerDescription_haltTransitionFree
      (by simpa [c0] using hforward)
      (by simpa [c0] using h)
  exact htape.symm

theorem cellListSuffixScannerDescription_runConfig_canonical_false_suffix_inv
    (cells baseLeft : List (Option Bool)) (suffixTail : Word Bool)
    {Tout : Tape Bool} {n : Nat}
    (h :
      CLSS.runConfig n
          (config CLSS.start baseLeft
            (List.append ((stageNatBits cells.length).map some)
              (List.append ((cellsCodeBits cells).map some)
                (some false :: suffixTail.map some)))) =
        { state := CLSS.halt
          tape := Tout }) :
      Tout =
        (cellListCanonicalHandoffConfigWithBase cells baseLeft
          (false :: suffixTail)).tape := by
  let c0 : Configuration :=
    config CLSS.start baseLeft
      (List.append ((stageNatBits cells.length).map some)
        (List.append ((cellsCodeBits cells).map some)
          (some false :: suffixTail.map some)))
  rcases run_cellList_raw_to_canonical_handoff_withBase
      cells baseLeft suffixTail with
    ⟨_forwardSteps, hforward⟩
  have htape :=
    runConfig_halt_tape_functional_from_config
      cellListSuffixScannerDescription_haltTransitionFree
      (by simpa [c0] using hforward)
      (by simpa [c0] using h)
  exact htape.symm

theorem cellListSuffixScannerDescription_runConfig_canonical_false_suffix_inv_withRight
    (cells baseLeft : List (Option Bool)) (suffixTail : Word Bool)
    (rightPadding : List (Option Bool))
    {Tout : Tape Bool} {n : Nat}
    (h :
      CLSS.runConfig n
          (config CLSS.start baseLeft
            (List.append ((stageNatBits cells.length).map some)
              (List.append ((cellsCodeBits cells).map some)
                (some false ::
                  List.append (suffixTail.map some) rightPadding)))) =
        { state := CLSS.halt
          tape := Tout }) :
      Tout =
        (cellListCanonicalHandoffConfigWithBaseAndRight cells baseLeft
          (false :: suffixTail) rightPadding).tape := by
  let c0 : Configuration :=
    config CLSS.start baseLeft
      (List.append ((stageNatBits cells.length).map some)
        (List.append ((cellsCodeBits cells).map some)
          (some false ::
            List.append (suffixTail.map some) rightPadding)))
  rcases run_cellList_raw_to_canonical_handoff_withBaseAndRight
      cells baseLeft suffixTail rightPadding with
    ⟨_forwardSteps, hforward⟩
  have htape :=
    runConfig_halt_tape_functional_from_config
      cellListSuffixScannerDescription_haltTransitionFree
      (by simpa [c0] using hforward)
      (by simpa [c0] using h)
  exact htape.symm

theorem tapeSuffixScannerDescription_runConfig_canonical_false_suffix_inv
    (T : Tape Bool) (baseLeft : List (Option Bool))
    (suffixTail : Word Bool)
    {Tout : Tape Bool} {n : Nat}
    (h :
      TapeSuffixScannerDescription.runConfig n
          { state := TapeSuffixScannerDescription.start
            tape :=
              tapeAtCells baseLeft
                ((tapeFieldBits T (false :: suffixTail)).map some) } =
        { state := TapeSuffixScannerDescription.halt
          tape := Tout }) :
      Tout =
        (cellListCanonicalHandoffConfigWithBase T.right
          (List.append ((cellCodeBits T.head).map some).reverse
            (cellListCanonicalRestoredLeftWithBase T.left baseLeft))
          (false :: suffixTail)).tape := by
  let c0 : Configuration :=
    { state := TapeSuffixScannerDescription.start
      tape :=
        tapeAtCells baseLeft
          ((tapeFieldBits T (false :: suffixTail)).map some) }
  rcases run_tapeSuffix_raw_to_handoff_withBase T baseLeft suffixTail with
    ⟨_forwardSteps, hforward⟩
  have htape :=
    MachineDescription.runConfig_halt_tape_functional_of_haltTransitionFree
      tapeSuffixScannerDescription_subroutineReady.right
      (by simpa [c0] using hforward)
      (by simpa [c0] using h)
  exact htape.symm

theorem configurationSuffixScannerDescription_runConfig_canonical_false_suffix_inv
    (cfg : Configuration)
    (baseLeft : List (Option Bool)) (suffixTail : Word Bool)
    {Tout : Tape Bool} {n : Nat}
    (h :
      ConfigurationSuffixScannerDescription.runConfig n
          { state := ConfigurationSuffixScannerDescription.start
            tape :=
              tapeAtCells baseLeft
                ((configurationFieldBits cfg (false :: suffixTail)).map
                  some) } =
        { state := ConfigurationSuffixScannerDescription.halt
          tape := Tout }) :
      Tout =
        (cellListCanonicalHandoffConfigWithBase cfg.tape.right
          (List.append ((cellCodeBits cfg.tape.head).map some).reverse
            (cellListCanonicalRestoredLeftWithBase cfg.tape.left
              (List.append ((stageNatBits cfg.state).map some).reverse
                baseLeft)))
          (false :: suffixTail)).tape := by
  let c0 : Configuration :=
    { state := ConfigurationSuffixScannerDescription.start
      tape :=
        tapeAtCells baseLeft
          ((configurationFieldBits cfg (false :: suffixTail)).map some) }
  rcases run_configurationSuffix_raw_to_handoff_withBase cfg baseLeft
      suffixTail with
    ⟨_forwardSteps, hforward⟩
  have htape :=
    MachineDescription.runConfig_halt_tape_functional_of_haltTransitionFree
      configurationSuffixScannerDescription_subroutineReady.right
      (by simpa [c0] using hforward)
      (by simpa [c0] using h)
  exact htape.symm

theorem finalHitFlagsScannerDescription_runConfig_canonical_inv
    (acceptHit rejectHit : Bool)
    (baseLeft : List (Option Bool))
    {Tout : Tape Bool} {n : Nat}
    (h :
      FinalHitFlagsScannerDescription.runConfig n
          { state := FinalHitFlagsScannerDescription.start
            tape :=
              tapeAtCells baseLeft
                ((boolFieldBits acceptHit
                  (boolFieldBits rejectHit [])).map some) } =
        { state := FinalHitFlagsScannerDescription.halt
          tape := Tout }) :
      Tout =
        (boolFinalHandoffConfigWithBase rejectHit
          (List.append ((cellCodeBits (some acceptHit)).map some).reverse
            baseLeft)).tape := by
  let c0 : Configuration :=
    { state := FinalHitFlagsScannerDescription.start
      tape :=
        tapeAtCells baseLeft
          ((boolFieldBits acceptHit
            (boolFieldBits rejectHit [])).map some) }
  rcases run_finalHitFlags_raw_to_handoff_withBase acceptHit rejectHit
      baseLeft with
    ⟨_forwardSteps, hforward⟩
  have htape :=
    MachineDescription.runConfig_halt_tape_functional_of_haltTransitionFree
      finalHitFlagsScannerDescription_subroutineReady.right
      (by simpa [c0] using hforward)
      (by simpa [c0] using h)
  exact htape.symm

theorem configurationsAndFinalFlagsScannerDescription_runConfig_canonical_inv
    (acceptConfig rejectConfig : Configuration)
    (acceptHit rejectHit : Bool)
    (baseLeft : List (Option Bool))
    {Tout : Tape Bool} {n : Nat}
    (h :
      ConfigurationsAndFinalFlagsScannerDescription.runConfig n
          { state := ConfigurationsAndFinalFlagsScannerDescription.start
            tape :=
              tapeAtCells baseLeft
                ((configurationFieldBits acceptConfig
                  (configurationFieldBits rejectConfig
                    (boolFieldBits acceptHit
                      (boolFieldBits rejectHit [])))).map some) } =
        { state := ConfigurationsAndFinalFlagsScannerDescription.halt
          tape := Tout }) :
      Tout =
        (boolFinalHandoffConfigWithBase rejectHit
          (List.append ((cellCodeBits (some acceptHit)).map some).reverse
            (configurationRestoredLeftWithBase rejectConfig
              (configurationRestoredLeftWithBase acceptConfig
                baseLeft)))).tape := by
  let c0 : Configuration :=
    { state := ConfigurationsAndFinalFlagsScannerDescription.start
      tape :=
        tapeAtCells baseLeft
          ((configurationFieldBits acceptConfig
            (configurationFieldBits rejectConfig
              (boolFieldBits acceptHit
                (boolFieldBits rejectHit [])))).map some) }
  rcases run_configurationsAndFinalFlags_raw_to_handoff_withBase
      acceptConfig rejectConfig acceptHit rejectHit baseLeft with
    ⟨_forwardSteps, hforward⟩
  have htape :=
    MachineDescription.runConfig_halt_tape_functional_of_haltTransitionFree
      configurationsAndFinalFlagsScannerDescription_subroutineReady.right
      (by simpa [c0] using hforward)
      (by simpa [c0] using h)
  exact htape.symm

theorem stageConfigurationsAndFinalFlagsScannerDescription_runConfig_canonical_inv
    (stage : Nat)
    (acceptConfig rejectConfig : Configuration)
    (acceptHit rejectHit : Bool)
    (baseLeft : List (Option Bool))
    {Tout : Tape Bool} {n : Nat}
    (h :
      StageConfigurationsAndFinalFlagsScannerDescription.runConfig n
          { state := StageConfigurationsAndFinalFlagsScannerDescription.start
            tape :=
              tapeAtCells baseLeft
                ((List.append (stageNatBits stage)
                  (configurationFieldBits acceptConfig
                    (configurationFieldBits rejectConfig
                      (boolFieldBits acceptHit
                        (boolFieldBits rejectHit []))))).map some) } =
        { state := StageConfigurationsAndFinalFlagsScannerDescription.halt
          tape := Tout }) :
      Tout =
        (boolFinalHandoffConfigWithBase rejectHit
          (List.append ((cellCodeBits (some acceptHit)).map some).reverse
            (configurationRestoredLeftWithBase rejectConfig
              (configurationRestoredLeftWithBase acceptConfig
                (List.append ((stageNatBits stage).map some).reverse
                  baseLeft))))).tape := by
  let c0 : Configuration :=
    { state := StageConfigurationsAndFinalFlagsScannerDescription.start
      tape :=
        tapeAtCells baseLeft
          ((List.append (stageNatBits stage)
            (configurationFieldBits acceptConfig
              (configurationFieldBits rejectConfig
                (boolFieldBits acceptHit
                  (boolFieldBits rejectHit []))))).map some) }
  rcases run_stageConfigurationsAndFinalFlags_raw_to_handoff_withBase
      stage acceptConfig rejectConfig acceptHit rejectHit baseLeft with
    ⟨_forwardSteps, hforward⟩
  have htape :=
    MachineDescription.runConfig_halt_tape_functional_of_haltTransitionFree
      stageConfigurationsAndFinalFlagsScannerDescription_subroutineReady.right
      (by simpa [c0] using hforward)
      (by simpa [c0] using h)
  exact htape.symm

theorem inputStageConfigurationsAndFinalFlagsScannerDescription_runConfig_canonical_inv
    (input : Word Bool) (stage : Nat)
    (acceptConfig rejectConfig : Configuration)
    (acceptHit rejectHit : Bool)
    (baseLeft : List (Option Bool))
    {Tout : Tape Bool} {n : Nat}
    (h :
      InputStageConfigurationsAndFinalFlagsScannerDescription.runConfig n
          { state := InputStageConfigurationsAndFinalFlagsScannerDescription.start
            tape :=
              tapeAtCells baseLeft
                ((boolWordFieldBits input
                  (List.append (stageNatBits stage)
                    (configurationFieldBits acceptConfig
                      (configurationFieldBits rejectConfig
                        (boolFieldBits acceptHit
                          (boolFieldBits rejectHit [])))))).map some) } =
        { state := InputStageConfigurationsAndFinalFlagsScannerDescription.halt
          tape := Tout }) :
      Tout =
        (boolFinalHandoffConfigWithBase rejectHit
          (List.append ((cellCodeBits (some acceptHit)).map some).reverse
            (configurationRestoredLeftWithBase rejectConfig
              (configurationRestoredLeftWithBase acceptConfig
                (List.append ((stageNatBits stage).map some).reverse
                  (cellListCanonicalRestoredLeftWithBase
                    (input.map some) baseLeft)))))).tape := by
  let c0 : Configuration :=
    { state := InputStageConfigurationsAndFinalFlagsScannerDescription.start
      tape :=
        tapeAtCells baseLeft
          ((boolWordFieldBits input
            (List.append (stageNatBits stage)
              (configurationFieldBits acceptConfig
                (configurationFieldBits rejectConfig
                  (boolFieldBits acceptHit
                    (boolFieldBits rejectHit [])))))).map some) }
  rcases run_inputStageConfigurationsAndFinalFlags_raw_to_handoff_withBase
      input stage acceptConfig rejectConfig acceptHit rejectHit baseLeft with
    ⟨_forwardSteps, hforward⟩
  have htape :=
    MachineDescription.runConfig_halt_tape_functional_of_haltTransitionFree
      inputStageConfigurationsAndFinalFlagsScannerDescription_subroutineReady.right
      (by simpa [c0] using hforward)
      (by simpa [c0] using h)
  exact htape.symm

end DovetailLayoutScanner
end CanonicalLayouts
end EncodedRewriters

end Computability
end FoC

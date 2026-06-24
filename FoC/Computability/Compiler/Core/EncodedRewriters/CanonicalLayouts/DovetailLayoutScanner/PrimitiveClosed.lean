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

namespace EncodedRewriters
namespace CanonicalLayouts
namespace DovetailLayoutScanner

open FoC.Computability.DovetailInitialLayoutInitializer
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner

theorem cellListSuffixScannerDescription_runConfig_start_cell_inv
    (baseLeft : List (Option Bool)) (first : Option Bool)
    (suffixTail : List (Option Bool))
    {Tout : Tape Bool} {n : Nat}
    (h :
      CellListSuffixScannerDescription.runConfig n
          (config CellListSuffixScannerDescription.start baseLeft
            (first :: suffixTail)) =
        { state := CellListSuffixScannerDescription.halt
          tape := Tout }) :
      first = some false := by
  cases first with
  | none =>
      exfalso
      cases n with
      | zero =>
          simp [CellListSuffixScannerDescription, config, tapeAtCells,
            MachineDescription.runConfig] at h
      | succ k =>
          let c0 : MachineDescription.Configuration :=
            config CellListSuffixScannerDescription.start baseLeft
              (none :: suffixTail)
          have hstep :
              CellListSuffixScannerDescription.stepConfig c0 = none := by
            cases suffixTail <;>
              simp [c0, CellListSuffixScannerDescription, config,
                tapeAtCells, keep, keepMove, writeMove,
                scanLeftToSentinelRestart,
                MachineDescription.stepConfig,
                MachineDescription.lookupTransition,
                MachineDescription.Matches,
                MachineDescription.transition, Tape.read]
          have hstay :
              CellListSuffixScannerDescription.runConfig (Nat.succ k) c0 =
                c0 := by
            exact MachineDescription.runConfig_of_stepConfig_none hstep
              (Nat.succ k)
          have hstate :=
            congrArg MachineDescription.Configuration.state
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
                MachineDescription.runConfig] at h
          | succ k =>
              let c0 : MachineDescription.Configuration :=
                config CellListSuffixScannerDescription.start baseLeft
                  (some true :: suffixTail)
              have hstep :
                  CellListSuffixScannerDescription.stepConfig c0 = none := by
                cases suffixTail <;>
                  simp [c0, CellListSuffixScannerDescription, config,
                    tapeAtCells, keep, keepMove, writeMove,
                    scanLeftToSentinelRestart,
                    MachineDescription.stepConfig,
                    MachineDescription.lookupTransition,
                    MachineDescription.Matches,
                    MachineDescription.transition, Tape.read]
              have hstay :
                  CellListSuffixScannerDescription.runConfig (Nat.succ k)
                      c0 =
                    c0 := by
                exact MachineDescription.runConfig_of_stepConfig_none hstep
                  (Nat.succ k)
              have hstate :=
                congrArg MachineDescription.Configuration.state
                  (hstay.symm.trans (by simpa [c0] using h))
              simp [c0, config, CellListSuffixScannerDescription] at hstate

theorem cellListSuffixScannerDescription_runConfig_start_bit_inv
    (baseLeft : List (Option Bool)) (first : Bool)
    (suffixTail : List (Option Bool))
    {Tout : Tape Bool} {n : Nat}
    (h :
      CellListSuffixScannerDescription.runConfig n
          (config CellListSuffixScannerDescription.start baseLeft
            (some first :: suffixTail)) =
        { state := CellListSuffixScannerDescription.halt
          tape := Tout }) :
      first = false := by
  have hcell :=
    cellListSuffixScannerDescription_runConfig_start_cell_inv
      baseLeft (some first) suffixTail h
  cases first <;> simp at hcell ⊢

theorem primitive_runConfig_state_ne_halt_of_reaches_stuck
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

theorem cellListSuffixScannerDescription_runConfig_start_nat_prefix_inv
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    {Tout : Tape Bool} {n : Nat}
    (h :
      CellListSuffixScannerDescription.runConfig n
          (config CellListSuffixScannerDescription.start baseLeft
            (bits.map some)) =
        { state := CellListSuffixScannerDescription.halt
          tape := Tout }) :
    exists doneBit : Bool,
    exists tail : Word Bool,
      bits = false :: false :: true :: doneBit :: tail := by
  let start : MachineDescription.Configuration :=
    config CellListSuffixScannerDescription.start baseLeft (bits.map some)
  have hhaltState :
      (CellListSuffixScannerDescription.runConfig n start).state =
        CellListSuffixScannerDescription.halt := by
    simpa [start] using
      congrArg MachineDescription.Configuration.state h
  cases bits with
  | nil =>
      let stuck : MachineDescription.Configuration := start
      have hstep :
          CellListSuffixScannerDescription.stepConfig stuck = none := by
        simp [stuck, start, CellListSuffixScannerDescription, config,
          tapeAtCells, keep, keepMove, writeMove,
          scanLeftToSentinelRestart, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read]
      have hstuck :
          stuck.state ≠ CellListSuffixScannerDescription.halt := by
        simp [stuck, start, CellListSuffixScannerDescription, config]
      exact False.elim
        (primitive_runConfig_state_ne_halt_of_reaches_stuck
          cellListSuffixScannerDescription_haltTransitionFree
          (D := CellListSuffixScannerDescription)
          (c := start) (stuck := stuck) (k := 0) (n := n)
          rfl hstep hstuck hhaltState)
  | cons first rest =>
      cases first
      · cases rest with
        | nil =>
            let stuck :=
              CellListSuffixScannerDescription.runConfig 1 start
            have hstep :
                CellListSuffixScannerDescription.stepConfig stuck = none := by
              simp [stuck, start, CellListSuffixScannerDescription, config,
                tapeAtCells, keep, keepMove, writeMove,
                scanLeftToSentinelRestart, MachineDescription.runConfig,
                MachineDescription.stepConfig,
                MachineDescription.lookupTransition,
                MachineDescription.Matches,
                MachineDescription.transition, Tape.read, Tape.write,
                Tape.move, Tape.moveRight]
            have hstuck :
                stuck.state ≠ CellListSuffixScannerDescription.halt := by
              simp [stuck, start, CellListSuffixScannerDescription, config,
                tapeAtCells, keep, keepMove, writeMove,
                scanLeftToSentinelRestart, MachineDescription.runConfig,
                MachineDescription.stepConfig,
                MachineDescription.lookupTransition,
                MachineDescription.Matches,
                MachineDescription.transition, Tape.read, Tape.write,
                Tape.move, Tape.moveRight]
            exact False.elim
              (primitive_runConfig_state_ne_halt_of_reaches_stuck
                cellListSuffixScannerDescription_haltTransitionFree
                (D := CellListSuffixScannerDescription)
                (c := start) (stuck := stuck) (k := 1) (n := n)
                rfl hstep hstuck hhaltState)
        | cons second restTail =>
            cases second
            · cases restTail with
              | nil =>
                  let stuck :=
                    CellListSuffixScannerDescription.runConfig 2 start
                  have hstep :
                      CellListSuffixScannerDescription.stepConfig stuck =
                        none := by
                    simp [stuck, start, CellListSuffixScannerDescription,
                      config, tapeAtCells, keep, keepMove, writeMove,
                      scanLeftToSentinelRestart,
                      MachineDescription.runConfig,
                      MachineDescription.stepConfig,
                      MachineDescription.lookupTransition,
                      MachineDescription.Matches,
                      MachineDescription.transition, Tape.read, Tape.write,
                      Tape.move, Tape.moveRight]
                  have hstuck :
                      stuck.state ≠
                        CellListSuffixScannerDescription.halt := by
                    simp [stuck, start, CellListSuffixScannerDescription,
                      config, tapeAtCells, keep, keepMove, writeMove,
                      scanLeftToSentinelRestart,
                      MachineDescription.runConfig,
                      MachineDescription.stepConfig,
                      MachineDescription.lookupTransition,
                      MachineDescription.Matches,
                      MachineDescription.transition, Tape.read, Tape.write,
                      Tape.move, Tape.moveRight]
                  exact False.elim
                    (primitive_runConfig_state_ne_halt_of_reaches_stuck
                      cellListSuffixScannerDescription_haltTransitionFree
                      (D := CellListSuffixScannerDescription)
                      (c := start) (stuck := stuck) (k := 2) (n := n)
                      rfl hstep hstuck hhaltState)
              | cons third tail =>
                  cases third
                  · let stuck :=
                      CellListSuffixScannerDescription.runConfig 2 start
                    have hstep :
                        CellListSuffixScannerDescription.stepConfig stuck =
                          none := by
                      cases tail <;>
                        simp [stuck, start,
                          CellListSuffixScannerDescription, config,
                          tapeAtCells, keep, keepMove, writeMove,
                          scanLeftToSentinelRestart,
                          MachineDescription.runConfig,
                          MachineDescription.stepConfig,
                          MachineDescription.lookupTransition,
                          MachineDescription.Matches,
                          MachineDescription.transition, Tape.read,
                          Tape.write, Tape.move, Tape.moveRight]
                    have hstuck :
                        stuck.state ≠
                          CellListSuffixScannerDescription.halt := by
                      cases tail <;>
                        simp [stuck, start,
                          CellListSuffixScannerDescription, config,
                          tapeAtCells, keep, keepMove, writeMove,
                          scanLeftToSentinelRestart,
                          MachineDescription.runConfig,
                          MachineDescription.stepConfig,
                          MachineDescription.lookupTransition,
                          MachineDescription.Matches,
                          MachineDescription.transition, Tape.read,
                          Tape.write, Tape.move, Tape.moveRight]
                    exact False.elim
                      (primitive_runConfig_state_ne_halt_of_reaches_stuck
                        cellListSuffixScannerDescription_haltTransitionFree
                        (D := CellListSuffixScannerDescription)
                        (c := start) (stuck := stuck) (k := 2) (n := n)
                        rfl hstep hstuck hhaltState)
                  · cases tail with
                    | nil =>
                        let stuck :=
                          CellListSuffixScannerDescription.runConfig 4 start
                        have hstep :
                            CellListSuffixScannerDescription.stepConfig
                                stuck = none := by
                          simp [stuck, start,
                            CellListSuffixScannerDescription, config,
                            tapeAtCells, keep, keepMove, writeMove,
                            scanLeftToSentinelRestart,
                            MachineDescription.runConfig,
                            MachineDescription.stepConfig,
                            MachineDescription.lookupTransition,
                            MachineDescription.Matches,
                            MachineDescription.transition, Tape.read,
                            Tape.write, Tape.move, Tape.moveRight]
                        have hstuck :
                            stuck.state ≠
                              CellListSuffixScannerDescription.halt := by
                          simp [stuck, start,
                            CellListSuffixScannerDescription, config,
                            tapeAtCells, keep, keepMove, writeMove,
                            scanLeftToSentinelRestart,
                            MachineDescription.runConfig,
                            MachineDescription.stepConfig,
                            MachineDescription.lookupTransition,
                            MachineDescription.Matches,
                            MachineDescription.transition, Tape.read,
                            Tape.write, Tape.move, Tape.moveRight]
                        exact False.elim
                          (primitive_runConfig_state_ne_halt_of_reaches_stuck
                            cellListSuffixScannerDescription_haltTransitionFree
                            (D := CellListSuffixScannerDescription)
                            (c := start) (stuck := stuck) (k := 4)
                            (n := n) rfl hstep hstuck hhaltState)
                    | cons doneBit tailRest =>
                        exact ⟨doneBit, tailRest, rfl⟩
            · let stuck :=
                CellListSuffixScannerDescription.runConfig 1 start
              have hstep :
                  CellListSuffixScannerDescription.stepConfig stuck = none := by
                cases restTail <;>
                  simp [stuck, start, CellListSuffixScannerDescription,
                    config, tapeAtCells, keep, keepMove, writeMove,
                    scanLeftToSentinelRestart,
                    MachineDescription.runConfig,
                    MachineDescription.stepConfig,
                    MachineDescription.lookupTransition,
                    MachineDescription.Matches,
                    MachineDescription.transition, Tape.read, Tape.write,
                    Tape.move, Tape.moveRight]
              have hstuck :
                  stuck.state ≠ CellListSuffixScannerDescription.halt := by
                cases restTail <;>
                  simp [stuck, start, CellListSuffixScannerDescription,
                    config, tapeAtCells, keep, keepMove, writeMove,
                    scanLeftToSentinelRestart,
                    MachineDescription.runConfig,
                    MachineDescription.stepConfig,
                    MachineDescription.lookupTransition,
                    MachineDescription.Matches,
                    MachineDescription.transition, Tape.read, Tape.write,
                    Tape.move, Tape.moveRight]
              exact False.elim
                (primitive_runConfig_state_ne_halt_of_reaches_stuck
                  cellListSuffixScannerDescription_haltTransitionFree
                  (D := CellListSuffixScannerDescription)
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
      BoolWordSuffixScannerDescription.runConfig n
          (config BoolWordSuffixScannerDescription.start baseLeft
            (first :: suffixTail)) =
        { state := BoolWordSuffixScannerDescription.halt
          tape := Tout }) :
      first = some false := by
  cases first with
  | none =>
      exfalso
      cases n with
      | zero =>
          simp [BoolWordSuffixScannerDescription, config, tapeAtCells,
            MachineDescription.runConfig] at h
      | succ k =>
          let c0 : MachineDescription.Configuration :=
            config BoolWordSuffixScannerDescription.start baseLeft
              (none :: suffixTail)
          have hstep :
              BoolWordSuffixScannerDescription.stepConfig c0 = none := by
            cases suffixTail <;>
              simp [c0, BoolWordSuffixScannerDescription, config,
                tapeAtCells, keep, keepMove, writeMove,
                scanLeftToSentinelRestart,
                MachineDescription.stepConfig,
                MachineDescription.lookupTransition,
                MachineDescription.Matches,
                MachineDescription.transition, Tape.read]
          have hstay :
              BoolWordSuffixScannerDescription.runConfig (Nat.succ k) c0 =
                c0 := by
            exact MachineDescription.runConfig_of_stepConfig_none hstep
              (Nat.succ k)
          have hstate :=
            congrArg MachineDescription.Configuration.state
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
                MachineDescription.runConfig] at h
          | succ k =>
              let c0 : MachineDescription.Configuration :=
                config BoolWordSuffixScannerDescription.start baseLeft
                  (some true :: suffixTail)
              have hstep :
                  BoolWordSuffixScannerDescription.stepConfig c0 = none := by
                cases suffixTail <;>
                  simp [c0, BoolWordSuffixScannerDescription, config,
                    tapeAtCells, keep, keepMove, writeMove,
                    scanLeftToSentinelRestart,
                    MachineDescription.stepConfig,
                    MachineDescription.lookupTransition,
                    MachineDescription.Matches,
                    MachineDescription.transition, Tape.read]
              have hstay :
                  BoolWordSuffixScannerDescription.runConfig (Nat.succ k)
                      c0 =
                    c0 := by
                exact MachineDescription.runConfig_of_stepConfig_none hstep
                  (Nat.succ k)
              have hstate :=
                congrArg MachineDescription.Configuration.state
                  (hstay.symm.trans (by simpa [c0] using h))
              simp [c0, config, BoolWordSuffixScannerDescription] at hstate

theorem boolWordSuffixScannerDescription_runConfig_start_bit_inv
    (baseLeft : List (Option Bool)) (first : Bool)
    (suffixTail : List (Option Bool))
    {Tout : Tape Bool} {n : Nat}
    (h :
      BoolWordSuffixScannerDescription.runConfig n
          (config BoolWordSuffixScannerDescription.start baseLeft
            (some first :: suffixTail)) =
        { state := BoolWordSuffixScannerDescription.halt
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
      BoolWordSuffixScannerDescription.runConfig n
          (config BoolWordSuffixScannerDescription.start baseLeft
            (bits.map some)) =
        { state := BoolWordSuffixScannerDescription.halt
          tape := Tout }) :
    exists doneBit : Bool,
    exists tail : Word Bool,
      bits = false :: false :: true :: doneBit :: tail := by
  let start : MachineDescription.Configuration :=
    config BoolWordSuffixScannerDescription.start baseLeft (bits.map some)
  have hhaltState :
      (BoolWordSuffixScannerDescription.runConfig n start).state =
        BoolWordSuffixScannerDescription.halt := by
    simpa [start] using
      congrArg MachineDescription.Configuration.state h
  cases bits with
  | nil =>
      let stuck : MachineDescription.Configuration := start
      have hstep :
          BoolWordSuffixScannerDescription.stepConfig stuck = none := by
        simp [stuck, start, BoolWordSuffixScannerDescription, config,
          tapeAtCells, keep, keepMove, writeMove,
          scanLeftToSentinelRestart, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read]
      have hstuck :
          stuck.state ≠ BoolWordSuffixScannerDescription.halt := by
        simp [stuck, start, BoolWordSuffixScannerDescription, config]
      exact False.elim
        (primitive_runConfig_state_ne_halt_of_reaches_stuck
          boolWordSuffixScannerDescription_haltTransitionFree
          (D := BoolWordSuffixScannerDescription)
          (c := start) (stuck := stuck) (k := 0) (n := n)
          rfl hstep hstuck hhaltState)
  | cons first rest =>
      cases first
      · cases rest with
        | nil =>
            let stuck :=
              BoolWordSuffixScannerDescription.runConfig 1 start
            have hstep :
                BoolWordSuffixScannerDescription.stepConfig stuck = none := by
              simp [stuck, start, BoolWordSuffixScannerDescription, config,
                tapeAtCells, keep, keepMove, writeMove,
                scanLeftToSentinelRestart, MachineDescription.runConfig,
                MachineDescription.stepConfig,
                MachineDescription.lookupTransition,
                MachineDescription.Matches,
                MachineDescription.transition, Tape.read, Tape.write,
                Tape.move, Tape.moveRight]
            have hstuck :
                stuck.state ≠ BoolWordSuffixScannerDescription.halt := by
              simp [stuck, start, BoolWordSuffixScannerDescription, config,
                tapeAtCells, keep, keepMove, writeMove,
                scanLeftToSentinelRestart, MachineDescription.runConfig,
                MachineDescription.stepConfig,
                MachineDescription.lookupTransition,
                MachineDescription.Matches,
                MachineDescription.transition, Tape.read, Tape.write,
                Tape.move, Tape.moveRight]
            exact False.elim
              (primitive_runConfig_state_ne_halt_of_reaches_stuck
                boolWordSuffixScannerDescription_haltTransitionFree
                (D := BoolWordSuffixScannerDescription)
                (c := start) (stuck := stuck) (k := 1) (n := n)
                rfl hstep hstuck hhaltState)
        | cons second restTail =>
            cases second
            · cases restTail with
              | nil =>
                  let stuck :=
                    BoolWordSuffixScannerDescription.runConfig 2 start
                  have hstep :
                      BoolWordSuffixScannerDescription.stepConfig stuck =
                        none := by
                    simp [stuck, start, BoolWordSuffixScannerDescription,
                      config, tapeAtCells, keep, keepMove, writeMove,
                      scanLeftToSentinelRestart,
                      MachineDescription.runConfig,
                      MachineDescription.stepConfig,
                      MachineDescription.lookupTransition,
                      MachineDescription.Matches,
                      MachineDescription.transition, Tape.read, Tape.write,
                      Tape.move, Tape.moveRight]
                  have hstuck :
                      stuck.state ≠
                        BoolWordSuffixScannerDescription.halt := by
                    simp [stuck, start, BoolWordSuffixScannerDescription,
                      config, tapeAtCells, keep, keepMove, writeMove,
                      scanLeftToSentinelRestart,
                      MachineDescription.runConfig,
                      MachineDescription.stepConfig,
                      MachineDescription.lookupTransition,
                      MachineDescription.Matches,
                      MachineDescription.transition, Tape.read, Tape.write,
                      Tape.move, Tape.moveRight]
                  exact False.elim
                    (primitive_runConfig_state_ne_halt_of_reaches_stuck
                      boolWordSuffixScannerDescription_haltTransitionFree
                      (D := BoolWordSuffixScannerDescription)
                      (c := start) (stuck := stuck) (k := 2) (n := n)
                      rfl hstep hstuck hhaltState)
              | cons third tail =>
                  cases third
                  · let stuck :=
                      BoolWordSuffixScannerDescription.runConfig 2 start
                    have hstep :
                        BoolWordSuffixScannerDescription.stepConfig stuck =
                          none := by
                      cases tail <;>
                        simp [stuck, start,
                          BoolWordSuffixScannerDescription, config,
                          tapeAtCells, keep, keepMove, writeMove,
                          scanLeftToSentinelRestart,
                          MachineDescription.runConfig,
                          MachineDescription.stepConfig,
                          MachineDescription.lookupTransition,
                          MachineDescription.Matches,
                          MachineDescription.transition, Tape.read,
                          Tape.write, Tape.move, Tape.moveRight]
                    have hstuck :
                        stuck.state ≠
                          BoolWordSuffixScannerDescription.halt := by
                      cases tail <;>
                        simp [stuck, start,
                          BoolWordSuffixScannerDescription, config,
                          tapeAtCells, keep, keepMove, writeMove,
                          scanLeftToSentinelRestart,
                          MachineDescription.runConfig,
                          MachineDescription.stepConfig,
                          MachineDescription.lookupTransition,
                          MachineDescription.Matches,
                          MachineDescription.transition, Tape.read,
                          Tape.write, Tape.move, Tape.moveRight]
                    exact False.elim
                      (primitive_runConfig_state_ne_halt_of_reaches_stuck
                        boolWordSuffixScannerDescription_haltTransitionFree
                        (D := BoolWordSuffixScannerDescription)
                        (c := start) (stuck := stuck) (k := 2) (n := n)
                        rfl hstep hstuck hhaltState)
                  · cases tail with
                    | nil =>
                        let stuck :=
                          BoolWordSuffixScannerDescription.runConfig 4 start
                        have hstep :
                            BoolWordSuffixScannerDescription.stepConfig
                                stuck = none := by
                          simp [stuck, start,
                            BoolWordSuffixScannerDescription, config,
                            tapeAtCells, keep, keepMove, writeMove,
                            scanLeftToSentinelRestart,
                            MachineDescription.runConfig,
                            MachineDescription.stepConfig,
                            MachineDescription.lookupTransition,
                            MachineDescription.Matches,
                            MachineDescription.transition, Tape.read,
                            Tape.write, Tape.move, Tape.moveRight]
                        have hstuck :
                            stuck.state ≠
                              BoolWordSuffixScannerDescription.halt := by
                          simp [stuck, start,
                            BoolWordSuffixScannerDescription, config,
                            tapeAtCells, keep, keepMove, writeMove,
                            scanLeftToSentinelRestart,
                            MachineDescription.runConfig,
                            MachineDescription.stepConfig,
                            MachineDescription.lookupTransition,
                            MachineDescription.Matches,
                            MachineDescription.transition, Tape.read,
                            Tape.write, Tape.move, Tape.moveRight]
                        exact False.elim
                          (primitive_runConfig_state_ne_halt_of_reaches_stuck
                            boolWordSuffixScannerDescription_haltTransitionFree
                            (D := BoolWordSuffixScannerDescription)
                            (c := start) (stuck := stuck) (k := 4)
                            (n := n) rfl hstep hstuck hhaltState)
                    | cons doneBit tailRest =>
                        exact ⟨doneBit, tailRest, rfl⟩
            · let stuck :=
                BoolWordSuffixScannerDescription.runConfig 1 start
              have hstep :
                  BoolWordSuffixScannerDescription.stepConfig stuck = none := by
                cases restTail <;>
                  simp [stuck, start, BoolWordSuffixScannerDescription,
                    config, tapeAtCells, keep, keepMove, writeMove,
                    scanLeftToSentinelRestart,
                    MachineDescription.runConfig,
                    MachineDescription.stepConfig,
                    MachineDescription.lookupTransition,
                    MachineDescription.Matches,
                    MachineDescription.transition, Tape.read, Tape.write,
                    Tape.move, Tape.moveRight]
              have hstuck :
                  stuck.state ≠ BoolWordSuffixScannerDescription.halt := by
                cases restTail <;>
                  simp [stuck, start, BoolWordSuffixScannerDescription,
                    config, tapeAtCells, keep, keepMove, writeMove,
                    scanLeftToSentinelRestart,
                    MachineDescription.runConfig,
                    MachineDescription.stepConfig,
                    MachineDescription.lookupTransition,
                    MachineDescription.Matches,
                    MachineDescription.transition, Tape.read, Tape.write,
                    Tape.move, Tape.moveRight]
              exact False.elim
                (primitive_runConfig_state_ne_halt_of_reaches_stuck
                  boolWordSuffixScannerDescription_haltTransitionFree
                  (D := BoolWordSuffixScannerDescription)
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
      DovetailStagePrefix.NatSuffixScannerDescription.runConfig n
          (config DovetailStagePrefix.NatSuffixScannerDescription.start
            baseLeft
            (List.append ((stageNatBits stage).map some)
              (some b :: suffixTail))) =
        { state := DovetailStagePrefix.NatSuffixScannerDescription.halt
          tape := Tout }) :
      Tout = Tape.move Direction.left
        (tapeAtCells
          (List.append ((stageNatBits stage).reverse.map some) baseLeft)
          (some b :: suffixTail)) := by
  let c0 : MachineDescription.Configuration :=
    config DovetailStagePrefix.NatSuffixScannerDescription.start baseLeft
      (List.append ((stageNatBits stage).map some) (some b :: suffixTail))
  let Tfinal : Tape Bool :=
    Tape.move Direction.left
      (tapeAtCells
        (List.append ((stageNatBits stage).reverse.map some) baseLeft)
        (some b :: suffixTail))
  have hforward :
      DovetailStagePrefix.NatSuffixScannerDescription.runConfig
          (4 * stage + 5) c0 =
        { state := DovetailStagePrefix.NatSuffixScannerDescription.halt
          tape := Tfinal } := by
    rcases
        DovetailStagePrefix.stageNatBits_reverse_map_some_cons stage with
      ⟨tail, htail⟩
    rw [show 4 * stage + 5 = (4 * stage + 4) + 1 by omega]
    rw [MachineDescription.runConfig_add]
    have hprefix :=
      DovetailStagePrefix.natSuffix_run_state200_stageNat_to_state210
        stage baseLeft (some b :: suffixTail)
    rw [show
        DovetailStagePrefix.NatSuffixScannerDescription.runConfig
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

theorem boolWordSuffixScannerDescription_runConfig_canonical_false_suffix_inv
    (bits : Word Bool) (baseLeft : List (Option Bool)) (suffixTail : Word Bool)
    {Tout : Tape Bool} {n : Nat}
    (h :
      BoolWordSuffixScannerDescription.runConfig n
          (config BoolWordSuffixScannerDescription.start baseLeft
            (List.append ((stageNatBits bits.length).map some)
              (List.append ((cellsCodeBits (bits.map some)).map some)
                (some false :: suffixTail.map some)))) =
        { state := BoolWordSuffixScannerDescription.halt
          tape := Tout }) :
      Tout =
        (boolWordCanonicalHandoffConfigWithBase bits baseLeft
          (false :: suffixTail)).tape := by
  let c0 : MachineDescription.Configuration :=
    config BoolWordSuffixScannerDescription.start baseLeft
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
      CellListSuffixScannerDescription.runConfig n
          (config CellListSuffixScannerDescription.start baseLeft
            (List.append ((stageNatBits cells.length).map some)
              (List.append ((cellsCodeBits cells).map some)
                (some false :: suffixTail.map some)))) =
        { state := CellListSuffixScannerDescription.halt
          tape := Tout }) :
      Tout =
        (cellListCanonicalHandoffConfigWithBase cells baseLeft
          (false :: suffixTail)).tape := by
  let c0 : MachineDescription.Configuration :=
    config CellListSuffixScannerDescription.start baseLeft
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
  let c0 : MachineDescription.Configuration :=
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
    (cfg : MachineDescription.Configuration)
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
  let c0 : MachineDescription.Configuration :=
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
  let c0 : MachineDescription.Configuration :=
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
    (acceptConfig rejectConfig : MachineDescription.Configuration)
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
  let c0 : MachineDescription.Configuration :=
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
    (acceptConfig rejectConfig : MachineDescription.Configuration)
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
  let c0 : MachineDescription.Configuration :=
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
    (acceptConfig rejectConfig : MachineDescription.Configuration)
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
  let c0 : MachineDescription.Configuration :=
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

theorem boolSuffixScannerDescription_runConfig_suffix_inv
    (flag : Bool) (baseLeft suffixCells : List (Option Bool))
    {Tout : Tape Bool} {n : Nat}
    (h :
      BoolSuffixScannerDescription.runConfig n
          { state := BoolSuffixScannerDescription.start
            tape := tapeAtCells baseLeft
              (List.append ((cellCodeBits (some flag)).map some)
                suffixCells) } =
        { state := BoolSuffixScannerDescription.halt
          tape := Tout }) :
    exists b : Bool,
    exists suffixTail : List (Option Bool),
      suffixCells = some b :: suffixTail ∧
        Tout = Tape.move Direction.left
          (tapeAtCells
            (List.append ((cellCodeBits (some flag)).reverse.map some)
              baseLeft)
            (some b :: suffixTail)) := by
  cases hflag : flag <;> cases n with
  | zero =>
      simp [BoolSuffixScannerDescription, MachineDescription.runConfig] at h
  | succ n1 =>
      cases n1 with
      | zero =>
          simp [hflag, BoolSuffixScannerDescription,
            MachineDescription.runConfig, MachineDescription.stepConfig,
            MachineDescription.lookupTransition,
            MachineDescription.Matches, MachineDescription.transition,
            keepMove, cellCodeBits, MachineDescription.encodeCell,
            MachineDescription.encodeCodeWordAsInput,
            MachineDescription.encodeCodeSymbolAsInput,
            tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight] at h
      | succ n2 =>
        cases n2 with
        | zero =>
          simp [hflag, BoolSuffixScannerDescription,
            MachineDescription.runConfig, MachineDescription.stepConfig,
            MachineDescription.lookupTransition,
            MachineDescription.Matches, MachineDescription.transition,
            keepMove, cellCodeBits, MachineDescription.encodeCell,
            MachineDescription.encodeCodeWordAsInput,
            MachineDescription.encodeCodeSymbolAsInput,
            tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight] at h
        | succ n3 =>
          cases n3 with
          | zero =>
            simp [hflag, BoolSuffixScannerDescription,
              MachineDescription.runConfig, MachineDescription.stepConfig,
              MachineDescription.lookupTransition,
              MachineDescription.Matches, MachineDescription.transition,
              keepMove, cellCodeBits, MachineDescription.encodeCell,
              MachineDescription.encodeCodeWordAsInput,
              MachineDescription.encodeCodeSymbolAsInput,
              tapeAtCells, Tape.read, Tape.write, Tape.move,
              Tape.moveRight] at h
          | succ n4 =>
            cases n4 with
            | zero =>
              simp [hflag, BoolSuffixScannerDescription,
                MachineDescription.runConfig, MachineDescription.stepConfig,
                MachineDescription.lookupTransition,
                MachineDescription.Matches, MachineDescription.transition,
                keepMove, cellCodeBits, MachineDescription.encodeCell,
                MachineDescription.encodeCodeWordAsInput,
                MachineDescription.encodeCodeSymbolAsInput,
                tapeAtCells, Tape.read, Tape.write, Tape.move,
                Tape.moveRight] at h
            | succ n5 =>
              cases suffixCells with
              | nil =>
                simp [hflag, BoolSuffixScannerDescription,
                  MachineDescription.runConfig, MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches, MachineDescription.transition,
                  keepMove, cellCodeBits, MachineDescription.encodeCell,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  tapeAtCells, Tape.read, Tape.write, Tape.move,
                  Tape.moveRight] at h
              | cons term rest =>
                cases term with
                | none =>
                  simp [hflag, BoolSuffixScannerDescription,
                    MachineDescription.runConfig, MachineDescription.stepConfig,
                    MachineDescription.lookupTransition,
                    MachineDescription.Matches, MachineDescription.transition,
                    keepMove, cellCodeBits, MachineDescription.encodeCell,
                    MachineDescription.encodeCodeWordAsInput,
                    MachineDescription.encodeCodeSymbolAsInput,
                    tapeAtCells, Tape.read, Tape.write, Tape.move,
                    Tape.moveRight] at h
                | some b =>
                  cases b
                  · refine ⟨false, rest, rfl, ?_⟩
                    let Tfinal : Tape Bool :=
                      Tape.move Direction.left
                        (tapeAtCells
                          (List.append
                            ((cellCodeBits (some flag)).reverse.map some)
                            baseLeft)
                          (some false :: rest))
                    have hsimp :
                        BoolSuffixScannerDescription.runConfig n5
                            { state := BoolSuffixScannerDescription.halt
                              tape := Tfinal } =
                          { state := BoolSuffixScannerDescription.halt
                            tape := Tout } := by
                      simpa [Tfinal, hflag, BoolSuffixScannerDescription,
                        MachineDescription.runConfig,
                        MachineDescription.stepConfig,
                        MachineDescription.lookupTransition,
                        MachineDescription.Matches,
                        MachineDescription.transition, keepMove, cellCodeBits,
                        MachineDescription.encodeCell,
                        MachineDescription.encodeCodeWordAsInput,
                        MachineDescription.encodeCodeSymbolAsInput,
                        tapeAtCells, Tape.read, Tape.write, Tape.move,
                        Tape.moveLeft, Tape.moveRight] using h
                    have hstay :=
                      MachineDescription.runConfig_halt
                        boolSuffixScannerDescription_haltTransitionFree
                        Tfinal n5
                    simpa [Tfinal, hflag] using
                      (congrArg MachineDescription.Configuration.tape
                        (hstay.symm.trans hsimp)).symm
                  · refine ⟨true, rest, rfl, ?_⟩
                    let Tfinal : Tape Bool :=
                      Tape.move Direction.left
                        (tapeAtCells
                          (List.append
                            ((cellCodeBits (some flag)).reverse.map some)
                            baseLeft)
                          (some true :: rest))
                    have hsimp :
                        BoolSuffixScannerDescription.runConfig n5
                            { state := BoolSuffixScannerDescription.halt
                              tape := Tfinal } =
                          { state := BoolSuffixScannerDescription.halt
                            tape := Tout } := by
                      simpa [Tfinal, hflag, BoolSuffixScannerDescription,
                        MachineDescription.runConfig,
                        MachineDescription.stepConfig,
                        MachineDescription.lookupTransition,
                        MachineDescription.Matches,
                        MachineDescription.transition, keepMove, cellCodeBits,
                        MachineDescription.encodeCell,
                        MachineDescription.encodeCodeWordAsInput,
                        MachineDescription.encodeCodeSymbolAsInput,
                        tapeAtCells, Tape.read, Tape.write, Tape.move,
                        Tape.moveLeft, Tape.moveRight] using h
                    have hstay :=
                      MachineDescription.runConfig_halt
                        boolSuffixScannerDescription_haltTransitionFree
                        Tfinal n5
                    simpa [Tfinal, hflag] using
                      (congrArg MachineDescription.Configuration.tape
                        (hstay.symm.trans hsimp)).symm

theorem boolFinalScannerDescription_runConfig_terminal_inv
    (flag : Bool) (baseLeft terminalCells : List (Option Bool))
    {Tout : Tape Bool} {n : Nat}
    (h :
      BoolFinalScannerDescription.runConfig n
          { state := BoolFinalScannerDescription.start
            tape := tapeAtCells baseLeft
              (List.append ((cellCodeBits (some flag)).map some)
                terminalCells) } =
        { state := BoolFinalScannerDescription.halt
          tape := Tout }) :
    (terminalCells = [] ∨
      exists rest : List (Option Bool), terminalCells = none :: rest) ∧
      Tout = Tape.move Direction.left
        (tapeAtCells
          (List.append ((cellCodeBits (some flag)).reverse.map some)
            baseLeft)
          terminalCells) := by
  cases hflag : flag <;> cases n with
  | zero =>
      simp [BoolFinalScannerDescription, MachineDescription.runConfig] at h
  | succ n1 =>
      cases n1 with
      | zero =>
          simp [hflag, BoolFinalScannerDescription,
            MachineDescription.runConfig, MachineDescription.stepConfig,
            MachineDescription.lookupTransition,
            MachineDescription.Matches, MachineDescription.transition,
            keepMove, cellCodeBits, MachineDescription.encodeCell,
            MachineDescription.encodeCodeWordAsInput,
            MachineDescription.encodeCodeSymbolAsInput,
            tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight] at h
      | succ n2 =>
        cases n2 with
        | zero =>
          simp [hflag, BoolFinalScannerDescription,
            MachineDescription.runConfig, MachineDescription.stepConfig,
            MachineDescription.lookupTransition,
            MachineDescription.Matches, MachineDescription.transition,
            keepMove, cellCodeBits, MachineDescription.encodeCell,
            MachineDescription.encodeCodeWordAsInput,
            MachineDescription.encodeCodeSymbolAsInput,
            tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight] at h
        | succ n3 =>
          cases n3 with
          | zero =>
            simp [hflag, BoolFinalScannerDescription,
              MachineDescription.runConfig, MachineDescription.stepConfig,
              MachineDescription.lookupTransition,
              MachineDescription.Matches, MachineDescription.transition,
              keepMove, cellCodeBits, MachineDescription.encodeCell,
              MachineDescription.encodeCodeWordAsInput,
              MachineDescription.encodeCodeSymbolAsInput,
              tapeAtCells, Tape.read, Tape.write, Tape.move,
              Tape.moveRight] at h
          | succ n4 =>
            cases n4 with
            | zero =>
              simp [hflag, BoolFinalScannerDescription,
                MachineDescription.runConfig, MachineDescription.stepConfig,
                MachineDescription.lookupTransition,
                MachineDescription.Matches, MachineDescription.transition,
                keepMove, cellCodeBits, MachineDescription.encodeCell,
                MachineDescription.encodeCodeWordAsInput,
                MachineDescription.encodeCodeSymbolAsInput,
                tapeAtCells, Tape.read, Tape.write, Tape.move,
                Tape.moveRight] at h
            | succ n5 =>
              cases terminalCells with
              | nil =>
                constructor
                · exact Or.inl rfl
                · let Tfinal : Tape Bool :=
                    Tape.move Direction.left
                      (tapeAtCells
                        (List.append
                          ((cellCodeBits (some flag)).reverse.map some)
                          baseLeft)
                        [])
                  have hsimp :
                      BoolFinalScannerDescription.runConfig n5
                          { state := BoolFinalScannerDescription.halt
                            tape := Tfinal } =
                        { state := BoolFinalScannerDescription.halt
                          tape := Tout } := by
                    simpa [Tfinal, hflag, BoolFinalScannerDescription,
                      MachineDescription.runConfig,
                      MachineDescription.stepConfig,
                      MachineDescription.lookupTransition,
                      MachineDescription.Matches, MachineDescription.transition,
                      keepMove, cellCodeBits, MachineDescription.encodeCell,
                      MachineDescription.encodeCodeWordAsInput,
                      MachineDescription.encodeCodeSymbolAsInput,
                      tapeAtCells, Tape.read, Tape.write, Tape.move,
                      Tape.moveLeft, Tape.moveRight] using h
                  have hstay :=
                    MachineDescription.runConfig_halt
                      boolFinalScannerDescription_haltTransitionFree
                      Tfinal n5
                  simpa [Tfinal, hflag] using
                    (congrArg MachineDescription.Configuration.tape
                      (hstay.symm.trans hsimp)).symm
              | cons term rest =>
                cases term with
                | none =>
                  constructor
                  · exact Or.inr ⟨rest, rfl⟩
                  · let Tfinal : Tape Bool :=
                      Tape.move Direction.left
                        (tapeAtCells
                          (List.append
                            ((cellCodeBits (some flag)).reverse.map some)
                            baseLeft)
                          (none :: rest))
                    have hsimp :
                        BoolFinalScannerDescription.runConfig n5
                            { state := BoolFinalScannerDescription.halt
                              tape := Tfinal } =
                          { state := BoolFinalScannerDescription.halt
                            tape := Tout } := by
                      simpa [Tfinal, hflag, BoolFinalScannerDescription,
                        MachineDescription.runConfig,
                        MachineDescription.stepConfig,
                        MachineDescription.lookupTransition,
                        MachineDescription.Matches,
                        MachineDescription.transition, keepMove, cellCodeBits,
                        MachineDescription.encodeCell,
                        MachineDescription.encodeCodeWordAsInput,
                        MachineDescription.encodeCodeSymbolAsInput,
                        tapeAtCells, Tape.read, Tape.write, Tape.move,
                        Tape.moveLeft, Tape.moveRight] using h
                    have hstay :=
                      MachineDescription.runConfig_halt
                        boolFinalScannerDescription_haltTransitionFree
                        Tfinal n5
                    simpa [Tfinal, hflag] using
                      (congrArg MachineDescription.Configuration.tape
                        (hstay.symm.trans hsimp)).symm
                | some bit =>
                  cases bit <;>
                    simp [hflag, BoolFinalScannerDescription,
                      MachineDescription.runConfig,
                      MachineDescription.stepConfig,
                      MachineDescription.lookupTransition,
                      MachineDescription.Matches,
                      MachineDescription.transition, keepMove, cellCodeBits,
                      MachineDescription.encodeCell,
                      MachineDescription.encodeCodeWordAsInput,
                      MachineDescription.encodeCodeSymbolAsInput,
                      tapeAtCells, Tape.read, Tape.write, Tape.move,
                      Tape.moveRight] at h

theorem runConfig_forward_inv
    (D : MachineDescription) (c0 c1 : MachineDescription.Configuration)
    (n k : Nat) {Tout : Tape Bool}
    (h_halt : D.runConfig n c0 = { state := D.halt, tape := Tout })
    (h_forward : D.runConfig k c0 = c1)
    (h_free : D.HaltTransitionFree) :
    exists m, m ≤ n ∧ D.runConfig m c1 = { state := D.halt, tape := Tout } := by
  by_cases h_le : k ≤ n
  · exists n - k
    constructor
    · omega
    · have h_add : n = k + (n - k) := by omega
      rw [h_add, MachineDescription.runConfig_add] at h_halt
      rw [h_forward] at h_halt
      exact h_halt
  · exists 0
    constructor
    · omega
    · have h_add : k = n + (k - n) := by omega
      rw [h_add, MachineDescription.runConfig_add] at h_forward
      rw [h_halt] at h_forward
      have h_halt2 := MachineDescription.runConfig_halt h_free Tout (k - n)
      rw [h_halt2] at h_forward
      rw [← h_forward]
      rfl

theorem boolWordSuffixScannerDescription_runConfig_120_nat_prefix_inv
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    {Tout : Tape Bool} {n : Nat}
    (h : BoolWordSuffixScannerDescription.runConfig n (config 120 baseLeft (bits.map some)) = { state := BoolWordSuffixScannerDescription.halt, tape := Tout }) :
    exists doneBit tail, bits = false :: false :: true :: doneBit :: tail := by
  sorry

theorem boolWordSuffixScannerDescription_runConfig_120_inv
    (n : Nat) (baseLeft : List (Option Bool)) (tail : Word Bool)
    {Tout : Tape Bool}
    (h : BoolWordSuffixScannerDescription.runConfig n (config 120 baseLeft (tail.map some)) = { state := BoolWordSuffixScannerDescription.halt, tape := Tout }) :
    exists stage : Nat, exists tail' : Word Bool, tail = List.append (stageNatBits stage) tail' ∧
      BoolWordSuffixScannerDescription.runConfig n (config 130 (List.append ((stageNatBits stage).reverse.map some) baseLeft) (tail'.map some)) = { state := BoolWordSuffixScannerDescription.halt, tape := Tout } := by
  sorry

theorem boolWordSuffixScannerDescription_runConfig_130_marked_prefix_inv
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    {Tout : Tape Bool} {n : Nat}
    (h : BoolWordSuffixScannerDescription.runConfig n (config 130 baseLeft (bits.map some)) = { state := BoolWordSuffixScannerDescription.halt, tape := Tout }) :
    (exists tail, bits = false :: tail) ∨
    (exists cell tailRest, bits = List.append (markedCellCodeBits cell) tailRest) := by
  sorry

theorem boolWordSuffixScannerDescription_runConfig_130_inv
    (n : Nat) (baseLeft : List (Option Bool)) (tail : Word Bool)
    {Tout : Tape Bool}
    (h : BoolWordSuffixScannerDescription.runConfig n (config 130 baseLeft (tail.map some)) = { state := BoolWordSuffixScannerDescription.halt, tape := Tout }) :
    exists processed : List (Option Bool), exists tail' : Word Bool, tail = List.append (markedCellsCodeBits processed) tail' ∧
      (tail' = [] ∨ exists suffixTail, tail' = false :: suffixTail) ∧
      BoolWordSuffixScannerDescription.runConfig n (config 130 (List.append ((markedCellsCodeBits processed).reverse.map some) baseLeft) (tail'.map some)) = { state := BoolWordSuffixScannerDescription.halt, tape := Tout } := by
  sorry

theorem boolWordSuffixScannerDescription_runConfig_inv_helper
    (n : Nat) (baseLeft : List (Option Bool)) (inputBits : Word Bool)
    (processed : Word Bool)
    {Tout : Tape Bool}
    (h :
      BoolWordSuffixScannerDescription.runConfig n
          (config BoolWordSuffixScannerDescription.start baseLeft (inputBits.map some)) =
        { state := BoolWordSuffixScannerDescription.halt
          tape := Tout }) :
    exists remaining : Word Bool,
    exists suffixTail : Word Bool,
      inputBits =
        List.append (stageNatBits remaining.length)
          (List.append (markedCellsCodeBits (processed.map some))
            (List.append (cellsCodeBits (remaining.map some))
              (false :: suffixTail))) := by
  sorry

theorem boolWordSuffixScannerDescription_runConfig_inv
    (baseLeft : List (Option Bool)) (inputBits : Word Bool)
    {Tout : Tape Bool} {n : Nat}
    (h :
      BoolWordSuffixScannerDescription.runConfig n
          (config BoolWordSuffixScannerDescription.start baseLeft
            (inputBits.map some)) =
        { state := BoolWordSuffixScannerDescription.halt
          tape := Tout }) :
    exists bits : Word Bool,
    exists suffixTail : Word Bool,
      inputBits =
        List.append (stageNatBits bits.length)
          (List.append (cellsCodeBits (bits.map some))
            (false :: suffixTail)) := by
  sorry

end DovetailLayoutScanner
end CanonicalLayouts
end EncodedRewriters

end Computability
end FoC

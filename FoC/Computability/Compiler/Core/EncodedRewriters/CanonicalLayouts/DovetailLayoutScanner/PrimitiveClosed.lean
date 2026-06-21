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

end DovetailLayoutScanner
end CanonicalLayouts
end EncodedRewriters

end Computability
end FoC

import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.HeadRouter

set_option doc.verso true

/-!
# StageInputValidator

Stage-input recognizer and identity validator specifications.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace DovetailInitialLayoutInitializer

def StageInputIdentityPrimitive :
    TapeCodePrimitive where
  transform := fun code =>
    match DovetailLayout.decodeStageInputComplete code with
    | some _ => some code
    | none => none

theorem stageInputIdentityPrimitive_transform_eq_some_iff
    (code out : Word MachineCodeSymbol) :
    StageInputIdentityPrimitive.transform code = some out <->
      exists w : Word Bool,
      exists stage : Nat,
        code = PairedRecognizerDovetailStageInputCode w stage ∧
          out = PairedRecognizerDovetailStageInputCode w stage := by
  constructor
  · intro h
    unfold StageInputIdentityPrimitive at h
    cases hdecode :
        DovetailLayout.decodeStageInputComplete code with
    | none =>
        simp [hdecode] at h
    | some parsed =>
        cases parsed with
        | mk w stage =>
            simp [hdecode] at h
            cases h
            exact
              ⟨w, stage,
                DovetailLayout.decodeStageInputComplete_eq_some_stageInputCode
                  hdecode,
                DovetailLayout.decodeStageInputComplete_eq_some_stageInputCode
                  hdecode⟩
  · intro h
    rcases h with ⟨w, stage, rfl, rfl⟩
    simp [StageInputIdentityPrimitive,
      PairedRecognizerDovetailStageInputCode,
      DovetailLayout.decodeStageInputComplete_stageInputCode]

def stageInputSecondBitTail
    (w : Word Bool) (stage : Nat) : Word Bool :=
  match stageInputBits w stage with
  | _ :: _ :: tail => tail
  | _ => []

theorem stageInputBits_eq_false_false_tail
    (w : Word Bool) (stage : Nat) :
    stageInputBits w stage =
      false :: false :: stageInputSecondBitTail w stage := by
  cases w with
  | nil =>
      simp [stageInputSecondBitTail, stageInputBits,
        PairedRecognizerDovetailStageInputCode,
        DovetailLayout.stageInputCode,
        DovetailLayout.stageInputCodeAppend,
        encodeBoolWordAppend,
        encodeCellListAppend,
        encodeNatAppend,
        encodeNat]
      simp [encodeCodeWordAsInput, encodeCodeSymbolAsInput]
  | cons b rest =>
      simp [stageInputSecondBitTail, stageInputBits,
        PairedRecognizerDovetailStageInputCode,
        DovetailLayout.stageInputCode,
        DovetailLayout.stageInputCodeAppend,
        encodeBoolWordAppend,
        encodeCellListAppend,
        encodeNatAppend,
        encodeNat]

def stageInputSecondBitMarkedTape
    (w : Word Bool) (stage : Nat) : Tape Bool :=
  tapeAtCells [some false]
    (none :: (stageInputSecondBitTail w stage).map some)

def stageInputSecondBitMarkedHandoffTape
    (w : Word Bool) (stage : Nat) : Tape Bool :=
  Tape.move Direction.right
    (stageInputSecondBitMarkedTape w stage)

def stageInputSecondBitMarkedCheckedTape
    (w : Word Bool) (stage : Nat) : Tape Bool :=
  tapeAtCells [some false]
    (List.append
      (none :: (stageInputSecondBitTail w stage).map some)
      [none])

def stageInputSecondBitMarkedCheckedHandoffTape
    (w : Word Bool) (stage : Nat) : Tape Bool :=
  Tape.move Direction.right
    (stageInputSecondBitMarkedCheckedTape w stage)

def stageInputCheckedInputTape
    (w : Word Bool) (stage : Nat) : Tape Bool :=
  tapeAtCells []
    (List.append (List.map some (stageInputBits w stage)) [none])

def stageInputCheckedValidatorTape
    (w : Word Bool) (stage : Nat) : Tape Bool :=
  Tape.move Direction.right
    (stageInputCheckedInputTape w stage)

def StageInputValidatorForwardSpec
    (validator : MachineDescription) : Prop :=
  forall w : Word Bool,
  forall stage : Nat,
    exists steps : Nat,
      validator.runConfig steps
          (validator.initial (stageInputBits w stage)) =
        { state := validator.halt
          tape :=
            stageInputCheckedValidatorTape w stage }

def StageInputValidatorClosedSpec
    (validator : MachineDescription) : Prop :=
  forall code : Word MachineCodeSymbol,
  forall T : Tape Bool,
    validator.HaltsWithTape
        (encodeCodeWordAsInput code) T ->
      exists w : Word Bool,
      exists stage : Nat,
        code = PairedRecognizerDovetailStageInputCode w stage ∧
          Tape.move Direction.left T =
            stageInputCheckedInputTape w stage

def StageInputValidatorSpec
    (validator : MachineDescription) : Prop :=
  validator.SubroutineReady ∧
    StageInputValidatorForwardSpec validator ∧
      StageInputValidatorClosedSpec validator

def StageInputIdentityClosedHandoffConstruction : Prop :=
  exists validator : MachineDescription,
    StageInputValidatorSpec validator

def StageInputRecognizerSpec
    (recognizer : MachineDescription) : Prop :=
  recognizer.SubroutineReady ∧
    (forall w : Word Bool,
     forall stage : Nat,
      exists steps : Nat,
        recognizer.runConfig steps
            (recognizer.initial (stageInputBits w stage)) =
          { state := recognizer.halt
            tape := stageInputCheckedInputTape w stage }) ∧
    (forall code : Word MachineCodeSymbol,
     forall T : Tape Bool,
      recognizer.HaltsWithTape
          (encodeCodeWordAsInput code) T ->
        exists w : Word Bool,
        exists stage : Nat,
          code = PairedRecognizerDovetailStageInputCode w stage ∧
            T =
              stageInputCheckedInputTape w stage)

def StageInputRecognizerConstruction : Prop :=
  exists recognizer : MachineDescription,
    StageInputRecognizerSpec recognizer

theorem
    stageInputSecondBitMarkedHandoffTape_move_left
    (w : Word Bool) (stage : Nat) :
    Tape.move Direction.left
        (stageInputSecondBitMarkedHandoffTape w stage) =
      stageInputSecondBitMarkedTape w stage := by
  cases w with
  | nil =>
      simp [stageInputSecondBitMarkedHandoffTape,
        stageInputSecondBitMarkedTape,
        stageInputSecondBitTail, stageInputBits,
        PairedRecognizerDovetailStageInputCode,
        DovetailLayout.stageInputCode,
        DovetailLayout.stageInputCodeAppend,
        encodeBoolWordAppend,
        encodeCellListAppend,
        encodeNatAppend,
        encodeNat,
        tapeAtCells, Tape.move, Tape.moveRight, Tape.moveLeft]
      simp [encodeCodeWordAsInput,
        encodeCodeSymbolAsInput]
  | cons b rest =>
      simp [stageInputSecondBitMarkedHandoffTape,
        stageInputSecondBitMarkedTape,
        stageInputSecondBitTail, stageInputBits,
        PairedRecognizerDovetailStageInputCode,
        DovetailLayout.stageInputCode,
        DovetailLayout.stageInputCodeAppend,
        encodeBoolWordAppend,
        encodeCellListAppend,
        encodeNatAppend,
        encodeNat,
        tapeAtCells, Tape.move, Tape.moveRight, Tape.moveLeft]

theorem
    stageInputSecondBitMarkedCheckedHandoffTape_move_left
    (w : Word Bool) (stage : Nat) :
    Tape.move Direction.left
        (stageInputSecondBitMarkedCheckedHandoffTape w stage) =
      stageInputSecondBitMarkedCheckedTape w stage := by
  cases w with
  | nil =>
      simp [stageInputSecondBitMarkedCheckedHandoffTape,
        stageInputSecondBitMarkedCheckedTape,
        stageInputSecondBitTail, stageInputBits,
        PairedRecognizerDovetailStageInputCode,
        DovetailLayout.stageInputCode,
        DovetailLayout.stageInputCodeAppend,
        encodeBoolWordAppend,
        encodeCellListAppend,
        encodeNatAppend,
        encodeNat,
        tapeAtCells, Tape.move, Tape.moveRight, Tape.moveLeft]
      simp [encodeCodeWordAsInput,
        encodeCodeSymbolAsInput]
  | cons b rest =>
      simp [stageInputSecondBitMarkedCheckedHandoffTape,
        stageInputSecondBitMarkedCheckedTape,
        stageInputSecondBitTail, stageInputBits,
        PairedRecognizerDovetailStageInputCode,
        DovetailLayout.stageInputCode,
        DovetailLayout.stageInputCodeAppend,
        encodeBoolWordAppend,
        encodeCellListAppend,
        encodeNatAppend,
        encodeNat,
        tapeAtCells, Tape.move, Tape.moveRight, Tape.moveLeft]

theorem stageInputCheckedInputTape_move_left_move_right
    (w : Word Bool) (stage : Nat) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (stageInputCheckedInputTape w stage)) =
      stageInputCheckedInputTape w stage := by
  unfold stageInputCheckedInputTape
  rw [stageInputBits_eq_false_false_tail w stage]
  simp [tapeAtCells,
    Tape.move, Tape.moveLeft, Tape.moveRight]

def RestoreStageInputSecondBitDescription :
    MachineDescription where
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [ transition
        0 none (some false) Direction.left 1 ]

private abbrev RSIB := RestoreStageInputSecondBitDescription

theorem restoreStageInputSecondBitDescription_wellFormed :
    RSIB.WellFormed := by
  refine ⟨by native_decide, by native_decide, by native_decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := RSIB.transitions)
      (stateCount :=
        RSIB.stateCount)
      (by native_decide)
  · exact transition_deterministic_of_all
      (l := RSIB.transitions)
      (by native_decide)

theorem restoreStageInputSecondBitDescription_haltTransitionFree :
    RSIB.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := RSIB.transitions)
    (state := RSIB.halt)
    (by native_decide)

theorem restoreStageInputSecondBitDescription_subroutineReady :
    RSIB.SubroutineReady :=
  ⟨restoreStageInputSecondBitDescription_wellFormed,
    restoreStageInputSecondBitDescription_haltTransitionFree⟩

theorem restoreStageInputSecondBitDescription_run
    (w : Word Bool) (stage : Nat) :
    RSIB.runConfig 1
        { state := RSIB.start
          tape := stageInputSecondBitMarkedTape w stage } =
      { state := RSIB.halt
        tape := Tape.input (stageInputBits w stage) } := by
  rw [stageInputBits_eq_false_false_tail w stage]
  simp [RestoreStageInputSecondBitDescription,
    stageInputSecondBitMarkedTape,
    stageInputSecondBitTail,
    tapeAtCells, runConfig,
    stepConfig, lookupTransition,
    Matches, transition,
    Tape.read, Tape.write, Tape.move, Tape.moveLeft]
  simp [Tape.input]

theorem restoreStageInputSecondBitDescription_run_checked
    (w : Word Bool) (stage : Nat) :
    RSIB.runConfig 1
        { state := RSIB.start
          tape := stageInputSecondBitMarkedCheckedTape w stage } =
      { state := RSIB.halt
        tape := stageInputCheckedInputTape w stage } := by
  unfold stageInputSecondBitMarkedCheckedTape
  unfold stageInputCheckedInputTape
  rw [stageInputBits_eq_false_false_tail w stage]
  simp [RestoreStageInputSecondBitDescription,
    stageInputSecondBitTail,
    tapeAtCells, runConfig,
    stepConfig, lookupTransition,
    Matches, transition,
    Tape.read, Tape.write, Tape.move, Tape.moveLeft]

theorem restoreStageInputSecondBitDescription_run_succ
    (n : Nat) (w : Word Bool) (stage : Nat) :
    RSIB.runConfig (n + 1)
        { state := RSIB.start
          tape := stageInputSecondBitMarkedTape w stage } =
      { state := RSIB.halt
        tape := Tape.input (stageInputBits w stage) } := by
  rw [show n + 1 = 1 + n by omega]
  rw [runConfig_add]
  rw [restoreStageInputSecondBitDescription_run]
  exact
    runConfig_halt
      restoreStageInputSecondBitDescription_haltTransitionFree
      (Tape.input (stageInputBits w stage)) n

theorem restoreStageInputSecondBitDescription_run_checked_succ
    (n : Nat) (w : Word Bool) (stage : Nat) :
    RSIB.runConfig (n + 1)
        { state := RSIB.start
          tape := stageInputSecondBitMarkedCheckedTape w stage } =
      { state := RSIB.halt
        tape := stageInputCheckedInputTape w stage } := by
  rw [show n + 1 = 1 + n by omega]
  rw [runConfig_add]
  rw [restoreStageInputSecondBitDescription_run_checked]
  exact
    runConfig_halt
      restoreStageInputSecondBitDescription_haltTransitionFree
      (stageInputCheckedInputTape w stage) n

def MarkStageInputSecondBitDescription :
    MachineDescription where
  stateCount := 4
  start := 0
  halt := 3
  transitions :=
    [ transition
        0 (some false) (some false) Direction.right 1
    , transition
        1 (some false) none Direction.left 2
    , transition
        2 (some false) (some false) Direction.right 3
    ]

private abbrev MSIB := MarkStageInputSecondBitDescription

theorem markStageInputSecondBitDescription_wellFormed :
    MSIB.WellFormed := by
  refine ⟨by native_decide, by native_decide, by native_decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := MSIB.transitions)
      (stateCount :=
        MSIB.stateCount)
      (by native_decide)
  · exact transition_deterministic_of_all
      (l := MSIB.transitions)
      (by native_decide)

theorem markStageInputSecondBitDescription_haltTransitionFree :
    MSIB.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := MSIB.transitions)
    (state := MSIB.halt)
    (by native_decide)

theorem markStageInputSecondBitDescription_subroutineReady :
    MSIB.SubroutineReady :=
  ⟨markStageInputSecondBitDescription_wellFormed,
    markStageInputSecondBitDescription_haltTransitionFree⟩

theorem markStageInputSecondBitDescription_run
    (w : Word Bool) (stage : Nat) :
    MSIB.runConfig 3
        (MSIB.initial
          (stageInputBits w stage)) =
      { state := MSIB.halt
        tape := stageInputSecondBitMarkedTape w stage } := by
  rw [stageInputBits_eq_false_false_tail w stage]
  simp [MarkStageInputSecondBitDescription,
    stageInputSecondBitMarkedTape,
    stageInputSecondBitTail,
    tapeAtCells, initial,
    runConfig, stepConfig,
    lookupTransition, Matches,
    transition, Tape.input, Tape.read, Tape.write,
    Tape.move, Tape.moveLeft, Tape.moveRight]

theorem markStageInputSecondBitDescription_run_bits
    (tail : Word Bool) :
    MSIB.runConfig 3
        (MSIB.initial
          (false :: false :: tail)) =
      { state := MSIB.halt
        tape := tapeAtCells [some false]
          (none :: tail.map some) } := by
  simp [MarkStageInputSecondBitDescription,
    tapeAtCells, initial,
    runConfig, stepConfig,
    lookupTransition, Matches,
    transition, Tape.input, Tape.read, Tape.write,
    Tape.move, Tape.moveLeft, Tape.moveRight]

theorem markStageInputSecondBitDescription_haltsWithTape_inv
    {bits : Word Bool} {T : Tape Bool}
    (h :
      MSIB.HaltsWithTape
        bits T) :
    exists tail : Word Bool,
      bits = false :: false :: tail ∧
        T =
          tapeAtCells [some false]
            (none :: tail.map some) := by
  rcases
      runConfig_eq_halt_of_haltsWithTape h with
    ⟨n, hn⟩
  cases bits with
  | nil =>
      have hstep :
          MSIB.stepConfig
              (MSIB.initial []) =
            none := by
        native_decide
      have hrun :=
        runConfig_of_stepConfig_none hstep n
      have hstate : 0 = 3 := by
        simpa [MarkStageInputSecondBitDescription,
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
              simp [MarkStageInputSecondBitDescription,
                  runConfig]
                  at hn
            | succ n =>
                let c1 : Configuration :=
                  { state := 1
                    tape := tapeAtCells [some false] [] }
                have hstep0 :
                    MSIB.stepConfig
                        (MSIB.initial
                          [false]) =
                      some c1 := by
                  simp [c1, MarkStageInputSecondBitDescription,
                    tapeAtCells, initial,
                    stepConfig,
                    lookupTransition,
                    Matches,
                    transition, Tape.input, Tape.read,
                    Tape.write, Tape.move, Tape.moveRight]
                have hrun :
                    MSIB.runConfig
                        (Nat.succ n)
                        (MSIB.initial
                          [false]) =
                      MSIB.runConfig
                        n c1 := by
                  simp [runConfig, hstep0]
                have hstep1 :
                    MSIB.stepConfig
                        c1 = none := by
                  simp [c1, MarkStageInputSecondBitDescription,
                    tapeAtCells,
                    stepConfig,
                    lookupTransition,
                    Matches,
                    transition, Tape.read]
                have hstay :=
                  runConfig_of_stepConfig_none hstep1 n
                have hrunFinal :
                    MSIB.runConfig
                        (Nat.succ n)
                        (MSIB.initial
                          [false]) =
                      c1 :=
                  hrun.trans hstay
                have hstate : 1 = 3 := by
                  simpa [c1, MarkStageInputSecondBitDescription]
                    using
                    congrArg Configuration.state
                      (hrunFinal.symm.trans hn)
                omega
        | cons c tail =>
            cases c
            · refine ⟨tail, rfl, ?_⟩
              cases n with
              | zero =>
                  simp [MarkStageInputSecondBitDescription,
                    runConfig]
                    at hn
              | succ n =>
                  cases n with
                  | zero =>
                      simp [MarkStageInputSecondBitDescription,
                        runConfig,
                        stepConfig,
                        lookupTransition,
                        Matches,
                        transition, Tape.input,
                        Tape.read, Tape.write, Tape.move, Tape.moveRight]
                        at hn
                  | succ n =>
                      cases n with
                      | zero =>
                          simp [
                            MarkStageInputSecondBitDescription,
                            runConfig,
                            stepConfig,
                            lookupTransition,
                            Matches,
                            transition, Tape.input,
                            Tape.read, Tape.write, Tape.move,
                            Tape.moveLeft, Tape.moveRight] at hn
                      | succ k =>
                          have hrun :
                              MSIB.runConfig
                                  (Nat.succ (Nat.succ (Nat.succ k)))
                                  (MSIB.initial
                                    (false :: false :: tail)) =
                                { state :=
                                    MSIB.halt
                                  tape :=
                                    tapeAtCells [some false]
                                      (none :: tail.map some) } := by
                            rw [show
                              Nat.succ (Nat.succ (Nat.succ k)) =
                                3 + k by omega]
                            rw [runConfig_add]
                            rw [markStageInputSecondBitDescription_run_bits
                              tail]
                            exact
                              runConfig_halt
                                markStageInputSecondBitDescription_haltTransitionFree
                                (tapeAtCells [some false]
                                  (none :: tail.map some)) k
                          let cfgGood :
                              Configuration :=
                            { state :=
                                MSIB.halt,
                              tape :=
                                tapeAtCells [some false]
                                  (none :: tail.map some) }
                          have hcfg :
                              cfgGood =
                                { state :=
                                    MSIB.halt,
                                  tape := T } := by
                            simpa [cfgGood] using hrun.symm.trans hn
                          exact
                            (congrArg
                              Configuration.tape
                              hcfg).symm
            · cases n with
              | zero =>
                  simp [MarkStageInputSecondBitDescription,
                    runConfig]
                    at hn
              | succ n =>
                  let c1 : Configuration :=
                    { state := 1
                      tape :=
                        tapeAtCells [some false]
                          (some true :: tail.map some) }
                  have hstep0 :
                      MSIB.stepConfig
                          (MSIB.initial
                            (false :: true :: tail)) =
                        some c1 := by
                    simp [c1, MarkStageInputSecondBitDescription,
                      tapeAtCells, initial,
                      stepConfig,
                      lookupTransition,
                      Matches,
                      transition, Tape.input, Tape.read,
                      Tape.write, Tape.move, Tape.moveRight]
                  have hrun :
                      MSIB.runConfig
                          (Nat.succ n)
                          (MSIB.initial
                            (false :: true :: tail)) =
                        MSIB.runConfig
                          n c1 := by
                    simp [runConfig, hstep0]
                  have hstep1 :
                      MSIB.stepConfig
                          c1 = none := by
                    simp [c1, MarkStageInputSecondBitDescription,
                      tapeAtCells,
                      stepConfig,
                      lookupTransition,
                      Matches,
                      transition, Tape.read]
                  have hstay :=
                    runConfig_of_stepConfig_none hstep1 n
                  have hrunFinal :
                      MSIB.runConfig
                          (Nat.succ n)
                          (MSIB.initial
                            (false :: true :: tail)) =
                        c1 :=
                    hrun.trans hstay
                  have hstate : 1 = 3 := by
                    simpa [c1, MarkStageInputSecondBitDescription]
                      using
                      congrArg Configuration.state
                        (hrunFinal.symm.trans hn)
                  omega
      · have hstep :
            MSIB.stepConfig
                (MSIB.initial
                  (true :: rest)) =
              none := by
          simp [MarkStageInputSecondBitDescription,
            initial,
            stepConfig,
            lookupTransition, Matches,
            transition, Tape.input, Tape.read]
        have hrun :=
          runConfig_of_stepConfig_none hstep n
        have hstate : 0 = 3 := by
          simpa [MarkStageInputSecondBitDescription,
            initial] using
            congrArg Configuration.state
              (hrun.symm.trans hn)
        omega

def StageInputMarkedScannerSpec
    (scanner : MachineDescription) : Prop :=
  scanner.SubroutineReady ∧
    (forall w : Word Bool,
     forall stage : Nat,
      exists steps : Nat,
        scanner.runConfig steps
            { state := scanner.start
              tape :=
                stageInputSecondBitMarkedHandoffTape w stage } =
          { state := scanner.halt
            tape :=
              stageInputSecondBitMarkedCheckedHandoffTape
                w stage }) ∧
    (forall code : Word MachineCodeSymbol,
     forall Tmark T : Tape Bool,
      MSIB.HaltsWithTape
          (encodeCodeWordAsInput code) Tmark ->
        (exists steps : Nat,
          scanner.runConfig steps
              { state := scanner.start
                tape := Tape.move Direction.right Tmark } =
            { state := scanner.halt, tape := T }) ->
          exists w : Word Bool,
          exists stage : Nat,
            code = PairedRecognizerDovetailStageInputCode w stage ∧
              T =
                stageInputSecondBitMarkedCheckedHandoffTape w stage)

def StageInputMarkedScannerConstruction : Prop :=
  exists scanner : MachineDescription,
    StageInputMarkedScannerSpec scanner

def StageInputMarkedCoreSpec
    (markedCore : MachineDescription) : Prop :=
  markedCore.SubroutineReady ∧
    (forall w : Word Bool,
     forall stage : Nat,
      exists steps : Nat,
        markedCore.runConfig steps
            (markedCore.initial (stageInputBits w stage)) =
          { state := markedCore.halt
            tape :=
              stageInputSecondBitMarkedCheckedHandoffTape
                w stage }) ∧
    (forall code : Word MachineCodeSymbol,
     forall T : Tape Bool,
      markedCore.HaltsWithTape
          (encodeCodeWordAsInput code) T ->
        exists w : Word Bool,
        exists stage : Nat,
          code = PairedRecognizerDovetailStageInputCode w stage ∧
            T =
              stageInputSecondBitMarkedCheckedHandoffTape w stage)

def StageInputMarkedCoreConstruction : Prop :=
  exists markedCore : MachineDescription,
    StageInputMarkedCoreSpec markedCore

def StageInputMarkedCoreDescription
    (scanner : MachineDescription) : MachineDescription :=
  seqSubroutine
    MSIB scanner Direction.right

private abbrev SIMC := StageInputMarkedCoreDescription

theorem stageInputMarkedCoreDescription_subroutineReady
    {scanner : MachineDescription}
    (hscanner : StageInputMarkedScannerSpec scanner) :
    (SIMC scanner).SubroutineReady :=
  seqSubroutine_subroutineReady
    markStageInputSecondBitDescription_subroutineReady
    hscanner.left

theorem stageInputMarkedCoreSpec_of_markedScanner
    {scanner : MachineDescription}
    (hscanner : StageInputMarkedScannerSpec scanner) :
    StageInputMarkedCoreSpec
      (SIMC scanner) := by
  constructor
  · exact
      stageInputMarkedCoreDescription_subroutineReady hscanner
  constructor
  · intro w stage
    let A := MSIB
    let B := scanner
    let Tmid := stageInputSecondBitMarkedTape w stage
    have hAready : A.SubroutineReady :=
      markStageInputSecondBitDescription_subroutineReady
    have hBready : B.SubroutineReady := hscanner.left
    have hArun :
        A.runConfig 3
            { state := A.start
              tape := Tape.input (stageInputBits w stage) } =
          { state := A.halt, tape := Tmid } := by
      simpa [A, Tmid, initial] using
        markStageInputSecondBitDescription_run w stage
    have hBReach :
        exists nB : Nat,
          B.runConfig nB
              { state := B.start
                tape := Tape.move Direction.right Tmid } =
            { state := B.halt
              tape :=
                stageInputSecondBitMarkedCheckedHandoffTape
                  w stage } := by
      rcases hscanner.right.left w stage with ⟨nB, hB⟩
      refine ⟨nB, ?_⟩
      simpa [B, Tmid,
        stageInputSecondBitMarkedCheckedHandoffTape] using hB
    rcases
        seqSubroutine_reaches_of_runConfig_eq
          (A := A) (B := B) (handoffMove := Direction.right)
          hAready hBready hArun hBReach with
      ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [StageInputMarkedCoreDescription, A, B,
      initial] using hn
  · intro code T hhalt
    let A := MSIB
    let B := scanner
    have hAready : A.SubroutineReady :=
      markStageInputSecondBitDescription_subroutineReady
    have hBready : B.SubroutineReady := hscanner.left
    rcases
        seqSubroutine_haltsWithTape_inv
          (A := A) (B := B) (handoffMove := Direction.right)
          hAready hBready hhalt with
      ⟨Tmark, hAhalt, hBReach⟩
    exact hscanner.right.right code Tmark T hAhalt hBReach

def StageInputRecognizerDescription
    (markedCore : MachineDescription) : MachineDescription :=
  seqSubroutine markedCore
    RSIB Direction.left

private abbrev SIR := StageInputRecognizerDescription

theorem stageInputRecognizerDescription_subroutineReady
    {markedCore : MachineDescription}
    (hmarkedCore : StageInputMarkedCoreSpec markedCore) :
    (SIR markedCore).SubroutineReady :=
  seqSubroutine_subroutineReady
    hmarkedCore.left
    restoreStageInputSecondBitDescription_subroutineReady

theorem stageInputRecognizerSpec_of_markedCore
    {markedCore : MachineDescription}
    (hmarkedCore : StageInputMarkedCoreSpec markedCore) :
    StageInputRecognizerSpec
      (SIR markedCore) := by
  constructor
  · exact stageInputRecognizerDescription_subroutineReady
      hmarkedCore
  constructor
  · intro w stage
    let A := markedCore
    let B := RSIB
    have hAready : A.SubroutineReady := hmarkedCore.left
    have hBready : B.SubroutineReady :=
      restoreStageInputSecondBitDescription_subroutineReady
    rcases hmarkedCore.right.left w stage with ⟨nA, hA⟩
    have hArun :
        A.runConfig nA
            { state := A.start
              tape := Tape.input (stageInputBits w stage) } =
          { state := A.halt
            tape :=
              stageInputSecondBitMarkedCheckedHandoffTape
                w stage } := by
      simpa [A, initial] using hA
    have hBReach :
        exists nB : Nat,
          B.runConfig nB
              { state := B.start
                tape :=
                  Tape.move Direction.left
                    (stageInputSecondBitMarkedCheckedHandoffTape
                      w stage) } =
            { state := B.halt
              tape := stageInputCheckedInputTape w stage } := by
      refine ⟨1, ?_⟩
      rw [stageInputSecondBitMarkedCheckedHandoffTape_move_left]
      simpa [B] using
        restoreStageInputSecondBitDescription_run_checked w stage
    rcases
        seqSubroutine_reaches_of_runConfig_eq
          (A := A) (B := B) (handoffMove := Direction.left)
          hAready hBready hArun hBReach with
      ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [StageInputRecognizerDescription, A, B,
      initial] using hn
  · intro code T hhalt
    let A := markedCore
    let B := RSIB
    have hAready : A.SubroutineReady := hmarkedCore.left
    have hBready : B.SubroutineReady :=
      restoreStageInputSecondBitDescription_subroutineReady
    rcases
        seqSubroutine_haltsWithTape_inv
          (A := A) (B := B) (handoffMove := Direction.left)
          hAready hBready hhalt with
      ⟨Tmid, hAhalt, hBReach⟩
    rcases hmarkedCore.right.right code Tmid hAhalt with
      ⟨w, stage, hcode, hTmid⟩
    rcases hBReach with ⟨nB, hBRun⟩
    have hBRunMarked :
        B.runConfig nB
            { state := B.start
              tape := stageInputSecondBitMarkedCheckedTape w stage } =
          { state := B.halt, tape := T } := by
      simpa [B, hTmid,
        stageInputSecondBitMarkedCheckedHandoffTape_move_left]
        using hBRun
    have hT :
        T = stageInputCheckedInputTape w stage := by
      cases nB with
      | zero =>
          have hstate : 0 = 1 := by
            simpa [B, RestoreStageInputSecondBitDescription,
              runConfig] using
              congrArg Configuration.state hBRunMarked
          omega
      | succ nB =>
          have htarget :
              B.runConfig (nB + 1)
                  { state := B.start
                    tape :=
                      stageInputSecondBitMarkedCheckedTape w stage } =
                { state := B.halt
                  tape :=
                    stageInputCheckedInputTape w stage } := by
            simpa [B] using
              restoreStageInputSecondBitDescription_run_checked_succ
                nB w stage
          have hcfg :
              ({ state := B.halt, tape := T } :
                  Configuration) =
                { state := B.halt
                  tape :=
                    stageInputCheckedInputTape w stage } :=
            hBRunMarked.symm.trans htarget
          exact congrArg Configuration.tape hcfg
    exact ⟨w, stage, hcode, hT⟩

theorem exactIdentityDescription_runConfig_from_start
    (n : Nat) (T : Tape Bool) :
    ExactIdentityDescription.runConfig n
        { state := ExactIdentityDescription.start
          tape := T } =
      { state := ExactIdentityDescription.halt
        tape := T } := by
  cases n <;>
    simp [ExactIdentityDescription,
      runConfig, stepConfig,
      lookupTransition]

def StageInputIdentityDescription
    (recognizer : MachineDescription) : MachineDescription :=
  seqSubroutine recognizer
    ExactIdentityDescription Direction.right

private abbrev SIID := StageInputIdentityDescription

theorem stageInputIdentityDescription_subroutineReady
    {recognizer : MachineDescription}
    (hrecognizer : StageInputRecognizerSpec recognizer) :
    (SIID recognizer).SubroutineReady :=
  seqSubroutine_subroutineReady
    hrecognizer.left
    ⟨exactIdentityDescription_wellFormed,
      exactIdentityDescription_haltTransitionFree⟩

theorem stageInputIdentityDescription_spec_of_recognizer
    {recognizer : MachineDescription}
    (hrecognizer : StageInputRecognizerSpec recognizer) :
    StageInputValidatorSpec
      (SIID recognizer) := by
  constructor
  · exact stageInputIdentityDescription_subroutineReady
      hrecognizer
  constructor
  · intro w stage
    let A := recognizer
    let B := ExactIdentityDescription
    have hAready : A.SubroutineReady := hrecognizer.left
    have hBready : B.SubroutineReady :=
      ⟨exactIdentityDescription_wellFormed,
        exactIdentityDescription_haltTransitionFree⟩
    rcases hrecognizer.right.left w stage with ⟨nA, hA⟩
    have hArun :
        A.runConfig nA
            { state := A.start
              tape :=
                Tape.input
                  (encodeCodeWordAsInput
                    (PairedRecognizerDovetailStageInputCode w stage)) } =
          { state := A.halt
            tape := stageInputCheckedInputTape w stage } := by
      simpa [A, stageInputBits] using hA
    have hBReach :
        exists nB : Nat,
          B.runConfig nB
              { state := B.start
                tape :=
                  Tape.move Direction.right
                    (stageInputCheckedInputTape w stage) } =
            { state := B.halt
              tape := stageInputCheckedValidatorTape w stage } := by
      refine ⟨0, ?_⟩
      simp [B, stageInputCheckedValidatorTape,
        runConfig,
        ExactIdentityDescription]
    rcases
        seqSubroutine_reaches_of_runConfig_eq
          (A := A) (B := B) (handoffMove := Direction.right)
          hAready hBready hArun hBReach with
      ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [StageInputIdentityDescription, A, B,
      initial, stageInputBits] using hn
  · intro code T hhalt
    let A := recognizer
    let B := ExactIdentityDescription
    have hAready : A.SubroutineReady := hrecognizer.left
    have hBready : B.SubroutineReady :=
      ⟨exactIdentityDescription_wellFormed,
        exactIdentityDescription_haltTransitionFree⟩
    rcases
        seqSubroutine_haltsWithTape_inv
          (A := A) (B := B) (handoffMove := Direction.right)
          hAready hBready hhalt with
      ⟨Tmid, hAhalt, hBReach⟩
    rcases hrecognizer.right.right code Tmid hAhalt with
      ⟨w, stage, hcode, hTmid⟩
    rcases hBReach with ⟨nB, hBRun⟩
    have hBRun' :
        Configuration.mk B.halt
            (Tape.move Direction.right Tmid) =
          Configuration.mk B.halt T := by
      simpa [B] using
        ((exactIdentityDescription_runConfig_from_start
            nB (Tape.move Direction.right Tmid)).symm.trans hBRun)
    have hT :
        T = Tape.move Direction.right Tmid := by
      exact (congrArg Configuration.tape hBRun').symm
    refine ⟨w, stage, hcode, ?_⟩
    rw [hT, hTmid]
    exact stageInputCheckedInputTape_move_left_move_right w stage

theorem
    stageInputIdentityClosedHandoffConstruction_of_recognizer
    {recognizer : MachineDescription}
    (hrecognizer : StageInputRecognizerSpec recognizer) :
    StageInputIdentityClosedHandoffConstruction :=
  ⟨SIID recognizer,
    stageInputIdentityDescription_spec_of_recognizer hrecognizer⟩

theorem stageInputValidatorSpec_of_identityClosedHandoff
    {validator : MachineDescription}
    (hvalidator : StageInputValidatorSpec validator) :
    StageInputValidatorSpec validator :=
  hvalidator


end DovetailInitialLayoutInitializer
end Computability
end FoC

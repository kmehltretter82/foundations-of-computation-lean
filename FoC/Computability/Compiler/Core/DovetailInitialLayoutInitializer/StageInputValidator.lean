import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.HeadRouter

set_option doc.verso true

namespace FoC
namespace Computability

open Languages

namespace DovetailInitialLayoutInitializer

def StageInputValidatorForwardSpec
    (validator : MachineDescription) : Prop :=
  forall w : Word Bool,
  forall stage : Nat,
    exists steps : Nat,
      validator.runConfig steps
          (validator.initial (stageInputBits w stage)) =
        { state := validator.halt
          tape :=
            Tape.move Direction.right
              (Tape.input (stageInputBits w stage)) }

def StageInputValidatorClosedSpec
    (validator : MachineDescription) : Prop :=
  forall code : Word MachineCodeSymbol,
  forall T : Tape Bool,
    validator.HaltsWithTape
        (MachineDescription.encodeCodeWordAsInput code) T ->
      exists w : Word Bool,
      exists stage : Nat,
        code = PairedRecognizerDovetailStageInputCode w stage ∧
          Tape.move Direction.left T =
            Tape.input (stageInputBits w stage)

def StageInputValidatorSpec
    (validator : MachineDescription) : Prop :=
  validator.SubroutineReady ∧
    StageInputValidatorForwardSpec validator ∧
      StageInputValidatorClosedSpec validator

def StageInputIdentityPrimitive :
    MachineDescription.TapeCodePrimitive where
  transform := fun code =>
    match MachineDescription.DovetailLayout.decodeStageInputComplete code with
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
        MachineDescription.DovetailLayout.decodeStageInputComplete code with
    | none =>
        simp [hdecode] at h
    | some parsed =>
        cases parsed with
        | mk w stage =>
            simp [hdecode] at h
            cases h
            exact
              ⟨w, stage,
                MachineDescription.DovetailLayout.decodeStageInputComplete_eq_some_stageInputCode
                  hdecode,
                MachineDescription.DovetailLayout.decodeStageInputComplete_eq_some_stageInputCode
                  hdecode⟩
  · intro h
    rcases h with ⟨w, stage, rfl, rfl⟩
    simp [StageInputIdentityPrimitive,
      PairedRecognizerDovetailStageInputCode,
      MachineDescription.DovetailLayout.decodeStageInputComplete_stageInputCode]

def StageInputIdentityClosedHandoffConstruction : Prop :=
  exists validator : MachineDescription,
    TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      StageInputIdentityPrimitive validator
      tapeCodePrimitiveCodeWordHandoffMove

def StageInputRecognizerSpec
    (recognizer : MachineDescription) : Prop :=
  recognizer.SubroutineReady ∧
    (forall w : Word Bool,
     forall stage : Nat,
      exists steps : Nat,
        recognizer.runConfig steps
            (recognizer.initial (stageInputBits w stage)) =
          { state := recognizer.halt
            tape := Tape.input (stageInputBits w stage) }) ∧
    (forall code : Word MachineCodeSymbol,
     forall T : Tape Bool,
      recognizer.HaltsWithTape
          (MachineDescription.encodeCodeWordAsInput code) T ->
        exists w : Word Bool,
        exists stage : Nat,
          code = PairedRecognizerDovetailStageInputCode w stage ∧
            T =
              Tape.input (MachineDescription.encodeCodeWordAsInput code))

def StageInputRecognizerConstruction : Prop :=
  exists recognizer : MachineDescription,
    StageInputRecognizerSpec recognizer

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
        MachineDescription.DovetailLayout.stageInputCode,
        MachineDescription.DovetailLayout.stageInputCodeAppend,
        MachineDescription.encodeBoolWordAppend,
        MachineDescription.encodeCellListAppend,
        MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat,
        MachineDescription.encodeCodeWordAsInput,
        MachineDescription.encodeCodeSymbolAsInput]
  | cons b rest =>
      simp [stageInputSecondBitTail, stageInputBits,
        PairedRecognizerDovetailStageInputCode,
        MachineDescription.DovetailLayout.stageInputCode,
        MachineDescription.DovetailLayout.stageInputCodeAppend,
        MachineDescription.encodeBoolWordAppend,
        MachineDescription.encodeCellListAppend,
        MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat,
        MachineDescription.encodeCodeWordAsInput,
        MachineDescription.encodeCodeSymbolAsInput]

def stageInputSecondBitMarkedTape
    (w : Word Bool) (stage : Nat) : Tape Bool :=
  tapeAtCells [some false]
    (none :: (stageInputSecondBitTail w stage).map some)

def stageInputSecondBitMarkedHandoffTape
    (w : Word Bool) (stage : Nat) : Tape Bool :=
  Tape.move Direction.right
    (stageInputSecondBitMarkedTape w stage)

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
        MachineDescription.DovetailLayout.stageInputCode,
        MachineDescription.DovetailLayout.stageInputCodeAppend,
        MachineDescription.encodeBoolWordAppend,
        MachineDescription.encodeCellListAppend,
        MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat,
        MachineDescription.encodeCodeWordAsInput,
        MachineDescription.encodeCodeSymbolAsInput,
        tapeAtCells, Tape.move, Tape.moveRight, Tape.moveLeft]
  | cons b rest =>
      simp [stageInputSecondBitMarkedHandoffTape,
        stageInputSecondBitMarkedTape,
        stageInputSecondBitTail, stageInputBits,
        PairedRecognizerDovetailStageInputCode,
        MachineDescription.DovetailLayout.stageInputCode,
        MachineDescription.DovetailLayout.stageInputCodeAppend,
        MachineDescription.encodeBoolWordAppend,
        MachineDescription.encodeCellListAppend,
        MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat,
        MachineDescription.encodeCodeWordAsInput,
        MachineDescription.encodeCodeSymbolAsInput,
        tapeAtCells, Tape.move, Tape.moveRight, Tape.moveLeft]

def RestoreStageInputSecondBitDescription :
    MachineDescription where
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [ MachineDescription.transition
        0 none (some false) Direction.left 1 ]

theorem
    restoreStageInputSecondBitDescription_wellFormed :
    RestoreStageInputSecondBitDescription.WellFormed := by
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · intro t ht
    exact transition_wellFormed_of_all
      (l := RestoreStageInputSecondBitDescription.transitions)
      (stateCount :=
        RestoreStageInputSecondBitDescription.stateCount)
      (by
        native_decide) t ht
  · intro t u ht hu hkey
    exact transition_deterministic_of_all
      (l := RestoreStageInputSecondBitDescription.transitions)
      (by
        native_decide) t u ht hu hkey

theorem
    restoreStageInputSecondBitDescription_haltTransitionFree :
    RestoreStageInputSecondBitDescription.HaltTransitionFree := by
  intro t ht
  exact transition_notFrom_of_all
    (l := RestoreStageInputSecondBitDescription.transitions)
    (state := RestoreStageInputSecondBitDescription.halt)
    (by
      native_decide) t ht

theorem
    restoreStageInputSecondBitDescription_subroutineReady :
    RestoreStageInputSecondBitDescription.SubroutineReady :=
  ⟨restoreStageInputSecondBitDescription_wellFormed,
    restoreStageInputSecondBitDescription_haltTransitionFree⟩

theorem restoreStageInputSecondBitDescription_run
    (w : Word Bool) (stage : Nat) :
    RestoreStageInputSecondBitDescription.runConfig 1
        { state := RestoreStageInputSecondBitDescription.start
          tape := stageInputSecondBitMarkedTape w stage } =
      { state := RestoreStageInputSecondBitDescription.halt
        tape := Tape.input (stageInputBits w stage) } := by
  rw [stageInputBits_eq_false_false_tail w stage]
  simp [RestoreStageInputSecondBitDescription,
    stageInputSecondBitMarkedTape,
    stageInputSecondBitTail,
    tapeAtCells, MachineDescription.runConfig,
    MachineDescription.stepConfig, MachineDescription.lookupTransition,
    MachineDescription.Matches, MachineDescription.transition,
    Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.input]

theorem restoreStageInputSecondBitDescription_run_succ
    (n : Nat) (w : Word Bool) (stage : Nat) :
    RestoreStageInputSecondBitDescription.runConfig (n + 1)
        { state := RestoreStageInputSecondBitDescription.start
          tape := stageInputSecondBitMarkedTape w stage } =
      { state := RestoreStageInputSecondBitDescription.halt
        tape := Tape.input (stageInputBits w stage) } := by
  rw [show n + 1 = 1 + n by omega]
  rw [MachineDescription.runConfig_add]
  rw [restoreStageInputSecondBitDescription_run]
  exact
    MachineDescription.runConfig_halt
      restoreStageInputSecondBitDescription_haltTransitionFree
      (Tape.input (stageInputBits w stage)) n

def MarkStageInputSecondBitDescription :
    MachineDescription where
  stateCount := 4
  start := 0
  halt := 3
  transitions :=
    [ MachineDescription.transition
        0 (some false) (some false) Direction.right 1
    , MachineDescription.transition
        1 (some false) none Direction.left 2
    , MachineDescription.transition
        2 (some false) (some false) Direction.right 3
    ]

theorem markStageInputSecondBitDescription_wellFormed :
    MarkStageInputSecondBitDescription.WellFormed := by
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · intro t ht
    exact transition_wellFormed_of_all
      (l := MarkStageInputSecondBitDescription.transitions)
      (stateCount :=
        MarkStageInputSecondBitDescription.stateCount)
      (by
        native_decide) t ht
  · intro t u ht hu hkey
    exact transition_deterministic_of_all
      (l := MarkStageInputSecondBitDescription.transitions)
      (by
        native_decide) t u ht hu hkey

theorem
    markStageInputSecondBitDescription_haltTransitionFree :
    MarkStageInputSecondBitDescription.HaltTransitionFree := by
  intro t ht
  exact transition_notFrom_of_all
    (l := MarkStageInputSecondBitDescription.transitions)
    (state := MarkStageInputSecondBitDescription.halt)
    (by
      native_decide) t ht

theorem
    markStageInputSecondBitDescription_subroutineReady :
    MarkStageInputSecondBitDescription.SubroutineReady :=
  ⟨markStageInputSecondBitDescription_wellFormed,
    markStageInputSecondBitDescription_haltTransitionFree⟩

theorem markStageInputSecondBitDescription_run
    (w : Word Bool) (stage : Nat) :
    MarkStageInputSecondBitDescription.runConfig 3
        (MarkStageInputSecondBitDescription.initial
          (stageInputBits w stage)) =
      { state := MarkStageInputSecondBitDescription.halt
        tape := stageInputSecondBitMarkedTape w stage } := by
  rw [stageInputBits_eq_false_false_tail w stage]
  simp [MarkStageInputSecondBitDescription,
    stageInputSecondBitMarkedTape,
    stageInputSecondBitTail,
    tapeAtCells, MachineDescription.initial,
    MachineDescription.runConfig, MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition, Tape.input, Tape.read, Tape.write,
    Tape.move, Tape.moveLeft, Tape.moveRight]

theorem markStageInputSecondBitDescription_run_bits
    (tail : Word Bool) :
    MarkStageInputSecondBitDescription.runConfig 3
        (MarkStageInputSecondBitDescription.initial
          (false :: false :: tail)) =
      { state := MarkStageInputSecondBitDescription.halt
        tape := tapeAtCells [some false]
          (none :: tail.map some) } := by
  simp [MarkStageInputSecondBitDescription,
    tapeAtCells, MachineDescription.initial,
    MachineDescription.runConfig, MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition, Tape.input, Tape.read, Tape.write,
    Tape.move, Tape.moveLeft, Tape.moveRight]

theorem markStageInputSecondBitDescription_haltsWithTape_inv
    {bits : Word Bool} {T : Tape Bool}
    (h :
      MarkStageInputSecondBitDescription.HaltsWithTape
        bits T) :
    exists tail : Word Bool,
      bits = false :: false :: tail ∧
        T =
          tapeAtCells [some false]
            (none :: tail.map some) := by
  rcases
      MachineDescription.runConfig_eq_halt_of_haltsWithTape h with
    ⟨n, hn⟩
  cases bits with
  | nil =>
      have hstep :
          MarkStageInputSecondBitDescription.stepConfig
              (MarkStageInputSecondBitDescription.initial []) =
            none := by
        native_decide
      have hrun :=
        MachineDescription.runConfig_of_stepConfig_none hstep n
      have hstate : 0 = 3 := by
        simpa [MarkStageInputSecondBitDescription,
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
              simp [MarkStageInputSecondBitDescription,
                  MachineDescription.runConfig]
                  at hn
            | succ n =>
                let c1 : MachineDescription.Configuration :=
                  { state := 1
                    tape := tapeAtCells [some false] [] }
                have hstep0 :
                    MarkStageInputSecondBitDescription.stepConfig
                        (MarkStageInputSecondBitDescription.initial
                          [false]) =
                      some c1 := by
                  simp [c1, MarkStageInputSecondBitDescription,
                    tapeAtCells, MachineDescription.initial,
                    MachineDescription.stepConfig,
                    MachineDescription.lookupTransition,
                    MachineDescription.Matches,
                    MachineDescription.transition, Tape.input, Tape.read,
                    Tape.write, Tape.move, Tape.moveRight]
                have hrun :
                    MarkStageInputSecondBitDescription.runConfig
                        (Nat.succ n)
                        (MarkStageInputSecondBitDescription.initial
                          [false]) =
                      MarkStageInputSecondBitDescription.runConfig
                        n c1 := by
                  simp [MachineDescription.runConfig, hstep0]
                have hstep1 :
                    MarkStageInputSecondBitDescription.stepConfig
                        c1 = none := by
                  simp [c1, MarkStageInputSecondBitDescription,
                    tapeAtCells,
                    MachineDescription.stepConfig,
                    MachineDescription.lookupTransition,
                    MachineDescription.Matches,
                    MachineDescription.transition, Tape.read]
                have hstay :=
                  MachineDescription.runConfig_of_stepConfig_none hstep1 n
                have hrunFinal :
                    MarkStageInputSecondBitDescription.runConfig
                        (Nat.succ n)
                        (MarkStageInputSecondBitDescription.initial
                          [false]) =
                      c1 :=
                  hrun.trans hstay
                have hstate : 1 = 3 := by
                  simpa [c1, MarkStageInputSecondBitDescription]
                    using
                    congrArg MachineDescription.Configuration.state
                      (hrunFinal.symm.trans hn)
                omega
        | cons c tail =>
            cases c
            · refine ⟨tail, rfl, ?_⟩
              cases n with
              | zero =>
                  simp [MarkStageInputSecondBitDescription,
                    MachineDescription.runConfig]
                    at hn
              | succ n =>
                  cases n with
                  | zero =>
                      simp [MarkStageInputSecondBitDescription,
                        MachineDescription.runConfig,
                        MachineDescription.stepConfig,
                        MachineDescription.lookupTransition,
                        MachineDescription.Matches,
                        MachineDescription.transition, Tape.input,
                        Tape.read, Tape.write, Tape.move, Tape.moveRight]
                        at hn
                  | succ n =>
                      cases n with
                      | zero =>
                          simp [
                            MarkStageInputSecondBitDescription,
                            MachineDescription.runConfig,
                            MachineDescription.stepConfig,
                            MachineDescription.lookupTransition,
                            MachineDescription.Matches,
                            MachineDescription.transition, Tape.input,
                            Tape.read, Tape.write, Tape.move,
                            Tape.moveLeft, Tape.moveRight] at hn
                      | succ k =>
                          have hrun :
                              MarkStageInputSecondBitDescription.runConfig
                                  (Nat.succ (Nat.succ (Nat.succ k)))
                                  (MarkStageInputSecondBitDescription.initial
                                    (false :: false :: tail)) =
                                { state :=
                                    MarkStageInputSecondBitDescription.halt
                                  tape :=
                                    tapeAtCells [some false]
                                      (none :: tail.map some) } := by
                            rw [show
                              Nat.succ (Nat.succ (Nat.succ k)) =
                                3 + k by omega]
                            rw [MachineDescription.runConfig_add]
                            rw [markStageInputSecondBitDescription_run_bits
                              tail]
                            exact
                              MachineDescription.runConfig_halt
                                markStageInputSecondBitDescription_haltTransitionFree
                                (tapeAtCells [some false]
                                  (none :: tail.map some)) k
                          let cfgGood :
                              MachineDescription.Configuration :=
                            { state :=
                                MarkStageInputSecondBitDescription.halt,
                              tape :=
                                tapeAtCells [some false]
                                  (none :: tail.map some) }
                          have hcfg :
                              cfgGood =
                                { state :=
                                    MarkStageInputSecondBitDescription.halt,
                                  tape := T } := by
                            simpa [cfgGood] using hrun.symm.trans hn
                          exact
                            (congrArg
                              MachineDescription.Configuration.tape
                              hcfg).symm
            · cases n with
              | zero =>
                  simp [MarkStageInputSecondBitDescription,
                    MachineDescription.runConfig]
                    at hn
              | succ n =>
                  let c1 : MachineDescription.Configuration :=
                    { state := 1
                      tape :=
                        tapeAtCells [some false]
                          (some true :: tail.map some) }
                  have hstep0 :
                      MarkStageInputSecondBitDescription.stepConfig
                          (MarkStageInputSecondBitDescription.initial
                            (false :: true :: tail)) =
                        some c1 := by
                    simp [c1, MarkStageInputSecondBitDescription,
                      tapeAtCells, MachineDescription.initial,
                      MachineDescription.stepConfig,
                      MachineDescription.lookupTransition,
                      MachineDescription.Matches,
                      MachineDescription.transition, Tape.input, Tape.read,
                      Tape.write, Tape.move, Tape.moveRight]
                  have hrun :
                      MarkStageInputSecondBitDescription.runConfig
                          (Nat.succ n)
                          (MarkStageInputSecondBitDescription.initial
                            (false :: true :: tail)) =
                        MarkStageInputSecondBitDescription.runConfig
                          n c1 := by
                    simp [MachineDescription.runConfig, hstep0]
                  have hstep1 :
                      MarkStageInputSecondBitDescription.stepConfig
                          c1 = none := by
                    simp [c1, MarkStageInputSecondBitDescription,
                      tapeAtCells,
                      MachineDescription.stepConfig,
                      MachineDescription.lookupTransition,
                      MachineDescription.Matches,
                      MachineDescription.transition, Tape.read]
                  have hstay :=
                    MachineDescription.runConfig_of_stepConfig_none hstep1 n
                  have hrunFinal :
                      MarkStageInputSecondBitDescription.runConfig
                          (Nat.succ n)
                          (MarkStageInputSecondBitDescription.initial
                            (false :: true :: tail)) =
                        c1 :=
                    hrun.trans hstay
                  have hstate : 1 = 3 := by
                    simpa [c1, MarkStageInputSecondBitDescription]
                      using
                      congrArg MachineDescription.Configuration.state
                        (hrunFinal.symm.trans hn)
                  omega
      · have hstep :
            MarkStageInputSecondBitDescription.stepConfig
                (MarkStageInputSecondBitDescription.initial
                  (true :: rest)) =
              none := by
          simp [MarkStageInputSecondBitDescription,
            MachineDescription.initial,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.input, Tape.read]
        have hrun :=
          MachineDescription.runConfig_of_stepConfig_none hstep n
        have hstate : 0 = 3 := by
          simpa [MarkStageInputSecondBitDescription,
            MachineDescription.initial] using
            congrArg MachineDescription.Configuration.state
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
              stageInputSecondBitMarkedHandoffTape w stage }) ∧
    (forall code : Word MachineCodeSymbol,
     forall Tmark T : Tape Bool,
      MarkStageInputSecondBitDescription.HaltsWithTape
          (MachineDescription.encodeCodeWordAsInput code) Tmark ->
        (exists steps : Nat,
          scanner.runConfig steps
              { state := scanner.start
                tape := Tape.move Direction.right Tmark } =
            { state := scanner.halt, tape := T }) ->
          exists w : Word Bool,
          exists stage : Nat,
            code = PairedRecognizerDovetailStageInputCode w stage ∧
              T =
                stageInputSecondBitMarkedHandoffTape w stage)

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
              stageInputSecondBitMarkedHandoffTape w stage }) ∧
    (forall code : Word MachineCodeSymbol,
     forall T : Tape Bool,
      markedCore.HaltsWithTape
          (MachineDescription.encodeCodeWordAsInput code) T ->
        exists w : Word Bool,
        exists stage : Nat,
          code = PairedRecognizerDovetailStageInputCode w stage ∧
            T =
              stageInputSecondBitMarkedHandoffTape w stage)

def StageInputMarkedCoreConstruction : Prop :=
  exists markedCore : MachineDescription,
    StageInputMarkedCoreSpec markedCore

def StageInputMarkedCoreDescription
    (scanner : MachineDescription) : MachineDescription :=
  MachineDescription.seqSubroutine
    MarkStageInputSecondBitDescription scanner Direction.right

theorem stageInputMarkedCoreDescription_subroutineReady
    {scanner : MachineDescription}
    (hscanner : StageInputMarkedScannerSpec scanner) :
    (StageInputMarkedCoreDescription scanner).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    markStageInputSecondBitDescription_subroutineReady
    hscanner.left

theorem stageInputMarkedCoreSpec_of_markedScanner
    {scanner : MachineDescription}
    (hscanner : StageInputMarkedScannerSpec scanner) :
    StageInputMarkedCoreSpec
      (StageInputMarkedCoreDescription scanner) := by
  constructor
  · exact
      stageInputMarkedCoreDescription_subroutineReady hscanner
  constructor
  · intro w stage
    let A := MarkStageInputSecondBitDescription
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
      simpa [A, Tmid, MachineDescription.initial] using
        markStageInputSecondBitDescription_run w stage
    have hBReach :
        exists nB : Nat,
          B.runConfig nB
              { state := B.start
                tape := Tape.move Direction.right Tmid } =
            { state := B.halt
              tape :=
                stageInputSecondBitMarkedHandoffTape w stage } := by
      rcases hscanner.right.left w stage with ⟨nB, hB⟩
      refine ⟨nB, ?_⟩
      simpa [B, Tmid,
        stageInputSecondBitMarkedHandoffTape] using hB
    rcases
        MachineDescription.seqSubroutine_reaches_of_runConfig_eq
          (A := A) (B := B) (handoffMove := Direction.right)
          hAready hBready hArun hBReach with
      ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [StageInputMarkedCoreDescription, A, B,
      MachineDescription.initial] using hn
  · intro code T hhalt
    let A := MarkStageInputSecondBitDescription
    let B := scanner
    have hAready : A.SubroutineReady :=
      markStageInputSecondBitDescription_subroutineReady
    have hBready : B.SubroutineReady := hscanner.left
    rcases
        MachineDescription.seqSubroutine_haltsWithTape_inv
          (A := A) (B := B) (handoffMove := Direction.right)
          hAready hBready hhalt with
      ⟨Tmark, hAhalt, hBReach⟩
    exact hscanner.right.right code Tmark T hAhalt hBReach

def StageInputRecognizerDescription
    (markedCore : MachineDescription) : MachineDescription :=
  MachineDescription.seqSubroutine markedCore
    RestoreStageInputSecondBitDescription Direction.left

theorem stageInputRecognizerDescription_subroutineReady
    {markedCore : MachineDescription}
    (hmarkedCore : StageInputMarkedCoreSpec markedCore) :
    (StageInputRecognizerDescription markedCore).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    hmarkedCore.left
    restoreStageInputSecondBitDescription_subroutineReady

theorem stageInputRecognizerSpec_of_markedCore
    {markedCore : MachineDescription}
    (hmarkedCore : StageInputMarkedCoreSpec markedCore) :
    StageInputRecognizerSpec
      (StageInputRecognizerDescription markedCore) := by
  constructor
  · exact stageInputRecognizerDescription_subroutineReady
      hmarkedCore
  constructor
  · intro w stage
    let A := markedCore
    let B := RestoreStageInputSecondBitDescription
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
              stageInputSecondBitMarkedHandoffTape w stage } := by
      simpa [A, MachineDescription.initial] using hA
    have hBReach :
        exists nB : Nat,
          B.runConfig nB
              { state := B.start
                tape :=
                  Tape.move Direction.left
                    (stageInputSecondBitMarkedHandoffTape
                      w stage) } =
            { state := B.halt
              tape := Tape.input (stageInputBits w stage) } := by
      refine ⟨1, ?_⟩
      rw [stageInputSecondBitMarkedHandoffTape_move_left]
      simpa [B] using
        restoreStageInputSecondBitDescription_run w stage
    rcases
        MachineDescription.seqSubroutine_reaches_of_runConfig_eq
          (A := A) (B := B) (handoffMove := Direction.left)
          hAready hBready hArun hBReach with
      ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [StageInputRecognizerDescription, A, B,
      MachineDescription.initial] using hn
  · intro code T hhalt
    let A := markedCore
    let B := RestoreStageInputSecondBitDescription
    have hAready : A.SubroutineReady := hmarkedCore.left
    have hBready : B.SubroutineReady :=
      restoreStageInputSecondBitDescription_subroutineReady
    rcases
        MachineDescription.seqSubroutine_haltsWithTape_inv
          (A := A) (B := B) (handoffMove := Direction.left)
          hAready hBready hhalt with
      ⟨Tmid, hAhalt, hBReach⟩
    rcases hmarkedCore.right.right code Tmid hAhalt with
      ⟨w, stage, hcode, hTmid⟩
    rcases hBReach with ⟨nB, hBRun⟩
    have hBRunMarked :
        B.runConfig nB
            { state := B.start
              tape := stageInputSecondBitMarkedTape w stage } =
          { state := B.halt, tape := T } := by
      simpa [B, hTmid,
        stageInputSecondBitMarkedHandoffTape_move_left]
        using hBRun
    have hT :
        T = Tape.input (MachineDescription.encodeCodeWordAsInput code) := by
      cases nB with
      | zero =>
          have hstate : 0 = 1 := by
            simpa [B, RestoreStageInputSecondBitDescription,
              MachineDescription.runConfig] using
              congrArg MachineDescription.Configuration.state hBRunMarked
          omega
      | succ nB =>
          have htarget :
              B.runConfig (nB + 1)
                  { state := B.start
                    tape :=
                      stageInputSecondBitMarkedTape w stage } =
                { state := B.halt
                  tape :=
                    Tape.input
                      (MachineDescription.encodeCodeWordAsInput code) } := by
            rw [hcode]
            simpa [B, stageInputBits] using
              restoreStageInputSecondBitDescription_run_succ
                nB w stage
          have hcfg :
              ({ state := B.halt, tape := T } :
                  MachineDescription.Configuration) =
                { state := B.halt
                  tape :=
                    Tape.input
                      (MachineDescription.encodeCodeWordAsInput code) } :=
            hBRunMarked.symm.trans htarget
          exact congrArg MachineDescription.Configuration.tape hcfg
    exact ⟨w, stage, hcode, hT⟩

theorem exactIdentityDescription_runConfig_from_start
    (n : Nat) (T : Tape Bool) :
    MachineDescription.ExactIdentityDescription.runConfig n
        { state := MachineDescription.ExactIdentityDescription.start
          tape := T } =
      { state := MachineDescription.ExactIdentityDescription.halt
        tape := T } := by
  cases n <;>
    simp [MachineDescription.ExactIdentityDescription,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition]

def StageInputIdentityDescription
    (recognizer : MachineDescription) : MachineDescription :=
  MachineDescription.seqSubroutine recognizer
    MachineDescription.ExactIdentityDescription Direction.right

theorem stageInputIdentityDescription_subroutineReady
    {recognizer : MachineDescription}
    (hrecognizer : StageInputRecognizerSpec recognizer) :
    (StageInputIdentityDescription recognizer).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    hrecognizer.left
    ⟨MachineDescription.exactIdentityDescription_wellFormed,
      MachineDescription.exactIdentityDescription_haltTransitionFree⟩

theorem
    stageInputIdentityDescription_haltsWithTape_of_transform_eq_some
    {recognizer : MachineDescription}
    (hrecognizer : StageInputRecognizerSpec recognizer)
    {code out : Word MachineCodeSymbol}
    (htransform :
      StageInputIdentityPrimitive.transform code = some out) :
    (StageInputIdentityDescription recognizer).HaltsWithTape
      (MachineDescription.encodeCodeWordAsInput code)
      (Tape.move Direction.right
        (Tape.input (MachineDescription.encodeCodeWordAsInput out))) := by
  rcases
      (stageInputIdentityPrimitive_transform_eq_some_iff
        code out).mp htransform with
    ⟨w, stage, hcode, hout⟩
  let A := recognizer
  let B := MachineDescription.ExactIdentityDescription
  let Tmid :=
    Tape.input (MachineDescription.encodeCodeWordAsInput code)
  let Tout :=
    Tape.move Direction.right
      (Tape.input (MachineDescription.encodeCodeWordAsInput out))
  have hAready : A.SubroutineReady := hrecognizer.left
  have hBready : B.SubroutineReady :=
    ⟨MachineDescription.exactIdentityDescription_wellFormed,
      MachineDescription.exactIdentityDescription_haltTransitionFree⟩
  rcases hrecognizer.right.left w stage with ⟨nA, hA⟩
  have hArun :
      A.runConfig nA
          { state := A.start
            tape :=
              Tape.input
                (MachineDescription.encodeCodeWordAsInput code) } =
        { state := A.halt, tape := Tmid } := by
    simpa [A, Tmid, stageInputBits, hcode]
      using hA
  have hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start
              tape := Tape.move Direction.right Tmid } =
          { state := B.halt, tape := Tout } := by
    refine ⟨0, ?_⟩
    simp [B, Tmid, Tout, hcode, hout,
      MachineDescription.runConfig,
      MachineDescription.ExactIdentityDescription]
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.right)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  have hn' :
      (StageInputIdentityDescription recognizer).runConfig n
          ((StageInputIdentityDescription recognizer).initial
            (MachineDescription.encodeCodeWordAsInput code)) =
        { state := (StageInputIdentityDescription recognizer).halt
          tape :=
            Tape.move Direction.right
              (Tape.input (MachineDescription.encodeCodeWordAsInput out)) } := by
    simpa [StageInputIdentityDescription, A, B, Tout] using hn
  constructor
  · exact congrArg MachineDescription.Configuration.state hn'
  · exact congrArg MachineDescription.Configuration.tape hn'

theorem
    stageInputIdentityDescription_haltsWithTape_inv
    {recognizer : MachineDescription}
    (hrecognizer : StageInputRecognizerSpec recognizer)
    {code : Word MachineCodeSymbol} {T : Tape Bool}
    (hhalt :
      (StageInputIdentityDescription recognizer).HaltsWithTape
        (MachineDescription.encodeCodeWordAsInput code) T) :
    exists w : Word Bool,
    exists stage : Nat,
      code = PairedRecognizerDovetailStageInputCode w stage ∧
        T =
          Tape.move Direction.right
            (Tape.input (MachineDescription.encodeCodeWordAsInput code)) := by
  let A := recognizer
  let B := MachineDescription.ExactIdentityDescription
  have hAready : A.SubroutineReady := hrecognizer.left
  have hBready : B.SubroutineReady :=
    ⟨MachineDescription.exactIdentityDescription_wellFormed,
      MachineDescription.exactIdentityDescription_haltTransitionFree⟩
  rcases
      MachineDescription.seqSubroutine_haltsWithTape_inv
        (A := A) (B := B) (handoffMove := Direction.right)
        hAready hBready hhalt with
    ⟨Tmid, hAhalt, hBReach⟩
  rcases hrecognizer.right.right code Tmid hAhalt with
    ⟨w, stage, hcode, hTmid⟩
  rcases hBReach with ⟨nB, hBRun⟩
  have hBRun' :
      MachineDescription.Configuration.mk B.halt
          (Tape.move Direction.right Tmid) =
        MachineDescription.Configuration.mk B.halt T := by
    simpa [B] using
      ((exactIdentityDescription_runConfig_from_start
          nB (Tape.move Direction.right Tmid)).symm.trans hBRun)
  have hT :
      T = Tape.move Direction.right Tmid := by
    exact (congrArg MachineDescription.Configuration.tape hBRun').symm
  refine ⟨w, stage, hcode, ?_⟩
  rw [hT, hTmid]

theorem
    stageInputIdentityClosedHandoffConstruction_of_recognizer
    {recognizer : MachineDescription}
    (hrecognizer : StageInputRecognizerSpec recognizer) :
    TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      StageInputIdentityPrimitive
      (StageInputIdentityDescription recognizer)
      tapeCodePrimitiveCodeWordHandoffMove := by
  constructor
  · constructor
    · constructor
      · exact
          (stageInputIdentityDescription_subroutineReady
            hrecognizer).left
      · intro code out
        constructor
        · intro houtput
          rcases houtput with ⟨n, hn⟩
          let D := StageInputIdentityDescription recognizer
          let T : Tape Bool :=
            (D.runConfig n
              (D.initial
                (MachineDescription.encodeCodeWordAsInput code))).tape
          have hhalt : D.HaltsWithTape
              (MachineDescription.encodeCodeWordAsInput code) T := by
            refine ⟨n, ?_⟩
            exact ⟨hn.left, rfl⟩
          rcases
              stageInputIdentityDescription_haltsWithTape_inv
                hrecognizer hhalt with
            ⟨w, stage, hcode, hT⟩
          have hnorm :
              Tape.normalizedOutput T =
                MachineDescription.encodeCodeWordAsInput code := by
            rw [hT]
            exact
              tape_normalizedOutput_move_right_input
                (MachineDescription.encodeCodeWordAsInput code)
          have hout :
              MachineDescription.encodeCodeWordAsInput code =
                MachineDescription.encodeCodeWordAsInput out := by
            simpa [D, T, hnorm] using hn.right
          have houtCode : out = code :=
            (MachineDescription.encodeCodeWordAsInput_injective hout).symm
          rw [houtCode]
          exact
            (stageInputIdentityPrimitive_transform_eq_some_iff
              code code).mpr ⟨w, stage, hcode, hcode⟩
        · intro htransform
          have hhalt :=
            stageInputIdentityDescription_haltsWithTape_of_transform_eq_some
              hrecognizer htransform
          rcases hhalt with ⟨n, hn⟩
          refine ⟨n, ?_⟩
          constructor
          · exact hn.left
          · rcases
                (stageInputIdentityPrimitive_transform_eq_some_iff
                  code out).mp htransform with
              ⟨w, stage, hcode, hout⟩
            rw [hn.right]
            rw [hout]
            exact
              tape_normalizedOutput_move_right_input
                (MachineDescription.encodeCodeWordAsInput
                  (PairedRecognizerDovetailStageInputCode w stage))
    · exact
        (stageInputIdentityDescription_subroutineReady
          hrecognizer).right
  · intro code T hhalt
    rcases
        stageInputIdentityDescription_haltsWithTape_inv
          hrecognizer hhalt with
      ⟨w, stage, hcode, hT⟩
    refine ⟨code, ?_, ?_, ?_⟩
    · exact
        (stageInputIdentityPrimitive_transform_eq_some_iff
          code code).mpr ⟨w, stage, hcode, hcode⟩
    · rw [hT]
      exact
        tape_normalizedOutput_move_right_input
          (MachineDescription.encodeCodeWordAsInput code)
    · rw [hT, hcode]
      simpa [tapeCodePrimitiveCodeWordHandoffMove,
        stageInputBits] using
        stageInputBits_move_left_move_right_input w stage

theorem stageInputValidatorSpec_of_identityClosedHandoff
    {validator : MachineDescription}
    (hvalidator :
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        StageInputIdentityPrimitive validator
        tapeCodePrimitiveCodeWordHandoffMove) :
    StageInputValidatorSpec validator := by
  constructor
  · exact
      tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_subroutineReady
        hvalidator
  constructor
  · intro w stage
    let code := PairedRecognizerDovetailStageInputCode w stage
    have htransform :
        StageInputIdentityPrimitive.transform code =
          some code := by
      exact
        (stageInputIdentityPrimitive_transform_eq_some_iff
          code code).mpr ⟨w, stage, rfl, rfl⟩
    rcases
        tapeCodePrimitiveHandoffCompiledSubroutineByDescription_haltsWithTape_of_transform_eq_some
          (tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_handoffCompiled
            hvalidator)
          htransform with
      ⟨T, hhalt, hmove⟩
    rcases hhalt with ⟨steps, hsteps⟩
    have hT :
        T =
          Tape.move Direction.right
            (Tape.input (stageInputBits w stage)) := by
      have hmove' :
          Tape.move Direction.left T =
            Tape.input (stageInputBits w stage) := by
        simpa [tapeCodePrimitiveCodeWordHandoffMove,
          stageInputBits, code] using hmove
      rcases stageInputBits_exists_cons_cons w stage with
        ⟨a, b, rest, hbits⟩
      rw [hbits] at hmove' ⊢
      exact
        tape_eq_move_right_input_of_move_left_eq_input_cons_cons
          hmove'
    refine ⟨steps, ?_⟩
    have hrunRaw :
        validator.runConfig steps
            (validator.initial
              (MachineDescription.encodeCodeWordAsInput code)) =
          { state := validator.halt, tape := T } := by
      cases hconfig :
          validator.runConfig steps
            (validator.initial
              (MachineDescription.encodeCodeWordAsInput code)) with
      | mk state tape =>
          have hstate : state = validator.halt := by
            simpa [MachineDescription.HaltsWithTapeIn,
              hconfig] using hsteps.left
          have htape : tape = T := by
            simpa [MachineDescription.HaltsWithTapeIn,
              hconfig] using hsteps.right
          cases hstate
          cases htape
          rfl
    have hrun :
        validator.runConfig steps
            (validator.initial (stageInputBits w stage)) =
          { state := validator.halt, tape := T } := by
      simpa [stageInputBits, code] using hrunRaw
    rw [hrun, hT]
  · intro code T hhalt
    rcases
        tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_haltsWithTape_output
          hvalidator hhalt with
      ⟨out, htransform, _hnorm, hmove⟩
    rcases
        (stageInputIdentityPrimitive_transform_eq_some_iff
          code out).mp htransform with
      ⟨w, stage, hcode, hout⟩
    refine ⟨w, stage, hcode, ?_⟩
    simpa [stageInputBits, hout] using hmove


end DovetailInitialLayoutInitializer
end Computability
end FoC

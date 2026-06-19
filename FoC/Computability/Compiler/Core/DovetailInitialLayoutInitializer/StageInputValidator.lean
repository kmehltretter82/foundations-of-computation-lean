import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.HeadRouter

set_option doc.verso true

/-!
# StageInputValidator

Supporting declarations and helper lemmas for Computability Compiler Core DovetailInitialLayoutInitializer StageInputValidator.
-/


namespace FoC
namespace Computability

open Languages

namespace DovetailInitialLayoutInitializer

def StageInputIdentityPrimitive :
    MachineDescription.TapeCodePrimitive where
  transform := fun code =>
    match MachineDescription.DovetailLayout.decodeStageInputComplete code with
    | some _ => some code
    | none => none

 /-- `stageInputIdentityPrimitive_transform_eq_some_iff` provides an important equivalence or equality lemma. -/
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

def stageInputSecondBitTail
    (w : Word Bool) (stage : Nat) : Word Bool :=
  match stageInputBits w stage with
  | _ :: _ :: tail => tail
  | _ => []

 /-- `stageInputBits_eq_false_false_tail` provides an important equivalence or equality lemma. -/
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
        MachineDescription.encodeNat]
      simp [MachineDescription.encodeCodeWordAsInput, MachineDescription.encodeCodeSymbolAsInput]
  | cons b rest =>
      simp [stageInputSecondBitTail, stageInputBits,
        PairedRecognizerDovetailStageInputCode,
        MachineDescription.DovetailLayout.stageInputCode,
        MachineDescription.DovetailLayout.stageInputCodeAppend,
        MachineDescription.encodeBoolWordAppend,
        MachineDescription.encodeCellListAppend,
        MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat]

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
        (MachineDescription.encodeCodeWordAsInput code) T ->
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
          (MachineDescription.encodeCodeWordAsInput code) T ->
        exists w : Word Bool,
        exists stage : Nat,
          code = PairedRecognizerDovetailStageInputCode w stage ∧
            T =
              stageInputCheckedInputTape w stage)

def StageInputRecognizerConstruction : Prop :=
  exists recognizer : MachineDescription,
    StageInputRecognizerSpec recognizer
     /-- `stageInputSecondBitMarkedHandoffTape_move_left` captures the core lemma for this local construction. -/

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
        tapeAtCells, Tape.move, Tape.moveRight, Tape.moveLeft]
      simp [MachineDescription.encodeCodeWordAsInput,
        MachineDescription.encodeCodeSymbolAsInput]
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
        tapeAtCells, Tape.move, Tape.moveRight, Tape.moveLeft]
     /-- `stageInputSecondBitMarkedCheckedHandoffTape_move_left` captures the core lemma for this local construction. -/

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
        MachineDescription.DovetailLayout.stageInputCode,
        MachineDescription.DovetailLayout.stageInputCodeAppend,
        MachineDescription.encodeBoolWordAppend,
        MachineDescription.encodeCellListAppend,
        MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat,
        tapeAtCells, Tape.move, Tape.moveRight, Tape.moveLeft]
      simp [MachineDescription.encodeCodeWordAsInput,
        MachineDescription.encodeCodeSymbolAsInput]
  | cons b rest =>
      simp [stageInputSecondBitMarkedCheckedHandoffTape,
        stageInputSecondBitMarkedCheckedTape,
        stageInputSecondBitTail, stageInputBits,
        PairedRecognizerDovetailStageInputCode,
        MachineDescription.DovetailLayout.stageInputCode,
        MachineDescription.DovetailLayout.stageInputCodeAppend,
        MachineDescription.encodeBoolWordAppend,
        MachineDescription.encodeCellListAppend,
        MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat,
        tapeAtCells, Tape.move, Tape.moveRight, Tape.moveLeft]

 /-- `stageInputCheckedInputTape_move_left_move_right` captures the core lemma for this local construction. -/
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
    [ MachineDescription.transition
        0 none (some false) Direction.left 1 ]
     /-- `restoreStageInputSecondBitDescription_wellFormed` captures the core lemma for this local construction. -/

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
     /-- `restoreStageInputSecondBitDescription_haltTransitionFree` establishes the halting condition in this construction. -/

theorem
    restoreStageInputSecondBitDescription_haltTransitionFree :
    RestoreStageInputSecondBitDescription.HaltTransitionFree := by
  intro t ht
  exact transition_notFrom_of_all
    (l := RestoreStageInputSecondBitDescription.transitions)
    (state := RestoreStageInputSecondBitDescription.halt)
    (by
      native_decide) t ht
     /-- `restoreStageInputSecondBitDescription_subroutineReady` packages a subroutine-ready composition step. -/

theorem
    restoreStageInputSecondBitDescription_subroutineReady :
    RestoreStageInputSecondBitDescription.SubroutineReady :=
  ⟨restoreStageInputSecondBitDescription_wellFormed,
    restoreStageInputSecondBitDescription_haltTransitionFree⟩

 /-- `restoreStageInputSecondBitDescription_run` captures the core lemma for this local construction. -/
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
    Tape.read, Tape.write, Tape.move, Tape.moveLeft]
  simp [Tape.input]

 /-- `restoreStageInputSecondBitDescription_run_checked` states the corresponding theorem run form. -/
theorem restoreStageInputSecondBitDescription_run_checked
    (w : Word Bool) (stage : Nat) :
    RestoreStageInputSecondBitDescription.runConfig 1
        { state := RestoreStageInputSecondBitDescription.start
          tape := stageInputSecondBitMarkedCheckedTape w stage } =
      { state := RestoreStageInputSecondBitDescription.halt
        tape := stageInputCheckedInputTape w stage } := by
  unfold stageInputSecondBitMarkedCheckedTape
  unfold stageInputCheckedInputTape
  rw [stageInputBits_eq_false_false_tail w stage]
  simp [RestoreStageInputSecondBitDescription,
    stageInputSecondBitTail,
    tapeAtCells, MachineDescription.runConfig,
    MachineDescription.stepConfig, MachineDescription.lookupTransition,
    MachineDescription.Matches, MachineDescription.transition,
    Tape.read, Tape.write, Tape.move, Tape.moveLeft]

 /-- `restoreStageInputSecondBitDescription_run_succ` states the corresponding theorem run form. -/
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

 /-- `restoreStageInputSecondBitDescription_run_checked_succ` states the corresponding theorem run form. -/
theorem restoreStageInputSecondBitDescription_run_checked_succ
    (n : Nat) (w : Word Bool) (stage : Nat) :
    RestoreStageInputSecondBitDescription.runConfig (n + 1)
        { state := RestoreStageInputSecondBitDescription.start
          tape := stageInputSecondBitMarkedCheckedTape w stage } =
      { state := RestoreStageInputSecondBitDescription.halt
        tape := stageInputCheckedInputTape w stage } := by
  rw [show n + 1 = 1 + n by omega]
  rw [MachineDescription.runConfig_add]
  rw [restoreStageInputSecondBitDescription_run_checked]
  exact
    MachineDescription.runConfig_halt
      restoreStageInputSecondBitDescription_haltTransitionFree
      (stageInputCheckedInputTape w stage) n

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

 /-- `markStageInputSecondBitDescription_wellFormed` captures the core lemma for this local construction. -/
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
     /-- `markStageInputSecondBitDescription_haltTransitionFree` establishes the halting condition in this construction. -/

theorem
    markStageInputSecondBitDescription_haltTransitionFree :
    MarkStageInputSecondBitDescription.HaltTransitionFree := by
  intro t ht
  exact transition_notFrom_of_all
    (l := MarkStageInputSecondBitDescription.transitions)
    (state := MarkStageInputSecondBitDescription.halt)
    (by
      native_decide) t ht
     /-- `markStageInputSecondBitDescription_subroutineReady` packages a subroutine-ready composition step. -/

theorem
    markStageInputSecondBitDescription_subroutineReady :
    MarkStageInputSecondBitDescription.SubroutineReady :=
  ⟨markStageInputSecondBitDescription_wellFormed,
    markStageInputSecondBitDescription_haltTransitionFree⟩

 /-- `markStageInputSecondBitDescription_run` captures the core lemma for this local construction. -/
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

 /-- `markStageInputSecondBitDescription_run_bits` states the corresponding theorem run form. -/
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

 /-- `markStageInputSecondBitDescription_haltsWithTape_inv` establishes the halting condition in this construction. -/
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
              stageInputSecondBitMarkedCheckedHandoffTape
                w stage }) ∧
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
          (MachineDescription.encodeCodeWordAsInput code) T ->
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
  MachineDescription.seqSubroutine
    MarkStageInputSecondBitDescription scanner Direction.right

 /-- `stageInputMarkedCoreDescription_subroutineReady` packages a subroutine-ready composition step. -/
theorem stageInputMarkedCoreDescription_subroutineReady
    {scanner : MachineDescription}
    (hscanner : StageInputMarkedScannerSpec scanner) :
    (StageInputMarkedCoreDescription scanner).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    markStageInputSecondBitDescription_subroutineReady
    hscanner.left

 /-- `stageInputMarkedCoreSpec_of_markedScanner` characterizes a scan safety phase. -/
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
                stageInputSecondBitMarkedCheckedHandoffTape
                  w stage } := by
      rcases hscanner.right.left w stage with ⟨nB, hB⟩
      refine ⟨nB, ?_⟩
      simpa [B, Tmid,
        stageInputSecondBitMarkedCheckedHandoffTape] using hB
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

 /-- `stageInputRecognizerDescription_subroutineReady` packages a subroutine-ready composition step. -/
theorem stageInputRecognizerDescription_subroutineReady
    {markedCore : MachineDescription}
    (hmarkedCore : StageInputMarkedCoreSpec markedCore) :
    (StageInputRecognizerDescription markedCore).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    hmarkedCore.left
    restoreStageInputSecondBitDescription_subroutineReady

 /-- `stageInputRecognizerSpec_of_markedCore` states the finite-machine specification. -/
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
              stageInputSecondBitMarkedCheckedHandoffTape
                w stage } := by
      simpa [A, MachineDescription.initial] using hA
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
              MachineDescription.runConfig] using
              congrArg MachineDescription.Configuration.state hBRunMarked
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
                  MachineDescription.Configuration) =
                { state := B.halt
                  tape :=
                    stageInputCheckedInputTape w stage } :=
            hBRunMarked.symm.trans htarget
          exact congrArg MachineDescription.Configuration.tape hcfg
    exact ⟨w, stage, hcode, hT⟩

 /-- `exactIdentityDescription_runConfig_from_start` states the corresponding theorem run form. -/
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

 /-- `stageInputIdentityDescription_subroutineReady` packages a subroutine-ready composition step. -/
theorem stageInputIdentityDescription_subroutineReady
    {recognizer : MachineDescription}
    (hrecognizer : StageInputRecognizerSpec recognizer) :
    (StageInputIdentityDescription recognizer).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    hrecognizer.left
    ⟨MachineDescription.exactIdentityDescription_wellFormed,
      MachineDescription.exactIdentityDescription_haltTransitionFree⟩

 /-- `stageInputIdentityDescription_spec_of_recognizer` states the finite-machine specification. -/
theorem stageInputIdentityDescription_spec_of_recognizer
    {recognizer : MachineDescription}
    (hrecognizer : StageInputRecognizerSpec recognizer) :
    StageInputValidatorSpec
      (StageInputIdentityDescription recognizer) := by
  constructor
  · exact stageInputIdentityDescription_subroutineReady
      hrecognizer
  constructor
  · intro w stage
    let A := recognizer
    let B := MachineDescription.ExactIdentityDescription
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
                  (MachineDescription.encodeCodeWordAsInput
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
        MachineDescription.runConfig,
        MachineDescription.ExactIdentityDescription]
    rcases
        MachineDescription.seqSubroutine_reaches_of_runConfig_eq
          (A := A) (B := B) (handoffMove := Direction.right)
          hAready hBready hArun hBReach with
      ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [StageInputIdentityDescription, A, B,
      MachineDescription.initial, stageInputBits] using hn
  · intro code T hhalt
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
    exact stageInputCheckedInputTape_move_left_move_right w stage
     /-- `stageInputIdentityClosedHandoffConstruction_of_recognizer` captures the core lemma for this local construction. -/

theorem
    stageInputIdentityClosedHandoffConstruction_of_recognizer
    {recognizer : MachineDescription}
    (hrecognizer : StageInputRecognizerSpec recognizer) :
    StageInputIdentityClosedHandoffConstruction :=
  ⟨StageInputIdentityDescription recognizer,
    stageInputIdentityDescription_spec_of_recognizer hrecognizer⟩

 /-- `stageInputValidatorSpec_of_identityClosedHandoff` states the finite-machine specification. -/
theorem stageInputValidatorSpec_of_identityClosedHandoff
    {validator : MachineDescription}
    (hvalidator : StageInputValidatorSpec validator) :
    StageInputValidatorSpec validator :=
  hvalidator


end DovetailInitialLayoutInitializer
end Computability
end FoC

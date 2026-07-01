import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Simulator.PaddedParser.Contracts

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner

namespace EncodedRewriters
namespace BoundedLayoutRunner

open CanonicalLayouts.DovetailLayoutScanner
open CanonicalLayouts.DovetailStagePrefix
open CommonGround.SeqComposition
def fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner :
    Word Bool :=
  encodeCodeSymbolAsInput MachineCodeSymbol.header

def FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner :
    MachineDescription where
  stateCount := 100
  start := 30
  halt := 99
  transitions :=
    [ keepMove 30 (some false) Direction.right 31
    , keepMove 31 (some false) Direction.right 32
    , keepMove 32 (some false) Direction.right 33
    , keepMove 33 (some false) Direction.right 40
    , keepMove 40 (some false) Direction.left 99
    , keepMove 40 (some true) Direction.left 99
    ]

theorem fixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_wellFormed_configRunner :
    FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l :=
        FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner.transitions)
      (stateCount :=
        FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l :=
        FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner.transitions)
      (by decide)

theorem fixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_haltTransitionFree_configRunner :
    FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner.HaltTransitionFree :=
  transition_notFrom_of_all
    (l :=
      FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner.transitions)
    (state :=
      FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner.halt)
    (by decide)

theorem fixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_subroutineReady_configRunner :
    FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner.SubroutineReady :=
  ⟨fixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_wellFormed_configRunner,
    fixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_haltTransitionFree_configRunner⟩

def fixedDescriptionBoundedSimulatorHeaderPrefixHandoffConfigWithBase_configRunner
    (baseLeft : List (Option Bool)) (suffixBits : Word Bool) :
    Configuration :=
  { state :=
      FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner.halt
    tape :=
      Tape.move Direction.left
        (DovetailInitialLayoutInitializer.tapeAtCells
          (List.append
            (fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner.reverse.map
              some)
            baseLeft)
          (suffixBits.map some)) }

def fixedDescriptionBoundedSimulatorHeaderPrefixHandoffConfigWithBaseAndRight_configRunner
    (baseLeft : List (Option Bool)) (suffixBits : Word Bool)
    (rightPadding : List (Option Bool)) : Configuration :=
  { state :=
      FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner.halt
    tape :=
      Tape.move Direction.left
        (DovetailInitialLayoutInitializer.tapeAtCells
          (List.append
            (fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner.reverse.map
              some)
            baseLeft)
          (List.append (suffixBits.map some) rightPadding)) }

theorem fixedDescriptionBoundedSimulatorHeaderPrefix_run_raw_to_handoff_withBase_configRunner
    (baseLeft : List (Option Bool)) (b : Bool)
    (suffixTail : Word Bool) :
    exists steps : Nat,
      FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner.runConfig
          steps
          (DovetailInitialLayoutInitializer.config
            FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner.start
            baseLeft
            (List.append
              (fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner.map
                some)
              (some b :: suffixTail.map some))) =
        fixedDescriptionBoundedSimulatorHeaderPrefixHandoffConfigWithBase_configRunner
          baseLeft (b :: suffixTail) := by
  refine ⟨5, ?_⟩
  cases b <;>
    simp [FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner,
      fixedDescriptionBoundedSimulatorHeaderPrefixHandoffConfigWithBase_configRunner,
      fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner,
      DovetailInitialLayoutInitializer.config,
      DovetailInitialLayoutInitializer.tapeAtCells, keepMove, runConfig,
      stepConfig,
      lookupTransition, Matches, transition, encodeCodeSymbolAsInput,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem fixedDescriptionBoundedSimulatorHeaderPrefix_run_raw_to_handoff_withBaseAndRight_configRunner
    (baseLeft : List (Option Bool)) (b : Bool)
    (suffixTail : Word Bool) (rightPadding : List (Option Bool)) :
    exists steps : Nat,
      FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner.runConfig
          steps
          (DovetailInitialLayoutInitializer.config
            FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner.start
            baseLeft
            (List.append
              (fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner.map
                some)
              (some b :: List.append (suffixTail.map some) rightPadding))) =
        fixedDescriptionBoundedSimulatorHeaderPrefixHandoffConfigWithBaseAndRight_configRunner
          baseLeft (b :: suffixTail) rightPadding := by
  refine ⟨5, ?_⟩
  cases b <;>
    simp [FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner,
      fixedDescriptionBoundedSimulatorHeaderPrefixHandoffConfigWithBaseAndRight_configRunner,
      fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner,
      DovetailInitialLayoutInitializer.config,
      DovetailInitialLayoutInitializer.tapeAtCells, keepMove, runConfig,
      stepConfig,
      lookupTransition, Matches, transition, encodeCodeSymbolAsInput,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem fixedDescriptionBoundedSimulatorHeaderPrefixHandoffConfigWithBase_move_right_configRunner
    (baseLeft : List (Option Bool)) (b : Bool)
    (suffixTail : Word Bool) :
    Tape.move Direction.right
        (fixedDescriptionBoundedSimulatorHeaderPrefixHandoffConfigWithBase_configRunner
          baseLeft (b :: suffixTail)).tape =
      DovetailInitialLayoutInitializer.tapeAtCells
        (List.append
          (fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner.reverse.map
            some)
          baseLeft)
        ((b :: suffixTail).map some) := by
  cases b <;>
    simp [fixedDescriptionBoundedSimulatorHeaderPrefixHandoffConfigWithBase_configRunner,
      fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner,
      encodeCodeSymbolAsInput,
      DovetailInitialLayoutInitializer.tapeAtCells,
      Tape.move, Tape.moveLeft, Tape.moveRight]

theorem fixedDescriptionBoundedSimulatorHeaderPrefixHandoffConfigWithBaseAndRight_move_right_configRunner
    (baseLeft : List (Option Bool)) (b : Bool)
    (suffixTail : Word Bool) (rightPadding : List (Option Bool)) :
    Tape.move Direction.right
        (fixedDescriptionBoundedSimulatorHeaderPrefixHandoffConfigWithBaseAndRight_configRunner
          baseLeft (b :: suffixTail) rightPadding).tape =
      DovetailInitialLayoutInitializer.tapeAtCells
        (List.append
          (fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner.reverse.map
            some)
          baseLeft)
        (List.append ((b :: suffixTail).map some) rightPadding) := by
  cases b <;>
    simp [fixedDescriptionBoundedSimulatorHeaderPrefixHandoffConfigWithBaseAndRight_configRunner,
      fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner,
      encodeCodeSymbolAsInput,
      DovetailInitialLayoutInitializer.tapeAtCells,
      Tape.move, Tape.moveLeft, Tape.moveRight]

def FixedDescriptionBoundedSimulatorHeaderPrefixScannerSpec_configRunner
    (scanner : MachineDescription) : Prop :=
  scanner.SubroutineReady ∧
    forall (baseLeft : List (Option Bool)) (b : Bool)
      (suffixTail : Word Bool),
      scanner.HaltsFromTape
        (DovetailInitialLayoutInitializer.tapeAtCells baseLeft
          (List.append
            (fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner.map
              some)
            (some b :: suffixTail.map some)))
        (fixedDescriptionBoundedSimulatorHeaderPrefixHandoffConfigWithBase_configRunner
          baseLeft (b :: suffixTail)).tape

def FixedDescriptionBoundedSimulatorHeaderPrefixScannerConstruction_configRunner :
    Prop :=
  exists scanner : MachineDescription,
    FixedDescriptionBoundedSimulatorHeaderPrefixScannerSpec_configRunner
      scanner

theorem fixedDescriptionBoundedSimulatorHeaderPrefixScannerConstruction_scaffold_configRunner :
    FixedDescriptionBoundedSimulatorHeaderPrefixScannerConstruction_configRunner := by
  refine
    ⟨FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner,
      ?_⟩
  constructor
  · exact
      fixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_subroutineReady_configRunner
  · intro baseLeft b suffixTail
    rcases
        fixedDescriptionBoundedSimulatorHeaderPrefix_run_raw_to_handoff_withBase_configRunner
          baseLeft b suffixTail with
      ⟨steps, hsteps⟩
    exact
      ⟨steps, by
        constructor
        · simpa [HaltsFromTapeIn] using
            congrArg Configuration.state hsteps
        · simpa [HaltsFromTapeIn] using
            congrArg Configuration.tape hsteps⟩

/--
Concrete scanner for the configuration field followed by the final simulator
hit flag.
-/
def FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner :
    MachineDescription :=
  seqSubroutine
    ConfigurationSuffixScannerDescription
    BoolFinalScannerDescription
    Direction.right

theorem fixedDescriptionBoundedSimulatorConfigHitScannerDescription_subroutineReady_configRunner :
    FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner.SubroutineReady :=
  seqSubroutine_subroutineReady
    configurationSuffixScannerDescription_subroutineReady
    boolFinalScannerDescription_subroutineReady

theorem run_fixedDescriptionBoundedSimulatorConfigHit_raw_to_handoff_withBase_configRunner
    (cfg : Configuration) (hit : Bool)
    (baseLeft : List (Option Bool)) :
    exists steps : Nat,
      FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner.runConfig
          steps
          { state :=
              FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner.start
            tape :=
              DovetailInitialLayoutInitializer.tapeAtCells baseLeft
                ((configurationFieldBits cfg
                  (boolFieldBits hit [])).map some) } =
        { state :=
            FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner.halt
          tape :=
            (boolFinalHandoffConfigWithBase hit
              (configurationRestoredLeftWithBase cfg baseLeft)).tape } := by
  rcases cellCodeBits_cons_false (some hit) with ⟨hitTail, hhitTail⟩
  rcases run_configurationSuffix_raw_to_handoff_withBase
      cfg baseLeft hitTail with
    ⟨configSteps, hconfig⟩
  let TmidTape : Tape Bool :=
    (cellListCanonicalHandoffConfigWithBase cfg.tape.right
      (List.append ((cellCodeBits cfg.tape.head).reverse.map some)
        (cellListCanonicalRestoredLeftWithBase cfg.tape.left
          (List.append ((stageNatBits cfg.state).reverse.map some)
            baseLeft)))
      (false :: hitTail)).tape
  have hArun :
      ConfigurationSuffixScannerDescription.runConfig configSteps
          { state := ConfigurationSuffixScannerDescription.start
            tape :=
              DovetailInitialLayoutInitializer.tapeAtCells baseLeft
                ((configurationFieldBits cfg
                  (boolFieldBits hit [])).map some) } =
        { state := ConfigurationSuffixScannerDescription.halt
          tape := TmidTape } := by
    rw [show
        ((configurationFieldBits cfg
          (boolFieldBits hit [])).map some) =
          (configurationFieldBits cfg (false :: hitTail)).map some by
      simp [boolFieldBits, cellFieldBits, hhitTail]]
    simpa [TmidTape] using hconfig
  have hBReach :
      exists nB : Nat,
        BoolFinalScannerDescription.runConfig nB
            { state := BoolFinalScannerDescription.start
              tape := Tape.move Direction.right TmidTape } =
          { state := BoolFinalScannerDescription.halt
            tape :=
              (boolFinalHandoffConfigWithBase hit
                (configurationRestoredLeftWithBase cfg baseLeft)).tape } := by
    rcases run_boolFinal_raw_to_handoff_withBase
        hit (configurationRestoredLeftWithBase cfg baseLeft) with
      ⟨finalSteps, hfinal⟩
    have hmove :
        Tape.move Direction.right TmidTape =
          DovetailInitialLayoutInitializer.tapeAtCells
            (configurationRestoredLeftWithBase cfg baseLeft)
            ((cellCodeBits (some hit)).map some) := by
      have hraw :
          Tape.move Direction.right TmidTape =
            DovetailInitialLayoutInitializer.tapeAtCells
              (configurationRestoredLeftWithBase cfg baseLeft)
              ((false :: hitTail).map some) := by
        simpa [TmidTape, configurationRestoredLeftWithBase] using
          cellListCanonicalHandoffConfigWithBase_move_right
            cfg.tape.right
            (List.append
              ((cellCodeBits cfg.tape.head).reverse.map some)
              (cellListCanonicalRestoredLeftWithBase cfg.tape.left
                (List.append
                  ((stageNatBits cfg.state).reverse.map some)
                  baseLeft)))
            false hitTail
      rw [hraw]
      have hhitCells :
          (false :: hitTail).map some =
            (cellCodeBits (some hit)).map some := by
        simpa using congrArg (fun bits => bits.map some) hhitTail.symm
      simp [hhitCells]
    exact
      runConfig_reaches_from_move_eq
        (B := BoolFinalScannerDescription)
        (handoffMove := Direction.right)
        hmove
        (by simpa [DovetailInitialLayoutInitializer.config] using hfinal)
  simpa [FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner,
    TmidTape] using
      seqSubroutine_runConfig_exists
        (A := ConfigurationSuffixScannerDescription)
        (B := BoolFinalScannerDescription)
        (handoffMove := Direction.right)
        configurationSuffixScannerDescription_subroutineReady
        boolFinalScannerDescription_subroutineReady
        hArun hBReach

theorem fixedDescriptionBoundedSimulatorConfigHitScannerDescription_runConfig_code_inv_configRunner
    (baseLeft : List (Option Bool)) (code : Word MachineCodeSymbol)
    {Tout : Tape Bool} {n : Nat}
    (h :
      FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner.runConfig
          n
          (DovetailInitialLayoutInitializer.config
            FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner.start
            baseLeft
            ((encodeCodeWordAsInput code).map some)) =
        { state :=
            FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner.halt
          tape := Tout }) :
    exists cfg : Configuration,
    exists hit : Bool,
    exists baseAfter : List (Option Bool),
      code = encodeConfigurationAppend cfg (encodeBoolAppend hit []) ∧
        Tape.move Direction.right Tout =
          DovetailInitialLayoutInitializer.tapeAtCells baseAfter [] := by
  have hseq :
      (seqSubroutine
        ConfigurationSuffixScannerDescription
        BoolFinalScannerDescription
        Direction.right).runConfig n
          (DovetailInitialLayoutInitializer.config
            (seqSubroutine
              ConfigurationSuffixScannerDescription
              BoolFinalScannerDescription
              Direction.right).start
            baseLeft
            ((encodeCodeWordAsInput code).map some)) =
        { state :=
            (seqSubroutine
              ConfigurationSuffixScannerDescription
              BoolFinalScannerDescription
              Direction.right).halt
          tape := Tout } := by
    simpa [FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner]
      using h
  rcases
      seqSubroutine_runConfig_inv
        (A := ConfigurationSuffixScannerDescription)
        (B := BoolFinalScannerDescription)
        (handoffMove := Direction.right)
        configurationSuffixScannerDescription_subroutineReady
        boolFinalScannerDescription_subroutineReady
        hseq with
    ⟨Tcfg, hcfg, hhit⟩
  rcases hcfg with ⟨nCfg, hcfgRun, _hcfgFirst⟩
  rcases
      configurationSuffixScannerDescription_runConfig_code_handoff
        baseLeft code
        (by simpa [DovetailInitialLayoutInitializer.config] using
          hcfgRun) with
    ⟨cfg, suffix, baseAfterCfg, hcode, hcfgMove⟩
  rcases hhit with ⟨nHit, hhitRun⟩
  have hhitCodeRun :
      BoolFinalScannerDescription.runConfig nHit
          (DovetailInitialLayoutInitializer.config
            BoolFinalScannerDescription.start baseAfterCfg
            ((encodeCodeWordAsInput suffix).map some)) =
        { state := BoolFinalScannerDescription.halt
          tape := Tout } := by
    simpa [DovetailInitialLayoutInitializer.config, hcfgMove] using
      hhitRun
  rcases
      boolFinalScannerDescription_runConfig_code_terminal_inv
        baseAfterCfg suffix hhitCodeRun with
    ⟨hit, hsuffix, hmove⟩
  refine ⟨cfg, hit, _, ?_, hmove⟩
  rw [hcode, hsuffix]

theorem fixedDescriptionBoundedSimulatorBoolFinalHandoffConfigWithBase_normalizedOutput_configRunner
    (hit : Bool) (baseLeft : List (Option Bool)) :
    Tape.normalizedOutput
        (boolFinalHandoffConfigWithBase hit baseLeft).tape =
      List.append (baseLeft.reverse.filterMap (fun cell => cell))
        (cellCodeBits (some hit)) := by
  cases hit <;>
    simp [boolFinalHandoffConfigWithBase, cellCodeBits,
      encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
      DovetailInitialLayoutInitializer.tapeAtCells,
      Tape.move, Tape.moveLeft, Tape.normalizedOutput, Tape.cells,
      List.filterMap_append, List.append_assoc]

theorem fixedDescriptionBoundedSimulatorConfigurationRestoredLeftWithBase_reverse_filterMap_configRunner
    (cfg : Configuration) (baseLeft : List (Option Bool)) :
    (configurationRestoredLeftWithBase cfg baseLeft).reverse.filterMap
        (fun cell => cell) =
      List.append (baseLeft.reverse.filterMap (fun cell => cell))
        (configurationFieldBits cfg []) := by
  rw [← configurationRestoredBitsRev_map_some_withBase cfg baseLeft]
  simp [Function.comp_def, List.reverse_append, List.filterMap_append,
    configurationRestoredBitsRev_reverse]

theorem fixedDescriptionBoundedSimulatorCellListCanonicalRestoredLeftWithBase_reverse_filterMap_configRunner
    (cells baseLeft : List (Option Bool)) :
    (cellListCanonicalRestoredLeftWithBase cells baseLeft).reverse.filterMap
        (fun cell => cell) =
      List.append (baseLeft.reverse.filterMap (fun cell => cell))
        (cellListFieldBits cells []) := by
  rw [← cellListCanonicalRestoredBitsRev_map_some_withBase cells baseLeft]
  simp [Function.comp_def, List.reverse_append, List.filterMap_append,
    cellListCanonicalRestoredBitsRev_reverse]

/--
Concrete scanner for the stage, configuration, and final hit fields of a
simulator layout.
-/
def FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner :
    MachineDescription :=
  seqSubroutine
    NonemptyNatSuffixScannerDescription
    FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner
    Direction.right

theorem fixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_subroutineReady_configRunner :
    FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner.SubroutineReady :=
  seqSubroutine_subroutineReady
    nonemptyNatSuffixScannerDescription_subroutineReady
    fixedDescriptionBoundedSimulatorConfigHitScannerDescription_subroutineReady_configRunner

theorem run_fixedDescriptionBoundedSimulatorStageConfigHit_raw_to_handoff_withBase_configRunner
    (stage : Nat) (cfg : Configuration) (hit : Bool)
    (baseLeft : List (Option Bool)) :
    exists steps : Nat,
      FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner.runConfig
          steps
          { state :=
              FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner.start
            tape :=
              DovetailInitialLayoutInitializer.tapeAtCells baseLeft
                ((List.append (stageNatBits stage)
                  (configurationFieldBits cfg
                    (boolFieldBits hit []))).map some) } =
        { state :=
            FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner.halt
          tape :=
            (boolFinalHandoffConfigWithBase hit
              (configurationRestoredLeftWithBase cfg
                (List.append ((stageNatBits stage).reverse.map some)
                  baseLeft))).tape } := by
  rcases configurationFieldBits_cons_false cfg (boolFieldBits hit []) with
    ⟨cfgTail, hcfgTail⟩
  rcases run_nonemptyNatSuffix_raw_to_handoff_withBase
      stage baseLeft false cfgTail with
    ⟨stageSteps, hstage⟩
  let TmidTape : Tape Bool :=
    (nonemptyNatSuffixHandoffConfigWithBase
      stage baseLeft (false :: cfgTail)).tape
  let baseAfterStage : List (Option Bool) :=
    List.append ((stageNatBits stage).reverse.map some) baseLeft
  have hArun :
      NonemptyNatSuffixScannerDescription.runConfig stageSteps
          { state := NonemptyNatSuffixScannerDescription.start
            tape :=
              DovetailInitialLayoutInitializer.tapeAtCells baseLeft
                ((List.append (stageNatBits stage)
                  (configurationFieldBits cfg
                    (boolFieldBits hit []))).map some) } =
        { state := NonemptyNatSuffixScannerDescription.halt
          tape := TmidTape } := by
    rw [show
        (List.append (stageNatBits stage)
          (configurationFieldBits cfg
            (boolFieldBits hit []))).map some =
          (List.append (stageNatBits stage)
            (false :: cfgTail)).map some by
      rw [hcfgTail]]
    simpa [TmidTape] using hstage
  have hBReach :
      exists nB : Nat,
        FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner.runConfig
            nB
            { state :=
                FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner.start
              tape := Tape.move Direction.right TmidTape } =
          { state :=
              FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner.halt
            tape :=
              (boolFinalHandoffConfigWithBase hit
                (configurationRestoredLeftWithBase cfg baseAfterStage)).tape } := by
    rcases
        run_fixedDescriptionBoundedSimulatorConfigHit_raw_to_handoff_withBase_configRunner
          cfg hit baseAfterStage with
      ⟨configSteps, hconfig⟩
    have hmove :
        Tape.move Direction.right TmidTape =
          DovetailInitialLayoutInitializer.tapeAtCells baseAfterStage
            ((configurationFieldBits cfg (boolFieldBits hit [])).map some) := by
      have hraw :
          Tape.move Direction.right TmidTape =
            DovetailInitialLayoutInitializer.tapeAtCells baseAfterStage
              ((false :: cfgTail).map some) := by
        simpa [TmidTape, baseAfterStage] using
          nonemptyNatSuffixHandoffConfigWithBase_move_right
            stage baseLeft false cfgTail
      rw [hraw]
      have hcfgCells :
          (false :: cfgTail).map some =
            (configurationFieldBits cfg (boolFieldBits hit [])).map some := by
        simpa using congrArg (fun bits => bits.map some) hcfgTail.symm
      simp [hcfgCells]
    exact
      runConfig_reaches_from_move_eq
        (B := FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner)
        (handoffMove := Direction.right)
        hmove
        hconfig
  simpa [FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner,
    TmidTape, baseAfterStage] using
      seqSubroutine_runConfig_exists
        (A := NonemptyNatSuffixScannerDescription)
        (B := FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner)
        (handoffMove := Direction.right)
        nonemptyNatSuffixScannerDescription_subroutineReady
        fixedDescriptionBoundedSimulatorConfigHitScannerDescription_subroutineReady_configRunner
        hArun hBReach

theorem fixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_runConfig_code_inv_configRunner
    (baseLeft : List (Option Bool)) (code : Word MachineCodeSymbol)
    {Tout : Tape Bool} {n : Nat}
    (h :
      FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner.runConfig
          n
          (DovetailInitialLayoutInitializer.config
            FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner.start
            baseLeft
            ((encodeCodeWordAsInput code).map some)) =
        { state :=
            FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner.halt
          tape := Tout }) :
    exists stage : Nat,
    exists cfg : Configuration,
    exists hit : Bool,
    exists baseAfter : List (Option Bool),
      code =
        encodeNatAppend stage
          (encodeConfigurationAppend cfg (encodeBoolAppend hit [])) ∧
        Tape.move Direction.right Tout =
          DovetailInitialLayoutInitializer.tapeAtCells baseAfter [] := by
  have hseq :
      (seqSubroutine
        NonemptyNatSuffixScannerDescription
        FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner
        Direction.right).runConfig n
          (DovetailInitialLayoutInitializer.config
            (seqSubroutine
              NonemptyNatSuffixScannerDescription
              FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner
              Direction.right).start
            baseLeft
            ((encodeCodeWordAsInput code).map some)) =
        { state :=
            (seqSubroutine
              NonemptyNatSuffixScannerDescription
              FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner
              Direction.right).halt
          tape := Tout } := by
    simpa [FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner]
      using h
  rcases
      seqSubroutine_runConfig_inv
        (A := NonemptyNatSuffixScannerDescription)
        (B := FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner)
        (handoffMove := Direction.right)
        nonemptyNatSuffixScannerDescription_subroutineReady
        fixedDescriptionBoundedSimulatorConfigHitScannerDescription_subroutineReady_configRunner
        hseq with
    ⟨Tstage, hstage, hrest⟩
  rcases hstage with ⟨nStage, hstageRun, _hstageFirst⟩
  rcases
      nonemptyNatSuffixScannerDescription_runConfig_code_inv
        baseLeft code
        (by simpa [DovetailInitialLayoutInitializer.config] using
          hstageRun) with
    ⟨stage, suffixSymbol, suffixRest, hcodeStage⟩
  rcases
      encodeCodeWordAsInput_cons_bits suffixSymbol suffixRest with
    ⟨suffixBit, suffixTail, hsuffixBits⟩
  rcases
      nonemptyNatSuffixScannerDescription_runConfig_encodeNatAppend_handoff
        baseLeft stage (suffixSymbol :: suffixRest) suffixBit suffixTail
        hsuffixBits
        (by
          simpa [DovetailInitialLayoutInitializer.config, hcodeStage] using
            hstageRun) with
    ⟨baseAfterStage, hstageMove⟩
  rcases hrest with ⟨nRest, hrestRun⟩
  have hrestCodeRun :
      FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner.runConfig
          nRest
          (DovetailInitialLayoutInitializer.config
            FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner.start
            baseAfterStage
            ((encodeCodeWordAsInput
              (suffixSymbol :: suffixRest)).map some)) =
        { state :=
            FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner.halt
          tape := Tout } := by
    simpa [DovetailInitialLayoutInitializer.config, hstageMove] using
      hrestRun
  rcases
      fixedDescriptionBoundedSimulatorConfigHitScannerDescription_runConfig_code_inv_configRunner
        baseAfterStage (suffixSymbol :: suffixRest) hrestCodeRun with
    ⟨cfg, hit, baseAfter, hsuffixCode, hmove⟩
  refine ⟨stage, cfg, hit, baseAfter, ?_, hmove⟩
  rw [hcodeStage, hsuffixCode]

/--
Concrete scanner for the simulator-layout payload after the leading header code
symbol.  It validates the bool-word input, stage, configuration, and final hit
flag using the existing canonical suffix scanners.
-/
def FixedDescriptionBoundedSimulatorLayoutPayloadScannerDescription_configRunner :
    MachineDescription :=
  seqSubroutine
    BoolWordSuffixScannerDescription
    FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner
    Direction.right

theorem fixedDescriptionBoundedSimulatorLayoutPayloadScannerDescription_subroutineReady_configRunner :
    FixedDescriptionBoundedSimulatorLayoutPayloadScannerDescription_configRunner.SubroutineReady :=
  seqSubroutine_subroutineReady
    boolWordSuffixScannerDescription_subroutineReady
    fixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_subroutineReady_configRunner

def fixedDescriptionBoundedSimulatorLayoutPayloadBits_configRunner
    (L : SimulatorLayout) : Word Bool :=
  boolWordFieldBits L.input
    (List.append (stageNatBits L.stage)
      (configurationFieldBits L.config (boolFieldBits L.hit [])))

theorem fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_header_payloadBits_configRunner
    (L : SimulatorLayout) :
    SimulatorLayout.asBoolInput L =
      List.append fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner
        (fixedDescriptionBoundedSimulatorLayoutPayloadBits_configRunner L) := by
  rw [SimulatorLayout.asBoolInput, SimulatorLayout.encode,
    SimulatorLayout.encodeAppend]
  change
    List.append (encodeCodeSymbolAsInput MachineCodeSymbol.header)
        (encodeCodeWordAsInput
          (encodeBoolWordAppend L.input
            (encodeNatAppend L.stage
              (encodeConfigurationAppend L.config
                (encodeBoolAppend L.hit []))))) =
      List.append fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner
        (fixedDescriptionBoundedSimulatorLayoutPayloadBits_configRunner L)
  rw [boolWordBits_eq_encodeBoolWordAppend]
  rw [natBits_eq_encodeNatAppend]
  rw [configurationFieldBits_eq_encodeConfigurationAppend]
  rw [boolBits_eq_encodeBoolAppend]
  simp [fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner,
    fixedDescriptionBoundedSimulatorLayoutPayloadBits_configRunner,
    boolWordFieldBits, cellListFieldBits, boolFieldBits,
    cellFieldBits, configurationFieldBits, tapeFieldBits,
    encodeCodeWordAsInput, List.append_nil]

theorem run_fixedDescriptionBoundedSimulatorLayoutPayload_raw_to_handoff_withBase_configRunner
    (L : SimulatorLayout) (baseLeft : List (Option Bool)) :
    exists steps : Nat,
      FixedDescriptionBoundedSimulatorLayoutPayloadScannerDescription_configRunner.runConfig
          steps
          { state :=
              FixedDescriptionBoundedSimulatorLayoutPayloadScannerDescription_configRunner.start
            tape :=
              DovetailInitialLayoutInitializer.tapeAtCells baseLeft
                ((boolWordFieldBits L.input
                  (List.append (stageNatBits L.stage)
                    (configurationFieldBits L.config
                      (boolFieldBits L.hit [])))).map some) } =
        { state :=
            FixedDescriptionBoundedSimulatorLayoutPayloadScannerDescription_configRunner.halt
          tape :=
            (boolFinalHandoffConfigWithBase L.hit
              (configurationRestoredLeftWithBase L.config
                (List.append ((stageNatBits L.stage).reverse.map some)
                  (cellListCanonicalRestoredLeftWithBase
                    (L.input.map some) baseLeft)))).tape } := by
  let stageSuffix : Word Bool :=
    configurationFieldBits L.config (boolFieldBits L.hit [])
  rcases stageNatBits_cons_false L.stage with ⟨stageTail, hstageTail⟩
  let inputSuffixTail : Word Bool :=
    List.append stageTail stageSuffix
  rcases run_boolWordSuffix_raw_to_canonical_handoff_withBase
      L.input baseLeft inputSuffixTail with
    ⟨inputSteps, hinput⟩
  let TmidTape : Tape Bool :=
    (boolWordCanonicalHandoffConfigWithBase L.input baseLeft
      (false :: inputSuffixTail)).tape
  let baseAfterInput : List (Option Bool) :=
    cellListCanonicalRestoredLeftWithBase (L.input.map some) baseLeft
  have hArun :
      BoolWordSuffixScannerDescription.runConfig inputSteps
          { state := BoolWordSuffixScannerDescription.start
            tape :=
              DovetailInitialLayoutInitializer.tapeAtCells baseLeft
                ((boolWordFieldBits L.input
                  (List.append (stageNatBits L.stage)
                    (configurationFieldBits L.config
                      (boolFieldBits L.hit [])))).map some) } =
        { state := BoolWordSuffixScannerDescription.halt
          tape := TmidTape } := by
    change
      BoolWordSuffixScannerDescription.runConfig inputSteps
          (DovetailInitialLayoutInitializer.config
            BoolWordSuffixScannerDescription.start baseLeft
            ((boolWordFieldBits L.input
              (List.append (stageNatBits L.stage) stageSuffix)).map some)) =
        { state := BoolWordSuffixScannerDescription.halt
          tape := TmidTape }
    rw [show
        ((boolWordFieldBits L.input
          (List.append (stageNatBits L.stage) stageSuffix)).map some) =
          List.append ((stageNatBits L.input.length).map some)
            (List.append ((cellsCodeBits (L.input.map some)).map some)
              (some false :: inputSuffixTail.map some)) by
      rw [hstageTail]
      simp [boolWordFieldBits, cellListFieldBits, inputSuffixTail,
        stageSuffix, List.map_append]]
    simpa [TmidTape, boolWordCanonicalHandoffConfigWithBase] using
      hinput
  have hBReach :
      exists nB : Nat,
        FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner.runConfig
            nB
            { state :=
                FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner.start
              tape := Tape.move Direction.right TmidTape } =
          { state :=
              FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner.halt
            tape :=
              (boolFinalHandoffConfigWithBase L.hit
                (configurationRestoredLeftWithBase L.config
                  (List.append ((stageNatBits L.stage).reverse.map some)
                    baseAfterInput))).tape } := by
    rcases
        run_fixedDescriptionBoundedSimulatorStageConfigHit_raw_to_handoff_withBase_configRunner
          L.stage L.config L.hit baseAfterInput with
      ⟨stageSteps, hstage⟩
    have hmove :
        Tape.move Direction.right TmidTape =
          DovetailInitialLayoutInitializer.tapeAtCells baseAfterInput
            ((List.append (stageNatBits L.stage) stageSuffix).map some) := by
      have hraw :
          Tape.move Direction.right TmidTape =
            DovetailInitialLayoutInitializer.tapeAtCells baseAfterInput
              ((false :: inputSuffixTail).map some) := by
        simpa [TmidTape, baseAfterInput,
          boolWordCanonicalHandoffConfigWithBase] using
          cellListCanonicalHandoffConfigWithBase_move_right
            (L.input.map some) baseLeft false inputSuffixTail
      rw [hraw]
      have hsuffixCells :
          (false :: inputSuffixTail).map some =
            (List.append (stageNatBits L.stage) stageSuffix).map some := by
        rw [hstageTail]
        simp [inputSuffixTail, List.map_append]
      simp [hsuffixCells]
    exact
      runConfig_reaches_from_move_eq
        (B := FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner)
        (handoffMove := Direction.right)
        hmove
        (by simpa [baseAfterInput, stageSuffix] using hstage)
  simpa [FixedDescriptionBoundedSimulatorLayoutPayloadScannerDescription_configRunner,
    TmidTape, baseAfterInput] using
      seqSubroutine_runConfig_exists
        (A := BoolWordSuffixScannerDescription)
        (B := FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner)
        (handoffMove := Direction.right)
        boolWordSuffixScannerDescription_subroutineReady
        fixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_subroutineReady_configRunner
        hArun hBReach

theorem fixedDescriptionBoundedSimulatorLayoutPayloadScannerDescription_runConfig_code_inv_configRunner
    (baseLeft : List (Option Bool)) (code : Word MachineCodeSymbol)
    {Tout : Tape Bool} {n : Nat}
    (h :
      FixedDescriptionBoundedSimulatorLayoutPayloadScannerDescription_configRunner.runConfig
          n
          (DovetailInitialLayoutInitializer.config
            FixedDescriptionBoundedSimulatorLayoutPayloadScannerDescription_configRunner.start
            baseLeft
            ((encodeCodeWordAsInput code).map some)) =
        { state :=
            FixedDescriptionBoundedSimulatorLayoutPayloadScannerDescription_configRunner.halt
          tape := Tout }) :
    exists input : Word Bool,
    exists stage : Nat,
    exists cfg : Configuration,
    exists hit : Bool,
    exists baseAfter : List (Option Bool),
      code =
        encodeBoolWordAppend input
          (encodeNatAppend stage
            (encodeConfigurationAppend cfg (encodeBoolAppend hit []))) ∧
        Tape.move Direction.right Tout =
          DovetailInitialLayoutInitializer.tapeAtCells baseAfter [] := by
  have hseq :
      (seqSubroutine
        BoolWordSuffixScannerDescription
        FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner
        Direction.right).runConfig n
          (DovetailInitialLayoutInitializer.config
            (seqSubroutine
              BoolWordSuffixScannerDescription
              FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner
              Direction.right).start
            baseLeft
            ((encodeCodeWordAsInput code).map some)) =
        { state :=
            (seqSubroutine
              BoolWordSuffixScannerDescription
              FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner
              Direction.right).halt
          tape := Tout } := by
    simpa [FixedDescriptionBoundedSimulatorLayoutPayloadScannerDescription_configRunner]
      using h
  rcases
      seqSubroutine_runConfig_inv
        (A := BoolWordSuffixScannerDescription)
        (B := FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner)
        (handoffMove := Direction.right)
        boolWordSuffixScannerDescription_subroutineReady
        fixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_subroutineReady_configRunner
        hseq with
    ⟨Tinput, hinput, hrest⟩
  rcases hinput with ⟨nInput, hinputRun, _hinputFirst⟩
  rcases
      boolWordSuffixScannerDescription_runConfig_code_inv
        baseLeft code
        (by simpa [DovetailInitialLayoutInitializer.config] using
          hinputRun) with
    ⟨input, suffix, hcodeInput⟩
  rcases
      boolWordSuffixScannerDescription_runConfig_encodeBoolWordAppend_handoff
        baseLeft input suffix
        (by
          simpa [DovetailInitialLayoutInitializer.config, hcodeInput] using
            hinputRun) with
    ⟨suffixTail, hsuffixBits, hTinput⟩
  let baseAfterInput : List (Option Bool) :=
    cellListCanonicalRestoredLeftWithBase (input.map some) baseLeft
  have hinputMove :
      Tape.move Direction.right Tinput =
        DovetailInitialLayoutInitializer.tapeAtCells baseAfterInput
          ((encodeCodeWordAsInput suffix).map some) := by
    rw [hTinput]
    have hraw :
        Tape.move Direction.right
            (boolWordCanonicalHandoffConfigWithBase input baseLeft
              (false :: suffixTail)).tape =
          DovetailInitialLayoutInitializer.tapeAtCells baseAfterInput
            ((false :: suffixTail).map some) := by
      simpa [boolWordCanonicalHandoffConfigWithBase, baseAfterInput]
        using
          cellListCanonicalHandoffConfigWithBase_move_right
            (input.map some) baseLeft false suffixTail
    rw [hraw]
    simp [hsuffixBits]
  rcases hrest with ⟨nRest, hrestRun⟩
  have hrestCodeRun :
      FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner.runConfig
          nRest
          (DovetailInitialLayoutInitializer.config
            FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner.start
            baseAfterInput
            ((encodeCodeWordAsInput suffix).map some)) =
        { state :=
            FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner.halt
          tape := Tout } := by
    simpa [DovetailInitialLayoutInitializer.config, hinputMove] using
      hrestRun
  rcases
      fixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_runConfig_code_inv_configRunner
        baseAfterInput suffix hrestCodeRun with
    ⟨stage, cfg, hit, baseAfter, hsuffixCode, hmove⟩
  refine ⟨input, stage, cfg, hit, baseAfter, ?_, hmove⟩
  rw [hcodeInput, hsuffixCode]

/--
Concrete scanner for a complete simulator-layout code word.  This chains the
fixed header-prefix block with the simulator payload scanner.
-/
def FixedDescriptionBoundedSimulatorLayoutScannerDescription_configRunner :
    MachineDescription :=
  seqSubroutine
    FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner
    FixedDescriptionBoundedSimulatorLayoutPayloadScannerDescription_configRunner
    Direction.right

theorem fixedDescriptionBoundedSimulatorLayoutScannerDescription_subroutineReady_configRunner :
    FixedDescriptionBoundedSimulatorLayoutScannerDescription_configRunner.SubroutineReady :=
  seqSubroutine_subroutineReady
    fixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_subroutineReady_configRunner
    fixedDescriptionBoundedSimulatorLayoutPayloadScannerDescription_subroutineReady_configRunner

def fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_configRunner
    (L : SimulatorLayout) (baseLeft : List (Option Bool)) : Tape Bool :=
  (boolFinalHandoffConfigWithBase L.hit
    (configurationRestoredLeftWithBase L.config
      (List.append ((stageNatBits L.stage).reverse.map some)
        (cellListCanonicalRestoredLeftWithBase (L.input.map some)
          (List.append
            (fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner.reverse.map
              some)
            baseLeft))))).tape

theorem fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_normalizedOutput_configRunner
    (L : SimulatorLayout) (baseLeft : List (Option Bool)) :
    Tape.normalizedOutput
        (fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_configRunner
          L baseLeft) =
      List.append (baseLeft.reverse.filterMap (fun cell => cell))
        (SimulatorLayout.asBoolInput L) := by
  rw [fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_configRunner]
  rw [fixedDescriptionBoundedSimulatorBoolFinalHandoffConfigWithBase_normalizedOutput_configRunner]
  rw [fixedDescriptionBoundedSimulatorConfigurationRestoredLeftWithBase_reverse_filterMap_configRunner]
  simp [List.reverse_append, List.filterMap_append, List.map_reverse,
    List.append_assoc]
  have hcellList :
      (List.filterMap (fun cell => cell)
          (cellListCanonicalRestoredLeftWithBase (L.input.map some)
            (List.append
              (fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner.map
                some).reverse
              baseLeft))).reverse =
        List.append
          ((List.append
            (fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner.map
              some).reverse
            baseLeft).reverse.filterMap (fun cell => cell))
          (cellListFieldBits (L.input.map some) []) := by
    rw [← Tape.filterMap_reverse]
    exact
      fixedDescriptionBoundedSimulatorCellListCanonicalRestoredLeftWithBase_reverse_filterMap_configRunner
        (L.input.map some)
        (List.append
          (fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner.map
            some).reverse
          baseLeft)
  rw [show
      (List.filterMap (fun cell => cell)
          (cellListCanonicalRestoredLeftWithBase (L.input.map some)
            ((fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner.map
              some).reverse ++ baseLeft))).reverse =
        List.append
          (((fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner.map
            some).reverse ++ baseLeft).reverse.filterMap
              (fun cell => cell))
          (cellListFieldBits (L.input.map some) []) by
    simpa using hcellList]
  rw [fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_header_payloadBits_configRunner]
  simp [fixedDescriptionBoundedSimulatorLayoutPayloadBits_configRunner,
    boolWordFieldBits, cellListFieldBits, boolFieldBits,
    cellFieldBits, configurationFieldBits, tapeFieldBits,
    Function.comp_def,
    List.reverse_append, List.filterMap_append,
    List.append_assoc]

theorem run_fixedDescriptionBoundedSimulatorLayoutScanner_raw_to_handoff_withBase_configRunner
    (L : SimulatorLayout) (baseLeft : List (Option Bool)) :
    exists steps : Nat,
      FixedDescriptionBoundedSimulatorLayoutScannerDescription_configRunner.runConfig
          steps
          { state :=
              FixedDescriptionBoundedSimulatorLayoutScannerDescription_configRunner.start
            tape :=
              DovetailInitialLayoutInitializer.tapeAtCells baseLeft
                ((SimulatorLayout.asBoolInput L).map some) } =
        { state :=
            FixedDescriptionBoundedSimulatorLayoutScannerDescription_configRunner.halt
          tape :=
            fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_configRunner
              L baseLeft } := by
  let payloadBits : Word Bool :=
    fixedDescriptionBoundedSimulatorLayoutPayloadBits_configRunner L
  rcases
      cellListFieldBits_cons_false (L.input.map some)
        (List.append (stageNatBits L.stage)
          (configurationFieldBits L.config (boolFieldBits L.hit []))) with
    ⟨payloadTail, hpayloadTail⟩
  rcases
      fixedDescriptionBoundedSimulatorHeaderPrefix_run_raw_to_handoff_withBase_configRunner
        baseLeft false payloadTail with
    ⟨headerSteps, hheader⟩
  let TmidTape : Tape Bool :=
    (fixedDescriptionBoundedSimulatorHeaderPrefixHandoffConfigWithBase_configRunner
      baseLeft (false :: payloadTail)).tape
  let baseAfterHeader : List (Option Bool) :=
    List.append
      (fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner.reverse.map
        some)
      baseLeft
  have hpayloadEq :
      payloadBits = false :: payloadTail := by
    simpa [payloadBits,
      fixedDescriptionBoundedSimulatorLayoutPayloadBits_configRunner,
      boolWordFieldBits] using hpayloadTail
  have hArun :
      FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner.runConfig
          headerSteps
          { state :=
              FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner.start
            tape :=
              DovetailInitialLayoutInitializer.tapeAtCells baseLeft
                ((SimulatorLayout.asBoolInput L).map some) } =
        { state :=
            FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner.halt
          tape := TmidTape } := by
    rw [fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_header_payloadBits_configRunner]
    rw [show
        fixedDescriptionBoundedSimulatorLayoutPayloadBits_configRunner L =
          false :: payloadTail by
      simpa [payloadBits] using hpayloadEq]
    simp [List.map_append]
    change
      FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner.runConfig
          headerSteps
          (DovetailInitialLayoutInitializer.config
            FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner.start
            baseLeft
            (List.append
              (fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner.map
                some)
              ((false :: payloadTail).map some))) =
        { state :=
            FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner.halt
          tape := TmidTape }
    simpa [TmidTape] using hheader
  have hBReach :
      exists nB : Nat,
        FixedDescriptionBoundedSimulatorLayoutPayloadScannerDescription_configRunner.runConfig
            nB
            { state :=
                FixedDescriptionBoundedSimulatorLayoutPayloadScannerDescription_configRunner.start
              tape := Tape.move Direction.right TmidTape } =
          { state :=
              FixedDescriptionBoundedSimulatorLayoutPayloadScannerDescription_configRunner.halt
            tape :=
              fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_configRunner
                L baseLeft } := by
    rcases
        run_fixedDescriptionBoundedSimulatorLayoutPayload_raw_to_handoff_withBase_configRunner
          L baseAfterHeader with
      ⟨payloadSteps, hpayload⟩
    have hmove :
        Tape.move Direction.right TmidTape =
          DovetailInitialLayoutInitializer.tapeAtCells baseAfterHeader
            (payloadBits.map some) := by
      have hraw :
          Tape.move Direction.right TmidTape =
            DovetailInitialLayoutInitializer.tapeAtCells baseAfterHeader
              ((false :: payloadTail).map some) := by
        simpa [TmidTape, baseAfterHeader] using
          fixedDescriptionBoundedSimulatorHeaderPrefixHandoffConfigWithBase_move_right_configRunner
            baseLeft false payloadTail
      rw [hraw]
      simp [hpayloadEq]
    exact
      runConfig_reaches_from_move_eq
        (B := FixedDescriptionBoundedSimulatorLayoutPayloadScannerDescription_configRunner)
        (handoffMove := Direction.right)
        hmove
        (by
          simpa [baseAfterHeader, payloadBits,
            fixedDescriptionBoundedSimulatorLayoutPayloadBits_configRunner,
            fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_configRunner]
            using hpayload)
  simpa [FixedDescriptionBoundedSimulatorLayoutScannerDescription_configRunner,
    TmidTape] using
      seqSubroutine_runConfig_exists
        (A := FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner)
        (B := FixedDescriptionBoundedSimulatorLayoutPayloadScannerDescription_configRunner)
        (handoffMove := Direction.right)
        fixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_subroutineReady_configRunner
        fixedDescriptionBoundedSimulatorLayoutPayloadScannerDescription_subroutineReady_configRunner
        hArun hBReach

theorem fixedDescriptionBoundedSimulatorLayoutScannerDescription_haltsWithOutput_configRunner
    (L : SimulatorLayout) :
    FixedDescriptionBoundedSimulatorLayoutScannerDescription_configRunner.HaltsWithOutput
      (SimulatorLayout.asBoolInput L)
      (SimulatorLayout.asBoolInput L) := by
  rcases
      run_fixedDescriptionBoundedSimulatorLayoutScanner_raw_to_handoff_withBase_configRunner
        L [] with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  constructor
  · simpa [MachineDescription.HaltsWithOutputIn,
      MachineDescription.initial,
      DovetailInitialLayoutInitializer.tapeAtCells,
      Tape.input] using congrArg Configuration.state hsteps
  · have htape :
        (FixedDescriptionBoundedSimulatorLayoutScannerDescription_configRunner.runConfig
            steps
            (FixedDescriptionBoundedSimulatorLayoutScannerDescription_configRunner.initial
              (SimulatorLayout.asBoolInput L))).tape =
          fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_configRunner
            L [] := by
      simpa [MachineDescription.initial,
        DovetailInitialLayoutInitializer.tapeAtCells,
        Tape.input] using congrArg Configuration.tape hsteps
    rw [htape]
    simpa using
      fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_normalizedOutput_configRunner
        L []

namespace FixedDescriptionBoundedSimulator

namespace LayoutScannerRestoredLeft

theorem eq_asBoolInput_reverse_map_some_configRunner
    (L : SimulatorLayout) :
    List.append ((cellCodeBits (some L.hit)).reverse.map some)
      (configurationRestoredLeftWithBase L.config
        (List.append ((stageNatBits L.stage).reverse.map some)
          (cellListCanonicalRestoredLeftWithBase (L.input.map some)
            (fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner.reverse.map
              some)))) =
      (SimulatorLayout.asBoolInput L).reverse.map some := by
  have hinput :
      cellListCanonicalRestoredLeftWithBase (L.input.map some)
          (fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner.reverse.map
            some) =
        List.append
          ((cellListCanonicalRestoredBitsRev (L.input.map some)).map some)
          (fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner.reverse.map
            some) := by
    exact
      (cellListCanonicalRestoredBitsRev_map_some_withBase
        (L.input.map some)
        (fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner.reverse.map
          some)).symm
  rw [hinput]
  have hconfig :
      configurationRestoredLeftWithBase L.config
        (List.append ((stageNatBits L.stage).reverse.map some)
          (List.append
            ((cellListCanonicalRestoredBitsRev (L.input.map some)).map some)
            (fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner.reverse.map
              some))) =
        List.append ((configurationRestoredBitsRev L.config).map some)
          (List.append ((stageNatBits L.stage).reverse.map some)
            (List.append
              ((cellListCanonicalRestoredBitsRev (L.input.map some)).map some)
              (fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner.reverse.map
                some))) := by
    exact
      (configurationRestoredBitsRev_map_some_withBase L.config _).symm
  rw [hconfig]
  have hinputBits :
      (cellListCanonicalRestoredBitsRev (L.input.map some)).map some =
        (cellListFieldBits (L.input.map some) []).reverse.map some := by
    have h :=
      congrArg (fun xs : Word Bool => xs.reverse.map some)
        (cellListCanonicalRestoredBitsRev_reverse (L.input.map some))
    simpa using h
  have hconfigBits :
      (configurationRestoredBitsRev L.config).map some =
        (configurationFieldBits L.config []).reverse.map some := by
    have h :=
      congrArg (fun xs : Word Bool => xs.reverse.map some)
        (configurationRestoredBitsRev_reverse L.config)
    simpa using h
  rw [hinputBits, hconfigBits]
  simp [SimulatorLayout.asBoolInput, SimulatorLayout.encode,
    SimulatorLayout.encodeAppend,
    fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner,
    boolWordBits_eq_encodeBoolWordAppend,
    natBits_eq_encodeNatAppend,
    configurationFieldBits_eq_encodeConfigurationAppend,
    boolBits_eq_encodeBoolAppend,
    cellListFieldBits, cellFieldBits, configurationFieldBits,
    tapeFieldBits, encodeCodeWordAsInput, List.append_assoc,
    List.map_append, List.reverse_append]

end LayoutScannerRestoredLeft

end FixedDescriptionBoundedSimulator

theorem fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_move_right_eq_terminal_configRunner
    (L : SimulatorLayout) :
    Tape.move Direction.right
        (fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_configRunner
          L []) =
      DovetailInitialLayoutInitializer.tapeAtCells
        ((SimulatorLayout.asBoolInput L).reverse.map some) [] := by
  rw [fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_configRunner]
  rw [boolFinalHandoffConfigWithBase_move_right]
  exact
    by
      simpa using
        congrArg
          (fun left =>
            DovetailInitialLayoutInitializer.tapeAtCells left [])
          (FixedDescriptionBoundedSimulator.LayoutScannerRestoredLeft.eq_asBoolInput_reverse_map_some_configRunner
            L)

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC

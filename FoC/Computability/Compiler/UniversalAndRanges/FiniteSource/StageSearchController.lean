import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.DecodedBoundedSimulator

set_option doc.verso true

/-!
# Finite-Source Stage Search Controller

This module factors the stage-search controller into a semantic staged program,
a bounded-budget checker obligation, and an unbounded search sequencing
obligation.  The final public construction remains a thin adapter from those
two finite-machine leaves.
-/

namespace FoC
namespace Computability

open Languages

universe uStage uDescription uSimulator

/-- Finite-machine construction target for the full stage-search controller. -/
def CodePrefixStageSearchControllerCoreConstruction : Prop :=
  forall {simulatorState : Type}
    (simulator : TuringMachine MachineCodeSymbol simulatorState),
    CodePrefixDecodedBoundedSimulatorSpec simulator ->
      exists searcherState : Type,
      exists searcher : TuringMachine MachineCodeSymbol searcherState,
        CodePrefixStageSearchControllerSpec simulator searcher

/--
Semantic reference program for the stage-search controller.  At stage
{lit}`stage`, it checks all simulator stage/fuel pairs bounded by
{lit}`stage`.
-/
noncomputable def codePrefixStageSearchControllerProgram
    (simulator : TuringMachine MachineCodeSymbol simulatorState) :
    StagedProgram MachineCodeSymbol Unit :=
  by
    classical
    exact
      { run := fun encoded stage =>
          if exists D : MachineDescription,
             exists input : Word MachineCodeSymbol,
             exists checkedStage : Nat,
             exists fuel : Nat,
              checkedStage ≤ stage ∧
                fuel ≤ stage ∧
              MachineDescription.decodeDescriptionPrefix encoded =
                  some (D, input) ∧
                TuringMachine.HaltsOnInputIn simulator fuel
                  (CodePrefixRecognizerStageCode encoded checkedStage) then
            some []
          else
            none }

theorem codePrefixStageSearchControllerProgram_accepts
    (simulator : TuringMachine MachineCodeSymbol simulatorState)
    (encoded : Word MachineCodeSymbol) :
    ProgramHaltsWithOutput
        (codePrefixStageSearchControllerProgram simulator) encoded [] <->
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
      exists stage : Nat,
        MachineDescription.decodeDescriptionPrefix encoded =
            some (D, input) ∧
          TuringMachine.HaltsOnInput simulator
            (CodePrefixRecognizerStageCode encoded stage) := by
  classical
  constructor
  · intro h
    rcases h with ⟨budget, hbudget⟩
    simp [codePrefixStageSearchControllerProgram] at hbudget
    rcases hbudget with
      ⟨D, input, stage, fuel, _hstage, _hfuel, hdecode, hsim⟩
    exact
      ⟨D, input, stage, hdecode,
        TuringMachine.halts_on_input_in_to_halts_on_input hsim⟩
  · intro h
    rcases h with ⟨D, input, stage, hdecode, hsim⟩
    rcases TuringMachine.halts_on_input_to_halts_on_input_in hsim with
      ⟨fuel, hsimFuel⟩
    refine ⟨stage + fuel, ?_⟩
    have hstageLe : stage ≤ stage + fuel := by
      omega
    have hfuelLe : fuel ≤ stage + fuel := by
      omega
    simp [codePrefixStageSearchControllerProgram, hdecode]
    exact
      ⟨D, input, stage, hstageLe, fuel, hfuelLe, rfl, rfl, hsimFuel⟩

theorem codePrefixStageSearchControllerProgram_accepts_of_simulatorSpec
    (simulator : TuringMachine MachineCodeSymbol simulatorState)
    (hsimulator : CodePrefixDecodedBoundedSimulatorSpec simulator)
    (encoded : Word MachineCodeSymbol) :
    ProgramHaltsWithOutput
        (codePrefixStageSearchControllerProgram simulator) encoded [] <->
      CodePrefixDecodedStageSearchAccepts encoded := by
  rw [codePrefixStageSearchControllerProgram_accepts]
  constructor
  · intro h
    rcases h with ⟨D, input, stage, hdecode, hsim⟩
    exact
      ⟨D, input, stage, hdecode,
        (hsimulator encoded D input stage hdecode).mp hsim⟩
  · intro h
    rcases h with ⟨D, input, stage, hdecode, hhalts⟩
    exact
      ⟨D, input, stage, hdecode,
        (hsimulator encoded D input stage hdecode).mpr hhalts⟩

theorem codePrefixStageSearchControllerProgram_accepts_recognizerProgram
    (simulator : TuringMachine MachineCodeSymbol simulatorState)
    (hsimulator : CodePrefixDecodedBoundedSimulatorSpec simulator)
    (encoded : Word MachineCodeSymbol) :
    ProgramHaltsWithOutput
        (codePrefixStageSearchControllerProgram simulator) encoded [] <->
      ProgramHaltsWithOutput CodePrefixRecognizerProgram encoded [] :=
  Iff.trans
    (codePrefixStageSearchControllerProgram_accepts_of_simulatorSpec
      simulator hsimulator encoded)
    (codePrefixDecodedStageSearchAccepts_iff_programHalts encoded)

def CodePrefixStageSearchControllerProgramCompilerConstruction : Prop :=
  forall {simulatorState : Type}
    (simulator : TuringMachine MachineCodeSymbol simulatorState),
      exists searcherState : Type,
      exists searcher : TuringMachine MachineCodeSymbol searcherState,
        forall encoded : Word MachineCodeSymbol,
          TuringMachine.HaltsOnInput searcher encoded <->
            ProgramHaltsWithOutput
              (codePrefixStageSearchControllerProgram simulator) encoded []

/--
Specification for the bounded checker: on a stage-coded input, it halts exactly
when the semantic controller program accepts within that same budget.
-/
def CodePrefixStageSearchControllerBudgetCheckerSpec
    {simulatorState checkerState : Type}
    (simulator : TuringMachine MachineCodeSymbol simulatorState)
    (checker : TuringMachine MachineCodeSymbol checkerState) : Prop :=
  forall encoded : Word MachineCodeSymbol,
  forall budget : Nat,
    TuringMachine.HaltsOnInput checker
        (CodePrefixRecognizerStageCode encoded budget) <->
      (codePrefixStageSearchControllerProgram simulator).run
          encoded budget = some []

def CodePrefixStageSearchControllerBudgetCheckerConstruction
    {simulatorState : Type}
    (simulator : TuringMachine MachineCodeSymbol simulatorState) : Prop :=
  exists checkerState : Type,
  exists checker : TuringMachine MachineCodeSymbol checkerState,
    CodePrefixStageSearchControllerBudgetCheckerSpec simulator checker

/--
Sequencing obligation that turns a bounded checker into an unbounded searcher
over budgets for one encoded input.
-/
def CodePrefixStageSearchControllerBudgetSearchSequencingConstruction :
    Prop :=
  forall {simulatorState checkerState : Type}
    (simulator : TuringMachine MachineCodeSymbol simulatorState)
    (checker : TuringMachine MachineCodeSymbol checkerState),
    CodePrefixStageSearchControllerBudgetCheckerSpec simulator checker ->
      exists searcherState : Type,
      exists searcher : TuringMachine MachineCodeSymbol searcherState,
        forall encoded : Word MachineCodeSymbol,
          TuringMachine.HaltsOnInput searcher encoded <->
            ProgramHaltsWithOutput
              (codePrefixStageSearchControllerProgram simulator) encoded []

theorem codePrefixStageSearchControllerProgramCompilerConstruction_of_components
    (hchecker :
      forall {simulatorState : Type}
        (simulator : TuringMachine MachineCodeSymbol simulatorState),
          CodePrefixStageSearchControllerBudgetCheckerConstruction simulator)
    (hsequence :
      CodePrefixStageSearchControllerBudgetSearchSequencingConstruction) :
    CodePrefixStageSearchControllerProgramCompilerConstruction := by
  intro simulatorState simulator
  rcases hchecker simulator with ⟨checkerState, checker, hcheckerSpec⟩
  exact hsequence simulator checker hcheckerSpec

theorem codePrefixStageSearchControllerCoreConstruction_of_programCompiler
    (hcompile : CodePrefixStageSearchControllerProgramCompilerConstruction) :
    CodePrefixStageSearchControllerCoreConstruction := by
  intro simulatorState simulator _hsimulator
  rcases hcompile simulator with ⟨searcherState, searcher, hsearcher⟩
  refine ⟨searcherState, searcher, ?_⟩
  intro encoded
  exact Iff.trans (hsearcher encoded)
    (codePrefixStageSearchControllerProgram_accepts simulator encoded)

/-!
**Stage-search driver core.**  This is the unbounded dovetailing leaf: given a
bounded decoded simulator, build a searcher that enumerates stage bounds for a
fixed encoded input and halts when the simulator accepts one stage code.
-/

theorem codePrefixStageSearchControllerProgram_run_eq_some_iff
    (simulator : TuringMachine MachineCodeSymbol simulatorState)
    (encoded : Word MachineCodeSymbol) (budget : Nat) :
    (codePrefixStageSearchControllerProgram simulator).run encoded budget =
        some [] <->
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
      exists checkedStage : Nat,
      exists fuel : Nat,
        checkedStage ≤ budget ∧
          fuel ≤ budget ∧
          MachineDescription.decodeDescriptionPrefix encoded =
            some (D, input) ∧
          TuringMachine.HaltsOnInputIn simulator fuel
            (CodePrefixRecognizerStageCode encoded checkedStage) := by
  classical
  by_cases h :
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
      exists checkedStage : Nat,
        checkedStage ≤ budget ∧
          exists fuel : Nat,
            fuel ≤ budget ∧
              MachineDescription.decodeDescriptionPrefix encoded =
                some (D, input) ∧
              TuringMachine.HaltsOnInputIn simulator fuel
                (CodePrefixRecognizerStageCode encoded checkedStage)
  · simp [codePrefixStageSearchControllerProgram, h]
    rfl
  · simp [codePrefixStageSearchControllerProgram, h]

/--
Finite-machine obligation for the bounded checker.  The checker must parse a
budget-coded input, enumerate all stage/fuel pairs bounded by that budget, and
simulate the supplied fixed simulator on the rebuilt stage-coded input.
-/
def CodePrefixStageSearchControllerBudgetCheckerFiniteMachineObligation
    (simulator : TuringMachine MachineCodeSymbol simulatorState) : Prop :=
  exists checkerState : Type,
  exists checker : TuringMachine MachineCodeSymbol checkerState,
    forall encoded : Word MachineCodeSymbol,
    forall budget : Nat,
      TuringMachine.HaltsOnInput checker
          (CodePrefixRecognizerStageCode encoded budget) <->
        exists D : MachineDescription,
        exists input : Word MachineCodeSymbol,
        exists checkedStage : Nat,
        exists fuel : Nat,
          checkedStage ≤ budget ∧
            fuel ≤ budget ∧
            MachineDescription.decodeDescriptionPrefix encoded =
              some (D, input) ∧
            TuringMachine.HaltsOnInputIn simulator fuel
              (CodePrefixRecognizerStageCode encoded checkedStage)

/--
Finite sequencing target for the bounded checker once the reusable stage-code
and description-prefix decoders have been supplied.  The remaining concrete
machine obligation is to combine those decoders with a bounded enumeration of
{lit}`(checkedStage, fuel)` pairs and a fixed-simulator bounded run.
-/
def CodePrefixStageSearchControllerBudgetCheckerSequencingConstruction :
    Prop :=
  forall {stageState : Type uStage}
    {descriptionState : Type uDescription}
    {simulatorState : Type uSimulator}
    (stageDecoder : TuringMachine MachineCodeSymbol stageState)
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState)
    (simulator : TuringMachine MachineCodeSymbol simulatorState),
    (forall tokens : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput stageDecoder tokens <->
        exists stage : Nat,
        exists encoded : Word MachineCodeSymbol,
          tokens = CodePrefixRecognizerStageCode encoded stage) ->
    (forall encoded : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput descriptionDecoder encoded <->
        exists D : MachineDescription,
        exists input : Word MachineCodeSymbol,
          MachineDescription.decodeDescriptionPrefix encoded =
            some (D, input)) ->
      CodePrefixStageSearchControllerBudgetCheckerFiniteMachineObligation
        simulator

/--
Finite-machine leaf for the actual bounded checker once the description
decoder has been supplied.  The concrete machine must recover the budget from
the stage-coded input, run the description decoder on the payload, enumerate
bounded {lit}`(checkedStage, fuel)` pairs, rebuild the checked stage-coded
input, and run the fixed simulator for the selected fuel.
-/
def CodePrefixStageSearchControllerBudgetCheckerDriverFiniteMachineObligation
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState)
    (simulator : TuringMachine MachineCodeSymbol simulatorState) : Prop :=
  exists checkerState : Type,
  exists checker : TuringMachine MachineCodeSymbol checkerState,
    forall encoded : Word MachineCodeSymbol,
    forall budget : Nat,
      TuringMachine.HaltsOnInput checker
          (CodePrefixRecognizerStageCode encoded budget) <->
        TuringMachine.HaltsOnInput descriptionDecoder encoded ∧
          exists checkedStage : Nat,
          exists fuel : Nat,
            checkedStage ≤ budget ∧
              fuel ≤ budget ∧
              TuringMachine.HaltsOnInputIn simulator fuel
                (CodePrefixRecognizerStageCode encoded checkedStage)

/--
Concrete sub-obligation for the first phase of the bounded checker driver:
recover the payload from a budget-coded input and run the supplied description
decoder on that payload.
-/
def CodePrefixStageSearchControllerBudgetCheckerDescriptionRunnerObligation
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState) :
    Prop :=
  exists runnerState : Type,
  exists runner : TuringMachine MachineCodeSymbol runnerState,
    forall encoded : Word MachineCodeSymbol,
    forall budget : Nat,
      TuringMachine.HaltsOnInput runner
          (CodePrefixRecognizerStageCode encoded budget) <->
        TuringMachine.HaltsOnInput descriptionDecoder encoded

/--
Concrete sub-obligation for the bounded simulator phase: on a budget-coded
input, enumerate bounded {lit}`(checkedStage, fuel)` pairs, rebuild each
checked stage code, and run the fixed simulator for the selected fuel.
-/
def CodePrefixStageSearchControllerBudgetCheckerBoundedSimulatorRunnerObligation
    (simulator : TuringMachine MachineCodeSymbol simulatorState) : Prop :=
  exists runnerState : Type,
  exists runner : TuringMachine MachineCodeSymbol runnerState,
    forall encoded : Word MachineCodeSymbol,
    forall budget : Nat,
      TuringMachine.HaltsOnInput runner
          (CodePrefixRecognizerStageCode encoded budget) <->
        exists checkedStage : Nat,
        exists fuel : Nat,
          checkedStage ≤ budget ∧
            fuel ≤ budget ∧
            TuringMachine.HaltsOnInputIn simulator fuel
              (CodePrefixRecognizerStageCode encoded checkedStage)

/--
Concrete sub-obligation for sequencing two recognizers on the same input by
finite dovetailing, halting exactly when both supplied recognizers halt.
-/
def CodePrefixStageSearchControllerBudgetCheckerIntersectionObligation :
    Prop :=
  forall {leftState rightState : Type}
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState),
      exists bothState : Type,
      exists both : TuringMachine MachineCodeSymbol bothState,
        forall input : Word MachineCodeSymbol,
          TuringMachine.HaltsOnInput both input <->
            TuringMachine.HaltsOnInput left input ∧
              TuringMachine.HaltsOnInput right input

/--
Raw finite-machine target for the bounded simulator loop.  This version states
the contract on arbitrary inputs after decoding the outer stage-code prefix;
the public budget-coded theorem below is the canonical-input adapter.
-/
def CodePrefixStageSearchControllerBudgetCheckerBoundedSimulatorRawLoopObligation
    (simulator : TuringMachine MachineCodeSymbol simulatorState) : Prop :=
  exists runnerState : Type,
  exists runner : TuringMachine MachineCodeSymbol runnerState,
    forall tokens : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput runner tokens <->
        exists budget : Nat,
        exists encoded : Word MachineCodeSymbol,
        exists checkedStage : Nat,
        exists fuel : Nat,
          tokens = CodePrefixRecognizerStageCode encoded budget ∧
            checkedStage ≤ budget ∧
            fuel ≤ budget ∧
            TuringMachine.HaltsOnInputIn simulator fuel
              (CodePrefixRecognizerStageCode encoded checkedStage)

/--
The same bounded simulator loop obligation stated against the primitive
{name}`MachineDescription.decodeNat` result.  This isolates the finite
transition-table work from the public stage-code normal form.
-/
def CodePrefixStageSearchControllerBudgetCheckerBoundedSimulatorRawLoopDecodeNatObligation
    (simulator : TuringMachine MachineCodeSymbol simulatorState) : Prop :=
  exists runnerState : Type,
  exists runner : TuringMachine MachineCodeSymbol runnerState,
    forall tokens : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput runner tokens <->
        exists budget : Nat,
        exists encoded : Word MachineCodeSymbol,
        exists checkedStage : Nat,
        exists fuel : Nat,
          MachineDescription.decodeNat tokens = some (budget, encoded) ∧
            checkedStage ≤ budget ∧
            fuel ≤ budget ∧
            TuringMachine.HaltsOnInputIn simulator fuel
              (CodePrefixRecognizerStageCode encoded checkedStage)

/--
Canonical finite-machine construction target for the bounded simulator loop.
This is the transition-table work after the input has been exposed as a
canonical stage-code word.  The decodeNat theorem below is only the parser
adapter from this raw loop.
-/
def CodePrefixStageSearchControllerBudgetCheckerBoundedSimulatorCanonicalRawLoopObligation
    (simulator : TuringMachine MachineCodeSymbol simulatorState) : Prop :=
  exists runnerState : Type,
  exists runner : TuringMachine MachineCodeSymbol runnerState,
    forall tokens : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput runner tokens <->
        exists budget : Nat,
        exists encoded : Word MachineCodeSymbol,
        exists checkedStage : Nat,
        exists fuel : Nat,
          tokens = CodePrefixRecognizerStageCode encoded budget ∧
            checkedStage ≤ budget ∧
            fuel ≤ budget ∧
            TuringMachine.HaltsOnInputIn simulator fuel
              (CodePrefixRecognizerStageCode encoded checkedStage)

/--
Finite-machine leaf for the canonical bounded simulator loop.  The machine
starts from an already stage-coded budget input, enumerates bounded
{lit}`(checkedStage, fuel)` pairs, rebuilds each checked stage-code input, and
runs the supplied simulator for the selected fuel.
-/
theorem codePrefixStageSearchControllerBudgetCheckerBoundedSimulatorCanonicalRawLoopFiniteLeaf
    (simulator : TuringMachine MachineCodeSymbol simulatorState) :
    CodePrefixStageSearchControllerBudgetCheckerBoundedSimulatorCanonicalRawLoopObligation
      simulator := by
  sorry

/--
Adapter from the canonical bounded simulator loop to the
{name}`MachineDescription.decodeNat` contract.  The transition-table work lives
in {name}`codePrefixStageSearchControllerBudgetCheckerBoundedSimulatorCanonicalRawLoopFiniteLeaf`;
this theorem only exposes the parsed budget and payload.
-/
theorem codePrefixStageSearchControllerBudgetCheckerBoundedSimulatorDecodeNatFiniteLeaf
    (simulator : TuringMachine MachineCodeSymbol simulatorState) :
    CodePrefixStageSearchControllerBudgetCheckerBoundedSimulatorRawLoopDecodeNatObligation
      simulator := by
  rcases
      codePrefixStageSearchControllerBudgetCheckerBoundedSimulatorCanonicalRawLoopFiniteLeaf
        simulator with
    ⟨runnerState, runner, hrunner⟩
  refine ⟨runnerState, runner, ?_⟩
  intro tokens
  constructor
  · intro hhalt
    rcases (hrunner tokens).mp hhalt with
      ⟨budget, encoded, checkedStage, fuel, htokens,
        hcheckedStage, hfuel, hsimulator⟩
    exact
      ⟨budget, encoded, checkedStage, fuel,
        by
          rw [htokens]
          exact codePrefixRecognizerStageCode_decodeNat encoded budget,
        hcheckedStage, hfuel, hsimulator⟩
  · intro htarget
    rcases htarget with
      ⟨budget, encoded, checkedStage, fuel, hdecode,
        hcheckedStage, hfuel, hsimulator⟩
    exact (hrunner tokens).mpr
      ⟨budget, encoded, checkedStage, fuel,
        codePrefixRecognizerStageCode_eq_of_decodeNat hdecode,
        hcheckedStage, hfuel, hsimulator⟩

/-- Canonical bounded-loop construction, exposed under the core name. -/
theorem codePrefixStageSearchControllerBudgetCheckerBoundedSimulatorCanonicalRawLoopObligation_core
    (simulator : TuringMachine MachineCodeSymbol simulatorState) :
    CodePrefixStageSearchControllerBudgetCheckerBoundedSimulatorCanonicalRawLoopObligation
      simulator := by
  exact
    codePrefixStageSearchControllerBudgetCheckerBoundedSimulatorCanonicalRawLoopFiniteLeaf
      simulator

/--
Concrete transition-table obligation for the bounded simulator loop after the
outer stage-code parser has been exposed as a
{name}`MachineDescription.decodeNat` contract.
-/
theorem codePrefixStageSearchControllerBudgetCheckerBoundedSimulatorRawLoopDecodeNatObligation_core
    (simulator : TuringMachine MachineCodeSymbol simulatorState) :
    CodePrefixStageSearchControllerBudgetCheckerBoundedSimulatorRawLoopDecodeNatObligation
      simulator := by
  exact
    codePrefixStageSearchControllerBudgetCheckerBoundedSimulatorDecodeNatFiniteLeaf
      simulator

/--
Concrete transition-table obligation for the bounded simulator loop.  It must
parse the outer budget code, enumerate bounded {lit}`(checkedStage, fuel)`
pairs, rebuild the checked stage-code input, and run the fixed simulator for
the selected fuel.
-/
theorem codePrefixStageSearchControllerBudgetCheckerBoundedSimulatorRawLoopObligation_core
    (simulator : TuringMachine MachineCodeSymbol simulatorState) :
    CodePrefixStageSearchControllerBudgetCheckerBoundedSimulatorRawLoopObligation
      simulator := by
  rcases
      codePrefixStageSearchControllerBudgetCheckerBoundedSimulatorRawLoopDecodeNatObligation_core
        simulator with
    ⟨runnerState, runner, hrunner⟩
  refine ⟨runnerState, runner, ?_⟩
  intro tokens
  constructor
  · intro hhalt
    rcases (hrunner tokens).mp hhalt with
      ⟨budget, encoded, checkedStage, fuel, hdecode,
        hcheckedStage, hfuel, hsimulator⟩
    exact
      ⟨budget, encoded, checkedStage, fuel,
        codePrefixRecognizerStageCode_eq_of_decodeNat hdecode,
        hcheckedStage, hfuel, hsimulator⟩
  · intro htarget
    rcases htarget with
      ⟨budget, encoded, checkedStage, fuel, htokens,
        hcheckedStage, hfuel, hsimulator⟩
    exact (hrunner tokens).mpr
      ⟨budget, encoded, checkedStage, fuel,
        by
          rw [htokens]
          exact codePrefixRecognizerStageCode_decodeNat encoded budget,
        hcheckedStage, hfuel, hsimulator⟩

theorem codePrefixRecognizerStageCode_injective
    {encoded1 encoded2 : Word MachineCodeSymbol}
    {stage1 stage2 : Nat}
    (h :
      CodePrefixRecognizerStageCode encoded1 stage1 =
        CodePrefixRecognizerStageCode encoded2 stage2) :
    stage1 = stage2 ∧ encoded1 = encoded2 := by
  have hdecode := congrArg MachineDescription.decodeNat h
  simp [CodePrefixRecognizerStageCode,
    MachineDescription.decodeNat_encodeNatAppend] at hdecode
  exact ⟨hdecode.left, hdecode.right⟩

inductive BudgetCheckerDescriptionRunnerState
    (descriptionState : Type uDescription) where
  | scan : BudgetCheckerDescriptionRunnerState descriptionState
  | run : descriptionState ->
      BudgetCheckerDescriptionRunnerState descriptionState

namespace BudgetCheckerDescriptionRunnerState

def finite (hdescription : Foundation.FiniteType descriptionState) :
    Foundation.FiniteType
      (BudgetCheckerDescriptionRunnerState descriptionState) where
  elems := scan :: hdescription.elems.map run
  complete := by
    intro state
    cases state with
    | scan =>
        simp
    | run state =>
        simp
        exact hdescription.complete state

end BudgetCheckerDescriptionRunnerState

def budgetCheckerDescriptionRunnerTape
    (blankPrefix : Nat) (rest : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  match rest with
  | [] =>
      { left := List.replicate blankPrefix none
        head := none
        right := [] }
  | symbol :: suffix =>
      { left := List.replicate blankPrefix none
        head := some symbol
        right := suffix.map some }

theorem budgetCheckerDescriptionRunnerTape_nil_eq_input
    (tokens : Word MachineCodeSymbol) :
    budgetCheckerDescriptionRunnerTape 0 tokens = Tape.input tokens := by
  cases tokens <;> rfl

theorem budgetCheckerDescriptionRunnerTape_move_right
    (blankPrefix : Nat) (symbol : MachineCodeSymbol)
    (suffix : Word MachineCodeSymbol) :
    Tape.move Direction.right
        (Tape.write none
          (budgetCheckerDescriptionRunnerTape blankPrefix
            (symbol :: suffix))) =
      budgetCheckerDescriptionRunnerTape (blankPrefix + 1) suffix := by
  cases suffix <;>
    simp [budgetCheckerDescriptionRunnerTape, Tape.move,
      Tape.moveRight, Tape.write]
  all_goals
    rw [List.replicate_succ]

def budgetCheckerDescriptionRunnerMachine
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState) :
    TuringMachine MachineCodeSymbol
      (BudgetCheckerDescriptionRunnerState descriptionState) where
  start := BudgetCheckerDescriptionRunnerState.scan
  halt := BudgetCheckerDescriptionRunnerState.run descriptionDecoder.halt
  transition := fun state cell =>
    match state with
    | BudgetCheckerDescriptionRunnerState.scan =>
        match cell with
        | some MachineCodeSymbol.tick =>
            some (none, Direction.right,
              BudgetCheckerDescriptionRunnerState.scan)
        | some MachineCodeSymbol.done =>
            some (none, Direction.right,
              BudgetCheckerDescriptionRunnerState.run
                descriptionDecoder.start)
        | _ => none
    | BudgetCheckerDescriptionRunnerState.run state =>
        match descriptionDecoder.transition state cell with
        | none => none
        | some (write, dir, nextState) =>
            some (write, dir,
              BudgetCheckerDescriptionRunnerState.run nextState)
  statesFinite :=
    BudgetCheckerDescriptionRunnerState.finite
      descriptionDecoder.statesFinite

theorem budgetCheckerDescriptionRunnerMachine_step_tick
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState)
    (blankPrefix : Nat) (suffix : Word MachineCodeSymbol) :
    TuringMachine.Step
      (budgetCheckerDescriptionRunnerMachine descriptionDecoder)
      { state := BudgetCheckerDescriptionRunnerState.scan
        tape :=
          budgetCheckerDescriptionRunnerTape blankPrefix
            (MachineCodeSymbol.tick :: suffix) }
      { state := BudgetCheckerDescriptionRunnerState.scan
        tape :=
          budgetCheckerDescriptionRunnerTape (blankPrefix + 1) suffix } := by
  rw [← budgetCheckerDescriptionRunnerTape_move_right
    blankPrefix MachineCodeSymbol.tick suffix]
  exact TuringMachine.Step.mk (by
    simp [budgetCheckerDescriptionRunnerMachine,
      budgetCheckerDescriptionRunnerTape, Tape.read])

theorem budgetCheckerDescriptionRunnerMachine_step_done
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState)
    (blankPrefix : Nat) (suffix : Word MachineCodeSymbol) :
    TuringMachine.Step
      (budgetCheckerDescriptionRunnerMachine descriptionDecoder)
      { state := BudgetCheckerDescriptionRunnerState.scan
        tape :=
          budgetCheckerDescriptionRunnerTape blankPrefix
            (MachineCodeSymbol.done :: suffix) }
      { state :=
          BudgetCheckerDescriptionRunnerState.run descriptionDecoder.start
        tape :=
          budgetCheckerDescriptionRunnerTape (blankPrefix + 1) suffix } := by
  rw [← budgetCheckerDescriptionRunnerTape_move_right
    blankPrefix MachineCodeSymbol.done suffix]
  exact TuringMachine.Step.mk (by
    simp [budgetCheckerDescriptionRunnerMachine,
      budgetCheckerDescriptionRunnerTape, Tape.read])

theorem budgetCheckerDescriptionRunnerMachine_step_run
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState)
    {state nextState : descriptionState}
    {tape : Tape MachineCodeSymbol} {write : Option MachineCodeSymbol}
    {dir : Direction}
    (haction :
      descriptionDecoder.transition state (Tape.read tape) =
        some (write, dir, nextState)) :
    TuringMachine.Step
      (budgetCheckerDescriptionRunnerMachine descriptionDecoder)
      { state := BudgetCheckerDescriptionRunnerState.run state
        tape := tape }
      { state := BudgetCheckerDescriptionRunnerState.run nextState
        tape := Tape.move dir (Tape.write write tape) } := by
  exact TuringMachine.Step.mk (by
    simp [budgetCheckerDescriptionRunnerMachine, haction])

theorem dropTrailingNone_replicate_none
    (n : Nat) :
    Tape.dropTrailingNone
        (List.replicate n (none : Option MachineCodeSymbol)) = [] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [List.replicate, Tape.dropTrailingNone, ih]

theorem budgetCheckerDescriptionRunnerTape_equiv_input
    (blankPrefix : Nat) (encoded : Word MachineCodeSymbol) :
    Tape.Equiv
      (budgetCheckerDescriptionRunnerTape blankPrefix encoded)
      (Tape.input encoded) := by
  cases encoded with
  | nil =>
      constructor
      · exact dropTrailingNone_replicate_none blankPrefix
      · constructor <;> rfl
  | cons symbol suffix =>
      constructor
      · exact dropTrailingNone_replicate_none blankPrefix
      · constructor <;> rfl

theorem turingMachine_step_of_tape_equiv
    {M : TuringMachine symbol state}
    {c d : TuringMachine.Configuration symbol state}
    {tape : Tape symbol}
    (hstep : TuringMachine.Step M c d)
    (htape : Tape.Equiv c.tape tape) :
    exists nextTape : Tape symbol,
      TuringMachine.Step M
        { state := c.state, tape := tape }
        { state := d.state, tape := nextTape } ∧
        Tape.Equiv d.tape nextTape := by
  cases hstep with
  | mk haction =>
      rename_i write dir nextState
      refine
        ⟨Tape.move dir (Tape.write write tape), ?_, ?_⟩
      · exact TuringMachine.Step.mk (by
          rw [← Tape.Equiv.read_eq htape]
          exact haction)
      · exact Tape.Equiv.move (Tape.Equiv.write htape write) dir

theorem turingMachine_computes_of_tape_equiv
    {M : TuringMachine symbol state}
    {c e : TuringMachine.Configuration symbol state}
    {tape : Tape symbol}
    (hcomp : TuringMachine.Computes M c e)
    (htape : Tape.Equiv c.tape tape) :
    exists e' : TuringMachine.Configuration symbol state,
      TuringMachine.Computes M { state := c.state, tape := tape } e' ∧
        e'.state = e.state ∧
        Tape.Equiv e.tape e'.tape := by
  induction hcomp generalizing tape with
  | refl c =>
      exact
        ⟨{ state := c.state, tape := tape },
          TuringMachine.Computes.refl _, rfl, htape⟩
  | step hstep hrest ih =>
      rcases turingMachine_step_of_tape_equiv hstep htape with
        ⟨nextTape, hstep', htape'⟩
      rcases ih htape' with ⟨e', hcomp', hstate'', htape''⟩
      exact
        ⟨e', TuringMachine.Computes.step hstep' hcomp',
          hstate'', htape''⟩

theorem turingMachine_haltsFrom_of_tape_equiv
    {M : TuringMachine symbol state}
    {state : state} {tape tape' : Tape symbol}
    (htape : Tape.Equiv tape tape')
    (hhalt : TuringMachine.HaltsFrom M { state := state, tape := tape }) :
    TuringMachine.HaltsFrom M { state := state, tape := tape' } := by
  rcases hhalt with ⟨final, hcomp, hfinal⟩
  rcases turingMachine_computes_of_tape_equiv hcomp htape with
    ⟨final', hcomp', hstate, _htape'⟩
  exact ⟨final', hcomp', by simpa [TuringMachine.Halted, hstate] using hfinal⟩

theorem turingMachine_haltsFrom_tape_equiv_iff
    (M : TuringMachine symbol state)
    (state : state) {tape tape' : Tape symbol}
    (htape : Tape.Equiv tape tape') :
    TuringMachine.HaltsFrom M { state := state, tape := tape } <->
      TuringMachine.HaltsFrom M { state := state, tape := tape' } := by
  constructor
  · exact turingMachine_haltsFrom_of_tape_equiv htape
  · exact turingMachine_haltsFrom_of_tape_equiv (Tape.Equiv.symm htape)

theorem budgetCheckerDescriptionRunnerMachine_computes_run
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState)
    {c d : TuringMachine.Configuration MachineCodeSymbol descriptionState}
    (hcomp : TuringMachine.Computes descriptionDecoder c d) :
    TuringMachine.Computes
      (budgetCheckerDescriptionRunnerMachine descriptionDecoder)
      { state := BudgetCheckerDescriptionRunnerState.run c.state
        tape := c.tape }
      { state := BudgetCheckerDescriptionRunnerState.run d.state
        tape := d.tape } := by
  induction hcomp with
  | refl c =>
      exact TuringMachine.Computes.refl _
  | step hstep hrest ih =>
      cases hstep with
      | mk haction =>
          exact TuringMachine.Computes.step
            (budgetCheckerDescriptionRunnerMachine_step_run
              descriptionDecoder haction)
            ih

theorem budgetCheckerDescriptionRunnerMachine_computesIn_scan
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState)
    (blankPrefix budget : Nat) (encoded : Word MachineCodeSymbol) :
    TuringMachine.ComputesIn
      (budgetCheckerDescriptionRunnerMachine descriptionDecoder)
      (budget + 1)
      { state := BudgetCheckerDescriptionRunnerState.scan
        tape :=
          budgetCheckerDescriptionRunnerTape blankPrefix
            (CodePrefixRecognizerStageCode encoded budget) }
      { state :=
          BudgetCheckerDescriptionRunnerState.run descriptionDecoder.start
        tape :=
          budgetCheckerDescriptionRunnerTape
            (blankPrefix + budget + 1) encoded } := by
  induction budget generalizing blankPrefix with
  | zero =>
      simpa [CodePrefixRecognizerStageCode,
        MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat, Nat.add_assoc] using
        TuringMachine.ComputesIn.succ
          (budgetCheckerDescriptionRunnerMachine_step_done
            descriptionDecoder blankPrefix encoded)
          (TuringMachine.ComputesIn.zero _)
  | succ budget ih =>
      have htail := ih (blankPrefix + 1)
      have hstep :=
        budgetCheckerDescriptionRunnerMachine_step_tick
          descriptionDecoder blankPrefix
          (CodePrefixRecognizerStageCode encoded budget)
      simpa [CodePrefixRecognizerStageCode,
        MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using
        TuringMachine.ComputesIn.succ hstep htail

theorem budgetCheckerDescriptionRunnerMachine_halts_run_only
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState)
    {steps : Nat} {state : descriptionState}
    {tape : Tape MachineCodeSymbol}
    (hhalt :
      TuringMachine.HaltsFromIn
        (budgetCheckerDescriptionRunnerMachine descriptionDecoder)
        steps
        { state := BudgetCheckerDescriptionRunnerState.run state
          tape := tape }) :
    TuringMachine.HaltsFrom descriptionDecoder
      { state := state, tape := tape } := by
  induction steps generalizing state tape with
  | zero =>
      rcases hhalt with ⟨final, hcomp, hfinal⟩
      cases hcomp
      cases hfinal
      exact TuringMachine.halts_from_halted rfl
  | succ steps ih =>
      rcases hhalt with ⟨final, hcomp, hfinal⟩
      cases hcomp with
      | succ hstep hrest =>
          cases hstep with
          | mk haction =>
              rename_i write dir nextState
              cases hdesc :
                  descriptionDecoder.transition state (Tape.read tape) with
              | none =>
                  simp [budgetCheckerDescriptionRunnerMachine, hdesc]
                    at haction
              | some action =>
                  rcases action with ⟨write', dir', nextState'⟩
                  simp [budgetCheckerDescriptionRunnerMachine, hdesc]
                    at haction
                  rcases haction with ⟨hwrite, hdir, hnext⟩
                  subst write
                  subst dir
                  cases hnext
                  have htail :
                      TuringMachine.HaltsFromIn
                        (budgetCheckerDescriptionRunnerMachine
                          descriptionDecoder)
                        steps
                        { state :=
                            BudgetCheckerDescriptionRunnerState.run
                              nextState'
                          tape :=
                            Tape.move dir' (Tape.write write' tape) } :=
                    ⟨final, hrest, hfinal⟩
                  rcases ih htail with
                    ⟨descFinal, hdescComp, hdescHalt⟩
                  exact
                    ⟨descFinal,
                      TuringMachine.Computes.step
                        (TuringMachine.Step.mk hdesc) hdescComp,
                      hdescHalt⟩

theorem budgetCheckerDescriptionRunnerMachine_halts_scan_only
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState)
    {steps blankPrefix budget : Nat}
    {encoded : Word MachineCodeSymbol}
    (hhalt :
      TuringMachine.HaltsFromIn
        (budgetCheckerDescriptionRunnerMachine descriptionDecoder)
        steps
        { state := BudgetCheckerDescriptionRunnerState.scan
          tape :=
            budgetCheckerDescriptionRunnerTape blankPrefix
              (CodePrefixRecognizerStageCode encoded budget) }) :
    TuringMachine.HaltsFrom descriptionDecoder
      { state := descriptionDecoder.start
        tape :=
          budgetCheckerDescriptionRunnerTape
            (blankPrefix + budget + 1) encoded } := by
  induction budget generalizing steps blankPrefix with
  | zero =>
      rcases hhalt with ⟨final, hcomp, hfinal⟩
      cases hcomp with
      | zero =>
          cases hfinal
      | succ hstep hrest =>
          rename_i tailSteps mid
          cases hstep with
          | mk haction =>
              rename_i write dir nextState
              simp [budgetCheckerDescriptionRunnerMachine,
                budgetCheckerDescriptionRunnerTape,
                CodePrefixRecognizerStageCode,
                MachineDescription.encodeNatAppend,
                MachineDescription.encodeNat, Tape.read] at haction
              rcases haction with ⟨hwrite, hdir, hnext⟩
              subst write
              subst dir
              cases hnext
              have htail :
                  TuringMachine.HaltsFromIn
                    (budgetCheckerDescriptionRunnerMachine
                      descriptionDecoder)
                    tailSteps
                    { state :=
                        BudgetCheckerDescriptionRunnerState.run
                          descriptionDecoder.start
                      tape :=
                        budgetCheckerDescriptionRunnerTape
                          (blankPrefix + 1) encoded } := by
                refine ⟨final, ?_, hfinal⟩
                simpa [CodePrefixRecognizerStageCode,
                  MachineDescription.encodeNatAppend,
                  MachineDescription.encodeNat,
                  budgetCheckerDescriptionRunnerTape_move_right]
                  using hrest
              simpa [Nat.add_assoc] using
                budgetCheckerDescriptionRunnerMachine_halts_run_only
                  descriptionDecoder htail
  | succ budget ih =>
      rcases hhalt with ⟨final, hcomp, hfinal⟩
      cases hcomp with
      | zero =>
          cases hfinal
      | succ hstep hrest =>
          rename_i tailSteps mid
          cases hstep with
          | mk haction =>
              rename_i write dir nextState
              simp [budgetCheckerDescriptionRunnerMachine,
                budgetCheckerDescriptionRunnerTape,
                CodePrefixRecognizerStageCode,
                MachineDescription.encodeNatAppend,
                MachineDescription.encodeNat, Tape.read] at haction
              rcases haction with ⟨hwrite, hdir, hnext⟩
              subst write
              subst dir
              cases hnext
              have htail :
                  TuringMachine.HaltsFromIn
                    (budgetCheckerDescriptionRunnerMachine
                      descriptionDecoder)
                    tailSteps
                    { state := BudgetCheckerDescriptionRunnerState.scan
                      tape :=
                        budgetCheckerDescriptionRunnerTape
                          (blankPrefix + 1)
                          (CodePrefixRecognizerStageCode encoded budget) } := by
                refine ⟨final, ?_, hfinal⟩
                simpa [CodePrefixRecognizerStageCode,
                  MachineDescription.encodeNatAppend,
                  MachineDescription.encodeNat,
                  budgetCheckerDescriptionRunnerTape_move_right]
                  using hrest
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                ih htail

noncomputable def finiteStateIndexOf
    {α : Type uDescription} (finite : Foundation.FiniteType α)
    (state : α) : Fin finite.elems.length :=
  let h : ∃ i, ∃ hlt : i < finite.elems.length,
      finite.elems[i] = state :=
    (List.mem_iff_getElem).mp (finite.complete state)
  ⟨Classical.choose h, Classical.choose (Classical.choose_spec h)⟩

def finiteStateValueOf
    {α : Type uDescription} (finite : Foundation.FiniteType α)
    (index : Fin finite.elems.length) : α :=
  finite.elems[index]

theorem finiteStateValueOf_indexOf
    {α : Type uDescription} (finite : Foundation.FiniteType α)
    (state : α) :
    finiteStateValueOf finite (finiteStateIndexOf finite state) = state := by
  unfold finiteStateValueOf finiteStateIndexOf
  let h : ∃ i, ∃ hlt : i < finite.elems.length,
      finite.elems[i] = state :=
    (List.mem_iff_getElem).mp (finite.complete state)
  exact Classical.choose_spec (Classical.choose_spec h)

def budgetCheckerDescriptionRunnerIndexedStateFinite (n : Nat) :
    Foundation.FiniteType (Option (Fin n)) where
  elems := none :: (List.finRange n).map some
  complete := by
    intro state
    cases state with
    | none =>
        simp
    | some index =>
        simp

noncomputable def budgetCheckerDescriptionRunnerIndexedMachine
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState) :
    TuringMachine MachineCodeSymbol
      (Option (Fin descriptionDecoder.statesFinite.elems.length)) where
  start := none
  halt :=
    some
      (finiteStateIndexOf descriptionDecoder.statesFinite
        descriptionDecoder.halt)
  transition := fun state cell =>
    match state with
    | none =>
        match cell with
        | some MachineCodeSymbol.tick =>
            some (none, Direction.right, none)
        | some MachineCodeSymbol.done =>
            some (none, Direction.right,
              some
                (finiteStateIndexOf descriptionDecoder.statesFinite
                  descriptionDecoder.start))
        | _ => none
    | some index =>
        match descriptionDecoder.transition
            (finiteStateValueOf descriptionDecoder.statesFinite index)
            cell with
        | none => none
        | some (write, dir, nextState) =>
            some (write, dir,
              some
                (finiteStateIndexOf descriptionDecoder.statesFinite
                  nextState))
  statesFinite :=
    budgetCheckerDescriptionRunnerIndexedStateFinite
      descriptionDecoder.statesFinite.elems.length

theorem budgetCheckerDescriptionRunnerIndexedMachine_step_tick
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState)
    (blankPrefix : Nat) (suffix : Word MachineCodeSymbol) :
    TuringMachine.Step
      (budgetCheckerDescriptionRunnerIndexedMachine descriptionDecoder)
      { state := none
        tape :=
          budgetCheckerDescriptionRunnerTape blankPrefix
            (MachineCodeSymbol.tick :: suffix) }
      { state := none
        tape :=
          budgetCheckerDescriptionRunnerTape (blankPrefix + 1) suffix } := by
  rw [← budgetCheckerDescriptionRunnerTape_move_right
    blankPrefix MachineCodeSymbol.tick suffix]
  exact TuringMachine.Step.mk (by
    simp [budgetCheckerDescriptionRunnerIndexedMachine,
      budgetCheckerDescriptionRunnerTape, Tape.read])

theorem budgetCheckerDescriptionRunnerIndexedMachine_step_done
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState)
    (blankPrefix : Nat) (suffix : Word MachineCodeSymbol) :
    TuringMachine.Step
      (budgetCheckerDescriptionRunnerIndexedMachine descriptionDecoder)
      { state := none
        tape :=
          budgetCheckerDescriptionRunnerTape blankPrefix
            (MachineCodeSymbol.done :: suffix) }
      { state :=
          some
            (finiteStateIndexOf descriptionDecoder.statesFinite
              descriptionDecoder.start)
        tape :=
          budgetCheckerDescriptionRunnerTape (blankPrefix + 1) suffix } := by
  rw [← budgetCheckerDescriptionRunnerTape_move_right
    blankPrefix MachineCodeSymbol.done suffix]
  exact TuringMachine.Step.mk (by
    simp [budgetCheckerDescriptionRunnerIndexedMachine,
      budgetCheckerDescriptionRunnerTape, Tape.read])

theorem budgetCheckerDescriptionRunnerIndexedMachine_step_run
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState)
    {state nextState : descriptionState}
    {tape : Tape MachineCodeSymbol} {write : Option MachineCodeSymbol}
    {dir : Direction}
    (haction :
      descriptionDecoder.transition state (Tape.read tape) =
        some (write, dir, nextState)) :
    TuringMachine.Step
      (budgetCheckerDescriptionRunnerIndexedMachine descriptionDecoder)
      { state :=
          some
            (finiteStateIndexOf descriptionDecoder.statesFinite state)
        tape := tape }
      { state :=
          some
            (finiteStateIndexOf descriptionDecoder.statesFinite nextState)
        tape := Tape.move dir (Tape.write write tape) } := by
  exact TuringMachine.Step.mk (by
    simp [budgetCheckerDescriptionRunnerIndexedMachine,
      finiteStateValueOf_indexOf, haction])

theorem budgetCheckerDescriptionRunnerIndexedMachine_computesIn_scan
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState)
    (blankPrefix budget : Nat) (encoded : Word MachineCodeSymbol) :
    TuringMachine.ComputesIn
      (budgetCheckerDescriptionRunnerIndexedMachine descriptionDecoder)
      (budget + 1)
      { state := none
        tape :=
          budgetCheckerDescriptionRunnerTape blankPrefix
            (CodePrefixRecognizerStageCode encoded budget) }
      { state :=
          some
            (finiteStateIndexOf descriptionDecoder.statesFinite
              descriptionDecoder.start)
        tape :=
          budgetCheckerDescriptionRunnerTape
            (blankPrefix + budget + 1) encoded } := by
  induction budget generalizing blankPrefix with
  | zero =>
      simpa [CodePrefixRecognizerStageCode,
        MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat, Nat.add_assoc] using
        TuringMachine.ComputesIn.succ
          (budgetCheckerDescriptionRunnerIndexedMachine_step_done
            descriptionDecoder blankPrefix encoded)
          (TuringMachine.ComputesIn.zero _)
  | succ budget ih =>
      have htail := ih (blankPrefix + 1)
      have hstep :=
        budgetCheckerDescriptionRunnerIndexedMachine_step_tick
          descriptionDecoder blankPrefix
          (CodePrefixRecognizerStageCode encoded budget)
      simpa [CodePrefixRecognizerStageCode,
        MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using
        TuringMachine.ComputesIn.succ hstep htail

theorem budgetCheckerDescriptionRunnerIndexedMachine_computes_run
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState)
    {c d : TuringMachine.Configuration MachineCodeSymbol descriptionState}
    (hcomp : TuringMachine.Computes descriptionDecoder c d) :
    TuringMachine.Computes
      (budgetCheckerDescriptionRunnerIndexedMachine descriptionDecoder)
      { state :=
          some
            (finiteStateIndexOf descriptionDecoder.statesFinite c.state)
        tape := c.tape }
      { state :=
          some
            (finiteStateIndexOf descriptionDecoder.statesFinite d.state)
        tape := d.tape } := by
  induction hcomp with
  | refl c =>
      exact TuringMachine.Computes.refl _
  | step hstep hrest ih =>
      cases hstep with
      | mk haction =>
          exact TuringMachine.Computes.step
            (budgetCheckerDescriptionRunnerIndexedMachine_step_run
              descriptionDecoder haction)
            ih

theorem budgetCheckerDescriptionRunnerIndexedMachine_halts_run_only
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState)
    {steps : Nat}
    {index : Fin descriptionDecoder.statesFinite.elems.length}
    {tape : Tape MachineCodeSymbol}
    (hhalt :
      TuringMachine.HaltsFromIn
        (budgetCheckerDescriptionRunnerIndexedMachine descriptionDecoder)
        steps
        { state := some index
          tape := tape }) :
    TuringMachine.HaltsFrom descriptionDecoder
      { state :=
          finiteStateValueOf descriptionDecoder.statesFinite index
        tape := tape } := by
  induction steps generalizing index tape with
  | zero =>
      rcases hhalt with ⟨final, hcomp, hfinal⟩
      cases hcomp
      simp [TuringMachine.Halted,
        budgetCheckerDescriptionRunnerIndexedMachine] at hfinal
      subst index
      exact TuringMachine.halts_from_halted (by
        exact finiteStateValueOf_indexOf
          descriptionDecoder.statesFinite descriptionDecoder.halt)
  | succ steps ih =>
      rcases hhalt with ⟨final, hcomp, hfinal⟩
      cases hcomp with
      | succ hstep hrest =>
          cases hstep with
          | mk haction =>
              rename_i write dir nextIndex
              let actual :=
                finiteStateValueOf descriptionDecoder.statesFinite index
              cases hdesc :
                  descriptionDecoder.transition actual (Tape.read tape) with
              | none =>
                  simp [budgetCheckerDescriptionRunnerIndexedMachine,
                    actual, hdesc] at haction
              | some action =>
                  rcases action with ⟨write', dir', nextState'⟩
                  simp [budgetCheckerDescriptionRunnerIndexedMachine,
                    actual, hdesc] at haction
                  rcases haction with ⟨hwrite, hdir, hnext⟩
                  subst write
                  subst dir
                  cases hnext
                  have htail :
                      TuringMachine.HaltsFromIn
                        (budgetCheckerDescriptionRunnerIndexedMachine
                          descriptionDecoder)
                        steps
                        { state :=
                            some
                              (finiteStateIndexOf
                                descriptionDecoder.statesFinite nextState')
                          tape :=
                            Tape.move dir' (Tape.write write' tape) } :=
                    ⟨final, hrest, hfinal⟩
                  rcases ih htail with
                    ⟨descFinal, hdescComp, hdescHalt⟩
                  have hdescComp' :
                      TuringMachine.Computes descriptionDecoder
                        { state := nextState'
                          tape :=
                            Tape.move dir' (Tape.write write' tape) }
                        descFinal := by
                    simpa [finiteStateValueOf_indexOf] using hdescComp
                  refine
                    ⟨descFinal,
                      TuringMachine.Computes.step
                        (TuringMachine.Step.mk hdesc) hdescComp',
                      hdescHalt⟩

theorem budgetCheckerDescriptionRunnerIndexedMachine_halts_scan_only
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState)
    {steps blankPrefix budget : Nat}
    {encoded : Word MachineCodeSymbol}
    (hhalt :
      TuringMachine.HaltsFromIn
        (budgetCheckerDescriptionRunnerIndexedMachine descriptionDecoder)
        steps
        { state := none
          tape :=
            budgetCheckerDescriptionRunnerTape blankPrefix
              (CodePrefixRecognizerStageCode encoded budget) }) :
    TuringMachine.HaltsFrom descriptionDecoder
      { state := descriptionDecoder.start
        tape :=
          budgetCheckerDescriptionRunnerTape
            (blankPrefix + budget + 1) encoded } := by
  induction budget generalizing steps blankPrefix with
  | zero =>
      rcases hhalt with ⟨final, hcomp, hfinal⟩
      cases hcomp with
      | zero =>
          cases hfinal
      | succ hstep hrest =>
          rename_i tailSteps mid
          cases hstep with
          | mk haction =>
              rename_i write dir nextState
              simp [budgetCheckerDescriptionRunnerIndexedMachine,
                budgetCheckerDescriptionRunnerTape,
                CodePrefixRecognizerStageCode,
                MachineDescription.encodeNatAppend,
                MachineDescription.encodeNat, Tape.read] at haction
              rcases haction with ⟨hwrite, hdir, hnext⟩
              subst write
              subst dir
              cases hnext
              have htail :
                  TuringMachine.HaltsFromIn
                    (budgetCheckerDescriptionRunnerIndexedMachine
                      descriptionDecoder)
                    tailSteps
                    { state :=
                        some
                          (finiteStateIndexOf
                            descriptionDecoder.statesFinite
                            descriptionDecoder.start)
                      tape :=
                        budgetCheckerDescriptionRunnerTape
                          (blankPrefix + 1) encoded } := by
                refine ⟨final, ?_, hfinal⟩
                simpa [CodePrefixRecognizerStageCode,
                  MachineDescription.encodeNatAppend,
                  MachineDescription.encodeNat,
                  budgetCheckerDescriptionRunnerTape_move_right]
                  using hrest
              have hrun :=
                budgetCheckerDescriptionRunnerIndexedMachine_halts_run_only
                  descriptionDecoder htail
              simpa [Nat.add_assoc, finiteStateValueOf_indexOf] using hrun
  | succ budget ih =>
      rcases hhalt with ⟨final, hcomp, hfinal⟩
      cases hcomp with
      | zero =>
          cases hfinal
      | succ hstep hrest =>
          rename_i tailSteps mid
          cases hstep with
          | mk haction =>
              rename_i write dir nextState
              simp [budgetCheckerDescriptionRunnerIndexedMachine,
                budgetCheckerDescriptionRunnerTape,
                CodePrefixRecognizerStageCode,
                MachineDescription.encodeNatAppend,
                MachineDescription.encodeNat, Tape.read] at haction
              rcases haction with ⟨hwrite, hdir, hnext⟩
              subst write
              subst dir
              cases hnext
              have htail :
                  TuringMachine.HaltsFromIn
                    (budgetCheckerDescriptionRunnerIndexedMachine
                      descriptionDecoder)
                    tailSteps
                    { state := none
                      tape :=
                        budgetCheckerDescriptionRunnerTape
                          (blankPrefix + 1)
                          (CodePrefixRecognizerStageCode encoded budget) } := by
                refine ⟨final, ?_, hfinal⟩
                simpa [CodePrefixRecognizerStageCode,
                  MachineDescription.encodeNatAppend,
                  MachineDescription.encodeNat,
                  budgetCheckerDescriptionRunnerTape_move_right]
                  using hrest
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                ih htail

/--
Finite-machine leaf for stripping the stage budget before invoking the
description decoder.  This isolates the head-positioning and blank-context
simulation work from the bounded-pair search.
-/
theorem codePrefixStageSearchControllerBudgetCheckerDescriptionRunnerObligation_core
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState) :
    CodePrefixStageSearchControllerBudgetCheckerDescriptionRunnerObligation
      descriptionDecoder := by
  refine
    ⟨Option (Fin descriptionDecoder.statesFinite.elems.length),
      budgetCheckerDescriptionRunnerIndexedMachine descriptionDecoder, ?_⟩
  intro encoded budget
  constructor
  · intro hrunner
    rcases
        TuringMachine.halts_on_input_to_halts_on_input_in hrunner with
      ⟨steps, hsteps⟩
    have hfrom :
        TuringMachine.HaltsFromIn
          (budgetCheckerDescriptionRunnerIndexedMachine descriptionDecoder)
          steps
          { state := none
            tape :=
              budgetCheckerDescriptionRunnerTape 0
                (CodePrefixRecognizerStageCode encoded budget) } := by
      simpa [TuringMachine.HaltsOnInputIn, TuringMachine.initial,
        budgetCheckerDescriptionRunnerIndexedMachine,
        budgetCheckerDescriptionRunnerTape_nil_eq_input] using hsteps
    have hdescFrom :=
      budgetCheckerDescriptionRunnerIndexedMachine_halts_scan_only
        descriptionDecoder hfrom
    have hequiv :
        Tape.Equiv
          (budgetCheckerDescriptionRunnerTape (0 + budget + 1) encoded)
          (Tape.input encoded) :=
      budgetCheckerDescriptionRunnerTape_equiv_input
        (0 + budget + 1) encoded
    exact
      (turingMachine_haltsFrom_tape_equiv_iff
        descriptionDecoder descriptionDecoder.start hequiv).mp hdescFrom
  · intro hdescription
    rcases hdescription with ⟨final, hcomp, hhalt⟩
    have hscanIn :=
      budgetCheckerDescriptionRunnerIndexedMachine_computesIn_scan
        descriptionDecoder 0 budget encoded
    have hscan :
        TuringMachine.Computes
          (budgetCheckerDescriptionRunnerIndexedMachine descriptionDecoder)
          { state := none
            tape :=
              budgetCheckerDescriptionRunnerTape 0
                (CodePrefixRecognizerStageCode encoded budget) }
          { state :=
              some
                (finiteStateIndexOf descriptionDecoder.statesFinite
                  descriptionDecoder.start)
            tape :=
              budgetCheckerDescriptionRunnerTape (0 + budget + 1)
                encoded } :=
      TuringMachine.computesIn_to_computes hscanIn
    have hequiv :
        Tape.Equiv (Tape.input encoded)
          (budgetCheckerDescriptionRunnerTape (0 + budget + 1)
            encoded) :=
      Tape.Equiv.symm
        (budgetCheckerDescriptionRunnerTape_equiv_input
          (0 + budget + 1) encoded)
    rcases turingMachine_computes_of_tape_equiv hcomp hequiv with
      ⟨final', hcomp', hstate, _htape⟩
    have hrun :
        TuringMachine.Computes
          (budgetCheckerDescriptionRunnerIndexedMachine descriptionDecoder)
          { state :=
              some
                (finiteStateIndexOf descriptionDecoder.statesFinite
                  descriptionDecoder.start)
            tape :=
              budgetCheckerDescriptionRunnerTape (0 + budget + 1)
                encoded }
          { state :=
              some
                (finiteStateIndexOf descriptionDecoder.statesFinite
                  final'.state)
            tape := final'.tape } :=
      budgetCheckerDescriptionRunnerIndexedMachine_computes_run
        descriptionDecoder hcomp'
    have hhalt' :
        TuringMachine.Halted
          (budgetCheckerDescriptionRunnerIndexedMachine descriptionDecoder)
          { state :=
              some
                (finiteStateIndexOf descriptionDecoder.statesFinite
                  final'.state)
            tape := final'.tape } := by
      have hfinalState : final'.state = descriptionDecoder.halt := by
        simpa [TuringMachine.Halted, hstate] using hhalt
      simp [TuringMachine.Halted,
        budgetCheckerDescriptionRunnerIndexedMachine, hfinalState]
    have hrunnerFrom :
        TuringMachine.HaltsFrom
          (budgetCheckerDescriptionRunnerIndexedMachine descriptionDecoder)
          { state := none
            tape :=
              budgetCheckerDescriptionRunnerTape 0
                (CodePrefixRecognizerStageCode encoded budget) } :=
      TuringMachine.halts_from_of_computes
        (TuringMachine.computes_trans hscan hrun) hhalt'
    simpa [TuringMachine.HaltsOnInput, TuringMachine.initial,
      budgetCheckerDescriptionRunnerIndexedMachine,
      budgetCheckerDescriptionRunnerTape_nil_eq_input] using hrunnerFrom

/--
Finite-machine leaf for the bounded stage/fuel simulator search used by the
budget checker.
-/
theorem codePrefixStageSearchControllerBudgetCheckerBoundedSimulatorRunnerObligation_core
    (simulator : TuringMachine MachineCodeSymbol simulatorState) :
    CodePrefixStageSearchControllerBudgetCheckerBoundedSimulatorRunnerObligation
      simulator := by
  rcases
      codePrefixStageSearchControllerBudgetCheckerBoundedSimulatorRawLoopObligation_core
        simulator with
    ⟨runnerState, runner, hrunner⟩
  refine ⟨runnerState, runner, ?_⟩
  intro encoded budget
  constructor
  · intro hhalt
    rcases
        (hrunner (CodePrefixRecognizerStageCode encoded budget)).mp
          hhalt with
      ⟨parsedBudget, parsedEncoded, checkedStage, fuel,
        htokens, hcheckedStage, hfuel, hsimulator⟩
    have hparsed :=
      codePrefixRecognizerStageCode_injective htokens.symm
    rcases hparsed with ⟨hbudget, hencoded⟩
    subst parsedBudget
    subst parsedEncoded
    exact ⟨checkedStage, fuel, hcheckedStage, hfuel, hsimulator⟩
  · intro htarget
    rcases htarget with
      ⟨checkedStage, fuel, hcheckedStage, hfuel, hsimulator⟩
    exact
      (hrunner (CodePrefixRecognizerStageCode encoded budget)).mpr
        ⟨budget, encoded, checkedStage, fuel, rfl,
          hcheckedStage, hfuel, hsimulator⟩

/--
Concrete finite-driver obligation for recognizer intersection.  The machine
must preserve the common input, enumerate bounded left/right fuel pairs, and
halt exactly when both simulations have halted within some finite pair.
-/
def CodePrefixStageSearchControllerBudgetCheckerIntersectionBoundedPairObligation :
    Prop :=
  forall {leftState rightState : Type}
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState),
      exists bothState : Type,
      exists both : TuringMachine MachineCodeSymbol bothState,
        forall input : Word MachineCodeSymbol,
          TuringMachine.HaltsOnInput both input <->
            exists leftFuel : Nat,
            exists rightFuel : Nat,
              TuringMachine.HaltsOnInputIn left leftFuel input ∧
                TuringMachine.HaltsOnInputIn right rightFuel input

theorem codePrefixStageSearchControllerBudgetCheckerIntersection_boundedPair_iff
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState)
    (input : Word MachineCodeSymbol) :
    (exists leftFuel : Nat,
      exists rightFuel : Nat,
        TuringMachine.HaltsOnInputIn left leftFuel input ∧
          TuringMachine.HaltsOnInputIn right rightFuel input) <->
      TuringMachine.HaltsOnInput left input ∧
        TuringMachine.HaltsOnInput right input := by
  constructor
  · intro h
    rcases h with ⟨leftFuel, rightFuel, hleft, hright⟩
    exact
      ⟨TuringMachine.halts_on_input_in_to_halts_on_input hleft,
        TuringMachine.halts_on_input_in_to_halts_on_input hright⟩
  · intro h
    rcases h with ⟨hleft, hright⟩
    rcases TuringMachine.halts_on_input_to_halts_on_input_in
        hleft with
      ⟨leftFuel, hleftFuel⟩
    rcases TuringMachine.halts_on_input_to_halts_on_input_in
        hright with
      ⟨rightFuel, hrightFuel⟩
    exact ⟨leftFuel, rightFuel, hleftFuel, hrightFuel⟩

/--
Finite-machine leaf for the bounded-pair driver used by recognizer
intersection.
-/
theorem codePrefixStageSearchControllerBudgetCheckerIntersectionBoundedPairObligation_core :
    CodePrefixStageSearchControllerBudgetCheckerIntersectionBoundedPairObligation := by
  sorry

/--
Finite-machine leaf for intersecting two same-alphabet recognizers.  The
intended construction dovetails the two computations on preserved copies of
the input and halts after both simulations have halted.
-/
theorem codePrefixStageSearchControllerBudgetCheckerIntersectionObligation_core :
    CodePrefixStageSearchControllerBudgetCheckerIntersectionObligation := by
  intro leftState rightState left right
  rcases
      codePrefixStageSearchControllerBudgetCheckerIntersectionBoundedPairObligation_core
        left right with
    ⟨bothState, both, hboth⟩
  refine ⟨bothState, both, ?_⟩
  intro input
  exact Iff.trans (hboth input)
    (codePrefixStageSearchControllerBudgetCheckerIntersection_boundedPair_iff
      left right input)

/--
Concrete finite-machine construction for the bounded checker driver.  This is
the remaining transition-table obligation after factoring out the semantic
adapter from the description decoder's recognizer spec.
-/
theorem codePrefixStageSearchControllerBudgetCheckerDriverFiniteMachineObligation_core
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState)
    (simulator : TuringMachine MachineCodeSymbol simulatorState) :
    CodePrefixStageSearchControllerBudgetCheckerDriverFiniteMachineObligation
      descriptionDecoder simulator := by
  rcases
      codePrefixStageSearchControllerBudgetCheckerDescriptionRunnerObligation_core
        descriptionDecoder with
    ⟨descriptionRunnerState, descriptionRunner, hdescriptionRunner⟩
  rcases
      codePrefixStageSearchControllerBudgetCheckerBoundedSimulatorRunnerObligation_core
        simulator with
    ⟨simulatorRunnerState, simulatorRunner, hsimulatorRunner⟩
  rcases
      codePrefixStageSearchControllerBudgetCheckerIntersectionObligation_core
        descriptionRunner simulatorRunner with
    ⟨checkerState, checker, hchecker⟩
  refine ⟨checkerState, checker, ?_⟩
  intro encoded budget
  constructor
  · intro hhalt
    rcases
        (hchecker (CodePrefixRecognizerStageCode encoded budget)).mp
          hhalt with
      ⟨hdescription, hsimulator⟩
    exact
      ⟨(hdescriptionRunner encoded budget).mp hdescription,
        (hsimulatorRunner encoded budget).mp hsimulator⟩
  · intro htarget
    rcases htarget with ⟨hdescription, hsimulator⟩
    exact
      (hchecker (CodePrefixRecognizerStageCode encoded budget)).mpr
        ⟨(hdescriptionRunner encoded budget).mpr hdescription,
          (hsimulatorRunner encoded budget).mpr hsimulator⟩

/--
Concrete finite-machine leaf for the bounded checker sequencing.  This is the
remaining transition-table construction after reusing the common stage-code and
description-prefix decoders.
-/
theorem codePrefixStageSearchControllerBudgetCheckerSequencingConstruction_core :
    CodePrefixStageSearchControllerBudgetCheckerSequencingConstruction := by
  intro stageState descriptionState simulatorState
    stageDecoder descriptionDecoder simulator _hstage hdescription
  rcases
      codePrefixStageSearchControllerBudgetCheckerDriverFiniteMachineObligation_core
        descriptionDecoder simulator with
    ⟨checkerState, checker, hchecker⟩
  refine ⟨checkerState, checker, ?_⟩
  intro encoded budget
  constructor
  · intro hhalt
    rcases (hchecker encoded budget).mp hhalt with
      ⟨hdecoded, checkedStage, fuel, hcheckedStage, hfuel, hsimulator⟩
    rcases (hdescription encoded).mp hdecoded with
      ⟨D, input, hdecode⟩
    exact
      ⟨D, input, checkedStage, fuel, hcheckedStage, hfuel,
        hdecode, hsimulator⟩
  · intro htarget
    rcases htarget with
      ⟨D, input, checkedStage, fuel, hcheckedStage, hfuel,
        hdecode, hsimulator⟩
    exact (hchecker encoded budget).mpr
      ⟨(hdescription encoded).mpr ⟨D, input, hdecode⟩,
        checkedStage, fuel, hcheckedStage, hfuel, hsimulator⟩

theorem codePrefixStageSearchControllerBudgetCheckerFiniteMachineObligation_core
    (simulator : TuringMachine MachineCodeSymbol simulatorState) :
    CodePrefixStageSearchControllerBudgetCheckerFiniteMachineObligation
      simulator := by
  rcases codePrefixDecodedBoundedSimulatorStageDecoderConstruction_core with
    ⟨stageState, stageDecoder, hstage⟩
  rcases
      codePrefixDecodedBoundedSimulatorDescriptionDecoderConstruction_core with
    ⟨descriptionState, descriptionDecoder, hdescription⟩
  exact
    codePrefixStageSearchControllerBudgetCheckerSequencingConstruction_core
      stageDecoder descriptionDecoder simulator hstage hdescription

theorem codePrefixStageSearchControllerBudgetCheckerFiniteLeaf :
    forall {simulatorState : Type}
      (simulator : TuringMachine MachineCodeSymbol simulatorState),
        exists checkerState : Type,
        exists checker : TuringMachine MachineCodeSymbol checkerState,
          forall encoded : Word MachineCodeSymbol,
          forall budget : Nat,
            TuringMachine.HaltsOnInput checker
                (CodePrefixRecognizerStageCode encoded budget) <->
              exists D : MachineDescription,
              exists input : Word MachineCodeSymbol,
              exists checkedStage : Nat,
              exists fuel : Nat,
                checkedStage ≤ budget ∧
                  fuel ≤ budget ∧
                  MachineDescription.decodeDescriptionPrefix encoded =
                    some (D, input) ∧
                  TuringMachine.HaltsOnInputIn simulator fuel
                    (CodePrefixRecognizerStageCode encoded checkedStage) := by
  intro simulatorState simulator
  exact
    codePrefixStageSearchControllerBudgetCheckerFiniteMachineObligation_core
      simulator

/-- Finite-machine leaf for checking one encoded input at one budget. -/
theorem codePrefixStageSearchControllerBudgetCheckerConstruction_core :
    forall {simulatorState : Type}
      (simulator : TuringMachine MachineCodeSymbol simulatorState),
        CodePrefixStageSearchControllerBudgetCheckerConstruction simulator := by
  intro simulatorState simulator
  rcases codePrefixStageSearchControllerBudgetCheckerFiniteLeaf
      simulator with
    ⟨checkerState, checker, hchecker⟩
  refine ⟨checkerState, checker, ?_⟩
  intro encoded budget
  exact Iff.trans (hchecker encoded budget)
    (Iff.symm
      (codePrefixStageSearchControllerProgram_run_eq_some_iff
        simulator encoded budget))

/--
Semantic target for the finite dovetailer: at some finite outer limit it has
checked one budget-coded input for a finite checker fuel.
-/
def CodePrefixStageSearchControllerBudgetDovetailWitness
    {checkerState : Type}
    (checker : TuringMachine MachineCodeSymbol checkerState)
    (encoded : Word MachineCodeSymbol) : Prop :=
  exists limit : Nat,
  exists budget : Nat,
  exists fuel : Nat,
    budget ≤ limit ∧
      fuel ≤ limit ∧
      TuringMachine.HaltsOnInputIn checker fuel
        (CodePrefixRecognizerStageCode encoded budget)

theorem codePrefixStageSearchControllerBudgetDovetailWitness_iff_budgetFuel
    {checkerState : Type}
    (checker : TuringMachine MachineCodeSymbol checkerState)
    (encoded : Word MachineCodeSymbol) :
    CodePrefixStageSearchControllerBudgetDovetailWitness checker encoded <->
      exists budget : Nat,
      exists fuel : Nat,
        TuringMachine.HaltsOnInputIn checker fuel
          (CodePrefixRecognizerStageCode encoded budget) := by
  constructor
  · intro h
    rcases h with ⟨_limit, budget, fuel, _hbudget, _hfuel, hrun⟩
    exact ⟨budget, fuel, hrun⟩
  · intro h
    rcases h with ⟨budget, fuel, hrun⟩
    refine ⟨Nat.max budget fuel, budget, fuel, ?_, ?_, hrun⟩
    · exact Nat.le_max_left budget fuel
    · exact Nat.le_max_right budget fuel

/--
Finite-machine construction obligation for the raw budget/fuel enumerator.
The machine enumerates pairs, builds the corresponding stage-coded checker
input, and runs the checker for the selected fuel.
-/
def CodePrefixStageSearchControllerBudgetFuelEnumeratorConstruction :
    Prop :=
  forall {checkerState : Type}
    (checker : TuringMachine MachineCodeSymbol checkerState),
      exists searcherState : Type,
      exists searcher : TuringMachine MachineCodeSymbol searcherState,
        forall encoded : Word MachineCodeSymbol,
          TuringMachine.HaltsOnInput searcher encoded <->
            exists budget : Nat,
            exists fuel : Nat,
              TuringMachine.HaltsOnInputIn checker fuel
                (CodePrefixRecognizerStageCode encoded budget)

/--
Concrete finite-driver obligation for the raw budget/fuel search.  The
machine runs an outer dovetail limit and, within that finite limit, checks
budget/fuel pairs for the supplied checker.
-/
def CodePrefixStageSearchControllerBudgetFuelFiniteDriverObligation
    {checkerState : Type}
    (checker : TuringMachine MachineCodeSymbol checkerState) : Prop :=
  exists searcherState : Type,
  exists searcher : TuringMachine MachineCodeSymbol searcherState,
    forall encoded : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput searcher encoded <->
        CodePrefixStageSearchControllerBudgetDovetailWitness checker encoded

/--
Raw finite-machine obligation for the budget/fuel driver.  This is the
transition-table construction that enumerates {lit}`(budget, fuel)` pairs,
rebuilds each stage-coded checker input, and runs the checker for the selected
fuel.
-/
def CodePrefixStageSearchControllerBudgetFuelRawDriverObligation
    {checkerState : Type}
    (checker : TuringMachine MachineCodeSymbol checkerState) : Prop :=
  exists searcherState : Type,
  exists searcher : TuringMachine MachineCodeSymbol searcherState,
    forall encoded : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput searcher encoded <->
        exists budget : Nat,
        exists fuel : Nat,
          TuringMachine.HaltsOnInputIn checker fuel
            (CodePrefixRecognizerStageCode encoded budget)

/--
Concrete finite-machine obligation for the budget searcher after hiding the
checker fuel in {name}`TuringMachine.HaltsOnInput`.  A construction here still
has to dovetail over budgets, but it no longer exposes the checker step bound
in its public contract.
-/
def CodePrefixStageSearchControllerBudgetRawSearchObligation
    {checkerState : Type}
    (checker : TuringMachine MachineCodeSymbol checkerState) : Prop :=
  exists searcherState : Type,
  exists searcher : TuringMachine MachineCodeSymbol searcherState,
    forall encoded : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput searcher encoded <->
        exists budget : Nat,
          TuringMachine.HaltsOnInput checker
            (CodePrefixRecognizerStageCode encoded budget)

/--
Concrete finite-machine obligation for one bounded outer attempt.  On input
{name}`CodePrefixRecognizerStageCode` with outer limit {lit}`limit`, the
machine enumerates all budget/fuel pairs bounded by that limit, rebuilds the
checker input for each budget, and runs the checker for the selected fuel.
-/
def CodePrefixStageSearchControllerBudgetFuelBoundedAttemptObligation
    {checkerState : Type}
    (checker : TuringMachine MachineCodeSymbol checkerState) : Prop :=
  exists attemptState : Type,
  exists attempt : TuringMachine MachineCodeSymbol attemptState,
    forall encoded : Word MachineCodeSymbol,
    forall limit : Nat,
      TuringMachine.HaltsOnInput attempt
          (CodePrefixRecognizerStageCode encoded limit) <->
        exists budget : Nat,
        exists fuel : Nat,
          budget ≤ limit ∧
            fuel ≤ limit ∧
            TuringMachine.HaltsOnInputIn checker fuel
              (CodePrefixRecognizerStageCode encoded budget)

/--
Concrete finite-machine obligation for the unbounded outer loop.  Given a
bounded attempt machine, it enumerates outer limits by prefixing the raw input
with each unary limit and invokes the attempt machine on the rebuilt input.
-/
def CodePrefixStageSearchControllerBudgetFuelOuterLoopObligation
    {attemptState : Type}
    (attempt : TuringMachine MachineCodeSymbol attemptState) : Prop :=
  exists searcherState : Type,
  exists searcher : TuringMachine MachineCodeSymbol searcherState,
    forall encoded : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput searcher encoded <->
        exists limit : Nat,
          TuringMachine.HaltsOnInput attempt
            (CodePrefixRecognizerStageCode encoded limit)

/--
Raw finite-machine obligation for the outer loop with the attempt fuel made
explicit.  This isolates the real transition-table work: preserve the raw
input, enumerate {lit}`(limit, fuel)` pairs, rebuild the corresponding
stage-coded input, and simulate the supplied attempt machine for the selected
fuel.
-/
def CodePrefixStageSearchControllerBudgetFuelOuterLoopFuelSearchObligation
    {attemptState : Type}
    (attempt : TuringMachine MachineCodeSymbol attemptState) : Prop :=
  exists searcherState : Type,
  exists searcher : TuringMachine MachineCodeSymbol searcherState,
    forall encoded : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput searcher encoded <->
        exists limit : Nat,
        exists fuel : Nat,
          TuringMachine.HaltsOnInputIn attempt fuel
            (CodePrefixRecognizerStageCode encoded limit)

/--
Concrete finite-machine leaf for the raw outer-loop fuel search.  The machine
must preserve the input, dovetail over generated stage prefixes and bounded
simulation fuel, rebuild each stage-coded input, and simulate the supplied
machine for the selected fuel.
-/
theorem codePrefixStageSearchControllerBudgetFuelOuterLoopFuelSearchFiniteLeaf
    {attemptState : Type}
    (attempt : TuringMachine MachineCodeSymbol attemptState) :
    CodePrefixStageSearchControllerBudgetFuelOuterLoopFuelSearchObligation
      attempt := by
  sorry

/--
Global wrapper for the raw stage-code/fuel search construction.  The concrete
transition-table obligation is the per-machine outer-loop fuel-search leaf.
-/
theorem codePrefixStageSearchControllerBudgetFuelEnumeratorConstruction_core :
    CodePrefixStageSearchControllerBudgetFuelEnumeratorConstruction := by
  intro checkerState checker
  exact
    codePrefixStageSearchControllerBudgetFuelOuterLoopFuelSearchFiniteLeaf
      checker

/--
Concrete finite-machine leaf for the raw outer-loop fuel search.  The concrete
machine has to dovetail over generated outer limits and bounded attempt fuel.
-/
theorem codePrefixStageSearchControllerBudgetFuelOuterLoopFuelSearchObligation_core
    {attemptState : Type}
    (attempt : TuringMachine MachineCodeSymbol attemptState) :
    CodePrefixStageSearchControllerBudgetFuelOuterLoopFuelSearchObligation
      attempt := by
  exact
    codePrefixStageSearchControllerBudgetFuelOuterLoopFuelSearchFiniteLeaf
      attempt

/--
Finite-machine leaf for the bounded attempt phase of the raw budget/fuel
driver.
-/
theorem codePrefixStageSearchControllerBudgetFuelBoundedAttemptObligation_core
    {checkerState : Type}
    (checker : TuringMachine MachineCodeSymbol checkerState) :
    CodePrefixStageSearchControllerBudgetFuelBoundedAttemptObligation
      checker := by
  rcases
      codePrefixStageSearchControllerBudgetCheckerBoundedSimulatorRawLoopObligation_core
        checker with
    ⟨attemptState, attempt, hattempt⟩
  refine ⟨attemptState, attempt, ?_⟩
  intro encoded limit
  constructor
  · intro hhalt
    rcases
        (hattempt (CodePrefixRecognizerStageCode encoded limit)).mp
          hhalt with
      ⟨outerBudget, encoded', budget, fuel, htokens,
        hbudget, hfuel, hchecker⟩
    rcases codePrefixRecognizerStageCode_injective htokens with
      ⟨hlimit, hencoded⟩
    subst outerBudget
    subst encoded'
    exact ⟨budget, fuel, hbudget, hfuel, hchecker⟩
  · intro htarget
    rcases htarget with ⟨budget, fuel, hbudget, hfuel, hchecker⟩
    exact
      (hattempt (CodePrefixRecognizerStageCode encoded limit)).mpr
        ⟨limit, encoded, budget, fuel, rfl, hbudget, hfuel, hchecker⟩

/--
Finite-machine leaf for the unbounded outer-loop phase of the raw budget/fuel
driver.
-/
theorem codePrefixStageSearchControllerBudgetFuelOuterLoopObligation_core
    {attemptState : Type}
    (attempt : TuringMachine MachineCodeSymbol attemptState) :
    CodePrefixStageSearchControllerBudgetFuelOuterLoopObligation
      attempt := by
  rcases
      codePrefixStageSearchControllerBudgetFuelOuterLoopFuelSearchObligation_core
        attempt with
    ⟨searcherState, searcher, hsearcher⟩
  refine ⟨searcherState, searcher, ?_⟩
  intro encoded
  constructor
  · intro hhalt
    rcases (hsearcher encoded).mp hhalt with
      ⟨limit, fuel, hattempt⟩
    exact
      ⟨limit,
        TuringMachine.halts_on_input_in_to_halts_on_input hattempt⟩
  · intro htarget
    rcases htarget with ⟨limit, hattempt⟩
    rcases TuringMachine.halts_on_input_to_halts_on_input_in
        hattempt with
      ⟨fuel, hfuel⟩
    exact (hsearcher encoded).mpr ⟨limit, fuel, hfuel⟩

/--
Concrete finite-machine construction for the raw budget/fuel dovetail driver.
This is the remaining transition-table work: enumerate budget/fuel pairs,
rebuild the stage-coded checker input, and run the checker for the selected
fuel.
-/
theorem codePrefixStageSearchControllerBudgetFuelRawDriverObligation_core
    {checkerState : Type}
    (checker : TuringMachine MachineCodeSymbol checkerState) :
    CodePrefixStageSearchControllerBudgetFuelRawDriverObligation
      checker := by
  rcases
      codePrefixStageSearchControllerBudgetFuelBoundedAttemptObligation_core
        checker with
    ⟨attemptState, attempt, hattempt⟩
  rcases
      codePrefixStageSearchControllerBudgetFuelOuterLoopObligation_core
        attempt with
    ⟨searcherState, searcher, hsearcher⟩
  refine ⟨searcherState, searcher, ?_⟩
  intro encoded
  constructor
  · intro hhalt
    rcases (hsearcher encoded).mp hhalt with
      ⟨limit, hattemptHalt⟩
    rcases (hattempt encoded limit).mp hattemptHalt with
      ⟨budget, fuel, _hbudget, _hfuel, hchecker⟩
    exact ⟨budget, fuel, hchecker⟩
  · intro htarget
    rcases htarget with ⟨budget, fuel, hchecker⟩
    let limit := Nat.max budget fuel
    have hbudget : budget ≤ limit := Nat.le_max_left budget fuel
    have hfuel : fuel ≤ limit := Nat.le_max_right budget fuel
    exact (hsearcher encoded).mpr
      ⟨limit,
        (hattempt encoded limit).mpr
          ⟨budget, fuel, hbudget, hfuel, hchecker⟩⟩

/--
Finite-machine construction for the budget-only searcher.  The remaining
transition-table work is the unbounded budget dovetailer that rebuilds
{name}`CodePrefixRecognizerStageCode` inputs and runs the checker.
-/
theorem codePrefixStageSearchControllerBudgetRawSearchObligation_core
    {checkerState : Type}
    (checker : TuringMachine MachineCodeSymbol checkerState) :
    CodePrefixStageSearchControllerBudgetRawSearchObligation checker := by
  rcases
      codePrefixStageSearchControllerBudgetFuelRawDriverObligation_core
        checker with
    ⟨searcherState, searcher, hsearcher⟩
  refine ⟨searcherState, searcher, ?_⟩
  intro encoded
  constructor
  · intro hhalt
    rcases (hsearcher encoded).mp hhalt with
      ⟨budget, fuel, hfuel⟩
    exact
      ⟨budget,
        TuringMachine.halts_on_input_in_to_halts_on_input hfuel⟩
  · intro hhit
    rcases hhit with ⟨budget, hbudget⟩
    rcases
        TuringMachine.halts_on_input_to_halts_on_input_in
          hbudget with
      ⟨fuel, hfuel⟩
    exact (hsearcher encoded).mpr ⟨budget, fuel, hfuel⟩

/--
Finite-machine obligation for the outer budget/fuel dovetail driver.  The raw
driver enumerates budget/fuel pairs directly; this adapter packages the same
hits as a finite outer-limit witness.
-/
theorem codePrefixStageSearchControllerBudgetFuelFiniteDriverObligation_core
    {checkerState : Type}
    (checker : TuringMachine MachineCodeSymbol checkerState) :
    CodePrefixStageSearchControllerBudgetFuelFiniteDriverObligation
      checker := by
  rcases
      codePrefixStageSearchControllerBudgetFuelRawDriverObligation_core
        checker with
    ⟨searcherState, searcher, hsearcher⟩
  refine ⟨searcherState, searcher, ?_⟩
  intro encoded
  exact Iff.trans (hsearcher encoded)
    (Iff.symm
      (codePrefixStageSearchControllerBudgetDovetailWitness_iff_budgetFuel
        checker encoded))

/--
Concrete finite-machine leaf for the raw budget/fuel enumerator.
This is adapter glue from the finite outer-limit driver to the raw
{lit}`(budget, fuel)` witness shape used by the surrounding controller proof.
-/
theorem codePrefixStageSearchControllerBudgetFuelEnumeratorFiniteLeaf :
    CodePrefixStageSearchControllerBudgetFuelEnumeratorConstruction := by
  intro checkerState checker
  rcases
      codePrefixStageSearchControllerBudgetFuelFiniteDriverObligation_core
        checker with
    ⟨searcherState, searcher, hsearcher⟩
  refine ⟨searcherState, searcher, ?_⟩
  intro encoded
  exact Iff.trans (hsearcher encoded)
    (codePrefixStageSearchControllerBudgetDovetailWitness_iff_budgetFuel
      checker encoded)

/--
Finite-machine leaf for the concrete unbounded search driver.  The machine
must enumerate bounded {lit}`(budget, fuel)` pairs, rebuild the stage-coded
checker input, and simulate the checker for the requested fuel.
-/
theorem codePrefixStageSearchControllerBudgetDovetailerFiniteLeaf
    {checkerState : Type}
    (checker : TuringMachine MachineCodeSymbol checkerState) :
    exists searcherState : Type,
    exists searcher : TuringMachine MachineCodeSymbol searcherState,
      forall encoded : Word MachineCodeSymbol,
        TuringMachine.HaltsOnInput searcher encoded <->
          CodePrefixStageSearchControllerBudgetDovetailWitness
            checker encoded := by
  rcases codePrefixStageSearchControllerBudgetFuelEnumeratorFiniteLeaf
      checker with
    ⟨searcherState, searcher, hsearcher⟩
  refine ⟨searcherState, searcher, ?_⟩
  intro encoded
  exact Iff.trans (hsearcher encoded)
    (Iff.symm
      (codePrefixStageSearchControllerBudgetDovetailWitness_iff_budgetFuel
        checker encoded))

theorem codePrefixStageSearchControllerBudgetDovetailWitness_iff
    {checkerState : Type}
    (checker : TuringMachine MachineCodeSymbol checkerState)
    (encoded : Word MachineCodeSymbol) :
    CodePrefixStageSearchControllerBudgetDovetailWitness checker encoded <->
      exists budget : Nat,
        TuringMachine.HaltsOnInput checker
          (CodePrefixRecognizerStageCode encoded budget) := by
  constructor
  · intro h
    rcases h with ⟨_limit, budget, fuel, _hbudget, _hfuel, hrun⟩
    exact
      ⟨budget,
        TuringMachine.halts_on_input_in_to_halts_on_input hrun⟩
  · intro h
    rcases h with ⟨budget, hhalt⟩
    rcases
        TuringMachine.halts_on_input_to_halts_on_input_in hhalt with
      ⟨fuel, hfuel⟩
    refine ⟨Nat.max budget fuel, budget, fuel, ?_, ?_, hfuel⟩
    · exact Nat.le_max_left budget fuel
    · exact Nat.le_max_right budget fuel

/-- Generic adapter from the bounded-pair dovetailer to budget enumeration. -/
theorem codePrefixStageSearchControllerBudgetEnumeratorConstruction_core
    {checkerState : Type}
    (checker : TuringMachine MachineCodeSymbol checkerState) :
    exists searcherState : Type,
    exists searcher : TuringMachine MachineCodeSymbol searcherState,
      forall encoded : Word MachineCodeSymbol,
        TuringMachine.HaltsOnInput searcher encoded <->
          exists budget : Nat,
            TuringMachine.HaltsOnInput checker
              (CodePrefixRecognizerStageCode encoded budget) := by
  rcases codePrefixStageSearchControllerBudgetDovetailerFiniteLeaf
      checker with
    ⟨searcherState, searcher, hsearcher⟩
  refine ⟨searcherState, searcher, ?_⟩
  intro encoded
  exact Iff.trans (hsearcher encoded)
    (codePrefixStageSearchControllerBudgetDovetailWitness_iff
      checker encoded)

/-- Finite-machine leaf for enumerating budgets using a bounded checker. -/
theorem codePrefixStageSearchControllerBudgetSearchSequencingConstruction_core :
    CodePrefixStageSearchControllerBudgetSearchSequencingConstruction := by
  intro simulatorState checkerState simulator checker hcheckerSpec
  rcases codePrefixStageSearchControllerBudgetEnumeratorConstruction_core
      checker with
    ⟨searcherState, searcher, hsearcher⟩
  refine ⟨searcherState, searcher, ?_⟩
  intro encoded
  constructor
  · intro hhalt
    rcases (hsearcher encoded).mp hhalt with ⟨budget, hbudget⟩
    exact ⟨budget, (hcheckerSpec encoded budget).mp hbudget⟩
  · intro hprogram
    rcases hprogram with ⟨budget, hrun⟩
    exact (hsearcher encoded).mpr
      ⟨budget, (hcheckerSpec encoded budget).mpr hrun⟩

theorem codePrefixStageSearchControllerProgramCompilerConstruction_core :
    CodePrefixStageSearchControllerProgramCompilerConstruction := by
  exact
    codePrefixStageSearchControllerProgramCompilerConstruction_of_components
      codePrefixStageSearchControllerBudgetCheckerConstruction_core
      codePrefixStageSearchControllerBudgetSearchSequencingConstruction_core

theorem codePrefixStageSearchControllerCoreConstruction_core :
    CodePrefixStageSearchControllerCoreConstruction :=
  codePrefixStageSearchControllerCoreConstruction_of_programCompiler
    codePrefixStageSearchControllerProgramCompilerConstruction_core

end Computability
end FoC

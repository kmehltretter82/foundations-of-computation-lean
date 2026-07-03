import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.DecodedBoundedSimulator

set_option doc.verso true

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

def codePrefixStageSearchControllerFuelHit
    [DecidableEq simulatorState]
    (simulator : TuringMachine MachineCodeSymbol simulatorState)
    (encoded : Word MachineCodeSymbol) (checkedStage : Nat) :
    Nat -> Bool
  | 0 =>
      decide
        (TuringMachine.HaltsOnInputIn simulator 0
          (CodePrefixRecognizerStageCode encoded checkedStage))
  | fuel + 1 =>
      decide
        (TuringMachine.HaltsOnInputIn simulator (fuel + 1)
          (CodePrefixRecognizerStageCode encoded checkedStage)) ||
        codePrefixStageSearchControllerFuelHit
          simulator encoded checkedStage fuel

theorem codePrefixStageSearchControllerFuelHit_eq_true_iff
    [DecidableEq simulatorState]
    (simulator : TuringMachine MachineCodeSymbol simulatorState)
    (encoded : Word MachineCodeSymbol) (checkedStage fuelBudget : Nat) :
    codePrefixStageSearchControllerFuelHit
        simulator encoded checkedStage fuelBudget = true <->
      exists fuel : Nat,
        fuel ≤ fuelBudget ∧
          TuringMachine.HaltsOnInputIn simulator fuel
            (CodePrefixRecognizerStageCode encoded checkedStage) := by
  induction fuelBudget with
  | zero =>
      simp [codePrefixStageSearchControllerFuelHit]
  | succ fuelBudget ih =>
      by_cases hcurrent :
          TuringMachine.HaltsOnInputIn simulator (fuelBudget + 1)
            (CodePrefixRecognizerStageCode encoded checkedStage)
      · constructor
        · intro _hhit
          exact ⟨fuelBudget + 1, by lia, hcurrent⟩
        · intro _hwitness
          simp [codePrefixStageSearchControllerFuelHit, hcurrent]
      · simp [codePrefixStageSearchControllerFuelHit, hcurrent, ih]
        constructor
        · intro h
          rcases h with ⟨fuel, hfuel, hhalt⟩
          exact ⟨fuel, by lia, hhalt⟩
        · intro h
          rcases h with ⟨fuel, hfuel, hhalt⟩
          by_cases hlast : fuel = fuelBudget + 1
          · subst fuel
            exact False.elim (hcurrent hhalt)
          · exact ⟨fuel, by lia, hhalt⟩

def codePrefixStageSearchControllerStageFuelHit
    [DecidableEq simulatorState]
    (simulator : TuringMachine MachineCodeSymbol simulatorState)
    (encoded : Word MachineCodeSymbol) (fuelBudget : Nat) :
    Nat -> Bool
  | 0 =>
      codePrefixStageSearchControllerFuelHit simulator encoded 0 fuelBudget
  | checkedStage + 1 =>
      codePrefixStageSearchControllerFuelHit
          simulator encoded (checkedStage + 1) fuelBudget ||
        codePrefixStageSearchControllerStageFuelHit
          simulator encoded fuelBudget checkedStage

theorem codePrefixStageSearchControllerStageFuelHit_eq_true_iff
    [DecidableEq simulatorState]
    (simulator : TuringMachine MachineCodeSymbol simulatorState)
    (encoded : Word MachineCodeSymbol)
    (stageBudget fuelBudget : Nat) :
    codePrefixStageSearchControllerStageFuelHit
        simulator encoded fuelBudget stageBudget = true <->
      exists checkedStage : Nat,
      exists fuel : Nat,
        checkedStage ≤ stageBudget ∧
          fuel ≤ fuelBudget ∧
          TuringMachine.HaltsOnInputIn simulator fuel
            (CodePrefixRecognizerStageCode encoded checkedStage) := by
  induction stageBudget with
  | zero =>
      simp [codePrefixStageSearchControllerStageFuelHit,
        codePrefixStageSearchControllerFuelHit_eq_true_iff]
  | succ stageBudget ih =>
      simp [codePrefixStageSearchControllerStageFuelHit,
        codePrefixStageSearchControllerFuelHit_eq_true_iff, ih]
      constructor
      · intro h
        rcases h with hlast | hprev
        ·
            rcases hlast with ⟨fuel, hfuel, hhalt⟩
            exact ⟨stageBudget + 1, by lia, fuel, hfuel, hhalt⟩
        ·
            rcases hprev with
              ⟨checkedStage, hstage, fuel, hfuel, hhalt⟩
            exact ⟨checkedStage, by lia, fuel, hfuel, hhalt⟩
      · intro h
        rcases h with ⟨checkedStage, hstage, fuel, hfuel, hhalt⟩
        by_cases hlast : checkedStage = stageBudget + 1
        · subst checkedStage
          exact Or.inl ⟨fuel, hfuel, hhalt⟩
        · exact Or.inr ⟨checkedStage, by lia, fuel, hfuel, hhalt⟩

def codePrefixStageSearchControllerProgramDecidable
    [DecidableEq simulatorState]
    (simulator : TuringMachine MachineCodeSymbol simulatorState) :
    StagedProgram MachineCodeSymbol Unit :=
  { run := fun encoded budget =>
      match MachineDescription.decodeDescriptionPrefix encoded with
      | none => none
      | some _ =>
          if codePrefixStageSearchControllerStageFuelHit
              simulator encoded budget budget = true then
            some []
          else
            none }

theorem codePrefixStageSearchControllerProgramDecidable_run_eq_some_iff
    [DecidableEq simulatorState]
    (simulator : TuringMachine MachineCodeSymbol simulatorState)
    (encoded : Word MachineCodeSymbol) (budget : Nat) :
    (codePrefixStageSearchControllerProgramDecidable simulator).run
        encoded budget = some [] <->
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
  cases hdecode : MachineDescription.decodeDescriptionPrefix encoded with
  | none =>
      simp [codePrefixStageSearchControllerProgramDecidable, hdecode]
  | some decoded =>
      rcases decoded with ⟨D, input⟩
      constructor
      · intro hrun
        by_cases hhit :
            codePrefixStageSearchControllerStageFuelHit
              simulator encoded budget budget = true
        ·
          rcases
              (codePrefixStageSearchControllerStageFuelHit_eq_true_iff
                simulator encoded budget budget).mp hhit with
            ⟨checkedStage, fuel, hstage, hfuel, hhalt⟩
          exact
            ⟨D, input, checkedStage, fuel, hstage, hfuel, rfl, hhalt⟩
        · simp [codePrefixStageSearchControllerProgramDecidable, hdecode, hhit]
            at hrun
      · intro h
        rcases h with
          ⟨D', input', checkedStage, fuel, hstage, hfuel, hdecode', hhalt⟩
        cases hdecode'
        have hhit :
            codePrefixStageSearchControllerStageFuelHit
              simulator encoded budget budget = true :=
          ((codePrefixStageSearchControllerStageFuelHit_eq_true_iff
            simulator encoded budget budget).mpr
            ⟨checkedStage, fuel, hstage, hfuel, hhalt⟩)
        simp [codePrefixStageSearchControllerProgramDecidable, hdecode, hhit]
        rfl

theorem codePrefixStageSearchControllerProgramDecidable_accepts
    [DecidableEq simulatorState]
    (simulator : TuringMachine MachineCodeSymbol simulatorState)
    (encoded : Word MachineCodeSymbol) :
    ProgramHaltsWithOutput
        (codePrefixStageSearchControllerProgramDecidable simulator)
        encoded [] <->
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
      exists stage : Nat,
        MachineDescription.decodeDescriptionPrefix encoded =
            some (D, input) ∧
          TuringMachine.HaltsOnInput simulator
            (CodePrefixRecognizerStageCode encoded stage) := by
  constructor
  · intro h
    rcases h with ⟨budget, hbudget⟩
    rcases
        (codePrefixStageSearchControllerProgramDecidable_run_eq_some_iff
          simulator encoded budget).mp hbudget with
      ⟨D, input, stage, fuel, _hstage, _hfuel, hdecode, hsim⟩
    exact
      ⟨D, input, stage, hdecode,
        TuringMachine.halts_on_input_in_to_halts_on_input hsim⟩
  · intro h
    rcases h with ⟨D, input, stage, hdecode, hsim⟩
    rcases TuringMachine.halts_on_input_to_halts_on_input_in hsim with
      ⟨fuel, hsimFuel⟩
    refine ⟨stage + fuel, ?_⟩
    exact
      (codePrefixStageSearchControllerProgramDecidable_run_eq_some_iff
        simulator encoded (stage + fuel)).mpr
        ⟨D, input, stage, fuel, by lia, by lia, hdecode, hsimFuel⟩

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
      lia
    have hfuelLe : fuel ≤ stage + fuel := by
      lia
    simp [codePrefixStageSearchControllerProgram, hdecode]
    exact
      ⟨D, input, stage, hstageLe, fuel, hfuelLe, rfl, rfl, hsimFuel⟩

theorem codePrefixStageSearchControllerProgramDecidable_accepts_program
    [DecidableEq simulatorState]
    (simulator : TuringMachine MachineCodeSymbol simulatorState)
    (encoded : Word MachineCodeSymbol) :
    ProgramHaltsWithOutput
        (codePrefixStageSearchControllerProgramDecidable simulator)
        encoded [] <->
      ProgramHaltsWithOutput
        (codePrefixStageSearchControllerProgram simulator) encoded [] := by
  rw [codePrefixStageSearchControllerProgramDecidable_accepts,
    codePrefixStageSearchControllerProgram_accepts]

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

theorem codePrefixStageSearchControllerProgramDecidable_accepts_of_simulatorSpec
    [DecidableEq simulatorState]
    (simulator : TuringMachine MachineCodeSymbol simulatorState)
    (hsimulator : CodePrefixDecodedBoundedSimulatorSpec simulator)
    (encoded : Word MachineCodeSymbol) :
    ProgramHaltsWithOutput
        (codePrefixStageSearchControllerProgramDecidable simulator)
        encoded [] <->
      CodePrefixDecodedStageSearchAccepts encoded := by
  rw [codePrefixStageSearchControllerProgramDecidable_accepts]
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

theorem codePrefixStageSearchControllerProgramDecidable_accepts_recognizerProgram
    [DecidableEq simulatorState]
    (simulator : TuringMachine MachineCodeSymbol simulatorState)
    (hsimulator : CodePrefixDecodedBoundedSimulatorSpec simulator)
    (encoded : Word MachineCodeSymbol) :
    ProgramHaltsWithOutput
        (codePrefixStageSearchControllerProgramDecidable simulator)
        encoded [] <->
      ProgramHaltsWithOutput CodePrefixRecognizerProgram encoded [] :=
  Iff.trans
    (codePrefixStageSearchControllerProgramDecidable_accepts_of_simulatorSpec
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

def CodePrefixStageSearchControllerProgramDecidableCompilerConstruction :
    Prop :=
  forall {simulatorState : Type} [DecidableEq simulatorState]
    (simulator : TuringMachine MachineCodeSymbol simulatorState),
      exists searcherState : Type,
      exists searcher : TuringMachine MachineCodeSymbol searcherState,
        forall encoded : Word MachineCodeSymbol,
          TuringMachine.HaltsOnInput searcher encoded <->
            ProgramHaltsWithOutput
              (codePrefixStageSearchControllerProgramDecidable simulator)
              encoded []

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

def CodePrefixStageSearchControllerBudgetCheckerDecidableSpec
    {simulatorState checkerState : Type} [DecidableEq simulatorState]
    (simulator : TuringMachine MachineCodeSymbol simulatorState)
    (checker : TuringMachine MachineCodeSymbol checkerState) : Prop :=
  forall encoded : Word MachineCodeSymbol,
  forall budget : Nat,
    TuringMachine.HaltsOnInput checker
        (CodePrefixRecognizerStageCode encoded budget) <->
      (codePrefixStageSearchControllerProgramDecidable simulator).run
          encoded budget = some []

def CodePrefixStageSearchControllerBudgetCheckerConstruction
    {simulatorState : Type}
    (simulator : TuringMachine MachineCodeSymbol simulatorState) : Prop :=
  exists checkerState : Type,
  exists checker : TuringMachine MachineCodeSymbol checkerState,
    CodePrefixStageSearchControllerBudgetCheckerSpec simulator checker

def CodePrefixStageSearchControllerBudgetCheckerDecidableConstruction
    {simulatorState : Type} [DecidableEq simulatorState]
    (simulator : TuringMachine MachineCodeSymbol simulatorState) : Prop :=
  exists checkerState : Type,
  exists checker : TuringMachine MachineCodeSymbol checkerState,
    CodePrefixStageSearchControllerBudgetCheckerDecidableSpec
      simulator checker

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

def CodePrefixStageSearchControllerBudgetSearchDecidableSequencingConstruction :
    Prop :=
  forall {simulatorState checkerState : Type}
    [DecidableEq simulatorState]
    (simulator : TuringMachine MachineCodeSymbol simulatorState)
    (checker : TuringMachine MachineCodeSymbol checkerState),
    CodePrefixStageSearchControllerBudgetCheckerDecidableSpec
      simulator checker ->
      exists searcherState : Type,
      exists searcher : TuringMachine MachineCodeSymbol searcherState,
        forall encoded : Word MachineCodeSymbol,
          TuringMachine.HaltsOnInput searcher encoded <->
            ProgramHaltsWithOutput
              (codePrefixStageSearchControllerProgramDecidable simulator)
              encoded []

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

theorem codePrefixStageSearchControllerProgramDecidableCompilerConstruction_of_components
    (hchecker :
      forall {simulatorState : Type} [DecidableEq simulatorState]
        (simulator : TuringMachine MachineCodeSymbol simulatorState),
          CodePrefixStageSearchControllerBudgetCheckerDecidableConstruction
            simulator)
    (hsequence :
      CodePrefixStageSearchControllerBudgetSearchDecidableSequencingConstruction) :
    CodePrefixStageSearchControllerProgramDecidableCompilerConstruction := by
  intro simulatorState hdec simulator
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

theorem codePrefixStageSearchControllerProgramDecidable_run_eq_some_iff_program
    [DecidableEq simulatorState]
    (simulator : TuringMachine MachineCodeSymbol simulatorState)
    (encoded : Word MachineCodeSymbol) (budget : Nat) :
    (codePrefixStageSearchControllerProgramDecidable simulator).run
        encoded budget = some [] <->
      (codePrefixStageSearchControllerProgram simulator).run
        encoded budget = some [] := by
  rw [codePrefixStageSearchControllerProgramDecidable_run_eq_some_iff,
    codePrefixStageSearchControllerProgram_run_eq_some_iff]

theorem codePrefixStageSearchControllerBudgetCheckerSpec_of_decidableSpec
    [DecidableEq simulatorState]
    {simulator : TuringMachine MachineCodeSymbol simulatorState}
    {checker : TuringMachine MachineCodeSymbol checkerState}
    (hchecker :
      CodePrefixStageSearchControllerBudgetCheckerDecidableSpec
        simulator checker) :
    CodePrefixStageSearchControllerBudgetCheckerSpec simulator checker := by
  intro encoded budget
  exact Iff.trans (hchecker encoded budget)
    (codePrefixStageSearchControllerProgramDecidable_run_eq_some_iff_program
      simulator encoded budget)

theorem codePrefixStageSearchControllerBudgetCheckerConstruction_of_decidable
    [DecidableEq simulatorState]
    {simulator : TuringMachine MachineCodeSymbol simulatorState}
    (hchecker :
      CodePrefixStageSearchControllerBudgetCheckerDecidableConstruction
        simulator) :
    CodePrefixStageSearchControllerBudgetCheckerConstruction simulator := by
  rcases hchecker with ⟨checkerState, checker, hcheckerSpec⟩
  exact
    ⟨checkerState, checker,
      codePrefixStageSearchControllerBudgetCheckerSpec_of_decidableSpec
        hcheckerSpec⟩

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


end Computability
end FoC

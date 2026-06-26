import FoC.Computability.Compiler.UniversalAndRanges.Basic

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

/-- Finite-machine leaf for checking one encoded input at one budget. -/
theorem codePrefixStageSearchControllerBudgetCheckerConstruction_core :
    forall {simulatorState : Type}
      (simulator : TuringMachine MachineCodeSymbol simulatorState),
        CodePrefixStageSearchControllerBudgetCheckerConstruction simulator := by
  sorry

/-- Finite-machine leaf for enumerating budgets using a bounded checker. -/
theorem codePrefixStageSearchControllerBudgetSearchSequencingConstruction_core :
    CodePrefixStageSearchControllerBudgetSearchSequencingConstruction := by
  sorry

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

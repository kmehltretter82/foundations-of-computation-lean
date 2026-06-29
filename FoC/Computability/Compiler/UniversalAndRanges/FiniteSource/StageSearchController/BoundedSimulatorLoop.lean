import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.StageSearchController.Basic
import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.StageSearchController.GeneratedCallSearch

set_option doc.verso true

namespace FoC
namespace Computability

open Languages

universe uStage uDescription uSimulator

/--
Canonical-input wrapper obligation for the bounded simulator loop.  The
machine parses a {name}`CodePrefixRecognizerStageCode` input and dispatches
the preserved canonical input to the supplied pair runner.
-/
def CodePrefixStageSearchControllerBudgetCheckerBoundedSimulatorCanonicalInputParserObligation
    {pairState : Type uStage}
    (pairRunner : TuringMachine MachineCodeSymbol pairState) : Prop :=
  exists runnerState : Type,
  exists runner : TuringMachine MachineCodeSymbol runnerState,
    forall tokens : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput runner tokens <->
        exists budget : Nat,
        exists encoded : Word MachineCodeSymbol,
          tokens = CodePrefixRecognizerStageCode encoded budget ∧
            TuringMachine.HaltsOnInput pairRunner
              (CodePrefixRecognizerStageCode encoded budget)

/--
Bounded pair-loop obligation for the canonical bounded simulator loop.  The
machine enumerates bounded {lit}`(checkedStage, fuel)` pairs, rebuilds each
checked stage-code input, and runs the supplied simulator for the selected
fuel.
-/
def CodePrefixStageSearchControllerBudgetCheckerBoundedSimulatorPairLoopObligation
    {simulatorState : Type uSimulator}
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
Finite-machine leaf for parsing canonical stage-code input before invoking a
bounded pair runner.
-/
theorem codePrefixStageSearchControllerBudgetCheckerBoundedSimulatorCanonicalInputParserFiniteLeaf
    {pairState : Type}
    (pairRunner : TuringMachine MachineCodeSymbol pairState) :
    CodePrefixStageSearchControllerBudgetCheckerBoundedSimulatorCanonicalInputParserObligation
      pairRunner := by
  exact boundedSimulatorCanonicalInputParserMachine_construction pairRunner

/--
Finite-machine leaf for the bounded pair loop.  This is the transition-table
work that enumerates bounded pairs, rebuilds checked stage-code inputs, and
runs the supplied simulator for the selected fuel.
-/
theorem codePrefixStageSearchControllerBudgetCheckerBoundedSimulatorPairLoopFiniteLeaf
    {simulatorState : Type uSimulator}
    (simulator : TuringMachine MachineCodeSymbol simulatorState) :
    CodePrefixStageSearchControllerBudgetCheckerBoundedSimulatorPairLoopObligation
      simulator := by
  rcases codePrefixExactFuelRunnerFiniteLeaf simulator with
    ⟨selectedState, selected, hselected⟩
  rcases codePrefixBoundedNestedPairEnumeratorFiniteLeaf selected with
    ⟨runnerState, runner, hrunner⟩
  refine ⟨runnerState, runner, ?_⟩
  intro encoded budget
  constructor
  · intro hhalt
    rcases (hrunner encoded budget).mp hhalt with
      ⟨checkedStage, fuel, hcheckedStage, hfuel, hselectedHalt⟩
    exact
      ⟨checkedStage, fuel, hcheckedStage, hfuel,
        (hselected
          (CodePrefixRecognizerStageCode encoded checkedStage) fuel).mp
          (by
            simpa [NestedCodePrefixRecognizerStageCode] using
              hselectedHalt)⟩
  · intro htarget
    rcases htarget with
      ⟨checkedStage, fuel, hcheckedStage, hfuel, hsimulator⟩
    exact (hrunner encoded budget).mpr
      ⟨checkedStage, fuel, hcheckedStage, hfuel, by
        simpa [NestedCodePrefixRecognizerStageCode] using
          (hselected
            (CodePrefixRecognizerStageCode encoded checkedStage) fuel).mpr
            hsimulator⟩

/--
Adapter from the parser wrapper and pair-loop construction to the canonical
raw-loop contract.
-/
theorem codePrefixStageSearchControllerBudgetCheckerBoundedSimulatorCanonicalRawLoopFiniteLeaf
    {simulatorState : Type uSimulator}
    (simulator : TuringMachine MachineCodeSymbol simulatorState) :
    CodePrefixStageSearchControllerBudgetCheckerBoundedSimulatorCanonicalRawLoopObligation
      simulator := by
  rcases
      codePrefixStageSearchControllerBudgetCheckerBoundedSimulatorPairLoopFiniteLeaf
        simulator with
    ⟨pairState, pairRunner, hpairRunner⟩
  rcases
      codePrefixStageSearchControllerBudgetCheckerBoundedSimulatorCanonicalInputParserFiniteLeaf
        pairRunner with
    ⟨runnerState, runner, hrunner⟩
  refine ⟨runnerState, runner, ?_⟩
  intro tokens
  constructor
  · intro hhalt
    rcases (hrunner tokens).mp hhalt with
      ⟨budget, encoded, htokens, hpair⟩
    rcases (hpairRunner encoded budget).mp hpair with
      ⟨checkedStage, fuel, hcheckedStage, hfuel, hsimulator⟩
    exact
      ⟨budget, encoded, checkedStage, fuel, htokens,
        hcheckedStage, hfuel, hsimulator⟩
  · intro htarget
    rcases htarget with
      ⟨budget, encoded, checkedStage, fuel, htokens,
        hcheckedStage, hfuel, hsimulator⟩
    exact (hrunner tokens).mpr
      ⟨budget, encoded, htokens,
        (hpairRunner encoded budget).mpr
          ⟨checkedStage, fuel, hcheckedStage, hfuel, hsimulator⟩⟩

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

end Computability
end FoC

import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.StageSearchController.Basic

set_option doc.verso true

namespace FoC
namespace Computability

open Languages

universe uStage uDescription uSimulator

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


end Computability
end FoC

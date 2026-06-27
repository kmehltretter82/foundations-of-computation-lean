import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.StageSearchController.DescriptionRunner

set_option doc.verso true

namespace FoC
namespace Computability

open Languages

universe uStage uDescription uSimulator

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


end Computability
end FoC

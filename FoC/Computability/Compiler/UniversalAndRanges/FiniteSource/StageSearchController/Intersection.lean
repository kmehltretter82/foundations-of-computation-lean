import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.StageSearchController.DescriptionRunner
import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.StageSearchController.GeneratedCallSearch

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

/--
Nested fuel/input code used internally by the intersection driver.  The outer
stage code carries the left fuel; the inner stage code carries the right fuel
and the preserved common input.
-/
def codePrefixStageSearchControllerBudgetCheckerIntersectionFuelPairCode
    (input : Word MachineCodeSymbol) (leftFuel rightFuel : Nat) :
    Word MachineCodeSymbol :=
  CodePrefixRecognizerStageCode
    (CodePrefixRecognizerStageCode input rightFuel) leftFuel

theorem codePrefixStageSearchControllerBudgetCheckerIntersectionFuelPairCode_eq
    (input : Word MachineCodeSymbol) (leftFuel rightFuel : Nat) :
    codePrefixStageSearchControllerBudgetCheckerIntersectionFuelPairCode
        input leftFuel rightFuel =
      NestedCodePrefixRecognizerStageCode input rightFuel leftFuel := by
  rfl

theorem codePrefixStageSearchControllerBudgetCheckerIntersectionFuelPairCode_injective
    {input₁ input₂ : Word MachineCodeSymbol}
    {leftFuel₁ leftFuel₂ rightFuel₁ rightFuel₂ : Nat}
    (h :
      codePrefixStageSearchControllerBudgetCheckerIntersectionFuelPairCode
          input₁ leftFuel₁ rightFuel₁ =
        codePrefixStageSearchControllerBudgetCheckerIntersectionFuelPairCode
          input₂ leftFuel₂ rightFuel₂) :
    leftFuel₁ = leftFuel₂ ∧ rightFuel₁ = rightFuel₂ ∧ input₁ = input₂ := by
  simpa [codePrefixStageSearchControllerBudgetCheckerIntersectionFuelPairCode_eq]
    using nestedCodePrefixRecognizerStageCode_injective
      (input₁ := input₁) (input₂ := input₂)
      (inner₁ := rightFuel₁) (inner₂ := rightFuel₂)
      (outer₁ := leftFuel₁) (outer₂ := leftFuel₂) h

/--
Selected-fuel runner for intersection.  The machine unpacks a fixed pair of
fuel bounds and runs the left and right recognizers on the same preserved
input for those exact bounds.
-/
def CodePrefixStageSearchControllerBudgetCheckerIntersectionSelectedFuelRunObligation :
    Prop :=
  forall {leftState : Type uStage} {rightState : Type uDescription}
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState),
      exists selectedState : Type,
      exists selected : TuringMachine MachineCodeSymbol selectedState,
        forall input : Word MachineCodeSymbol,
        forall leftFuel : Nat,
        forall rightFuel : Nat,
          TuringMachine.HaltsOnInput selected
              (codePrefixStageSearchControllerBudgetCheckerIntersectionFuelPairCode
                input leftFuel rightFuel) <->
            TuringMachine.HaltsOnInputIn left leftFuel input ∧
              TuringMachine.HaltsOnInputIn right rightFuel input

/--
Fuel-pair enumerator for intersection.  The machine preserves the common
input, enumerates finite left/right fuel pairs, and calls the supplied
selected-fuel runner on the nested fuel/input code.
-/
def CodePrefixStageSearchControllerBudgetCheckerIntersectionFuelPairEnumeratorObligation
    {selectedState : Type uSimulator}
    (selected : TuringMachine MachineCodeSymbol selectedState) : Prop :=
  exists bothState : Type,
  exists both : TuringMachine MachineCodeSymbol bothState,
    forall input : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput both input <->
        exists leftFuel : Nat,
        exists rightFuel : Nat,
          TuringMachine.HaltsOnInput selected
            (codePrefixStageSearchControllerBudgetCheckerIntersectionFuelPairCode
              input leftFuel rightFuel)

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
  exact
    exists_pair_haltsOnInputIn_and_iff_haltsOnInput_and
      left right input

/--
Finite-machine leaf for the selected-fuel runner used by recognizer
intersection.
-/
theorem codePrefixStageSearchControllerBudgetCheckerIntersectionSelectedFuelRunFiniteLeaf :
    CodePrefixStageSearchControllerBudgetCheckerIntersectionSelectedFuelRunObligation := by
  intro leftState rightState left right
  rcases codePrefixExactFuelProductRunnerFiniteLeaf left right with
    ⟨selectedState, selected, hselected⟩
  refine ⟨selectedState, selected, ?_⟩
  intro input leftFuel rightFuel
  simpa [codePrefixStageSearchControllerBudgetCheckerIntersectionFuelPairCode,
    NestedCodePrefixRecognizerStageCode] using
    hselected input leftFuel rightFuel

/--
Finite-machine leaf for the fuel-pair enumerator used by recognizer
intersection.
-/
theorem codePrefixStageSearchControllerBudgetCheckerIntersectionFuelPairEnumeratorFiniteLeaf
    {selectedState : Type uSimulator}
    (selected : TuringMachine MachineCodeSymbol selectedState) :
    CodePrefixStageSearchControllerBudgetCheckerIntersectionFuelPairEnumeratorObligation
      selected := by
  rcases codePrefixNestedPairEnumeratorFiniteLeaf selected with
    ⟨bothState, both, hboth⟩
  refine ⟨bothState, both, ?_⟩
  intro input
  constructor
  · intro hhalt
    rcases (hboth input).mp hhalt with
      ⟨rightFuel, leftFuel, hselected⟩
    exact ⟨leftFuel, rightFuel, by
      simpa [codePrefixStageSearchControllerBudgetCheckerIntersectionFuelPairCode,
        NestedCodePrefixRecognizerStageCode] using hselected⟩
  · intro htarget
    rcases htarget with ⟨leftFuel, rightFuel, hselected⟩
    exact (hboth input).mpr
      ⟨rightFuel, leftFuel, by
        simpa [codePrefixStageSearchControllerBudgetCheckerIntersectionFuelPairCode,
          NestedCodePrefixRecognizerStageCode] using hselected⟩

/--
Adapter from the selected-fuel runner and fuel-pair enumerator to the
bounded-pair driver used by recognizer intersection.
-/
theorem codePrefixStageSearchControllerBudgetCheckerIntersectionBoundedPairObligation_core :
    CodePrefixStageSearchControllerBudgetCheckerIntersectionBoundedPairObligation := by
  intro leftState rightState left right
  rcases
      codePrefixStageSearchControllerBudgetCheckerIntersectionSelectedFuelRunFiniteLeaf
        left right with
    ⟨selectedState, selected, hselected⟩
  rcases
      codePrefixStageSearchControllerBudgetCheckerIntersectionFuelPairEnumeratorFiniteLeaf
        selected with
    ⟨bothState, both, hboth⟩
  refine ⟨bothState, both, ?_⟩
  intro input
  constructor
  · intro hhalt
    rcases (hboth input).mp hhalt with
      ⟨leftFuel, rightFuel, hselectedHalt⟩
    exact
      ⟨leftFuel, rightFuel,
        (hselected input leftFuel rightFuel).mp hselectedHalt⟩
  · intro htarget
    rcases htarget with
      ⟨leftFuel, rightFuel, hleft, hright⟩
    exact (hboth input).mpr
      ⟨leftFuel, rightFuel,
        (hselected input leftFuel rightFuel).mpr ⟨hleft, hright⟩⟩

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

import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.StageSearchController.Intersection
import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.StageSearchController.GeneratedCallSearch

set_option doc.verso true

namespace FoC
namespace Computability

open Languages

universe uStage uDescription uSimulator

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
  exact
    exists_bounded_pair_iff_exists_pair
      (fun budget fuel =>
        TuringMachine.HaltsOnInputIn checker fuel
          (CodePrefixRecognizerStageCode encoded budget))

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
    {attemptState : Type uStage}
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
Nested limit/fuel code used internally by the raw outer-loop searcher.  The
outer stage code carries the selected attempt fuel; the inner stage code
carries the generated outer limit and the preserved raw input.
-/
def codePrefixStageSearchControllerBudgetFuelOuterLoopLimitFuelCode
    (encoded : Word MachineCodeSymbol) (limit fuel : Nat) :
    Word MachineCodeSymbol :=
  CodePrefixRecognizerStageCode
    (CodePrefixRecognizerStageCode encoded limit) fuel

theorem codePrefixStageSearchControllerBudgetFuelOuterLoopLimitFuelCode_eq
    (encoded : Word MachineCodeSymbol) (limit fuel : Nat) :
    codePrefixStageSearchControllerBudgetFuelOuterLoopLimitFuelCode
        encoded limit fuel =
      NestedCodePrefixRecognizerStageCode encoded limit fuel := by
  rfl

theorem codePrefixStageSearchControllerBudgetFuelOuterLoopLimitFuelCode_injective
    {encoded₁ encoded₂ : Word MachineCodeSymbol}
    {limit₁ limit₂ fuel₁ fuel₂ : Nat}
    (h :
      codePrefixStageSearchControllerBudgetFuelOuterLoopLimitFuelCode
          encoded₁ limit₁ fuel₁ =
        codePrefixStageSearchControllerBudgetFuelOuterLoopLimitFuelCode
          encoded₂ limit₂ fuel₂) :
    fuel₁ = fuel₂ ∧ limit₁ = limit₂ ∧ encoded₁ = encoded₂ := by
  simpa [codePrefixStageSearchControllerBudgetFuelOuterLoopLimitFuelCode_eq]
    using nestedCodePrefixRecognizerStageCode_injective
      (input₁ := encoded₁) (input₂ := encoded₂)
      (inner₁ := limit₁) (inner₂ := limit₂)
      (outer₁ := fuel₁) (outer₂ := fuel₂) h

/--
Selected-attempt runner for the raw outer-loop search.  The machine unpacks a
fixed generated limit and attempt fuel, rebuilds the corresponding
stage-coded attempt input, and simulates the supplied attempt machine for that
fuel.
-/
def CodePrefixStageSearchControllerBudgetFuelOuterLoopSelectedAttemptObligation
    {attemptState : Type uStage}
    (attempt : TuringMachine MachineCodeSymbol attemptState) : Prop :=
  exists selectedState : Type,
  exists selected : TuringMachine MachineCodeSymbol selectedState,
    forall encoded : Word MachineCodeSymbol,
    forall limit : Nat,
    forall fuel : Nat,
      TuringMachine.HaltsOnInput selected
          (codePrefixStageSearchControllerBudgetFuelOuterLoopLimitFuelCode
            encoded limit fuel) <->
        TuringMachine.HaltsOnInputIn attempt fuel
          (CodePrefixRecognizerStageCode encoded limit)

/--
Limit/fuel enumerator for the raw outer-loop search.  The machine preserves
the raw encoded input, enumerates generated outer limits and attempt fuels,
and calls the supplied selected-attempt runner on the nested code.
-/
def CodePrefixStageSearchControllerBudgetFuelOuterLoopLimitFuelEnumeratorObligation
    {selectedState : Type uSimulator}
    (selected : TuringMachine MachineCodeSymbol selectedState) : Prop :=
  exists searcherState : Type,
  exists searcher : TuringMachine MachineCodeSymbol searcherState,
    forall encoded : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput searcher encoded <->
        exists limit : Nat,
        exists fuel : Nat,
          TuringMachine.HaltsOnInput selected
            (codePrefixStageSearchControllerBudgetFuelOuterLoopLimitFuelCode
              encoded limit fuel)

/--
Finite-machine leaf for the selected-attempt runner used by the raw
outer-loop fuel search.
-/
theorem codePrefixStageSearchControllerBudgetFuelOuterLoopSelectedAttemptFiniteLeaf
    {attemptState : Type uStage}
    (attempt : TuringMachine MachineCodeSymbol attemptState) :
    CodePrefixStageSearchControllerBudgetFuelOuterLoopSelectedAttemptObligation
      attempt := by
  rcases codePrefixExactFuelRunnerFiniteLeaf attempt with
    ⟨selectedState, selected, hselected⟩
  refine ⟨selectedState, selected, ?_⟩
  intro encoded limit fuel
  simpa [codePrefixStageSearchControllerBudgetFuelOuterLoopLimitFuelCode]
    using
      codePrefixExactFuelRunner_haltsOnNested_iff
        hselected encoded limit fuel

/--
Finite-machine leaf for the limit/fuel enumerator used by the raw outer-loop
fuel search.
-/
theorem codePrefixStageSearchControllerBudgetFuelOuterLoopLimitFuelEnumeratorFiniteLeaf
    {selectedState : Type uSimulator}
    (selected : TuringMachine MachineCodeSymbol selectedState) :
    CodePrefixStageSearchControllerBudgetFuelOuterLoopLimitFuelEnumeratorObligation
      selected := by
  rcases codePrefixNestedPairEnumeratorFiniteLeaf selected with
    ⟨searcherState, searcher, hsearcher⟩
  refine ⟨searcherState, searcher, ?_⟩
  intro encoded
  constructor
  · intro hhalt
    rcases (hsearcher encoded).mp hhalt with
      ⟨limit, fuel, hselected⟩
    exact ⟨limit, fuel, by
      simpa [codePrefixStageSearchControllerBudgetFuelOuterLoopLimitFuelCode,
        NestedCodePrefixRecognizerStageCode] using hselected⟩
  · intro htarget
    rcases htarget with ⟨limit, fuel, hselected⟩
    exact (hsearcher encoded).mpr
      ⟨limit, fuel, by
        simpa [codePrefixStageSearchControllerBudgetFuelOuterLoopLimitFuelCode,
          NestedCodePrefixRecognizerStageCode] using hselected⟩

/--
Adapter from the selected-attempt runner and limit/fuel enumerator to the raw
outer-loop fuel-search contract.
-/
theorem codePrefixStageSearchControllerBudgetFuelOuterLoopFuelSearchFiniteLeaf
    {attemptState : Type uStage}
    (attempt : TuringMachine MachineCodeSymbol attemptState) :
    CodePrefixStageSearchControllerBudgetFuelOuterLoopFuelSearchObligation
      attempt := by
  exact codePrefixNestedExactFuelSearchFiniteLeaf attempt

/--
Global wrapper for the raw stage-code/fuel search construction.  The concrete
transition-table obligation is the per-machine outer-loop fuel-search leaf.
-/
theorem codePrefixStageSearchControllerBudgetFuelEnumeratorConstruction_core :
    CodePrefixStageSearchControllerBudgetFuelEnumeratorConstruction := by
  intro checkerState checker
  exact codePrefixNestedExactFuelSearchFiniteLeaf checker

/--
Concrete finite-machine leaf for the raw outer-loop fuel search.  The shared
generated-call helper supplies the dovetail over generated outer limits and
attempt fuels.
-/
theorem codePrefixStageSearchControllerBudgetFuelOuterLoopFuelSearchObligation_core
    {attemptState : Type}
    (attempt : TuringMachine MachineCodeSymbol attemptState) :
    CodePrefixStageSearchControllerBudgetFuelOuterLoopFuelSearchObligation
      attempt := by
  exact codePrefixNestedExactFuelSearchFiniteLeaf attempt

/--
Finite-machine leaf for the bounded attempt phase of the raw budget/fuel
driver.
-/
theorem codePrefixStageSearchControllerBudgetFuelBoundedAttemptObligation_core
    {checkerState : Type}
    (checker : TuringMachine MachineCodeSymbol checkerState) :
    CodePrefixStageSearchControllerBudgetFuelBoundedAttemptObligation
      checker := by
  exact codePrefixBoundedNestedExactFuelSearchFiniteLeaf checker

/--
Finite-machine leaf for the unbounded outer-loop phase of the raw budget/fuel
driver.
-/
theorem codePrefixStageSearchControllerBudgetFuelOuterLoopObligation_core
    {attemptState : Type}
    (attempt : TuringMachine MachineCodeSymbol attemptState) :
    CodePrefixStageSearchControllerBudgetFuelOuterLoopObligation
      attempt := by
  exact codePrefixNestedHaltingSearchFiniteLeaf attempt

/--
Concrete finite-machine construction for the raw budget/fuel dovetail driver.
The shared generated-call helper enumerates budget/fuel pairs, rebuilds the
stage-coded checker input, and runs the checker for the selected fuel.
-/
theorem codePrefixStageSearchControllerBudgetFuelRawDriverObligation_core
    {checkerState : Type}
    (checker : TuringMachine MachineCodeSymbol checkerState) :
    CodePrefixStageSearchControllerBudgetFuelRawDriverObligation
      checker := by
  exact codePrefixNestedExactFuelSearchFiniteLeaf checker

/--
Finite-machine construction for the budget-only searcher.  The remaining
transition-table work is the unbounded budget dovetailer that rebuilds
{name}`CodePrefixRecognizerStageCode` inputs and runs the checker.
-/
theorem codePrefixStageSearchControllerBudgetRawSearchObligation_core
    {checkerState : Type}
    (checker : TuringMachine MachineCodeSymbol checkerState) :
    CodePrefixStageSearchControllerBudgetRawSearchObligation checker := by
  exact codePrefixNestedHaltingSearchFiniteLeaf checker

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
  exact
    exists_bounded_pair_haltsOnInputIn_iff_exists_haltsOnInput
      checker
      (fun budget => CodePrefixRecognizerStageCode encoded budget)

/-- Generic generated-call searcher for budget enumeration. -/
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
  exact codePrefixNestedHaltingSearchFiniteLeaf checker

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

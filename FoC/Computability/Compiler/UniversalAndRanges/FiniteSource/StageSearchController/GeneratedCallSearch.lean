import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.StageSearchController.GeneratedCallHandoff

set_option doc.verso true

namespace FoC
namespace Computability

open Languages

universe uStage uDescription uSimulator

/-!
# Generated stage-code calls

Shared shape lemmas for controller helpers that generate a fresh unary stage
code around an already stage-coded input.  The concrete finite drivers use
this nested form for selected generated calls, fuel-pair runners, and bounded
outer-loop attempts.
-/

/-- Nested stage code: an inner generated bound over a preserved payload, then
an outer generated bound around that whole call. -/
def NestedCodePrefixRecognizerStageCode
    (input : Word MachineCodeSymbol) (inner outer : Nat) :
    Word MachineCodeSymbol :=
  CodePrefixRecognizerStageCode
    (CodePrefixRecognizerStageCode input inner) outer

theorem nestedCodePrefixRecognizerStageCode_eq
    (input : Word MachineCodeSymbol) (inner outer : Nat) :
    NestedCodePrefixRecognizerStageCode input inner outer =
      CodePrefixRecognizerStageCode
        (CodePrefixRecognizerStageCode input inner) outer := by
  rfl

theorem nestedCodePrefixRecognizerStageCode_decodeNat_outer
    (input : Word MachineCodeSymbol) (inner outer : Nat) :
    MachineDescription.decodeNat
        (NestedCodePrefixRecognizerStageCode input inner outer) =
      some (outer, CodePrefixRecognizerStageCode input inner) := by
  simp [NestedCodePrefixRecognizerStageCode,
    codePrefixRecognizerStageCode_decodeNat]

theorem nestedCodePrefixRecognizerStageCode_decodeNat_inner
    (input : Word MachineCodeSymbol) (inner : Nat) :
    MachineDescription.decodeNat
        (CodePrefixRecognizerStageCode input inner) =
      some (inner, input) := by
  simp [codePrefixRecognizerStageCode_decodeNat]

theorem nestedCodePrefixRecognizerStageCode_injective
    {input₁ input₂ : Word MachineCodeSymbol}
    {inner₁ inner₂ outer₁ outer₂ : Nat}
    (h :
      NestedCodePrefixRecognizerStageCode input₁ inner₁ outer₁ =
        NestedCodePrefixRecognizerStageCode input₂ inner₂ outer₂) :
    outer₁ = outer₂ ∧ inner₁ = inner₂ ∧ input₁ = input₂ := by
  rcases
      codePrefixRecognizerStageCode_injective
        (by
          simpa [NestedCodePrefixRecognizerStageCode] using h) with
    ⟨houter, hinnerCode⟩
  rcases codePrefixRecognizerStageCode_injective hinnerCode with
    ⟨hinner, hinput⟩
  exact ⟨houter, hinner, hinput⟩

theorem nestedCodePrefixRecognizerStageCode_eq_iff
    {input₁ input₂ : Word MachineCodeSymbol}
    {inner₁ inner₂ outer₁ outer₂ : Nat} :
    NestedCodePrefixRecognizerStageCode input₁ inner₁ outer₁ =
        NestedCodePrefixRecognizerStageCode input₂ inner₂ outer₂ <->
      outer₁ = outer₂ ∧ inner₁ = inner₂ ∧ input₁ = input₂ := by
  constructor
  · exact nestedCodePrefixRecognizerStageCode_injective
  · intro h
    rcases h with ⟨houter, hinner, hinput⟩
    subst outer₂
    subst inner₂
    subst input₂
    rfl

/--
Ordinary generated-call parser construction.  This is the reusable wrapper
already supplied by {module}`FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.StageSearchController.GeneratedCallHandoff`:
it parses a generated stage-code prefix and invokes the supplied runner on the
rebuilt input.  It does not expose an exact step count for the wrapped runner.
-/
def CodePrefixGeneratedCallParserConstruction
    {selectedState : Type u}
    (selected : TuringMachine MachineCodeSymbol selectedState) : Prop :=
  exists runnerState : Type,
  exists runner : TuringMachine MachineCodeSymbol runnerState,
    forall tokens : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput runner tokens <->
        exists fuel : Nat,
        exists input : Word MachineCodeSymbol,
          tokens = CodePrefixRecognizerStageCode input fuel ∧
            TuringMachine.HaltsOnInput selected
              (CodePrefixRecognizerStageCode input fuel)

/--
Named adapter for the ordinary generated-call parser.  Keep this separate from
{lit}`CodePrefixExactFuelRunnerConstruction`: the exact-fuel contract below
requires {name}`TuringMachine.HaltsOnInputIn`, while this parser preserves only
ordinary halting of the wrapped machine.
-/
theorem codePrefixGeneratedCallParserConstruction_finite
    {selectedState : Type u}
    (selected : TuringMachine MachineCodeSymbol selectedState) :
    CodePrefixGeneratedCallParserConstruction selected := by
  rcases
      boundedSimulatorCanonicalInputParserMachine_construction selected with
    ⟨runnerState, runner, hrunner⟩
  refine
    ⟨Fin runner.statesFinite.elems.length,
      TuringMachine.indexed runner, ?_⟩
  intro tokens
  exact
    Iff.trans
      (TuringMachine.indexed_haltsOnInput_iff runner tokens)
      (hrunner tokens)

/--
Exact-fuel generated-call runner.  The concrete machine parses a generated
stage code, treats the parsed natural as the exact simulation fuel, rebuilds
the payload as the wrapped machine's input, and halts precisely when the
wrapped machine halts in that exact number of steps.
-/
def CodePrefixExactFuelRunnerConstruction
    {machineState : Type u}
    (M : TuringMachine MachineCodeSymbol machineState) : Prop :=
  exists runnerState : Type,
  exists runner : TuringMachine MachineCodeSymbol runnerState,
    forall input : Word MachineCodeSymbol,
    forall fuel : Nat,
      TuringMachine.HaltsOnInput runner
          (CodePrefixRecognizerStageCode input fuel) <->
        TuringMachine.HaltsOnInputIn M fuel input

/--
Finite-machine leaf for {name}`CodePrefixExactFuelRunnerConstruction`.
This is the shared exact-fuel runner promised by the generated-call helper
plan.
-/
theorem codePrefixExactFuelRunnerFiniteLeaf
    {machineState : Type u}
    (M : TuringMachine MachineCodeSymbol machineState) :
    CodePrefixExactFuelRunnerConstruction M := by
  sorry

/--
Specialization of an exact-fuel runner to a nested generated call.  The outer
bound is the exact fuel for the wrapped machine, and the inner generated call
is preserved as the wrapped input.
-/
theorem codePrefixExactFuelRunner_haltsOnNested_iff
    {machineState : Type u} {runnerState : Type v}
    {M : TuringMachine MachineCodeSymbol machineState}
    {runner : TuringMachine MachineCodeSymbol runnerState}
    (hrunner :
      forall input : Word MachineCodeSymbol,
      forall fuel : Nat,
        TuringMachine.HaltsOnInput runner
            (CodePrefixRecognizerStageCode input fuel) <->
          TuringMachine.HaltsOnInputIn M fuel input)
    (input : Word MachineCodeSymbol) (inner outer : Nat) :
    TuringMachine.HaltsOnInput runner
        (NestedCodePrefixRecognizerStageCode input inner outer) <->
      TuringMachine.HaltsOnInputIn M outer
        (CodePrefixRecognizerStageCode input inner) := by
  simpa [NestedCodePrefixRecognizerStageCode] using
    hrunner (CodePrefixRecognizerStageCode input inner) outer

/--
Unbounded search over generated inner inputs and exact outer fuels for a
wrapped machine.
-/
def CodePrefixNestedExactFuelSearchConstruction
    {machineState : Type u}
    (M : TuringMachine MachineCodeSymbol machineState) : Prop :=
  exists searcherState : Type,
  exists searcher : TuringMachine MachineCodeSymbol searcherState,
    forall input : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput searcher input <->
        exists inner : Nat,
        exists outer : Nat,
          TuringMachine.HaltsOnInputIn M outer
            (CodePrefixRecognizerStageCode input inner)

/--
Unbounded generated-pair enumerator.  The concrete machine preserves the raw
input, enumerates two unary natural parameters, rebuilds the nested generated
call, and invokes the supplied selected runner.
-/
def CodePrefixNestedPairEnumeratorConstruction
    {selectedState : Type u}
    (selected : TuringMachine MachineCodeSymbol selectedState) : Prop :=
  exists searcherState : Type,
  exists searcher : TuringMachine MachineCodeSymbol searcherState,
    forall input : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput searcher input <->
        exists inner : Nat,
        exists outer : Nat,
          TuringMachine.HaltsOnInput selected
            (NestedCodePrefixRecognizerStageCode input inner outer)

/--
Finite-machine leaf for unbounded generated-pair enumeration.
-/
theorem codePrefixNestedPairEnumeratorFiniteLeaf
    {selectedState : Type u}
    (selected : TuringMachine MachineCodeSymbol selectedState) :
    CodePrefixNestedPairEnumeratorConstruction selected := by
  sorry

/--
Composition of the exact-fuel runner and unbounded generated-pair enumerator.
This is the shared helper behind raw budget/fuel searches.
-/
theorem codePrefixNestedExactFuelSearchFiniteLeaf
    {machineState : Type u}
    (M : TuringMachine MachineCodeSymbol machineState) :
    CodePrefixNestedExactFuelSearchConstruction M := by
  rcases codePrefixExactFuelRunnerFiniteLeaf M with
    ⟨selectedState, selected, hselected⟩
  rcases codePrefixNestedPairEnumeratorFiniteLeaf selected with
    ⟨searcherState, searcher, hsearcher⟩
  refine ⟨searcherState, searcher, ?_⟩
  intro input
  constructor
  · intro hhalt
    rcases (hsearcher input).mp hhalt with
      ⟨inner, outer, hselectedHalt⟩
    exact
      ⟨inner, outer,
        (codePrefixExactFuelRunner_haltsOnNested_iff
          hselected input inner outer).mp hselectedHalt⟩
  · intro htarget
    rcases htarget with ⟨inner, outer, hM⟩
    exact (hsearcher input).mpr
      ⟨inner, outer,
        (codePrefixExactFuelRunner_haltsOnNested_iff
          hselected input inner outer).mpr hM⟩

/--
Bounded generated-pair enumerator.  The input carries an outer budget; the
machine enumerates pairs bounded by that budget and invokes the selected
runner on each rebuilt nested generated call.
-/
def CodePrefixBoundedNestedPairEnumeratorConstruction
    {selectedState : Type u}
    (selected : TuringMachine MachineCodeSymbol selectedState) : Prop :=
  exists searcherState : Type,
  exists searcher : TuringMachine MachineCodeSymbol searcherState,
    forall input : Word MachineCodeSymbol,
    forall budget : Nat,
      TuringMachine.HaltsOnInput searcher
          (CodePrefixRecognizerStageCode input budget) <->
        exists inner : Nat,
        exists outer : Nat,
          inner ≤ budget ∧
            outer ≤ budget ∧
            TuringMachine.HaltsOnInput selected
              (NestedCodePrefixRecognizerStageCode input inner outer)

/--
Bounded search over generated inner inputs and exact outer fuels for a wrapped
machine.
-/
def CodePrefixBoundedNestedExactFuelSearchConstruction
    {machineState : Type u}
    (M : TuringMachine MachineCodeSymbol machineState) : Prop :=
  exists searcherState : Type,
  exists searcher : TuringMachine MachineCodeSymbol searcherState,
    forall input : Word MachineCodeSymbol,
    forall budget : Nat,
      TuringMachine.HaltsOnInput searcher
          (CodePrefixRecognizerStageCode input budget) <->
        exists inner : Nat,
        exists outer : Nat,
          inner ≤ budget ∧
            outer ≤ budget ∧
            TuringMachine.HaltsOnInputIn M outer
              (CodePrefixRecognizerStageCode input inner)

/--
Finite-machine leaf for bounded generated-pair enumeration.
-/
theorem codePrefixBoundedNestedPairEnumeratorFiniteLeaf
    {selectedState : Type u}
    (selected : TuringMachine MachineCodeSymbol selectedState) :
    CodePrefixBoundedNestedPairEnumeratorConstruction selected := by
  sorry

/--
Composition of the exact-fuel runner and bounded generated-pair enumerator.
This is the shared helper behind bounded simulator pair loops.
-/
theorem codePrefixBoundedNestedExactFuelSearchFiniteLeaf
    {machineState : Type u}
    (M : TuringMachine MachineCodeSymbol machineState) :
    CodePrefixBoundedNestedExactFuelSearchConstruction M := by
  rcases codePrefixExactFuelRunnerFiniteLeaf M with
    ⟨selectedState, selected, hselected⟩
  rcases codePrefixBoundedNestedPairEnumeratorFiniteLeaf selected with
    ⟨searcherState, searcher, hsearcher⟩
  refine ⟨searcherState, searcher, ?_⟩
  intro input budget
  constructor
  · intro hhalt
    rcases (hsearcher input budget).mp hhalt with
      ⟨inner, outer, hinner, houter, hselectedHalt⟩
    exact
      ⟨inner, outer, hinner, houter,
        (codePrefixExactFuelRunner_haltsOnNested_iff
          hselected input inner outer).mp hselectedHalt⟩
  · intro htarget
    rcases htarget with ⟨inner, outer, hinner, houter, hM⟩
    exact (hsearcher input budget).mpr
      ⟨inner, outer, hinner, houter,
        (codePrefixExactFuelRunner_haltsOnNested_iff
          hselected input inner outer).mpr hM⟩

/--
Product exact-fuel runner for recognizer intersection.  The input carries two
generated fuel parameters; the machine runs the left recognizer for the outer
fuel and the right recognizer for the inner fuel on the same preserved input.
-/
def CodePrefixExactFuelProductRunnerConstruction
    {leftState : Type uStage} {rightState : Type uDescription}
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState) : Prop :=
  exists selectedState : Type,
  exists selected : TuringMachine MachineCodeSymbol selectedState,
    forall input : Word MachineCodeSymbol,
    forall leftFuel : Nat,
    forall rightFuel : Nat,
      TuringMachine.HaltsOnInput selected
          (NestedCodePrefixRecognizerStageCode
            input rightFuel leftFuel) <->
        TuringMachine.HaltsOnInputIn left leftFuel input ∧
          TuringMachine.HaltsOnInputIn right rightFuel input

/--
Finite-machine leaf for the product exact-fuel runner.
-/
theorem codePrefixExactFuelProductRunnerFiniteLeaf
    {leftState : Type uStage} {rightState : Type uDescription}
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState) :
    CodePrefixExactFuelProductRunnerConstruction left right := by
  sorry

/--
Unbounded product search over exact left/right fuel witnesses for a preserved
input.
-/
def CodePrefixExactFuelProductSearchConstruction
    {leftState : Type uStage} {rightState : Type uDescription}
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState) : Prop :=
  exists bothState : Type,
  exists both : TuringMachine MachineCodeSymbol bothState,
    forall input : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput both input <->
        exists leftFuel : Nat,
        exists rightFuel : Nat,
          TuringMachine.HaltsOnInputIn left leftFuel input ∧
            TuringMachine.HaltsOnInputIn right rightFuel input

/--
Composition of the exact-fuel product runner and unbounded generated-pair
enumerator.  This is the shared helper behind recognizer-intersection fuel
search.
-/
theorem codePrefixExactFuelProductSearchFiniteLeaf
    {leftState : Type uStage} {rightState : Type uDescription}
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState) :
    CodePrefixExactFuelProductSearchConstruction left right := by
  rcases codePrefixExactFuelProductRunnerFiniteLeaf left right with
    ⟨selectedState, selected, hselected⟩
  rcases codePrefixNestedPairEnumeratorFiniteLeaf selected with
    ⟨bothState, both, hboth⟩
  refine ⟨bothState, both, ?_⟩
  intro input
  constructor
  · intro hhalt
    rcases (hboth input).mp hhalt with
      ⟨rightFuel, leftFuel, hselectedHalt⟩
    exact
      ⟨leftFuel, rightFuel,
        (hselected input leftFuel rightFuel).mp hselectedHalt⟩
  · intro htarget
    rcases htarget with ⟨leftFuel, rightFuel, hleftRight⟩
    exact (hboth input).mpr
      ⟨rightFuel, leftFuel,
        (hselected input leftFuel rightFuel).mpr hleftRight⟩

/--
Generic pair-bounding algebra for dovetail drivers: existential search over a
raw pair is equivalent to existential search under some finite outer limit.
-/
theorem exists_bounded_pair_iff_exists_pair
    (P : Nat -> Nat -> Prop) :
    (exists limit : Nat,
      exists m : Nat,
      exists n : Nat,
        m ≤ limit ∧ n ≤ limit ∧ P m n) <->
      exists m : Nat, exists n : Nat, P m n := by
  constructor
  · intro h
    rcases h with ⟨_limit, m, n, _hm, _hn, hp⟩
    exact ⟨m, n, hp⟩
  · intro h
    rcases h with ⟨m, n, hp⟩
    exact
      ⟨Nat.max m n, m, n,
        Nat.le_max_left m n, Nat.le_max_right m n, hp⟩

/--
Search over an explicit fuel component is the same as unbounded halting for
the selected generated input.
-/
theorem exists_pair_haltsOnInputIn_iff_exists_haltsOnInput
    {symbol : Type u} {state : Type v}
    (M : TuringMachine symbol state)
    (inputOf : Nat -> Word symbol) :
    (exists m : Nat,
      exists fuel : Nat,
        TuringMachine.HaltsOnInputIn M fuel (inputOf m)) <->
      exists m : Nat,
        TuringMachine.HaltsOnInput M (inputOf m) := by
  constructor
  · intro h
    rcases h with ⟨m, fuel, hfuel⟩
    exact
      ⟨m,
        TuringMachine.halts_on_input_in_to_halts_on_input
          (n := fuel) hfuel⟩
  · intro h
    rcases h with ⟨m, hhalt⟩
    rcases
        TuringMachine.halts_on_input_to_halts_on_input_in hhalt with
      ⟨fuel, hfuel⟩
    exact ⟨m, fuel, hfuel⟩

/--
Bounded dovetailing over a generated input index and an explicit fuel is
equivalent to unbounded halting for some generated input.
-/
theorem exists_bounded_pair_haltsOnInputIn_iff_exists_haltsOnInput
    {symbol : Type u} {state : Type v}
    (M : TuringMachine symbol state)
    (inputOf : Nat -> Word symbol) :
    (exists limit : Nat,
      exists m : Nat,
      exists fuel : Nat,
        m ≤ limit ∧
          fuel ≤ limit ∧
          TuringMachine.HaltsOnInputIn M fuel (inputOf m)) <->
      exists m : Nat,
        TuringMachine.HaltsOnInput M (inputOf m) := by
  exact
    Iff.trans
      (exists_bounded_pair_iff_exists_pair
        (fun m fuel =>
          TuringMachine.HaltsOnInputIn M fuel (inputOf m)))
      (exists_pair_haltsOnInputIn_iff_exists_haltsOnInput
        M inputOf)

/--
Two explicit fuel witnesses for the same input are equivalent to unbounded
halting of both machines on that input.
-/
theorem exists_pair_haltsOnInputIn_and_iff_haltsOnInput_and
    {symbol : Type u}
    {leftState : Type v} {rightState : Type w}
    (left : TuringMachine symbol leftState)
    (right : TuringMachine symbol rightState)
    (input : Word symbol) :
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
      ⟨TuringMachine.halts_on_input_in_to_halts_on_input
          (n := leftFuel) hleft,
        TuringMachine.halts_on_input_in_to_halts_on_input
          (n := rightFuel) hright⟩
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
Unbounded search over generated inner inputs for a wrapped machine, hiding the
exact simulation fuel behind ordinary halting.
-/
def CodePrefixNestedHaltingSearchConstruction
    {machineState : Type u}
    (M : TuringMachine MachineCodeSymbol machineState) : Prop :=
  exists searcherState : Type,
  exists searcher : TuringMachine MachineCodeSymbol searcherState,
    forall input : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput searcher input <->
        exists inner : Nat,
          TuringMachine.HaltsOnInput M
            (CodePrefixRecognizerStageCode input inner)

/--
Composition of nested exact-fuel search with the standard equivalence between
unbounded halting and exact-step halting.
-/
theorem codePrefixNestedHaltingSearchFiniteLeaf
    {machineState : Type u}
    (M : TuringMachine MachineCodeSymbol machineState) :
    CodePrefixNestedHaltingSearchConstruction M := by
  rcases codePrefixNestedExactFuelSearchFiniteLeaf M with
    ⟨searcherState, searcher, hsearcher⟩
  refine ⟨searcherState, searcher, ?_⟩
  intro input
  exact Iff.trans (hsearcher input)
    (exists_pair_haltsOnInputIn_iff_exists_haltsOnInput
      M (fun inner => CodePrefixRecognizerStageCode input inner))

/--
Unbounded product search for recognizer intersection, hiding both exact fuel
witnesses behind ordinary halting.
-/
def CodePrefixProductHaltingSearchConstruction
    {leftState : Type uStage} {rightState : Type uDescription}
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState) : Prop :=
  exists bothState : Type,
  exists both : TuringMachine MachineCodeSymbol bothState,
    forall input : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput both input <->
        TuringMachine.HaltsOnInput left input ∧
          TuringMachine.HaltsOnInput right input

/--
Composition of product exact-fuel search with the standard exact-step
existential equivalence.
-/
theorem codePrefixProductHaltingSearchFiniteLeaf
    {leftState : Type uStage} {rightState : Type uDescription}
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState) :
    CodePrefixProductHaltingSearchConstruction left right := by
  rcases codePrefixExactFuelProductSearchFiniteLeaf left right with
    ⟨bothState, both, hboth⟩
  refine ⟨bothState, both, ?_⟩
  intro input
  exact Iff.trans (hboth input)
    (exists_pair_haltsOnInputIn_and_iff_haltsOnInput_and
      left right input)

/--
Bounded dovetailing over two fuel components is equivalent to both machines
halting on the preserved input.
-/
theorem exists_bounded_pair_haltsOnInputIn_and_iff_haltsOnInput_and
    {symbol : Type u}
    {leftState : Type v} {rightState : Type w}
    (left : TuringMachine symbol leftState)
    (right : TuringMachine symbol rightState)
    (input : Word symbol) :
    (exists limit : Nat,
      exists leftFuel : Nat,
      exists rightFuel : Nat,
        leftFuel ≤ limit ∧
          rightFuel ≤ limit ∧
          (TuringMachine.HaltsOnInputIn left leftFuel input ∧
            TuringMachine.HaltsOnInputIn right rightFuel input)) <->
      TuringMachine.HaltsOnInput left input ∧
        TuringMachine.HaltsOnInput right input := by
  exact
    Iff.trans
      (exists_bounded_pair_iff_exists_pair
        (fun leftFuel rightFuel =>
          TuringMachine.HaltsOnInputIn left leftFuel input ∧
            TuringMachine.HaltsOnInputIn right rightFuel input))
      (exists_pair_haltsOnInputIn_and_iff_haltsOnInput_and
        left right input)

end Computability
end FoC

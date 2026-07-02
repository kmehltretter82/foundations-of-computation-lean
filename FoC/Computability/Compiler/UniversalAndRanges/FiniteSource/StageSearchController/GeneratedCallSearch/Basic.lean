import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.StageSearchController.GeneratedCallHandoff
import FoC.Computability.Compiler.Core.CommonGround.SearchAlgebra

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

theorem nestedCodePrefixRecognizerStageCode_eq_of_decodeNat_outer_inner
    {tokens innerCode input : Word MachineCodeSymbol}
    {inner outer : Nat}
    (houter :
      MachineDescription.decodeNat tokens =
        some (outer, innerCode))
    (hinner :
      MachineDescription.decodeNat innerCode =
        some (inner, input)) :
    tokens = NestedCodePrefixRecognizerStageCode input inner outer := by
  have htokens :
      tokens = CodePrefixRecognizerStageCode innerCode outer :=
    codePrefixRecognizerStageCode_eq_of_decodeNat houter
  have hinnerCode :
      innerCode = CodePrefixRecognizerStageCode input inner :=
    codePrefixRecognizerStageCode_eq_of_decodeNat hinner
  rw [htokens, hinnerCode]
  rfl

theorem nestedCodePrefixRecognizerStageCode_decodeNat_outer_eq_some_iff
    {tokens input : Word MachineCodeSymbol}
    {inner outer : Nat} :
    MachineDescription.decodeNat tokens =
        some (outer, CodePrefixRecognizerStageCode input inner) <->
      tokens =
        NestedCodePrefixRecognizerStageCode input inner outer := by
  constructor
  · intro h
    exact
      nestedCodePrefixRecognizerStageCode_eq_of_decodeNat_outer_inner
        h
        (nestedCodePrefixRecognizerStageCode_decodeNat_inner
          input inner)
  · intro h
    rw [h]
    exact
      nestedCodePrefixRecognizerStageCode_decodeNat_outer
        input inner outer

theorem nestedCodePrefixRecognizerStageCode_decodeNat_pair_iff
    {tokens input : Word MachineCodeSymbol}
    {inner outer : Nat} :
    (exists innerCode : Word MachineCodeSymbol,
      MachineDescription.decodeNat tokens =
          some (outer, innerCode) ∧
        MachineDescription.decodeNat innerCode =
          some (inner, input)) <->
      tokens =
        NestedCodePrefixRecognizerStageCode input inner outer := by
  constructor
  · intro h
    rcases h with ⟨innerCode, houter, hinner⟩
    exact
      nestedCodePrefixRecognizerStageCode_eq_of_decodeNat_outer_inner
        houter hinner
  · intro h
    subst tokens
    exact
      ⟨CodePrefixRecognizerStageCode input inner,
        nestedCodePrefixRecognizerStageCode_decodeNat_outer
          input inner outer,
        nestedCodePrefixRecognizerStageCode_decodeNat_inner
          input inner⟩

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

end Computability
end FoC

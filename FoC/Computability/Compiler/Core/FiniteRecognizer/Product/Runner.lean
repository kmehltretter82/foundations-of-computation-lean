import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StageProgram.Composition
import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.Construction
import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.Duplicator

set_option doc.verso true

/-!
# Generated product exact-fuel runner boundary

Concrete finite-state construction boundary for recognizer-product exact-fuel
calls. The runner layer is independent of generated tuple search.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer

universe uLeft uRight

/--
Semantic parser/recognizer for one generated product exact-fuel call.  The
outer unary field is the left-machine fuel; the inner unary field is the
right-machine fuel, followed by the raw shared input.
-/
def generatedProductExactFuelRun
    {leftN rightN : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftN))
    (right : TuringMachine MachineCodeSymbol (Fin rightN))
    (tokens : Word MachineCodeSymbol) :
    Option (Word MachineCodeSymbol) :=
  match MachineDescription.decodeNat tokens with
  | none => none
  | some (leftFuel, innerCode) =>
      match MachineDescription.decodeNat innerCode with
      | none => none
      | some (rightFuel, input) =>
          if TuringMachine.HaltsOnInputIn left leftFuel input ∧
              TuringMachine.HaltsOnInputIn right rightFuel input then
            some ([] : Word MachineCodeSymbol)
          else
            none

theorem generatedProductExactFuelRun_eq_some_empty_of_eq_some
    {leftN rightN : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftN))
    (right : TuringMachine MachineCodeSymbol (Fin rightN))
    {tokens output : Word MachineCodeSymbol}
    (h :
      generatedProductExactFuelRun left right tokens =
        some output) :
    output = ([] : Word MachineCodeSymbol) := by
  unfold generatedProductExactFuelRun at h
  cases houter : MachineDescription.decodeNat tokens with
  | none =>
      simp [houter] at h
  | some outerDecoded =>
      rcases outerDecoded with ⟨leftFuel, innerCode⟩
      cases hinner : MachineDescription.decodeNat innerCode with
      | none =>
          simp [houter, hinner] at h
      | some innerDecoded =>
          rcases innerDecoded with ⟨rightFuel, input⟩
          by_cases htarget :
              TuringMachine.HaltsOnInputIn left leftFuel input ∧
                TuringMachine.HaltsOnInputIn right rightFuel input
          · simpa [houter, hinner, htarget] using h.symm
          · simp [houter, hinner, htarget] at h

theorem generatedProductExactFuelRun_nestedStageCode_eq_some_iff
    {leftN rightN : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftN))
    (right : TuringMachine MachineCodeSymbol (Fin rightN))
    (input : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat) :
    generatedProductExactFuelRun left right
        (GeneratedCode.nestedStageCode input rightFuel leftFuel) =
        some ([] : Word MachineCodeSymbol) <->
      TuringMachine.HaltsOnInputIn left leftFuel input ∧
        TuringMachine.HaltsOnInputIn right rightFuel input := by
  unfold generatedProductExactFuelRun
  by_cases htarget :
      TuringMachine.HaltsOnInputIn left leftFuel input ∧
        TuringMachine.HaltsOnInputIn right rightFuel input
  · simp [GeneratedCode.nestedStageCode_decodeNat_outer,
      GeneratedCode.nestedStageCode_decodeNat_inner, htarget]
    rfl
  · simp [GeneratedCode.nestedStageCode_decodeNat_outer,
      GeneratedCode.nestedStageCode_decodeNat_inner, htarget]

theorem generatedProductExactFuelRun_eq_some_iff
    {leftN rightN : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftN))
    (right : TuringMachine MachineCodeSymbol (Fin rightN))
    (tokens output : Word MachineCodeSymbol) :
    generatedProductExactFuelRun left right tokens = some output <->
      exists input : Word MachineCodeSymbol,
      exists leftFuel : Nat,
      exists rightFuel : Nat,
        tokens =
            GeneratedCode.nestedStageCode input rightFuel leftFuel /\
          output = ([] : Word MachineCodeSymbol) /\
          TuringMachine.HaltsOnInputIn left leftFuel input ∧
            TuringMachine.HaltsOnInputIn right rightFuel input := by
  constructor
  · intro h
    unfold generatedProductExactFuelRun at h
    cases houter : MachineDescription.decodeNat tokens with
    | none =>
        simp [houter] at h
    | some outerDecoded =>
        rcases outerDecoded with ⟨leftFuel, innerCode⟩
        cases hinner : MachineDescription.decodeNat innerCode with
        | none =>
            simp [houter, hinner] at h
        | some innerDecoded =>
            rcases innerDecoded with ⟨rightFuel, input⟩
            by_cases htarget :
                TuringMachine.HaltsOnInputIn left leftFuel input ∧
                  TuringMachine.HaltsOnInputIn right rightFuel input
            · have houtput :
                  output = ([] : Word MachineCodeSymbol) :=
                generatedProductExactFuelRun_eq_some_empty_of_eq_some
                  left right h
              exact
                ⟨input, leftFuel, rightFuel,
                  GeneratedCode.nestedStageCode_eq_of_decodeNat_outer_inner
                    houter hinner,
                  houtput, htarget⟩
            · simp [houter, hinner, htarget] at h
  · intro h
    rcases h with
      ⟨input, leftFuel, rightFuel, htokens, houtput, htarget⟩
    subst tokens
    subst output
    exact
      (generatedProductExactFuelRun_nestedStageCode_eq_some_iff
        left right input leftFuel rightFuel).mpr htarget

/--
Exact-output primitive boundary for the generated product parser.  This is the
concrete backend target for product exact-fuel calls: parse both generated fuel
fields, preserve the raw input, and accept exactly when both selected machines
halt within their corresponding exact fuels.
-/
def GeneratedProductExactFuelRunnerExactOutputPrimitiveConstruction
    {leftN rightN : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftN))
    (right : TuringMachine MachineCodeSymbol (Fin rightN)) : Prop :=
  exists selectedState : Type,
  exists selected : TuringMachine MachineCodeSymbol selectedState,
    FoC.Computability.FiniteRecognizer.ExactFuel.StageProgram.ExactOutputSpec
        selected
        (generatedProductExactFuelRun left right) ∧
      FoC.Computability.FiniteRecognizer.ExactFuel.StageProgram.ExactOutputCanonicalSpec
        selected
        (generatedProductExactFuelRun left right) ∧
      TuringMachine.HaltingTransitionsDisabled selected

def GeneratedProductExactFuelRunnerExactOutputPrimitiveFinStateConstruction :
    Prop :=
  forall leftN rightN : Nat,
    forall left : TuringMachine MachineCodeSymbol (Fin leftN),
    forall right : TuringMachine MachineCodeSymbol (Fin rightN),
      GeneratedProductExactFuelRunnerExactOutputPrimitiveConstruction
        left right

/--
Decoded forward contract for one generated product exact-fuel call.
-/
def GeneratedProductDecodedExactOutputForwardSpec
    {leftN rightN : Nat}
    (selected : TuringMachine MachineCodeSymbol selectedState)
    (left : TuringMachine MachineCodeSymbol (Fin leftN))
    (right : TuringMachine MachineCodeSymbol (Fin rightN)) : Prop :=
  forall input : Word MachineCodeSymbol,
  forall leftFuel rightFuel : Nat,
    TuringMachine.HaltsWithExactOutput selected
        (GeneratedCode.nestedStageCode input rightFuel leftFuel)
        ([] : Word MachineCodeSymbol) <->
      TuringMachine.HaltsOnInputIn left leftFuel input ∧
        TuringMachine.HaltsOnInputIn right rightFuel input

/--
Closed decoded-output contract for generated product exact-fuel calls.
-/
def GeneratedProductDecodedExactOutputClosedSpec
    {leftN rightN : Nat}
    (selected : TuringMachine MachineCodeSymbol selectedState)
    (left : TuringMachine MachineCodeSymbol (Fin leftN))
    (right : TuringMachine MachineCodeSymbol (Fin rightN)) : Prop :=
  forall tokens output : Word MachineCodeSymbol,
    TuringMachine.HaltsWithExactOutput selected tokens output ->
      exists input : Word MachineCodeSymbol,
      exists leftFuel : Nat,
      exists rightFuel : Nat,
        tokens =
            GeneratedCode.nestedStageCode input rightFuel leftFuel /\
          output = ([] : Word MachineCodeSymbol) /\
          TuringMachine.HaltsOnInputIn left leftFuel input ∧
            TuringMachine.HaltsOnInputIn right rightFuel input

def GeneratedProductDecodedExactOutputSpec
    {leftN rightN : Nat}
    (selected : TuringMachine MachineCodeSymbol selectedState)
    (left : TuringMachine MachineCodeSymbol (Fin leftN))
    (right : TuringMachine MachineCodeSymbol (Fin rightN)) : Prop :=
  GeneratedProductDecodedExactOutputForwardSpec selected left right ∧
    GeneratedProductDecodedExactOutputClosedSpec selected left right

/--
Sharper finite-table target for generated product exact-fuel calls.  It keeps
the nested generated parameters visible instead of hiding them behind the raw
partial transformer.
-/
def GeneratedProductDecodedExactOutputPrimitiveConstruction
    {leftN rightN : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftN))
    (right : TuringMachine MachineCodeSymbol (Fin rightN)) : Prop :=
  exists selectedState : Type,
  exists selected : TuringMachine MachineCodeSymbol selectedState,
    GeneratedProductDecodedExactOutputSpec selected left right ∧
      FoC.Computability.FiniteRecognizer.ExactFuel.StageProgram.ExactOutputCanonicalSpec
        selected
        (generatedProductExactFuelRun left right) ∧
      TuringMachine.HaltingTransitionsDisabled selected

def GeneratedProductDecodedExactOutputPrimitiveFinStateConstruction :
    Prop :=
  forall leftN rightN : Nat,
    forall left : TuringMachine MachineCodeSymbol (Fin leftN),
    forall right : TuringMachine MachineCodeSymbol (Fin rightN),
      GeneratedProductDecodedExactOutputPrimitiveConstruction
        left right

private def generatedProductExactOutputCounterexampleMachine :
    TuringMachine MachineCodeSymbol (Fin 1) where
  start := 0
  halt := 0
  transition := fun _ _ => none
  statesFinite := Foundation.FiniteType.fin 1

private theorem generatedProductExactOutputCounterexampleMachine_haltsIn
    (input : Word MachineCodeSymbol) :
    TuringMachine.HaltsOnInputIn
      generatedProductExactOutputCounterexampleMachine 0 input := by
  refine ⟨TuringMachine.initial
    generatedProductExactOutputCounterexampleMachine input, ?_, ?_⟩
  · exact TuringMachine.ComputesIn.zero _
  · rfl

/--
The generated product runner cannot erase every nested generated call to the
literal blank tape. The stored input context is nonempty and cannot shrink.
-/
theorem not_generatedProductDecodedExactOutputPrimitiveFinStateConstruction :
    ¬ GeneratedProductDecodedExactOutputPrimitiveFinStateConstruction := by
  intro hconstruction
  rcases hconstruction 1 1
      generatedProductExactOutputCounterexampleMachine
      generatedProductExactOutputCounterexampleMachine with
    ⟨_state, selected, hspec, _hcanonical, _hstop⟩
  have hhalt :=
    (hspec.left ([] : Word MachineCodeSymbol) 0 0).mpr
      ⟨generatedProductExactOutputCounterexampleMachine_haltsIn [],
        generatedProductExactOutputCounterexampleMachine_haltsIn []⟩
  apply
    TuringMachine.not_haltsWithExactOutput_empty_of_input_contextLength_pos
      (M := selected)
      (w := GeneratedCode.nestedStageCode
        ([] : Word MachineCodeSymbol) 0 0) ?_ hhalt
  decide

theorem generatedProductExactOutputSpec_iff_decoded
    {leftN rightN : Nat} {selectedState : Type}
    (selected : TuringMachine MachineCodeSymbol selectedState)
    (left : TuringMachine MachineCodeSymbol (Fin leftN))
    (right : TuringMachine MachineCodeSymbol (Fin rightN)) :
    FoC.Computability.FiniteRecognizer.ExactFuel.StageProgram.ExactOutputSpec
        selected
        (generatedProductExactFuelRun left right) <->
      GeneratedProductDecodedExactOutputSpec selected left right := by
  constructor
  · intro hexact
    constructor
    · intro input leftFuel rightFuel
      exact Iff.trans
        (hexact
          (GeneratedCode.nestedStageCode input rightFuel leftFuel)
          ([] : Word MachineCodeSymbol))
        (generatedProductExactFuelRun_nestedStageCode_eq_some_iff
          left right input leftFuel rightFuel)
    · intro tokens output hhalt
      exact
        (generatedProductExactFuelRun_eq_some_iff
          left right tokens output).mp
          ((hexact tokens output).mp hhalt)
  · intro hdecoded
    intro tokens output
    constructor
    · intro hhalt
      exact
        (generatedProductExactFuelRun_eq_some_iff
          left right tokens output).mpr
          (hdecoded.right tokens output hhalt)
    · intro hrun
      rcases
          (generatedProductExactFuelRun_eq_some_iff
            left right tokens output).mp hrun with
        ⟨input, leftFuel, rightFuel, htokens, houtput, htarget⟩
      subst tokens
      subst output
      exact (hdecoded.left input leftFuel rightFuel).mpr htarget

theorem generatedProductExactOutputPrimitiveConstruction_iff_decoded
    {leftN rightN : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftN))
    (right : TuringMachine MachineCodeSymbol (Fin rightN)) :
    GeneratedProductExactFuelRunnerExactOutputPrimitiveConstruction
        left right <->
      GeneratedProductDecodedExactOutputPrimitiveConstruction left right := by
  constructor
  · intro hprimitive
    rcases hprimitive with
      ⟨selectedState, selected, hexact, hcanonical, hstop⟩
    refine ⟨selectedState, selected, ?_, hcanonical, hstop⟩
    exact
      (generatedProductExactOutputSpec_iff_decoded
        selected left right).mp hexact
  · intro hdecoded
    rcases hdecoded with
      ⟨selectedState, selected, hspec, hcanonical, hstop⟩
    refine ⟨selectedState, selected, ?_, hcanonical, hstop⟩
    exact
      (generatedProductExactOutputSpec_iff_decoded
        selected left right).mpr hspec

theorem generatedProductExactOutputPrimitiveFinStateConstruction_iff_decoded :
    GeneratedProductExactFuelRunnerExactOutputPrimitiveFinStateConstruction <->
      GeneratedProductDecodedExactOutputPrimitiveFinStateConstruction := by
  constructor
  · intro hconstruction leftN rightN left right
    exact
      (generatedProductExactOutputPrimitiveConstruction_iff_decoded
        left right).mp
        (hconstruction leftN rightN left right)
  · intro hconstruction leftN rightN left right
    exact
      (generatedProductExactOutputPrimitiveConstruction_iff_decoded
        left right).mpr
        (hconstruction leftN rightN left right)

/-- The transformer-shaped exact-output product target is refuted as well. -/
theorem not_generatedProductExactFuelRunnerExactOutputPrimitiveFinStateConstruction :
    ¬ GeneratedProductExactFuelRunnerExactOutputPrimitiveFinStateConstruction := by
  intro hconstruction
  exact
    not_generatedProductDecodedExactOutputPrimitiveFinStateConstruction
      (generatedProductExactOutputPrimitiveFinStateConstruction_iff_decoded.mp
        hconstruction)

/--
Concrete-state generated exact-fuel product runner target.
-/
def GeneratedProductExactFuelRunnerFinStateConstruction : Prop :=
  forall leftN rightN : Nat,
    forall left : TuringMachine MachineCodeSymbol (Fin leftN),
    forall right : TuringMachine MachineCodeSymbol (Fin rightN),
      exists selectedState : Type,
      exists selected : TuringMachine MachineCodeSymbol selectedState,
        ProductExactFuelRunnerSpec
          selected left right GeneratedCode.nestedStageCode

/--
Generated exact-fuel product runner for arbitrary finite recognizer state
types.
-/
def GeneratedProductExactFuelRunnerConstruction
    {leftState : Type uLeft} {rightState : Type uRight}
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState) : Prop :=
  exists selectedState : Type,
  exists selected : TuringMachine MachineCodeSymbol selectedState,
    ProductExactFuelRunnerSpec
      selected left right GeneratedCode.nestedStageCode

theorem generatedProductExactFuelRunnerConstruction_of_exactOutputPrimitive
    {leftN rightN : Nat}
    {left : TuringMachine MachineCodeSymbol (Fin leftN)}
    {right : TuringMachine MachineCodeSymbol (Fin rightN)}
    (hprimitive :
      GeneratedProductExactFuelRunnerExactOutputPrimitiveConstruction
        left right) :
    GeneratedProductExactFuelRunnerConstruction left right := by
  rcases hprimitive with
    ⟨selectedState, selected, hexact, hcanonical, _hstop⟩
  refine ⟨selectedState, selected, ?_⟩
  intro input leftFuel rightFuel
  have hselected :
      TuringMachine.HaltsOnInput selected
          (GeneratedCode.nestedStageCode input rightFuel leftFuel) <->
        generatedProductExactFuelRun left right
          (GeneratedCode.nestedStageCode input rightFuel leftFuel) =
          some ([] : Word MachineCodeSymbol) :=
    ExactFuel.StageProgram.haltsOnInput_iff_some_empty_of_exactOutput
      hexact hcanonical
      (by
        intro tokens output houtput
        exact generatedProductExactFuelRun_eq_some_empty_of_eq_some
          left right houtput)
      (GeneratedCode.nestedStageCode input rightFuel leftFuel)
  exact Iff.trans hselected
    (generatedProductExactFuelRun_nestedStageCode_eq_some_iff
      left right input leftFuel rightFuel)

theorem generatedProductExactFuelRunnerFinStateConstruction_of_exactOutputPrimitive
    (hprimitive :
      GeneratedProductExactFuelRunnerExactOutputPrimitiveFinStateConstruction) :
    GeneratedProductExactFuelRunnerFinStateConstruction := by
  intro leftN rightN left right
  exact
    generatedProductExactFuelRunnerConstruction_of_exactOutputPrimitive
      (hprimitive leftN rightN left right)

/--
Generated exact-fuel product runners are stable under replacing both
recognizers by indexed copies.
-/
theorem generatedProductExactFuelRunnerConstruction_of_indexed
    {leftState : Type uLeft} {rightState : Type uRight}
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState)
    (hindexed :
      GeneratedProductExactFuelRunnerConstruction
        (TuringMachine.indexed left) (TuringMachine.indexed right)) :
    GeneratedProductExactFuelRunnerConstruction left right := by
  rcases hindexed with ⟨selectedState, selected, hselected⟩
  refine ⟨selectedState, selected, ?_⟩
  intro input leftFuel rightFuel
  constructor
  · intro hhalt
    rcases (hselected input leftFuel rightFuel).mp hhalt with
      ⟨hleft, hright⟩
    exact
      ⟨(TuringMachine.indexed_haltsOnInputIn_iff
          left leftFuel input).mp hleft,
        (TuringMachine.indexed_haltsOnInputIn_iff
          right rightFuel input).mp hright⟩
  · intro htarget
    rcases htarget with ⟨hleft, hright⟩
    exact (hselected input leftFuel rightFuel).mpr
      ⟨(TuringMachine.indexed_haltsOnInputIn_iff
          left leftFuel input).mpr hleft,
        (TuringMachine.indexed_haltsOnInputIn_iff
          right rightFuel input).mpr hright⟩

theorem generatedProductExactFuelRunnerConstruction_of_indexedDecidable
    {leftState : Type uLeft} {rightState : Type uRight}
    [DecidableEq leftState] [DecidableEq rightState]
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState)
    (hindexed :
      GeneratedProductExactFuelRunnerConstruction
        (TuringMachine.indexedDecidable left)
        (TuringMachine.indexedDecidable right)) :
    GeneratedProductExactFuelRunnerConstruction left right := by
  rcases hindexed with ⟨selectedState, selected, hselected⟩
  refine ⟨selectedState, selected, ?_⟩
  intro input leftFuel rightFuel
  constructor
  · intro hhalt
    rcases (hselected input leftFuel rightFuel).mp hhalt with
      ⟨hleft, hright⟩
    exact
      ⟨(TuringMachine.indexedDecidable_haltsOnInputIn_iff
          left leftFuel input).mp hleft,
        (TuringMachine.indexedDecidable_haltsOnInputIn_iff
          right rightFuel input).mp hright⟩
  · intro htarget
    rcases htarget with ⟨hleft, hright⟩
    exact (hselected input leftFuel rightFuel).mpr
      ⟨(TuringMachine.indexedDecidable_haltsOnInputIn_iff
          left leftFuel input).mpr hleft,
        (TuringMachine.indexedDecidable_haltsOnInputIn_iff
          right rightFuel input).mpr hright⟩

theorem generatedProductExactFuelRunnerConstruction_of_finStateConstruction
    {leftState : Type uLeft} {rightState : Type uRight}
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState)
    (hFin : GeneratedProductExactFuelRunnerFinStateConstruction) :
    GeneratedProductExactFuelRunnerConstruction left right := by
  exact
    generatedProductExactFuelRunnerConstruction_of_indexed left right
      (hFin left.statesFinite.elems.length
        right.statesFinite.elems.length
        (TuringMachine.indexed left) (TuringMachine.indexed right))

theorem generatedProductExactFuelRunnerConstruction_of_finStateConstructionDecidable
    {leftState : Type uLeft} {rightState : Type uRight}
    [DecidableEq leftState] [DecidableEq rightState]
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState)
    (hFin : GeneratedProductExactFuelRunnerFinStateConstruction) :
    GeneratedProductExactFuelRunnerConstruction left right := by
  exact
    generatedProductExactFuelRunnerConstruction_of_indexedDecidable
      left right
      (hFin left.statesFinite.elems.length
        right.statesFinite.elems.length
        (TuringMachine.indexedDecidable left)
        (TuringMachine.indexedDecidable right))

/--
Remaining finite-state generated product runner. Its contract observes only
ordinary halting on the nested generated call, not erasure of the physical
input tape.
-/
theorem generatedProductExactFuelRunnerFinStateFiniteLeaf :
    GeneratedProductExactFuelRunnerFinStateConstruction := by
  intro leftN rightN left right
  cases leftN with
  | zero =>
      exact False.elim (Fin.elim0 left.start)
  | succ _ =>
      cases rightN with
      | zero =>
          exact False.elim (Fin.elim0 right.start)
      | succ _ =>
          -- Obligation: construct the positive-state finite product runner.
          sorry

/--
Finite-machine leaf for generated exact-fuel product runners over arbitrary
finite recognizer state types.
-/
theorem generatedProductExactFuelRunnerFiniteLeaf
    {leftState : Type uLeft} {rightState : Type uRight}
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState) :
    GeneratedProductExactFuelRunnerConstruction left right := by
  exact
    generatedProductExactFuelRunnerConstruction_of_finStateConstruction
      left right generatedProductExactFuelRunnerFinStateFiniteLeaf

theorem generatedProductExactFuelRunnerFiniteLeafDecidable
    {leftState : Type uLeft} {rightState : Type uRight}
    [DecidableEq leftState] [DecidableEq rightState]
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState) :
    GeneratedProductExactFuelRunnerConstruction left right := by
  exact
    generatedProductExactFuelRunnerConstruction_of_finStateConstructionDecidable
      left right generatedProductExactFuelRunnerFinStateFiniteLeaf

end FiniteRecognizer

end Computability
end FoC

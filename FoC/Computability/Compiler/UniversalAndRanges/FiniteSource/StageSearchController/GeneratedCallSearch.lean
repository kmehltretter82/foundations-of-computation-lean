import FoC.Computability.Compiler.UniversalAndRanges.Basic

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

private theorem generatedCall_turingMachine_step_of_tape_equiv
    {M : TuringMachine symbol state}
    {c d : TuringMachine.Configuration symbol state}
    {tape : Tape symbol}
    (hstep : TuringMachine.Step M c d)
    (htape : Tape.Equiv c.tape tape) :
    exists nextTape : Tape symbol,
      TuringMachine.Step M
        { state := c.state, tape := tape }
        { state := d.state, tape := nextTape } ∧
        Tape.Equiv d.tape nextTape := by
  cases hstep with
  | mk haction =>
      rename_i write dir nextState
      refine
        ⟨Tape.move dir (Tape.write write tape), ?_, ?_⟩
      · exact TuringMachine.Step.mk (by
          rw [← Tape.Equiv.read_eq htape]
          exact haction)
      · exact Tape.Equiv.move (Tape.Equiv.write htape write) dir

/--
Exact computations are stable under tape equivalence at the starting tape,
with the same step count and final state.
-/
theorem turingMachine_computesIn_of_tape_equiv
    {M : TuringMachine symbol state}
    {n : Nat}
    {c e : TuringMachine.Configuration symbol state}
    {tape : Tape symbol}
    (hcomp : TuringMachine.ComputesIn M n c e)
    (htape : Tape.Equiv c.tape tape) :
    exists e' : TuringMachine.Configuration symbol state,
      TuringMachine.ComputesIn M n
        { state := c.state, tape := tape } e' ∧
        e'.state = e.state ∧
        Tape.Equiv e.tape e'.tape := by
  induction hcomp generalizing tape with
  | zero c =>
      exact
        ⟨{ state := c.state, tape := tape },
          TuringMachine.ComputesIn.zero _, rfl, htape⟩
  | succ hstep hrest ih =>
      rcases
          generatedCall_turingMachine_step_of_tape_equiv
            hstep htape with
        ⟨nextTape, hstep', htape'⟩
      rcases ih htape' with
        ⟨e', hcomp', hstate'', htape''⟩
      exact
        ⟨e', TuringMachine.ComputesIn.succ hstep' hcomp',
          hstate'', htape''⟩

/--
Exact halting from a configuration is stable under tape equivalence at the
starting tape, preserving the same step bound.
-/
theorem turingMachine_haltsFromIn_of_tape_equiv
    {M : TuringMachine symbol state}
    {n : Nat} {state : state} {tape tape' : Tape symbol}
    (htape : Tape.Equiv tape tape')
    (hhalt :
      TuringMachine.HaltsFromIn M n { state := state, tape := tape }) :
    TuringMachine.HaltsFromIn M n { state := state, tape := tape' } := by
  rcases hhalt with ⟨final, hcomp, hfinal⟩
  rcases turingMachine_computesIn_of_tape_equiv hcomp htape with
    ⟨final', hcomp', hstate, _htape'⟩
  exact
    ⟨final', hcomp',
      by simpa [TuringMachine.Halted, hstate] using hfinal⟩

/--
Exact halting from equivalent starting tapes is equivalent for the same step
bound.
-/
theorem turingMachine_haltsFromIn_tape_equiv_iff
    (M : TuringMachine symbol state)
    (n : Nat) (state : state) {tape tape' : Tape symbol}
    (htape : Tape.Equiv tape tape') :
    TuringMachine.HaltsFromIn M n { state := state, tape := tape } <->
      TuringMachine.HaltsFromIn M n { state := state, tape := tape' } := by
  constructor
  · exact turingMachine_haltsFromIn_of_tape_equiv htape
  · exact
      turingMachine_haltsFromIn_of_tape_equiv
        (Tape.Equiv.symm htape)

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

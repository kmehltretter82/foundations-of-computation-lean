import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorTransitionScanner.Spec
import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorTransitionScanner.BlockMachine.Basic

set_option doc.verso true

/-!
# Exact-code validator: pairwise determinism specification

This module fixes the semantic currency and collision audit for M4 leaf 5.
The executable machine selects rows from left to right, checking each selected
row only against the rows physically following it.  The triangular Boolean
below is proved equivalent to the existing full nested pair check from
{module}`FoC.Computability.Compiler.Core.TransitionTableChecks`.

The successful source and target are the same exact transition-scanner handoff
tape.  Three invalid block symbols have disjoint temporary roles:
{lit}`marker001` marks transition boundaries, {lit}`marker010` pairs unary
ticks, and {lit}`marker011` marks the final description boundary.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer
namespace ValidatorDeterminismGate

open Languages
open MachineDescription

/-- Check every unordered transition pair once, with the current head row
paired against its remaining tail. -/
def transitionUpperPairsBool : List TransitionDescription -> Bool
  | [] => true
  | row :: rest =>
      rest.all (fun other => transitionDeterministicPairBool row other) &&
        transitionUpperPairsBool rest

/-- Reversed triangular form, useful when a consumer presents rows from the
opposite end of the encoded list. -/
def transitionReversePairsBool
    (rows : List TransitionDescription) : Bool :=
  transitionUpperPairsBool rows.reverse

/-- A transition is pairwise compatible with itself. -/
theorem transitionDeterministicPairBool_self
    (row : TransitionDescription) :
    transitionDeterministicPairBool row row = true := by
  simp [transitionDeterministicPairBool, transitionSameKeyBool,
    transitionSameActionBool]

/-- Pairwise transition compatibility is symmetric. -/
theorem transitionDeterministicPairBool_comm
    (left right : TransitionDescription) :
    transitionDeterministicPairBool left right =
      transitionDeterministicPairBool right left := by
  simp [transitionDeterministicPairBool, transitionSameKeyBool,
    transitionSameActionBool, eq_comm]

/-- The one-pass triangular check is exactly the full nested pair check. -/
theorem transitionUpperPairsBool_eq_true_iff
    (rows : List TransitionDescription) :
    transitionUpperPairsBool rows = true <->
      rows.all (fun left =>
        rows.all (fun right =>
          transitionDeterministicPairBool left right)) = true := by
  constructor
  · intro hupper
    induction rows with
    | nil => rfl
    | cons row rest ih =>
        simp only [transitionUpperPairsBool, Bool.and_eq_true] at hupper
        have hfullRest := ih hupper.2
        apply List.all_eq_true.mpr
        intro left hleft
        apply List.all_eq_true.mpr
        intro right hright
        simp only [List.mem_cons] at hleft hright
        rcases hleft with rfl | hleft
        · rcases hright with rfl | hright
          · exact transitionDeterministicPairBool_self _
          · exact List.all_eq_true.mp hupper.1 right hright
        · rcases hright with rfl | hright
          · rw [transitionDeterministicPairBool_comm]
            exact List.all_eq_true.mp hupper.1 left hleft
          · exact List.all_eq_true.mp
              (List.all_eq_true.mp hfullRest left hleft) right hright
  · intro hfull
    induction rows with
    | nil => rfl
    | cons row rest ih =>
        simp only [transitionUpperPairsBool, Bool.and_eq_true]
        constructor
        · apply List.all_eq_true.mpr
          intro right hright
          have hrow := List.all_eq_true.mp hfull row (by simp)
          exact List.all_eq_true.mp hrow right (by simp [hright])
        · apply ih
          apply List.all_eq_true.mpr
          intro left hleft
          apply List.all_eq_true.mpr
          intro right hright
          have hleftAll := List.all_eq_true.mp hfull left (by simp [hleft])
          exact List.all_eq_true.mp hleftAll right (by simp [hright])

private theorem transitionFullPairsBool_reverse_eq_true_iff
    (rows : List TransitionDescription) :
    rows.reverse.all (fun left =>
        rows.reverse.all (fun right =>
          transitionDeterministicPairBool left right)) = true <->
      rows.all (fun left =>
        rows.all (fun right =>
          transitionDeterministicPairBool left right)) = true := by
  constructor
  · intro hreverse
    apply List.all_eq_true.mpr
    intro left hleft
    apply List.all_eq_true.mpr
    intro right hright
    have hleftReverse : left ∈ rows.reverse := by simpa using hleft
    have hrightReverse : right ∈ rows.reverse := by simpa using hright
    exact List.all_eq_true.mp
      (List.all_eq_true.mp hreverse left hleftReverse) right hrightReverse
  · intro hforward
    apply List.all_eq_true.mpr
    intro left hleft
    apply List.all_eq_true.mpr
    intro right hright
    have hleftForward : left ∈ rows := by simpa using hleft
    have hrightForward : right ∈ rows := by simpa using hright
    exact List.all_eq_true.mp
      (List.all_eq_true.mp hforward left hleftForward) right hrightForward

/-- Reversing the triangular scan still matches the canonical full determinism
Boolean used by description well-formedness. -/
theorem transitionReversePairsBool_eq_true_iff
    (rows : List TransitionDescription) :
    transitionReversePairsBool rows = true <->
      rows.all (fun left =>
        rows.all (fun right =>
          transitionDeterministicPairBool left right)) = true := by
  exact (transitionUpperPairsBool_eq_true_iff rows.reverse).trans
    (transitionFullPairsBool_reverse_eq_true_iff rows)

/-- Exact successful leaf-5 source at the blank immediately after a complete
description. -/
def sourceTape
    (stateCount start halt transitionCount : Nat)
    (rows : List TransitionDescription) : Tape Bool :=
  validatorTransitionScannerHandoffTape
    stateCount start halt transitionCount rows []

/-- Leaf 5 restores every temporary marker and preserves its source tape. -/
def targetTape
    (stateCount start halt transitionCount : Nat)
    (rows : List TransitionDescription) : Tape Bool :=
  sourceTape stateCount start halt transitionCount rows

/-- The successful target is physically identical to the source. -/
theorem targetTape_eq_sourceTape
    (stateCount start halt transitionCount : Nat)
    (rows : List TransitionDescription) :
    targetTape stateCount start halt transitionCount rows =
      sourceTape stateCount start halt transitionCount rows := by
  rfl

/-- The leaf starts on the unique blank boundary certified by the suffix gate. -/
theorem sourceTape_read_eq_none
    (stateCount start halt transitionCount : Nat)
    (rows : List TransitionDescription) :
    (sourceTape stateCount start halt transitionCount rows).read = none := by
  simp [sourceTape, validatorTransitionScannerHandoffTape,
    Tape.read, DovetailInitialLayoutInitializer.tapeAtCells,
    encodeCodeWordAsInput]

private theorem list_append_fixedPrefix_injective
    {α : Type} (fixed left right : List α)
    (h : List.append fixed left = List.append fixed right) :
    left = right := by
  induction fixed with
  | nil => exact h
  | cons head tail ih =>
      exact ih (List.cons.inj h).2

/-- Equal counted transition encodings cannot demand different leaf-5 row
targets.  This is the semantic collision audit for the exact-tape contract. -/
theorem transitionPrefix_collision_free_of_count
    {stateCount start halt transitionCount : Nat}
    {leftRows rightRows : List TransitionDescription}
    (hleftCount : transitionCount = leftRows.length)
    (hrightCount : transitionCount = rightRows.length)
    (hprefix :
      validatorTransitionScannerPrefix
          stateCount start halt transitionCount leftRows =
        validatorTransitionScannerPrefix
          stateCount start halt transitionCount rightRows) :
    leftRows = rightRows := by
  have htransitions :
      encodeTransitions leftRows = encodeTransitions rightRows := by
    simp only [validatorTransitionScannerPrefix] at hprefix
    exact list_append_fixedPrefix_injective
      (validatorHeaderFieldsPrefix stateCount start halt transitionCount)
      (encodeTransitions leftRows) (encodeTransitions rightRows) hprefix
  exact (encodeTransitionsAppend_inj_of_count
    hleftCount hrightCount
      (by simpa [encodeTransitions] using htransitions)).1

/-- Canonical input blocks cannot collide with any of leaf 5's three reserved
markers. -/
theorem canonicalBlock_ne_reservedMarkers
    (symbol : MachineCodeSymbol) :
    ValidatorBlockSymbol.ofMachineCodeSymbol symbol ≠ .marker001 ∧
      ValidatorBlockSymbol.ofMachineCodeSymbol symbol ≠ .marker010 ∧
        ValidatorBlockSymbol.ofMachineCodeSymbol symbol ≠ .marker011 := by
  cases symbol <;> decide

/-- The three temporary marker roles are pairwise disjoint. -/
theorem reservedMarkers_pairwise_ne :
    ValidatorBlockSymbol.marker001 ≠ .marker010 ∧
      ValidatorBlockSymbol.marker001 ≠ .marker011 ∧
        ValidatorBlockSymbol.marker010 ≠ .marker011 := by
  decide

end ValidatorDeterminismGate
end SelfHaltingRecognizer
end Computability
end FoC

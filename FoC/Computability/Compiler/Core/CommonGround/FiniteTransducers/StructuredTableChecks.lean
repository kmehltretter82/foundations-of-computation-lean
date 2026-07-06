import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.Structured

set_option doc.verso true

/-!
# Structured transition-table checking helpers

This module is the structured-logical-tape analogue of the ordinary one-tape
transition-table checker.  It packages the finite Boolean checks used for
concrete generated structured machines into small reusable theorems.  The
intended use is:

* define a concrete structured description;
* discharge its row well-formedness, determinism, and halt-row absence with
  closed Boolean computations; and
* pass the resulting structured subroutine-readiness proof to the structured
  lowering layer.

The helpers deliberately live beside the structured finite-transducer layer
instead of extending the older one-tape table checker.  That keeps the
dependency direction one-way: ordinary one-tape machine code does not import
the structured intermediate language.
-/

namespace FoC
namespace Computability

namespace CommonGround
namespace FiniteTransducers

/-! ## Row-level Boolean predicates -/

def structuredTransitionWellFormedBool
    (stateCount tapeCount : Nat) (t : Structured.Transition) : Bool :=
  decide (t.source < stateCount) &&
    decide (t.target < stateCount) &&
    decide (t.reads.length = tapeCount) &&
    decide (t.actions.length = tapeCount)

def structuredTransitionSameKeyBool
    (t u : Structured.Transition) : Bool :=
  decide (t.source = u.source) && decide (t.reads = u.reads)

def structuredTransitionSameActionBool
    (t u : Structured.Transition) : Bool :=
  decide (t.actions = u.actions) && decide (t.target = u.target)

def structuredTransitionDeterministicPairBool
    (t u : Structured.Transition) : Bool :=
  !structuredTransitionSameKeyBool t u ||
    structuredTransitionSameActionBool t u

def structuredTransitionPairAllBool
    (l r : List Structured.Transition) : Bool :=
  l.all (fun t =>
    r.all (fun u => structuredTransitionDeterministicPairBool t u))

def structuredTransitionTableDeterministicBool
    (l : List Structured.Transition) : Bool :=
  l.all (fun t =>
    l.all (fun u => structuredTransitionDeterministicPairBool t u))

def structuredTransitionChunksDeterministicBool
    (chunks : List (List Structured.Transition)) : Bool :=
  chunks.all (fun l =>
    chunks.all (fun r => structuredTransitionPairAllBool l r))

def structuredTransitionNotFromBool
    (state : Nat) (t : Structured.Transition) : Bool :=
  decide (t.source ≠ state)

/-! ## Flattening table checks -/

private theorem list_all_flatten_of_chunk_all
    {α : Type} {p : α -> Bool} {chunks : List (List α)}
    (h : chunks.all (fun l => l.all p) = true) :
    chunks.flatten.all p = true := by
  apply List.all_eq_true.mpr
  intro x hx
  rw [List.mem_flatten] at hx
  rcases hx with ⟨l, hl, hx⟩
  exact List.all_eq_true.mp (List.all_eq_true.mp h l hl) x hx

theorem structuredTransition_wellFormed_of_all
    {stateCount tapeCount : Nat} {l : List Structured.Transition}
    (h :
      l.all (structuredTransitionWellFormedBool stateCount tapeCount) =
        true) :
    forall t : Structured.Transition,
      t ∈ l ->
        Structured.Transition.WellFormed stateCount tapeCount t := by
  intro t ht
  have htbool := (List.all_eq_true.mp h) t ht
  simpa [structuredTransitionWellFormedBool,
    Structured.Transition.WellFormed, and_assoc] using htbool

theorem structuredTransition_wellFormed_of_chunk_all
    {stateCount tapeCount : Nat}
    {chunks : List (List Structured.Transition)}
    (h :
      chunks.all
        (fun l =>
          l.all (structuredTransitionWellFormedBool stateCount tapeCount)) =
        true) :
    forall t : Structured.Transition,
      t ∈ chunks.flatten ->
        Structured.Transition.WellFormed stateCount tapeCount t :=
  structuredTransition_wellFormed_of_all
    (list_all_flatten_of_chunk_all h)

theorem structuredTransition_deterministic_of_all
    {l : List Structured.Transition}
    (h : structuredTransitionTableDeterministicBool l = true) :
    forall t u : Structured.Transition,
      t ∈ l ->
      u ∈ l ->
      Structured.Transition.SameKey t u ->
        Structured.Transition.SameAction t u := by
  intro t u ht hu hkey
  have htbool := (List.all_eq_true.mp h) t ht
  have hubool := (List.all_eq_true.mp htbool) u hu
  have hkeyBool :
      structuredTransitionSameKeyBool t u = true := by
    simpa [structuredTransitionSameKeyBool,
      Structured.Transition.SameKey] using hkey
  simpa [structuredTransitionTableDeterministicBool,
    structuredTransitionDeterministicPairBool, hkeyBool,
    structuredTransitionSameActionBool, Structured.Transition.SameAction,
    and_assoc] using hubool

private theorem structuredTransition_deterministic_bool_flatten_of_chunks
    {chunks : List (List Structured.Transition)}
    (h : structuredTransitionChunksDeterministicBool chunks = true) :
    structuredTransitionTableDeterministicBool chunks.flatten = true := by
  apply List.all_eq_true.mpr
  intro t ht
  apply List.all_eq_true.mpr
  intro u hu
  rw [List.mem_flatten] at ht hu
  rcases ht with ⟨lt, hlt, ht⟩
  rcases hu with ⟨lu, hlu, hu⟩
  have hltAll := List.all_eq_true.mp h lt hlt
  have hluAll := List.all_eq_true.mp hltAll lu hlu
  have htAll := List.all_eq_true.mp hluAll t ht
  exact List.all_eq_true.mp htAll u hu

theorem structuredTransition_deterministic_of_chunk_all
    {chunks : List (List Structured.Transition)}
    (h : structuredTransitionChunksDeterministicBool chunks = true) :
    forall t u : Structured.Transition,
      t ∈ chunks.flatten ->
      u ∈ chunks.flatten ->
      Structured.Transition.SameKey t u ->
        Structured.Transition.SameAction t u :=
  structuredTransition_deterministic_of_all
    (structuredTransition_deterministic_bool_flatten_of_chunks h)

theorem structuredTransition_notFrom_of_all
    {state : Nat} {l : List Structured.Transition}
    (h : l.all (structuredTransitionNotFromBool state) = true) :
    forall t : Structured.Transition, t ∈ l -> t.source ≠ state := by
  intro t ht
  have htbool := (List.all_eq_true.mp h) t ht
  simpa [structuredTransitionNotFromBool] using htbool

theorem structuredTransition_notFrom_of_chunk_all
    {state : Nat} {chunks : List (List Structured.Transition)}
    (h :
      chunks.all (fun l => l.all (structuredTransitionNotFromBool state)) =
        true) :
    forall t : Structured.Transition,
      t ∈ chunks.flatten -> t.source ≠ state :=
  structuredTransition_notFrom_of_all
    (list_all_flatten_of_chunk_all h)

/-! ## Description-level wrappers -/

def structuredDescriptionRowsWellFormedBool
    (D : Structured.Description) : Bool :=
  D.transitions.all
    (structuredTransitionWellFormedBool D.stateCount D.tapeCount)

def structuredDescriptionRowsDeterministicBool
    (D : Structured.Description) : Bool :=
  structuredTransitionTableDeterministicBool D.transitions

def structuredDescriptionRowsHaltFreeBool
    (D : Structured.Description) : Bool :=
  D.transitions.all (structuredTransitionNotFromBool D.halt)

def structuredDescriptionHeaderWellFormedBool
    (D : Structured.Description) : Bool :=
  decide (0 < D.tapeCount) &&
    decide (0 < D.stateCount) &&
    decide (D.start < D.stateCount) &&
    decide (D.halt < D.stateCount)

def structuredDescriptionWellFormedBool
    (D : Structured.Description) : Bool :=
  structuredDescriptionHeaderWellFormedBool D &&
    structuredDescriptionRowsWellFormedBool D &&
    structuredDescriptionRowsDeterministicBool D

def structuredDescriptionSubroutineReadyBool
    (D : Structured.Description) : Bool :=
  structuredDescriptionWellFormedBool D &&
    structuredDescriptionRowsHaltFreeBool D

theorem structuredDescription_wellFormed_of_transition_checks
    (D : Structured.Description)
    (htape : 0 < D.tapeCount)
    (hstate : 0 < D.stateCount)
    (hstart : D.start < D.stateCount)
    (hhalt : D.halt < D.stateCount)
    (hwell : structuredDescriptionRowsWellFormedBool D = true)
    (hdet : structuredDescriptionRowsDeterministicBool D = true) :
    D.WellFormed := by
  refine ⟨htape, hstate, hstart, hhalt, ?_, ?_⟩
  · exact
      structuredTransition_wellFormed_of_all
        (l := D.transitions)
        (stateCount := D.stateCount)
        (tapeCount := D.tapeCount)
        hwell
  · exact
      structuredTransition_deterministic_of_all
        (l := D.transitions)
        hdet

theorem structuredDescription_haltTransitionFree_of_transition_checks
    (D : Structured.Description)
    (hnot : structuredDescriptionRowsHaltFreeBool D = true) :
    D.HaltTransitionFree :=
  structuredTransition_notFrom_of_all
    (l := D.transitions)
    (state := D.halt)
    hnot

theorem structuredDescription_subroutineReady_of_transition_checks
    (D : Structured.Description)
    (htape : 0 < D.tapeCount)
    (hstate : 0 < D.stateCount)
    (hstart : D.start < D.stateCount)
    (hhalt : D.halt < D.stateCount)
    (hwell : structuredDescriptionRowsWellFormedBool D = true)
    (hdet : structuredDescriptionRowsDeterministicBool D = true)
    (hnot : structuredDescriptionRowsHaltFreeBool D = true) :
    D.SubroutineReady :=
  ⟨structuredDescription_wellFormed_of_transition_checks
      D htape hstate hstart hhalt hwell hdet,
    structuredDescription_haltTransitionFree_of_transition_checks D hnot⟩

theorem structuredDescription_wellFormed_of_bool
    (D : Structured.Description)
    (h : structuredDescriptionWellFormedBool D = true) :
    D.WellFormed := by
  have hparts :
      structuredDescriptionHeaderWellFormedBool D = true ∧
        structuredDescriptionRowsWellFormedBool D = true ∧
        structuredDescriptionRowsDeterministicBool D = true := by
    simpa [structuredDescriptionWellFormedBool, and_assoc] using h
  have hheader :
      decide (0 < D.tapeCount) = true ∧
        decide (0 < D.stateCount) = true ∧
        decide (D.start < D.stateCount) = true ∧
        decide (D.halt < D.stateCount) = true := by
    simpa [structuredDescriptionHeaderWellFormedBool, and_assoc] using
      hparts.left
  exact
    structuredDescription_wellFormed_of_transition_checks
      D
      (of_decide_eq_true hheader.left)
      (of_decide_eq_true hheader.right.left)
      (of_decide_eq_true hheader.right.right.left)
      (of_decide_eq_true hheader.right.right.right)
      hparts.right.left
      hparts.right.right

theorem structuredDescription_haltTransitionFree_of_bool
    (D : Structured.Description)
    (h : structuredDescriptionRowsHaltFreeBool D = true) :
    D.HaltTransitionFree :=
  structuredDescription_haltTransitionFree_of_transition_checks D h

theorem structuredDescription_subroutineReady_of_bool
    (D : Structured.Description)
    (h : structuredDescriptionSubroutineReadyBool D = true) :
    D.SubroutineReady := by
  have hparts :
      structuredDescriptionWellFormedBool D = true ∧
        structuredDescriptionRowsHaltFreeBool D = true := by
    simpa [structuredDescriptionSubroutineReadyBool] using h
  exact
    ⟨structuredDescription_wellFormed_of_bool D hparts.left,
      structuredDescription_haltTransitionFree_of_bool D hparts.right⟩

theorem structuredDescription_subroutineReady_of_ready_checks
    (D : Structured.Description)
    (hwell : D.WellFormed)
    (hnot : structuredDescriptionRowsHaltFreeBool D = true) :
    D.SubroutineReady :=
  ⟨hwell, structuredDescription_haltTransitionFree_of_transition_checks D hnot⟩

end FiniteTransducers
end CommonGround

end Computability
end FoC

import FoC.Computability.Encoding

set_option doc.verso true

/-!
# Transition-table checking helpers
-/

namespace FoC
namespace Computability

def transitionWellFormedBool
    (stateCount : Nat) (t : TransitionDescription) : Bool :=
  decide (t.source < stateCount) && decide (t.target < stateCount)

def transitionSameKeyBool
    (t u : TransitionDescription) : Bool :=
  decide (t.source = u.source) && decide (t.read = u.read)

def transitionSameActionBool
    (t u : TransitionDescription) : Bool :=
  decide (t.write = u.write) && decide (t.move = u.move) &&
    decide (t.target = u.target)

def transitionDeterministicPairBool
    (t u : TransitionDescription) : Bool :=
  !transitionSameKeyBool t u || transitionSameActionBool t u

def transitionPairAllBool
    (l r : List TransitionDescription) : Bool :=
  l.all (fun t =>
    r.all (fun u => transitionDeterministicPairBool t u))

def transitionChunksDeterministicBool
    (chunks : List (List TransitionDescription)) : Bool :=
  chunks.all (fun l =>
    chunks.all (fun r => transitionPairAllBool l r))

def transitionNotFromBool
    (state : Nat) (t : TransitionDescription) : Bool :=
  decide (t.source ≠ state)

theorem list_all_flatten_of_chunk_all
    {α : Type} {p : α -> Bool} {chunks : List (List α)}
    (h : chunks.all (fun l => l.all p) = true) :
    chunks.flatten.all p = true := by
  apply List.all_eq_true.mpr
  intro x hx
  rw [List.mem_flatten] at hx
  rcases hx with ⟨l, hl, hx⟩
  exact List.all_eq_true.mp (List.all_eq_true.mp h l hl) x hx

theorem transition_wellFormed_of_all
    {stateCount : Nat} {l : List TransitionDescription}
    (h : l.all (transitionWellFormedBool stateCount) = true) :
    forall t : TransitionDescription,
      t ∈ l -> TransitionDescription.WellFormed stateCount t := by
  intro t ht
  have htbool := (List.all_eq_true.mp h) t ht
  simpa [transitionWellFormedBool, TransitionDescription.WellFormed] using
    htbool

theorem transition_wellFormed_of_chunk_all
    {stateCount : Nat} {chunks : List (List TransitionDescription)}
    (h :
      chunks.all (fun l => l.all (transitionWellFormedBool stateCount)) =
        true) :
    forall t : TransitionDescription,
      t ∈ chunks.flatten ->
        TransitionDescription.WellFormed stateCount t :=
  transition_wellFormed_of_all
    (list_all_flatten_of_chunk_all h)

theorem transition_deterministic_of_all
    {l : List TransitionDescription}
    (h :
      l.all (fun t =>
        l.all (fun u => transitionDeterministicPairBool t u)) = true) :
    forall t u : TransitionDescription,
      t ∈ l ->
      u ∈ l ->
      TransitionDescription.SameKey t u ->
        TransitionDescription.SameAction t u := by
  intro t u ht hu hkey
  have htbool := (List.all_eq_true.mp h) t ht
  have hubool := (List.all_eq_true.mp htbool) u hu
  have hkeyBool :
      transitionSameKeyBool t u = true := by
    simpa [transitionSameKeyBool, TransitionDescription.SameKey] using hkey
  simpa [transitionDeterministicPairBool, hkeyBool, transitionSameActionBool,
    TransitionDescription.SameAction, and_assoc] using hubool

theorem transition_deterministic_bool_flatten_of_chunks
    {chunks : List (List TransitionDescription)}
    (h : transitionChunksDeterministicBool chunks = true) :
    chunks.flatten.all (fun t =>
      chunks.flatten.all (fun u => transitionDeterministicPairBool t u)) =
        true := by
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

theorem transition_deterministic_of_chunk_all
    {chunks : List (List TransitionDescription)}
    (h : transitionChunksDeterministicBool chunks = true) :
    forall t u : TransitionDescription,
      t ∈ chunks.flatten ->
      u ∈ chunks.flatten ->
      TransitionDescription.SameKey t u ->
        TransitionDescription.SameAction t u :=
  transition_deterministic_of_all
    (transition_deterministic_bool_flatten_of_chunks h)

theorem transition_notFrom_of_all
    {state : Nat} {l : List TransitionDescription}
    (h : l.all (transitionNotFromBool state) = true) :
    forall t : TransitionDescription, t ∈ l -> t.source ≠ state := by
  intro t ht
  have htbool := (List.all_eq_true.mp h) t ht
  exact of_decide_eq_true htbool

theorem transition_notFrom_of_chunk_all
    {state : Nat} {chunks : List (List TransitionDescription)}
    (h :
      chunks.all (fun l => l.all (transitionNotFromBool state)) = true) :
    forall t : TransitionDescription,
      t ∈ chunks.flatten -> t.source ≠ state :=
  transition_notFrom_of_all
    (list_all_flatten_of_chunk_all h)

end Computability
end FoC

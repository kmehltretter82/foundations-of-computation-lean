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

def transitionNotFromBool
    (state : Nat) (t : TransitionDescription) : Bool :=
  decide (t.source ≠ state)

theorem transition_wellFormed_of_all
    {stateCount : Nat} {l : List TransitionDescription}
    (h : l.all (transitionWellFormedBool stateCount) = true) :
    forall t : TransitionDescription,
      t ∈ l -> TransitionDescription.WellFormed stateCount t := by
  intro t ht
  have htbool := (List.all_eq_true.mp h) t ht
  simpa [transitionWellFormedBool, TransitionDescription.WellFormed] using
    htbool

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
  simp [transitionDeterministicPairBool, hkeyBool, transitionSameActionBool,
    TransitionDescription.SameAction] at hubool ⊢
  rcases hubool with ⟨⟨hwrite, hmove⟩, htarget⟩
  exact ⟨hwrite, hmove, htarget⟩

theorem transition_notFrom_of_all
    {state : Nat} {l : List TransitionDescription}
    (h : l.all (transitionNotFromBool state) = true) :
    forall t : TransitionDescription, t ∈ l -> t.source ≠ state := by
  intro t ht
  have htbool := (List.all_eq_true.mp h) t ht
  exact of_decide_eq_true htbool

end Computability
end FoC

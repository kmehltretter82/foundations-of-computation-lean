import FoC.Computability.MachineBuilder.StateTables

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

/-- Executably check all clauses of finite-description well-formedness. -/
def machineDescriptionWellFormedBool (D : MachineDescription) : Bool :=
  decide (0 < D.stateCount) &&
    decide (D.start < D.stateCount) &&
    decide (D.halt < D.stateCount) &&
    D.transitions.all (transitionWellFormedBool D.stateCount) &&
    D.transitions.all (fun t =>
      D.transitions.all (fun u => transitionDeterministicPairBool t u))

/-- The pairwise Boolean check is exactly deterministic-key compatibility. -/
theorem transitionDeterministicPairBool_eq_true_iff
    (t u : TransitionDescription) :
    transitionDeterministicPairBool t u = true <->
      (TransitionDescription.SameKey t u ->
        TransitionDescription.SameAction t u) := by
  constructor
  · intro h hkey
    have hkeyBool : transitionSameKeyBool t u = true := by
      simpa [transitionSameKeyBool, TransitionDescription.SameKey] using hkey
    simpa [transitionDeterministicPairBool, hkeyBool,
      transitionSameActionBool, TransitionDescription.SameAction, and_assoc]
      using h
  · intro h
    by_cases hsource : t.source = u.source
    · by_cases hread : t.read = u.read
      · have haction := h (And.intro hsource hread)
        simpa [transitionDeterministicPairBool, transitionSameKeyBool,
          transitionSameActionBool, TransitionDescription.SameAction,
          hsource, hread, and_assoc] using haction
      · simp [transitionDeterministicPairBool, transitionSameKeyBool,
          hsource, hread]
    · simp [transitionDeterministicPairBool, transitionSameKeyBool, hsource]

private theorem list_all_flatten_of_chunk_all
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

private theorem transition_deterministic_bool_flatten_of_chunks
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

theorem machineDescription_wellFormed_of_transition_checks
    (D : MachineDescription)
    (hstate : 0 < D.stateCount)
    (hstart : D.start < D.stateCount)
    (hhalt : D.halt < D.stateCount)
    (hwell :
      D.transitions.all (transitionWellFormedBool D.stateCount) = true)
    (hdet :
      D.transitions.all (fun t =>
        D.transitions.all (fun u =>
          transitionDeterministicPairBool t u)) = true) :
    D.WellFormed := by
  refine ⟨hstate, hstart, hhalt, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := D.transitions)
      (stateCount := D.stateCount)
      hwell
  · exact transition_deterministic_of_all
      (l := D.transitions)
      hdet

/-- The executable description checker is sound and complete. -/
theorem machineDescriptionWellFormedBool_eq_true_iff
    (D : MachineDescription) :
    machineDescriptionWellFormedBool D = true <-> D.WellFormed := by
  simp only [machineDescriptionWellFormedBool, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · intro h
    rcases h with ⟨⟨⟨⟨hstate, hstart⟩, hhalt⟩, hwell⟩, hdet⟩
    exact machineDescription_wellFormed_of_transition_checks
      D hstate hstart hhalt hwell hdet
  · intro h
    rcases h with ⟨hstate, hstart, hhalt, hwell, hdet⟩
    refine ⟨⟨⟨⟨hstate, hstart⟩, hhalt⟩, ?_⟩, ?_⟩
    · apply List.all_eq_true.mpr
      intro t ht
      simpa [transitionWellFormedBool, TransitionDescription.WellFormed]
        using hwell t ht
    · apply List.all_eq_true.mpr
      intro t ht
      apply List.all_eq_true.mpr
      intro u hu
      exact (transitionDeterministicPairBool_eq_true_iff t u).mpr
        (hdet t u ht hu)

theorem machineDescription_haltTransitionFree_of_transition_checks
    (D : MachineDescription)
    (hnot :
      D.transitions.all (transitionNotFromBool D.halt) = true) :
    D.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := D.transitions)
    (state := D.halt)
    hnot

theorem machineDescription_subroutineReady_of_transition_checks
    (D : MachineDescription)
    (hstate : 0 < D.stateCount)
    (hstart : D.start < D.stateCount)
    (hhalt : D.halt < D.stateCount)
    (hwell :
      D.transitions.all (transitionWellFormedBool D.stateCount) = true)
    (hdet :
      D.transitions.all (fun t =>
        D.transitions.all (fun u =>
          transitionDeterministicPairBool t u)) = true)
    (hnot :
      D.transitions.all (transitionNotFromBool D.halt) = true) :
    D.SubroutineReady :=
  ⟨machineDescription_wellFormed_of_transition_checks
      D hstate hstart hhalt hwell hdet,
    machineDescription_haltTransitionFree_of_transition_checks
      D hnot⟩

end Computability
end FoC

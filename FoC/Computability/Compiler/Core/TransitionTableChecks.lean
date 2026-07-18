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

/-- Rank the three possible symbols read by a Boolean transition. -/
def transitionReadRank : Option Bool -> Nat
  | none => 0
  | some false => 1
  | some true => 2

/-- Injectively rank a Boolean transition's lookup key. -/
def transitionKeyRank (row : TransitionDescription) : Nat :=
  3 * row.source + transitionReadRank row.read

private def natAdjacentIncreasing : List Nat -> Prop
  | [] => True
  | [_] => True
  | first :: second :: rest =>
      first < second ∧ natAdjacentIncreasing (second :: rest)

private def natAdjacentIncreasingBool : List Nat -> Bool
  | [] => true
  | [_] => true
  | first :: second :: rest =>
      decide (first < second) &&
        natAdjacentIncreasingBool (second :: rest)

/-- Check that the lookup-key ranks in a transition table strictly increase. -/
def transitionKeyRanksAdjacentIncreasingBool
    (rows : List TransitionDescription) : Bool :=
  natAdjacentIncreasingBool (rows.map transitionKeyRank)

private theorem natAdjacentIncreasing_of_bool
    {values : List Nat}
    (h : natAdjacentIncreasingBool values = true) :
    natAdjacentIncreasing values := by
  induction values with
  | nil => trivial
  | cons first rest ih =>
      cases rest with
      | nil => trivial
      | cons second tail =>
          simp only [natAdjacentIncreasingBool, Bool.and_eq_true,
            decide_eq_true_eq] at h
          exact And.intro h.1 (ih h.2)

private theorem natAdjacentIncreasing_tail
    {first : Nat} {rest : List Nat}
    (h : natAdjacentIncreasing (first :: rest)) :
    natAdjacentIncreasing rest := by
  cases rest with
  | nil => trivial
  | cons second tail => exact h.2

private theorem natAdjacentIncreasing_head_lt_of_mem
    {first value : Nat} {rest : List Nat}
    (h : natAdjacentIncreasing (first :: rest))
    (hvalue : value ∈ rest) :
    first < value := by
  induction rest generalizing first with
  | nil => simp at hvalue
  | cons second tail ih =>
      rcases h with ⟨hfirst, htail⟩
      simp only [List.mem_cons] at hvalue
      rcases hvalue with rfl | hvalue
      · exact hfirst
      · exact Nat.lt_trans hfirst (ih htail hvalue)

private theorem nat_nodup_of_adjacentIncreasing
    {values : List Nat}
    (h : natAdjacentIncreasing values) : values.Nodup := by
  induction values with
  | nil => exact List.nodup_nil
  | cons first rest ih =>
      apply List.nodup_cons.mpr
      refine And.intro ?_ (ih (natAdjacentIncreasing_tail h))
      intro hmem
      exact (Nat.lt_irrefl first)
        (natAdjacentIncreasing_head_lt_of_mem h hmem)

private theorem eq_of_mem_of_mem_of_transitionKeyRank_eq
    {rows : List TransitionDescription} {left right : TransitionDescription}
    (hnodup : (rows.map transitionKeyRank).Nodup)
    (hleft : left ∈ rows) (hright : right ∈ rows)
    (hkey : transitionKeyRank left = transitionKeyRank right) :
    left = right := by
  induction rows with
  | nil =>
      simp at hleft
  | cons first rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      rcases hnodup with ⟨hfirst, hrest⟩
      simp only [List.mem_cons] at hleft hright
      rcases hleft with rfl | hleft
      · rcases hright with rfl | hright
        · rfl
        · exfalso
          apply hfirst
          rw [hkey]
          exact List.mem_map.mpr ⟨right, hright, rfl⟩
      · rcases hright with rfl | hright
        · exfalso
          apply hfirst
          rw [← hkey]
          exact List.mem_map.mpr ⟨left, hleft, rfl⟩
        · exact ih hrest hleft hright

/-- Strictly increasing lookup-key ranks certify table determinism in linear
time, avoiding the quadratic executable pair check for generated tables. -/
theorem transition_deterministic_of_keyRanksAdjacentIncreasingBool
    {rows : List TransitionDescription}
    (h : transitionKeyRanksAdjacentIncreasingBool rows = true) :
    forall left right : TransitionDescription,
      left ∈ rows ->
      right ∈ rows ->
      TransitionDescription.SameKey left right ->
        TransitionDescription.SameAction left right := by
  have hincreasing :
      natAdjacentIncreasing (rows.map transitionKeyRank) := by
    apply natAdjacentIncreasing_of_bool
    simpa [transitionKeyRanksAdjacentIncreasingBool] using h
  have hnodup : (rows.map transitionKeyRank).Nodup :=
    nat_nodup_of_adjacentIncreasing hincreasing
  intro left right hleft hright hsameKey
  have hkey : transitionKeyRank left = transitionKeyRank right := by
    simp [transitionKeyRank, hsameKey.1, hsameKey.2]
  have heq := eq_of_mem_of_mem_of_transitionKeyRank_eq
    hnodup hleft hright hkey
  subst right
  exact ⟨rfl, rfl, rfl⟩

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

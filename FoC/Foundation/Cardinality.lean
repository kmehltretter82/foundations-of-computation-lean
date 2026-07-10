import FoC.Foundation.Finite
import FoC.Foundation.Functions

set_option doc.verso true

/-!
# Finite cardinality

## Finite-cardinality models

The book's finite-cardinality laws are represented by explicit list models:
products are nested lists of pairs, powersets are lists of sublists, and
function spaces are lists of finite tuples. Duplicate-free enumeration is the
bridge from these list models back to finite sets: cardinality is unique,
every set with a cardinality is finite, every finite set with decidable
equality has a cardinality, and the product and union cardinality laws are
proved for predicate sets themselves.

The finite pigeonhole principle uses the same bridge: map the duplicate-free
enumeration of the larger set into the smaller one, then compare list lengths.
The initial segments of the natural numbers model the book's counting sets
{lit}`N_n`, including the theorem that distinct segments admit no one-to-one
correspondence.

## Book coordinates

Used by:
- Chapter 2, Section 2.6: finite cardinality arithmetic
- Later finite-state models with explicit state/alphabet lists
-/

namespace FoC
namespace Foundation

namespace FSet

/-!
**Cardinality witnesses.**

Cardinality is defined by a duplicate-free finite enumeration whose length is
the displayed cardinal.  The first lemmas transport that witness across
extensional equality and give the empty and singleton cases.
-/

def HasCardinality (A : FSet alpha) (n : Nat) : Prop :=
  exists xs : List alpha, ListUniquelyEnumerates xs A ∧ xs.length = n

theorem hasCardinality_of_equal {A B : FSet alpha} {n : Nat}
    (hAB : Equal A B) (hA : HasCardinality A n) : HasCardinality B n := by
  cases hA with
  | intro xs hxs =>
      exists xs
      constructor
      · constructor
        · exact hxs.left.left
        · intro x
          constructor
          · intro hxB
            exact (hxs.left.right x).mp ((hAB x).mpr hxB)
          · intro hx
            exact (hAB x).mp ((hxs.left.right x).mpr hx)
      · exact hxs.right

theorem empty_has_cardinality_zero : HasCardinality (Empty : FSet alpha) 0 := by
  exists []
  constructor
  · constructor
    · simp [ListDuplicateFree]
    · intro x
      constructor
      · intro hx
        cases hx
      · intro hx
        cases hx
  · rfl

theorem singleton_has_cardinality_one (a : alpha) :
    HasCardinality (Singleton a) 1 := by
  exists [a]
  constructor
  · constructor
    · simp [ListDuplicateFree]
    · intro x
      constructor
      · intro hx
        rw [hx]
        exact List.Mem.head []
      · intro hx
        cases hx with
        | head => rfl
        | tail _ htail => cases htail
  · rfl

/-!
**Finite pigeonhole principle.**

If a function maps every member of a finite set {lit}`A` into a finite set
{lit}`B` and is injective on {lit}`A`, then {lit}`A` cannot have larger
cardinality than {lit}`B`.  The contrapositive gives the book-facing
pigeonhole theorem: a map from more listed objects into fewer listed boxes must
identify two distinct inputs.
-/

theorem cardinality_le_of_injective_maps_to {A : FSet alpha} {B : FSet beta}
    {m n : Nat} [DecidableEq beta]
    (hA : HasCardinality A m) (hB : HasCardinality B n)
    (f : alpha -> beta)
    (hinj : forall {x y}, x ∈ A -> y ∈ A -> f x = f y -> x = y)
    (hmap : forall x, x ∈ A -> f x ∈ B) : m <= n := by
  cases hA with
  | intro xs hxs =>
      cases hB with
      | intro ys hys =>
          have hndImage : (xs.map f).Nodup :=
            list_nodup_map_of_injective_on_list hxs.left.left (by
              intro a b ha hb hfab
              exact hinj
                ((hxs.left.right a).mpr ha)
                ((hxs.left.right b).mpr hb)
                hfab)
          have hsub : forall y, y ∈ xs.map f -> y ∈ ys := by
            intro y hy
            cases (List.mem_map).mp hy with
            | intro x hx =>
                have hxA : x ∈ A := (hxs.left.right x).mpr hx.left
                have hfyB : f x ∈ B := hmap x hxA
                exact (hys.left.right y).mp (by
                  rw [← hx.right]
                  exact hfyB)
          have hle := list_nodup_length_le_of_subset hndImage hsub
          simpa [List.length_map, hxs.right, hys.right] using hle

theorem not_injective_of_cardinality_lt_maps_to {A : FSet alpha} {B : FSet beta}
    {m n : Nat} [DecidableEq beta]
    (hA : HasCardinality A m) (hB : HasCardinality B n)
    (hlt : n < m) (f : alpha -> beta)
    (hmap : forall x, x ∈ A -> f x ∈ B) :
    ¬ Fn.Injective f := by
  intro hf
  have hle : m <= n :=
    cardinality_le_of_injective_maps_to hA hB f
      (by
        intro x y _hx _hy hxy
        exact hf hxy)
      hmap
  lia

theorem pigeonhole_collision_of_cardinality_lt {A : FSet alpha} {B : FSet beta}
    {m n : Nat} [DecidableEq beta]
    (hA : HasCardinality A m) (hB : HasCardinality B n)
    (hlt : n < m) (f : alpha -> beta)
    (hmap : forall x, x ∈ A -> f x ∈ B) :
    exists x y, x ∈ A ∧ y ∈ A ∧ x ≠ y ∧ f x = f y := by
  classical
  apply Classical.byContradiction
  intro hno
  have hinjOn : forall {x y}, x ∈ A -> y ∈ A -> f x = f y -> x = y := by
    intro x y hx hy hxy
    by_cases hEq : x = y
    · exact hEq
    · exfalso
      apply hno
      exact Exists.intro x
        (Exists.intro y
          (And.intro hx
            (And.intro hy
              (And.intro hEq hxy))))
  have hle : m <= n :=
    cardinality_le_of_injective_maps_to hA hB f hinjOn hmap
  lia

/-!
**Cardinality is well-defined.**

Exercise 5 from Section 2.6 asks for the key sanity property of finite
cardinality: any two duplicate-free enumerations of the same set have the same
length.  The subset form compares enumerations of a set and a superset; the
uniqueness theorem follows by comparing a set with itself.
-/

theorem hasCardinality_le_of_subset {A B : FSet alpha} {m n : Nat}
    [DecidableEq alpha]
    (hAB : Subset A B) (hA : HasCardinality A m) (hB : HasCardinality B n) :
    m <= n := by
  cases hA with
  | intro xs hxs =>
      cases hB with
      | intro ys hys =>
          have hsub : forall a, a ∈ xs -> a ∈ ys := by
            intro a ha
            exact (hys.left.right a).mp (hAB a ((hxs.left.right a).mpr ha))
          have hle := list_nodup_length_le_of_subset hxs.left.left hsub
          rw [hxs.right, hys.right] at hle
          exact hle

theorem hasCardinality_unique {A : FSet alpha} {m n : Nat} [DecidableEq alpha]
    (hm : HasCardinality A m) (hn : HasCardinality A n) : m = n := by
  apply Nat.le_antisymm
  · exact hasCardinality_le_of_subset (fun _ hx => hx) hm hn
  · exact hasCardinality_le_of_subset (fun _ hx => hx) hn hm

theorem hasCardinality_unique_classical {A : FSet alpha} {m n : Nat}
    (hm : HasCardinality A m) (hn : HasCardinality A n) : m = n := by
  classical
  exact hasCardinality_unique hm hn

/-!
**Bridges to finiteness.**

A cardinality witness is in particular a finite enumeration.  Conversely,
deduplicating a finite enumeration produces a cardinality witness, so every
finite set has some cardinality.
-/

theorem finite_of_hasCardinality {A : FSet alpha} {n : Nat}
    (h : HasCardinality A n) : Finite A := by
  cases h with
  | intro xs hxs =>
      exact Exists.intro xs hxs.left.right

theorem exists_hasCardinality_of_finite [DecidableEq alpha] {A : FSet alpha}
    (h : Finite A) : exists n, HasCardinality A n := by
  cases finiteWithNoDuplicates_of_finite h with
  | intro xs hxs =>
      exact Exists.intro xs.length (Exists.intro xs (And.intro hxs rfl))

theorem exists_hasCardinality_of_finite_classical {A : FSet alpha}
    (h : Finite A) : exists n, HasCardinality A n := by
  classical
  exact exists_hasCardinality_of_finite h

/-!
**Counting segments.**

The book's basis for counting is the family of initial segments
{lit}`N_n = {0, 1, ..., n-1}` of the natural numbers.  Each segment has
cardinality {lit}`n`.  Theorem 2.6 of Section 2.6 states that distinct
segments admit no one-to-one correspondence: any function that maps
{lit}`N_m` into {lit}`N_n` injectively and onto forces {lit}`m = n`.
-/

def Segment (n : Nat) : FSet Nat :=
  fun k => k < n

theorem segment_hasCardinality (n : Nat) : HasCardinality (Segment n) n := by
  exists List.range n
  constructor
  · constructor
    · exact List.nodup_range
    · intro x
      constructor
      · intro hx
        exact List.mem_range.mpr hx
      · intro hx
        exact List.mem_range.mp hx
  · simp

theorem segment_correspondence_eq {m n : Nat} (f : Nat -> Nat)
    (hmap : forall x, x ∈ Segment m -> f x ∈ Segment n)
    (hinj : forall x y, x ∈ Segment m -> y ∈ Segment m -> f x = f y -> x = y)
    (hsurj : forall y, y ∈ Segment n -> exists x, x ∈ Segment m ∧ f x = y) :
    m = n := by
  apply Nat.le_antisymm
  · exact cardinality_le_of_injective_maps_to
      (segment_hasCardinality m) (segment_hasCardinality n) f
      (by
        intro x y hx hy hxy
        exact hinj x y hx hy hxy)
      hmap
  · have hsub : forall y, y ∈ List.range n -> y ∈ (List.range m).map f := by
      intro y hy
      cases hsurj y (List.mem_range.mp hy) with
      | intro x hx =>
          exact List.mem_map.mpr
            (Exists.intro x (And.intro (List.mem_range.mpr hx.left) hx.right))
    have hle := list_nodup_length_le_of_subset List.nodup_range hsub
    simpa using hle

theorem no_segment_correspondence_of_ne {m n : Nat} (hmn : m ≠ n)
    (f : Nat -> Nat) :
    ¬ ((forall x, x ∈ Segment m -> f x ∈ Segment n) ∧
        (forall x y, x ∈ Segment m -> y ∈ Segment m -> f x = f y -> x = y) ∧
        (forall y, y ∈ Segment n -> exists x, x ∈ Segment m ∧ f x = y)) := by
  intro h
  exact hmn (segment_correspondence_eq f h.left h.right.left h.right.right)

end FSet

namespace ListCard

/-!
**Products and disjoint parts.**

The finite-cardinality theorems are proved first as list-length identities.
Product cardinality uses nested lists of pairs, and union arithmetic is reduced
to disjoint parts.
-/

def Pairs {alpha : Type u} {beta : Type v} : List alpha -> List beta -> List (alpha × beta)
  | [], _ => []
  | x :: xs, ys => (ys.map fun y => (x, y)) ++ Pairs xs ys

/-!
Product cardinality is first proved at the list level: a nested list of pairs
has length equal to the product of the input lengths.
-/
theorem length_pairs {alpha : Type u} {beta : Type v} (xs : List alpha) (ys : List beta) :
    (Pairs xs ys).length = xs.length * ys.length := by
  induction xs with
  | nil => simp [Pairs]
  | cons x xs ih =>
      simp [Pairs, ih, Nat.add_mul, Nat.add_comm]

/-!
The pair list is a faithful model of the cross product: it contains exactly
the pairs with coordinates from the two input lists, and it is duplicate-free
whenever both inputs are.  These two lemmas upgrade the length identity above
to the set-level product cardinality law proved at the end of this module.
-/
theorem mem_pairs {alpha : Type u} {beta : Type v}
    {xs : List alpha} {ys : List beta} {p : alpha × beta} :
    p ∈ Pairs xs ys <-> p.1 ∈ xs ∧ p.2 ∈ ys := by
  induction xs with
  | nil =>
      simp [Pairs]
  | cons x xs ih =>
      simp only [Pairs]
      constructor
      · intro hp
        cases List.mem_append.mp hp with
        | inl hleft =>
            cases List.mem_map.mp hleft with
            | intro y hy =>
                rw [← hy.right]
                exact And.intro (List.Mem.head xs) hy.left
        | inr hright =>
            have h := ih.mp hright
            exact And.intro (List.Mem.tail x h.left) h.right
      · intro hp
        cases p with
        | mk a b =>
            cases hp.left with
            | head =>
                exact List.mem_append.mpr
                  (Or.inl (List.mem_map.mpr
                    (Exists.intro b (And.intro hp.right rfl))))
            | tail _ ha =>
                exact List.mem_append.mpr
                  (Or.inr (ih.mpr (And.intro ha hp.right)))

theorem pairs_nodup {alpha : Type u} {beta : Type v}
    {xs : List alpha} {ys : List beta}
    (hxs : xs.Nodup) (hys : ys.Nodup) : (Pairs xs ys).Nodup := by
  induction xs with
  | nil =>
      simp [Pairs]
  | cons x xs ih =>
      rw [List.nodup_cons] at hxs
      simp only [Pairs]
      rw [List.nodup_append]
      constructor
      · exact list_nodup_map_of_injective_on_list hys (by
          intro a b _ _ hab
          have hsnd := congrArg Prod.snd hab
          simpa using hsnd)
      constructor
      · exact ih hxs.right
      · intro p hp q hq hpq
        cases List.mem_map.mp hp with
        | intro y hy =>
            have hq1 : q.1 ∈ xs := (mem_pairs.mp hq).left
            rw [← hpq, ← hy.right] at hq1
            exact hxs.left hq1

/-!
Disjoint union cardinality is represented by appending the two finite lists.
-/
theorem length_append (xs ys : List alpha) :
    (xs ++ ys).length = xs.length + ys.length := by
  exact List.length_append

/-!
This identity is the arithmetic core of inclusion-exclusion: splitting a union
into elements only on the left, elements in both sets, and elements only on
the right.  It carries no set content by itself; the genuine set-level law is
{lit}`FSet.union_hasCardinality_inclusion_exclusion`, proved at the end of
this module.
-/
theorem union_cardinality_by_parts (leftOnly both rightOnly : Nat) :
    leftOnly + both + rightOnly =
      (leftOnly + both) + (both + rightOnly) - both := by
  lia

/-!
**Powersets.**

The powerset model enumerates sublists.  Each input element is either omitted or
included, yielding the expected power-of-two length.
-/

def Sublists {alpha : Type u} : List alpha -> List (List alpha)
  | [] => [[]]
  | x :: xs => Sublists xs ++ (Sublists xs).map (fun ys => x :: ys)

/-!
The powerset model enumerates all sublists.  Its length is {lit}`2 ^ n`, matching the
book's finite powerset cardinality law.
-/
theorem length_sublists {alpha : Type u} (xs : List alpha) :
    (Sublists xs).length = 2 ^ xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [Sublists, ih, Nat.pow_succ]
      lia

/-!
The sublist model is complete: the enumerated lists are exactly the sublists
(in the sense of {name}`List.Sublist`) of the input.  When the input list is
duplicate-free, the enumeration itself is duplicate-free, so its length
{lit}`2 ^ n` is an honest count of the distinct sublists.  Together these
lemmas justify reading {name}`length_sublists` as the powerset cardinality law
for a set presented by a duplicate-free enumeration.
-/
theorem mem_sublists {alpha : Type u} {xs l : List alpha} :
    l ∈ Sublists xs <-> l.Sublist xs := by
  induction xs generalizing l with
  | nil =>
      simp [Sublists, List.sublist_nil]
  | cons x xs ih =>
      simp only [Sublists]
      constructor
      · intro hl
        cases List.mem_append.mp hl with
        | inl h =>
            exact List.Sublist.cons x (ih.mp h)
        | inr h =>
            cases List.mem_map.mp h with
            | intro t ht =>
                rw [← ht.right]
                exact List.Sublist.cons_cons x (ih.mp ht.left)
      · intro hl
        cases hl with
        | cons _ h =>
            exact List.mem_append.mpr (Or.inl (ih.mpr h))
        | cons_cons _ h =>
            exact List.mem_append.mpr
              (Or.inr (List.mem_map.mpr
                (Exists.intro _ (And.intro (ih.mpr h) rfl))))

theorem sublists_nodup {alpha : Type u} {xs : List alpha}
    (hxs : xs.Nodup) : (Sublists xs).Nodup := by
  induction xs with
  | nil =>
      simp [Sublists]
  | cons x xs ih =>
      rw [List.nodup_cons] at hxs
      simp only [Sublists]
      rw [List.nodup_append]
      constructor
      · exact ih hxs.right
      constructor
      · exact list_nodup_map_of_injective_on_list (ih hxs.right) (by
          intro a b _ _ hab
          injection hab)
      · intro l hl t ht hlt
        cases List.mem_map.mp ht with
        | intro t' ht' =>
            have hsub := mem_sublists.mp hl
            rw [hlt, ← ht'.right] at hsub
            exact hxs.left (hsub.subset (List.Mem.head t'))

private theorem sublist_eq_of_same_members {alpha : Type u}
    {xs l t : List alpha} (hxs : xs.Nodup)
    (hl : l.Sublist xs) (ht : t.Sublist xs)
    (hmem : forall x, x ∈ l <-> x ∈ t) : l = t := by
  induction hxs generalizing l t with
  | nil =>
      cases hl
      cases ht
      rfl
  | @cons x xs hx hxs ih =>
      cases hl with
      | cons _ hl =>
          cases ht with
          | cons _ ht => exact ih hl ht hmem
          | cons_cons _ ht =>
              exact False.elim
                (hx x (hl.subset ((hmem x).mpr (List.Mem.head _))) rfl)
      | cons_cons _ hl =>
          cases ht with
          | cons _ ht =>
              exact False.elim
                (hx x (ht.subset ((hmem x).mp (List.Mem.head _))) rfl)
          | cons_cons _ ht =>
              congr 1
              apply ih hl ht
              intro a
              by_cases hax : a = x
              · subst a
                constructor <;> intro ha
                · exact False.elim (hx x (hl.subset ha) rfl)
                · exact False.elim (hx x (ht.subset ha) rfl)
              · simpa [hax] using hmem a

/-!
**Function spaces.**

Finite function spaces are modeled as fixed-length tuples of choices.  The tuple
length theorem is the list-level core of the book's finite function-space
cardinality law.
-/

private def ExtendTuples {alpha : Type u} (choices : List alpha) : List (List alpha) -> List (List alpha)
  | [] => []
  | tail :: tails => (choices.map fun x => x :: tail) ++ ExtendTuples choices tails

def Tuples {alpha : Type u} (choices : List alpha) : Nat -> List (List alpha)
  | 0 => [[]]
  | n + 1 => ExtendTuples choices (Tuples choices n)

private theorem length_extendTuples {alpha : Type u} (choices : List alpha) (tails : List (List alpha)) :
    (ExtendTuples choices tails).length = tails.length * choices.length := by
  induction tails with
  | nil => simp [ExtendTuples]
  | cons tail tails ih =>
      simp [ExtendTuples, ih, Nat.add_mul, Nat.add_comm]

/-!
Finite function spaces are represented as tuples of choices.  If there are
{lit}`k` choices and {lit}`n` input positions, the tuple list has length
{lit}`k ^ n`.
-/
theorem length_tuples {alpha : Type u} (choices : List alpha) (n : Nat) :
    (Tuples choices n).length = choices.length ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Tuples, length_extendTuples, ih, Nat.pow_succ]

private theorem mem_extendTuples {alpha : Type u} {choices : List alpha}
    {tails : List (List alpha)} {l : List alpha} :
    l ∈ ExtendTuples choices tails <->
      exists x t, x ∈ choices ∧ t ∈ tails ∧ l = x :: t := by
  induction tails with
  | nil =>
      simp [ExtendTuples]
  | cons tail tails ih =>
      simp only [ExtendTuples]
      constructor
      · intro hl
        cases List.mem_append.mp hl with
        | inl h =>
            cases List.mem_map.mp h with
            | intro x hx =>
                exact Exists.intro x (Exists.intro tail
                  (And.intro hx.left
                    (And.intro (List.Mem.head tails) hx.right.symm)))
        | inr h =>
            cases ih.mp h with
            | intro x hx =>
                cases hx with
                | intro t ht =>
                    exact Exists.intro x (Exists.intro t
                      (And.intro ht.left
                        (And.intro (List.Mem.tail tail ht.right.left)
                          ht.right.right)))
      · intro h
        cases h with
        | intro x hx =>
            cases hx with
            | intro t ht =>
                cases ht.right.left with
                | head =>
                    exact List.mem_append.mpr
                      (Or.inl (List.mem_map.mpr
                        (Exists.intro x
                          (And.intro ht.left ht.right.right.symm))))
                | tail _ ht' =>
                    exact List.mem_append.mpr
                      (Or.inr (ih.mpr (Exists.intro x (Exists.intro t
                        (And.intro ht.left
                          (And.intro ht' ht.right.right))))))

/-!
The tuple model is complete and duplicate-free: its members are exactly the
length-{lit}`n` lists drawn from the choice list, and the enumeration has no
duplicates when the choice list has none.  These lemmas upgrade
{name}`length_tuples` to an honest count of the distinct tuples.
-/
theorem mem_tuples {alpha : Type u} {choices : List alpha} {n : Nat}
    {l : List alpha} :
    l ∈ Tuples choices n <->
      l.length = n ∧ forall x, x ∈ l -> x ∈ choices := by
  induction n generalizing l with
  | zero =>
      simp only [Tuples]
      constructor
      · intro hl
        have hnil : l = [] := by
          cases hl with
          | head => rfl
          | tail _ h => cases h
        rw [hnil]
        exact And.intro rfl (by
          intro x hx
          cases hx)
      · intro h
        rw [List.length_eq_zero_iff.mp h.left]
        exact List.Mem.head []
  | succ n ih =>
      rw [Tuples, mem_extendTuples]
      constructor
      · intro h
        cases h with
        | intro x hx =>
            cases hx with
            | intro t ht =>
                have ht' := ih.mp ht.right.left
                rw [ht.right.right]
                constructor
                · simp [ht'.left]
                · intro y hy
                  cases hy with
                  | head => exact ht.left
                  | tail _ h => exact ht'.right y h
      · intro h
        cases l with
        | nil =>
            cases h.left
        | cons y t =>
            exact Exists.intro y (Exists.intro t
              (And.intro (h.right y (List.Mem.head t))
                (And.intro (ih.mpr (And.intro
                  (by
                    have hlen := h.left
                    simp at hlen
                    exact hlen)
                  (by
                    intro z hz
                    exact h.right z (List.Mem.tail y hz))))
                  rfl)))

private theorem extendTuples_nodup {alpha : Type u} {choices : List alpha}
    {tails : List (List alpha)}
    (hc : choices.Nodup) (ht : tails.Nodup) :
    (ExtendTuples choices tails).Nodup := by
  induction tails with
  | nil =>
      simp [ExtendTuples]
  | cons tail tails ih =>
      rw [List.nodup_cons] at ht
      simp only [ExtendTuples]
      rw [List.nodup_append]
      constructor
      · exact list_nodup_map_of_injective_on_list hc (by
          intro a b _ _ hab
          injection hab)
      constructor
      · exact ih ht.right
      · intro l hl t' ht' hlt
        cases List.mem_map.mp hl with
        | intro x hx =>
            cases mem_extendTuples.mp ht' with
            | intro y hy =>
                cases hy with
                | intro u hu =>
                    have hcons : x :: tail = y :: u := by
                      rw [hx.right, hlt, hu.right.right]
                    have htail : tail = u := by
                      injection hcons
                    apply ht.left
                    rw [htail]
                    exact hu.right.left

theorem tuples_nodup {alpha : Type u} {choices : List alpha}
    (hc : choices.Nodup) (n : Nat) : (Tuples choices n).Nodup := by
  induction n with
  | zero =>
      simp [Tuples]
  | succ n ih =>
      rw [Tuples]
      exact extendTuples_nodup hc ih

end ListCard

namespace FiniteType

/-!
**Finite powerset types.**

The powerset of a finite type is itself finite.  The construction enumerates
all sublists of a covering list and interprets each sublist extensionally as a
predicate set.  It is noncomputable because equality and membership of
arbitrary predicate sets are classical at this boundary.
-/

private theorem filter_mem_sublists (xs : List alpha) (p : alpha -> Prop)
    [DecidablePred p] :
    xs.filter (fun x => decide (p x)) ∈ ListCard.Sublists xs := by
  induction xs with
  | nil =>
      simp [ListCard.Sublists]
  | cons x rest ih =>
      by_cases hx : p x
      · apply List.mem_append.mpr
        apply Or.inr
        apply List.mem_map.mpr
        exists rest.filter (fun y => decide (p y))
        constructor
        · exact ih
        · simp [hx]
      · apply List.mem_append.mpr
        apply Or.inl
        simpa [hx] using ih

/-- A classical finite witness for all predicate subsets of a finite type. -/
noncomputable def powerset (finite : FiniteType alpha) :
    FiniteType (FSet alpha) := by
  classical
  exact
    { elems := (ListCard.Sublists finite.elems).map FSet.OfList
      complete := by
        intro A
        let xs := finite.elems.filter (fun x => decide (x ∈ A))
        have hxs : xs ∈ ListCard.Sublists finite.elems := by
          exact filter_mem_sublists finite.elems (fun x => x ∈ A)
        have hA : A = FSet.OfList xs := by
          funext x
          apply propext
          constructor
          · intro hxA
            show x ∈ xs
            have hxFilter : x ∈ finite.elems ∧ x ∈ A :=
              And.intro (finite.complete x) hxA
            simpa [xs] using hxFilter
          · intro hx
            change x ∈ xs at hx
            have hxFilter : x ∈ finite.elems ∧ x ∈ A := by
              simpa [xs] using hx
            exact hxFilter.right
        rw [hA]
        apply List.mem_map.mpr
        exists xs }

end FiniteType

namespace FSet

/-!
**Set-level cardinality laws.**

The list models above become genuine set-level theorems here: the cross
product of sets with cardinalities {lit}`m` and {lit}`n` has cardinality
{lit}`m * n`, and the union of two finite sets satisfies the book's
inclusion-exclusion law.  These are the statements surfaced as Theorem 2.8 of
Section 2.6.
-/

theorem product_hasCardinality {A : FSet alpha} {B : FSet beta} {m n : Nat}
    (hA : HasCardinality A m) (hB : HasCardinality B n) :
    HasCardinality (Product A B) (m * n) := by
  cases hA with
  | intro xs hxs =>
      cases hB with
      | intro ys hys =>
          exists ListCard.Pairs xs ys
          constructor
          · constructor
            · exact ListCard.pairs_nodup hxs.left.left hys.left.left
            · intro p
              constructor
              · intro hp
                exact ListCard.mem_pairs.mpr
                  (And.intro ((hxs.left.right p.1).mp hp.left)
                    ((hys.left.right p.2).mp hp.right))
              · intro hp
                have h := ListCard.mem_pairs.mp hp
                exact And.intro ((hxs.left.right p.1).mpr h.left)
                  ((hys.left.right p.2).mpr h.right)
          · rw [ListCard.length_pairs, hxs.right, hys.right]

/-!
The list-of-sublists construction also yields the genuine set-level powerset
law.  A sublist is interpreted extensionally as a predicate set; filtering the
enumeration of {lit}`A` by an arbitrary subset proves completeness.
-/
theorem powerset_hasCardinality {A : FSet alpha} {n : Nat}
    (hA : HasCardinality A n) :
    HasCardinality (Powerset A) (2 ^ n) := by
  classical
  rcases hA with ⟨xs, hxs⟩
  let sets := (ListCard.Sublists xs).map OfList
  refine ⟨sets, ?_, ?_⟩
  · constructor
    · apply list_nodup_map_of_injective_on_list
        (ListCard.sublists_nodup hxs.left.left)
      intro l t hl ht hlt
      have hsl : l.Sublist xs := ListCard.mem_sublists.mp hl
      have hst : t.Sublist xs := ListCard.mem_sublists.mp ht
      have hmem : forall x, x ∈ l <-> x ∈ t := by
        intro x
        exact Iff.of_eq (congrFun hlt x)
      exact ListCard.sublist_eq_of_same_members hxs.left.left hsl hst hmem
    · intro S
      constructor
      · intro hS
        let selected := xs.filter (fun x => decide (x ∈ S))
        have hselected : selected ∈ ListCard.Sublists xs :=
          ListCard.mem_sublists.mpr (List.filter_sublist)
        have heq : OfList selected = S := by
          apply eq_of_equal
          intro x
          change x ∈ selected <-> x ∈ S
          rw [List.mem_filter]
          simp only [decide_eq_true_eq]
          constructor
          · exact fun hx => hx.right
          · intro hx
            exact ⟨(hxs.left.right x).mp (hS x hx), hx⟩
        exact List.mem_map.mpr ⟨selected, hselected, heq⟩
      · intro hS
        rcases List.mem_map.mp hS with ⟨l, hl, rfl⟩
        intro x hx
        exact (hxs.left.right x).mpr
          ((ListCard.mem_sublists.mp hl).subset hx)
  · simp [sets, ListCard.length_sublists, hxs.right]

theorem hasCardinality_of_setBijection {A : FSet alpha} {B : FSet beta}
    {n : Nat} (e : Fn.SetBijection A B) (hA : HasCardinality A n) :
    HasCardinality B n := by
  rcases hA with ⟨xs, hxs⟩
  let ys := xs.attach.map (fun x =>
    (e.toFun ⟨x.val, (hxs.left.right x.val).mpr x.property⟩).val)
  refine ⟨ys, ?_, ?_⟩
  · constructor
    · apply list_nodup_map_of_injective_on_list
        (list_attach_nodup hxs.left.left)
      intro x y _hx _hy hxy
      have he :
          e.toFun ⟨x.val, (hxs.left.right x.val).mpr x.property⟩ =
          e.toFun ⟨y.val, (hxs.left.right y.val).mpr y.property⟩ :=
        Subtype.ext hxy
      have hsource := e.injective he
      exact Subtype.ext
        (congrArg (fun z : {z // z ∈ A} => z.val) hsource)
    · intro y
      constructor
      · intro hy
        rcases e.surjective ⟨y, hy⟩ with ⟨x, hx⟩
        have hxmem : x.val ∈ xs := (hxs.left.right x.val).mp x.property
        let xmem : {z // z ∈ xs} := ⟨x.val, hxmem⟩
        apply List.mem_map.mpr
        refine ⟨xmem, List.mem_attach xs xmem, ?_⟩
        exact congrArg Subtype.val hx
      · intro hy
        rcases List.mem_map.mp hy with ⟨x, _hx, rfl⟩
        exact (e.toFun ⟨x.val, (hxs.left.right x.val).mpr x.property⟩).property
  · simp [ys, hxs.right]

private theorem indexOfMemDecidable_getElem [DecidableEq alpha]
    {xs : List alpha} (hxs : xs.Nodup) (i : Nat) (hi : i < xs.length) :
    (FiniteType.indexOfMemDecidable xs xs[i] (List.getElem_mem hi)).val = i := by
  apply (List.getElem_inj hxs).mp
  have hvalue := FiniteType.get_indexOfMemDecidable
    xs xs[i] (List.getElem_mem hi)
  simpa [List.get_eq_getElem] using hvalue

theorem hasCardinality_iff_setBijection_segment {A : FSet alpha} {n : Nat} :
    HasCardinality A n <-> Nonempty (Fn.SetBijection A (Segment n)) := by
  classical
  constructor
  · rintro ⟨xs, hxs⟩
    refine ⟨{
      toFun := fun x =>
        let hx : x.val ∈ xs := (hxs.left.right x.val).mp x.property
        let i := FiniteType.indexOfMemDecidable xs x.val hx
        ⟨i.val, hxs.right ▸ i.isLt⟩
      injective := ?_
      surjective := ?_
    }⟩
    · intro x y hxy
      have hindex :
          (FiniteType.indexOfMemDecidable xs x.val
            ((hxs.left.right x.val).mp x.property)).val =
          (FiniteType.indexOfMemDecidable xs y.val
            ((hxs.left.right y.val).mp y.property)).val :=
        congrArg Subtype.val hxy
      apply Subtype.ext
      have hxvalue := FiniteType.get_indexOfMemDecidable xs x.val
        ((hxs.left.right x.val).mp x.property)
      have hyvalue := FiniteType.get_indexOfMemDecidable xs y.val
        ((hxs.left.right y.val).mp y.property)
      have hfin :
          FiniteType.indexOfMemDecidable xs x.val
              ((hxs.left.right x.val).mp x.property) =
            FiniteType.indexOfMemDecidable xs y.val
              ((hxs.left.right y.val).mp y.property) :=
        Fin.ext hindex
      have hget := congrArg (List.get xs) hfin
      exact hxvalue.symm.trans (hget.trans hyvalue)
    · intro i
      have hi : i.val < xs.length := hxs.right.symm ▸ i.property
      let x : {x // x ∈ A} :=
        ⟨xs[i.val], (hxs.left.right xs[i.val]).mpr (List.getElem_mem hi)⟩
      refine ⟨x, ?_⟩
      apply Subtype.ext
      exact indexOfMemDecidable_getElem hxs.left.left i.val hi
  · rintro ⟨e⟩
    exact hasCardinality_of_setBijection e.symm (segment_hasCardinality n)

private def restrictedFunctionOfTuple [DecidableEq alpha]
    {A : FSet alpha} {B : FSet beta}
    (xs : List alpha) (hA : ListEnumerates xs A)
    (ys : List beta) (hB : ListEnumerates ys B)
    (l : List beta) (hlen : l.length = xs.length)
    (hchoices : forall y, y ∈ l -> y ∈ ys) :
    Fn.RestrictedFunction A B :=
  fun x =>
    let hx : x.val ∈ xs := (hA x.val).mp x.property
    let i := FiniteType.indexOfMemDecidable xs x.val hx
    have hi : i.val < l.length := by
      rw [hlen]
      exact i.isLt
    ⟨l[i.val], (hB l[i.val]).mpr (hchoices l[i.val] (List.getElem_mem hi))⟩

/-!
Functions from {lit}`A` to {lit}`B` are represented by the tuple of outputs in
the order of a duplicate-free enumeration of {lit}`A`.  This upgrades
{name}`ListCard.length_tuples` to the book's set-level exponentiation law.
-/
theorem restrictedFunctionSpace_hasCardinality
    {A : FSet alpha} {B : FSet beta} {m n : Nat}
    (hA : HasCardinality A m) (hB : HasCardinality B n) :
    HasCardinality (Fn.RestrictedFunctionSpace A B) (n ^ m) := by
  classical
  rcases hA with ⟨xs, hxs⟩
  rcases hB with ⟨ys, hys⟩
  let tuples := ListCard.Tuples ys xs.length
  let functions := tuples.attach.map (fun l =>
    restrictedFunctionOfTuple xs hxs.left.right ys hys.left.right l.val
      (ListCard.mem_tuples.mp l.property).left
      (ListCard.mem_tuples.mp l.property).right)
  refine ⟨functions, ?_, ?_⟩
  · constructor
    · apply list_nodup_map_of_injective_on_list
        (list_attach_nodup (ListCard.tuples_nodup hys.left.left xs.length))
      intro l t _hl _ht hfun
      apply Subtype.ext
      apply List.ext_getElem
      · exact (ListCard.mem_tuples.mp l.property).left.trans
          (ListCard.mem_tuples.mp t.property).left.symm
      · intro i hil hit
        have hixs : i < xs.length := by
          rw [← (ListCard.mem_tuples.mp l.property).left]
          exact hil
        let x : {x // x ∈ A} :=
          ⟨xs[i], (hxs.left.right xs[i]).mpr (List.getElem_mem hixs)⟩
        have hvalue := congrArg Subtype.val (congrFun hfun x)
        have hindex := indexOfMemDecidable_getElem hxs.left.left i hixs
        simpa [restrictedFunctionOfTuple, x, hindex] using hvalue
    · intro f
      constructor
      · intro _
        let outputs := xs.attach.map (fun x =>
          (f ⟨x.val, (hxs.left.right x.val).mpr x.property⟩).val)
        have houtputsLength : outputs.length = xs.length := by
          simp [outputs]
        have houtputsChoices : forall y, y ∈ outputs -> y ∈ ys := by
          intro y hy
          rcases List.mem_map.mp hy with ⟨x, _hx, rfl⟩
          exact (hys.left.right _).mp
            (f ⟨x.val, (hxs.left.right x.val).mpr x.property⟩).property
        have houtputs : outputs ∈ tuples := by
          exact ListCard.mem_tuples.mpr ⟨houtputsLength, houtputsChoices⟩
        let outputMember : {l // l ∈ tuples} := ⟨outputs, houtputs⟩
        apply List.mem_map.mpr
        refine ⟨outputMember, List.mem_attach tuples outputMember, ?_⟩
        funext x
        apply Subtype.ext
        have hxmem : x.val ∈ xs := (hxs.left.right x.val).mp x.property
        let i := FiniteType.indexOfMemDecidable xs x.val hxmem
        have hi : i.val < xs.length := i.isLt
        have hvalue := FiniteType.get_indexOfMemDecidable xs x.val hxmem
        simp only [restrictedFunctionOfTuple]
        change outputs[i.val] = (f x).val
        simp [outputs, i]
        apply congrArg Subtype.val
        apply congrArg f
        exact Subtype.ext hvalue
      · intro _
        exact True.intro
  · simp [functions, tuples, ListCard.length_tuples, hxs.right, hys.right]

private theorem list_nodup_filter (p : alpha -> Bool)
    {xs : List alpha} (h : xs.Nodup) : (xs.filter p).Nodup := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.nodup_cons] at h
      rw [List.filter_cons]
      by_cases hx : p x = true
      · rw [if_pos hx, List.nodup_cons]
        constructor
        · intro hmem
          exact h.left (List.mem_filter.mp hmem).left
        · exact ih h.right
      · rw [if_neg hx]
        exact ih h.right

private theorem list_length_filter_split (p : alpha -> Bool) (xs : List alpha) :
    (xs.filter p).length + (xs.filter (fun x => !(p x))).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      by_cases hx : p x = true
      · simp [hx]
        lia
      · simp [hx]
        lia

/-!
The union of two finite sets is enumerated by listing the first set and then
the members of the second set that were not already listed.  The skipped
members are exactly the intersection, which yields the inclusion-exclusion
count.  The primed form uses truncated subtraction on the outside; the
subtraction is total because the intersection is a subset of either set.
-/
theorem union_inter_hasCardinality_parts [DecidableEq alpha]
    {A B : FSet alpha} {m n k : Nat}
    (hA : HasCardinality A m) (hB : HasCardinality B n)
    (hI : HasCardinality (Inter A B) k) :
    HasCardinality (Union A B) (m + (n - k)) := by
  cases hA with
  | intro xs hxs =>
      cases hB with
      | intro ys hys =>
          have hBothEnum : ListUniquelyEnumerates
              (ys.filter (fun y => decide (y ∈ xs))) (Inter A B) := by
            constructor
            · exact list_nodup_filter _ hys.left.left
            · intro x
              constructor
              · intro hx
                apply List.mem_filter.mpr
                constructor
                · exact (hys.left.right x).mp hx.right
                · simp
                  exact (hxs.left.right x).mp hx.left
              · intro hx
                have hx' := List.mem_filter.mp hx
                have hxxs : x ∈ xs := by
                  simpa using hx'.right
                exact And.intro ((hxs.left.right x).mpr hxxs)
                  ((hys.left.right x).mpr hx'.left)
          have hkLen : (ys.filter (fun y => decide (y ∈ xs))).length = k :=
            hasCardinality_unique
              (Exists.intro _ (And.intro hBothEnum rfl)) hI
          have hsplit :=
            list_length_filter_split (fun y => decide (y ∈ xs)) ys
          exists xs ++ ys.filter (fun y => !(decide (y ∈ xs)))
          constructor
          · constructor
            · show (xs ++ ys.filter (fun y => !(decide (y ∈ xs)))).Nodup
              rw [List.nodup_append]
              constructor
              · exact hxs.left.left
              constructor
              · exact list_nodup_filter _ hys.left.left
              · intro a ha b hb hab
                have hb' := List.mem_filter.mp hb
                have hbxs : ¬ b ∈ xs := by
                  simpa using hb'.right
                rw [hab] at ha
                exact hbxs ha
            · intro x
              constructor
              · intro hx
                by_cases hxxs : x ∈ xs
                · exact List.mem_append.mpr (Or.inl hxxs)
                · cases hx with
                  | inl hxA =>
                      exact False.elim (hxxs ((hxs.left.right x).mp hxA))
                  | inr hxB =>
                      apply List.mem_append.mpr
                      apply Or.inr
                      apply List.mem_filter.mpr
                      constructor
                      · exact (hys.left.right x).mp hxB
                      · simp [hxxs]
              · intro hx
                cases List.mem_append.mp hx with
                | inl hxxs =>
                    exact Or.inl ((hxs.left.right x).mpr hxxs)
                | inr hxfilter =>
                    exact Or.inr ((hys.left.right x).mpr
                      (List.mem_filter.mp hxfilter).left)
          · rw [List.length_append, hxs.right]
            rw [hkLen, hys.right] at hsplit
            lia

theorem union_hasCardinality_inclusion_exclusion [DecidableEq alpha]
    {A B : FSet alpha} {m n k : Nat}
    (hA : HasCardinality A m) (hB : HasCardinality B n)
    (hI : HasCardinality (Inter A B) k) :
    HasCardinality (Union A B) (m + n - k) := by
  have hk : k <= n :=
    hasCardinality_le_of_subset (fun _ hx => hx.right) hI hB
  have h := union_inter_hasCardinality_parts hA hB hI
  have heq : m + (n - k) = m + n - k := by lia
  rw [heq] at h
  exact h

theorem union_hasCardinality_inclusion_exclusion_classical
    {A B : FSet alpha} {m n k : Nat}
    (hA : HasCardinality A m) (hB : HasCardinality B n)
    (hI : HasCardinality (Inter A B) k) :
    HasCardinality (Union A B) (m + n - k) := by
  classical
  exact union_hasCardinality_inclusion_exclusion hA hB hI

/-!
The additive form avoids natural-number subtraction entirely: the cardinality
of the union plus the cardinality of the intersection equals the sum of the
two cardinalities.
-/
theorem union_add_inter_cardinality [DecidableEq alpha]
    {A B : FSet alpha} {m n u k : Nat}
    (hA : HasCardinality A m) (hB : HasCardinality B n)
    (hU : HasCardinality (Union A B) u)
    (hI : HasCardinality (Inter A B) k) :
    u + k = m + n := by
  have hk : k <= n :=
    hasCardinality_le_of_subset (fun _ hx => hx.right) hI hB
  have h := union_inter_hasCardinality_parts hA hB hI
  have hu : u = m + (n - k) := hasCardinality_unique hU h
  lia

theorem union_add_inter_cardinality_classical
    {A B : FSet alpha} {m n u k : Nat}
    (hA : HasCardinality A m) (hB : HasCardinality B n)
    (hU : HasCardinality (Union A B) u)
    (hI : HasCardinality (Inter A B) k) :
    u + k = m + n := by
  classical
  exact union_add_inter_cardinality hA hB hU hI

theorem union_hasCardinality_of_disjoint [DecidableEq alpha]
    {A B : FSet alpha} {m n : Nat}
    (hA : HasCardinality A m) (hB : HasCardinality B n)
    (hAB : Disjoint A B) :
    HasCardinality (Union A B) (m + n) := by
  have hI : HasCardinality (Inter A B) 0 := by
    apply hasCardinality_of_equal (A := (Empty : FSet alpha))
    · intro x
      constructor
      · intro hx
        cases hx
      · intro hx
        exact False.elim (hAB x hx)
    · exact empty_has_cardinality_zero
  have h := union_inter_hasCardinality_parts hA hB hI
  simpa using h

theorem union_hasCardinality_of_disjoint_classical
    {A B : FSet alpha} {m n : Nat}
    (hA : HasCardinality A m) (hB : HasCardinality B n)
    (hAB : Disjoint A B) :
    HasCardinality (Union A B) (m + n) := by
  classical
  exact union_hasCardinality_of_disjoint hA hB hAB

end FSet

end Foundation
end FoC

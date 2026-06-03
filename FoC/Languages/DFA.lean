import FoC.Foundation.Finite
import FoC.Languages.Language

set_option doc.verso true

/-!
# Deterministic finite automata

## Deterministic runs

A DFA is represented by a start state, a deterministic transition function, an
accepting-state predicate, and a finite-state witness.  The extended transition
function runs by recursion over input words, matching the textbook construction.

## Book coordinates

Used by:
- Chapter 3, Section 3.4: DFA definitions, extended transition function, and
  accepted language
- Chapter 3, Section 3.6: closure of DFA-recognizable languages under Boolean
  operations
- Chapter 3, Section 3.7: pumping-lemma vocabulary
-/

namespace FoC
namespace Languages

open Foundation

namespace FiniteState

/-!
# Finite product states

Closure under Boolean operations uses product automata. This helper packages
the finite-state witness for a product of two finite state types.
-/

def PairElems : List state₁ -> List state₂ -> List (state₁ × state₂)
  | [], _ => []
  | x :: xs, ys => (ys.map fun y => (x, y)) ++ PairElems xs ys

theorem pair_mem {xs : List state₁} {ys : List state₂}
    {x : state₁} {y : state₂} (hx : x ∈ xs) (hy : y ∈ ys) :
    (x, y) ∈ PairElems xs ys := by
  induction xs with
  | nil =>
      cases hx
  | cons z zs ih =>
      cases hx with
      | head =>
          simp [PairElems, hy]
      | tail _ htail =>
          exact List.mem_append.mpr (Or.inr (ih htail))

def Product (A : FiniteType state₁) (B : FiniteType state₂) :
    FiniteType (state₁ × state₂) where
  elems := PairElems A.elems B.elems
  complete := by
    intro p
    exact pair_mem (A.complete p.1) (B.complete p.2)

end FiniteState

/-!
# DFA structure

A deterministic automaton consists of a start state, one next state for each
state-symbol pair, an accepting predicate, and a finite-state witness.
-/

structure DFA (alpha : Type u) (state : Type v) where
  start : state
  step : state -> alpha -> state
  accept : state -> Prop
  statesFinite : FiniteType state

namespace DFA

/-!
# Runs and accepted language

The extended transition function consumes a word recursively. Acceptance and
recognizability are then stated as predicates on the resulting final state.
-/

def RunFrom (M : DFA alpha state) : state -> Word alpha -> state
  | q, [] => q
  | q, a :: w => RunFrom M (M.step q a) w

def Run (M : DFA alpha state) (w : Word alpha) : state :=
  RunFrom M M.start w

def Accepts (M : DFA alpha state) (w : Word alpha) : Prop :=
  M.accept (Run M w)

def Language (M : DFA alpha state) : Languages.Language alpha :=
  fun w => Accepts M w

def Recognizable (L : Languages.Language alpha) : Prop :=
  exists state : Type, exists M : DFA alpha state, Languages.Language.Equal (Language M) L

/-!
# Product and complement automata

The closure constructions change only the accepting predicate for complements
and run two machines in lockstep for intersections and unions.
-/

def Complement (M : DFA alpha state) : DFA alpha state where
  start := M.start
  step := M.step
  accept := fun q => ¬ M.accept q
  statesFinite := M.statesFinite

def Intersection (M : DFA alpha state₁) (N : DFA alpha state₂) :
    DFA alpha (state₁ × state₂) where
  start := (M.start, N.start)
  step := fun q a => (M.step q.1 a, N.step q.2 a)
  accept := fun q => M.accept q.1 ∧ N.accept q.2
  statesFinite := FiniteState.Product M.statesFinite N.statesFinite

def Union (M : DFA alpha state₁) (N : DFA alpha state₂) :
    DFA alpha (state₁ × state₂) where
  start := (M.start, N.start)
  step := fun q a => (M.step q.1 a, N.step q.2 a)
  accept := fun q => M.accept q.1 ∨ N.accept q.2
  statesFinite := FiniteState.Product M.statesFinite N.statesFinite

/-!
# Run equations

These equations are the computational facts used to relate constructed
automata to the intended language operations.
-/

theorem runFrom_empty (M : DFA alpha state) (q : state) :
    RunFrom M q Word.Empty = q :=
  rfl

theorem runFrom_cons (M : DFA alpha state) (q : state) (a : alpha) (w : Word alpha) :
    RunFrom M q (a :: w) = RunFrom M (M.step q a) w :=
  rfl

theorem runFrom_append (M : DFA alpha state) (q : state) (x y : Word alpha) :
    RunFrom M q (Word.Concat x y) = RunFrom M (RunFrom M q x) y := by
  induction x generalizing q with
  | nil => rfl
  | cons a rest ih =>
      exact ih (M.step q a)

theorem runFrom_concatWords_loop (M : DFA alpha state) (q : state)
    (pieces : List (Word alpha))
    (hall : forall p, p ∈ pieces -> RunFrom M q p = q) :
    RunFrom M q (Language.ConcatWords pieces) = q := by
  induction pieces with
  | nil =>
      rfl
  | cons p rest ih =>
      rw [Language.ConcatWords, runFrom_append, hall p (List.Mem.head rest)]
      exact ih (by
        intro x hx
        exact hall x (List.Mem.tail p hx))

theorem complement_accepts (M : DFA alpha state) (w : Word alpha) :
    Accepts (Complement M) w <-> ¬ Accepts M w := by
  unfold Accepts Run
  have hrun : forall q, RunFrom (Complement M) q w = RunFrom M q w := by
    induction w with
    | nil =>
        intro q
        rfl
    | cons a rest ih =>
        intro q
        exact ih (M.step q a)
  change (Complement M).accept (RunFrom (Complement M) M.start w) ↔
    ¬ M.accept (RunFrom M M.start w)
  rw [hrun M.start]
  rfl

theorem runFrom_intersection (M : DFA alpha state₁) (N : DFA alpha state₂)
    (q : state₁ × state₂) (w : Word alpha) :
    RunFrom (Intersection M N) q w = (RunFrom M q.1 w, RunFrom N q.2 w) := by
  induction w generalizing q with
  | nil => rfl
  | cons a rest ih =>
      exact ih (M.step q.1 a, N.step q.2 a)

theorem runFrom_union (M : DFA alpha state₁) (N : DFA alpha state₂)
    (q : state₁ × state₂) (w : Word alpha) :
    RunFrom (Union M N) q w = (RunFrom M q.1 w, RunFrom N q.2 w) := by
  induction w generalizing q with
  | nil => rfl
  | cons a rest ih =>
      exact ih (M.step q.1 a, N.step q.2 a)

/-!
# Recognizable closure

The final theorems package the automata constructions as language-level closure
properties for DFA-recognizable languages.
-/

theorem intersection_accepts (M : DFA alpha state₁) (N : DFA alpha state₂)
    (w : Word alpha) :
    Accepts (Intersection M N) w <-> Accepts M w ∧ Accepts N w := by
  unfold Accepts Run
  change (Intersection M N).accept (RunFrom (Intersection M N) (M.start, N.start) w) ↔
    M.accept (RunFrom M M.start w) ∧ N.accept (RunFrom N N.start w)
  rw [runFrom_intersection M N (M.start, N.start) w]
  rfl

theorem union_accepts (M : DFA alpha state₁) (N : DFA alpha state₂)
    (w : Word alpha) :
    Accepts (Union M N) w <-> Accepts M w ∨ Accepts N w := by
  unfold Accepts Run
  change (Union M N).accept (RunFrom (Union M N) (M.start, N.start) w) ↔
    M.accept (RunFrom M M.start w) ∨ N.accept (RunFrom N N.start w)
  rw [runFrom_union M N (M.start, N.start) w]
  rfl

theorem recognizable_complement {L : Languages.Language alpha}
    (hL : Recognizable L) : Recognizable (Languages.Language.Compl L) := by
  cases hL with
  | intro state hstate =>
      cases hstate with
      | intro M hM =>
          exists state
          exists Complement M
          intro w
          constructor
          · intro hw hmem
            exact (complement_accepts M w).mp hw ((hM w).mpr hmem)
          · intro hw
            exact (complement_accepts M w).mpr (by
              intro hAccept
              exact hw ((hM w).mp hAccept))

theorem recognizable_intersection {L MLang : Languages.Language alpha}
    (hL : Recognizable L) (hMLang : Recognizable MLang) :
    Recognizable (Languages.Language.Inter L MLang) := by
  cases hL with
  | intro state₁ hstate₁ =>
      cases hstate₁ with
      | intro M hM_L =>
          cases hMLang with
          | intro state₂ hstate₂ =>
              cases hstate₂ with
              | intro N hN_L =>
                  exists state₁ × state₂
                  exists Intersection M N
                  intro w
                  constructor
                  · intro hw
                    exact And.intro ((hM_L w).mp ((intersection_accepts M N w).mp hw).left)
                      ((hN_L w).mp ((intersection_accepts M N w).mp hw).right)
                  · intro hw
                    exact (intersection_accepts M N w).mpr
                      (And.intro ((hM_L w).mpr hw.left) ((hN_L w).mpr hw.right))

theorem recognizable_union {L MLang : Languages.Language alpha}
    (hL : Recognizable L) (hMLang : Recognizable MLang) :
    Recognizable (Languages.Language.Union L MLang) := by
  cases hL with
  | intro state₁ hstate₁ =>
      cases hstate₁ with
      | intro M hM_L =>
          cases hMLang with
          | intro state₂ hstate₂ =>
              cases hstate₂ with
              | intro N hN_L =>
                  exists state₁ × state₂
                  exists Union M N
                  intro w
                  constructor
                  · intro hw
                    cases (union_accepts M N w).mp hw with
                    | inl hwM => exact Or.inl ((hM_L w).mp hwM)
                    | inr hwN => exact Or.inr ((hN_L w).mp hwN)
                  · intro hw
                    cases hw with
                    | inl hwL => exact (union_accepts M N w).mpr (Or.inl ((hM_L w).mpr hwL))
                    | inr hwR => exact (union_accepts M N w).mpr (Or.inr ((hN_L w).mpr hwR))

end DFA
end Languages
end FoC

import FoC.Foundation.Sets
import FoC.Foundation.Finite
import FoC.Languages.Words

set_option doc.verso true

/-!
# Languages as sets of words

## Languages as predicates

The book defines a language as a set of strings.  This module represents a
language as a predicate on words and then reuses the extensional set operations
from {module}`FoC.Foundation.Sets`.

## Book coordinates

Used by:
- Chapter 3, Section 3.1: language definition and operations
- Chapter 3, Section 3.2: regular-expression semantics
- Chapter 3, Section 3.6: closure properties of regular languages
- Chapter 3, Section 3.7: pumping-lemma statements
-/

namespace FoC
namespace Languages

open Foundation

/-!
# Predicates over words

A language is represented extensionally as a predicate on words. The empty,
universal, singleton, pair, equality, and subset definitions mirror the first
set-theoretic language operations from Chapter 3.
-/

def Language (alpha : Type u) : Type u :=
  Word alpha -> Prop

namespace Language

instance : Membership (Word alpha) (Language alpha) where
  mem L w := L w

/-!
# Boolean operations

Union, intersection, complement, and difference are pointwise set operations on
the word predicate.
-/

def Empty : Language alpha :=
  fun _ => False

def Universal : Language alpha :=
  fun _ => True

def Singleton (w : Word alpha) : Language alpha :=
  fun x => x = w

def Pair (x y : Word alpha) : Language alpha :=
  fun w => w = x ∨ w = y

def Equal (L M : Language alpha) : Prop :=
  FSet.Equal L M

def Subset (L M : Language alpha) : Prop :=
  FSet.Subset L M

def Union (L M : Language alpha) : Language alpha :=
  FSet.Union L M

def Inter (L M : Language alpha) : Language alpha :=
  FSet.Inter L M

def Compl (L : Language alpha) : Language alpha :=
  FSet.Compl L

def Diff (L M : Language alpha) : Language alpha :=
  FSet.Diff L M

/-!
# Concatenation, reversal, and star

The operations that are specific to formal languages are defined by splitting a
word into pieces, reversing words, and concatenating finite lists of pieces.
-/

def Reverse (L : Language alpha) : Language alpha :=
  fun w => (Word.Reverse w) ∈ L

def Concat (L M : Language alpha) : Language alpha :=
  fun w => exists x y, x ∈ L ∧ y ∈ M ∧ w = Word.Concat x y

def ConcatWords : List (Word alpha) -> Word alpha
  | [] => Word.Empty
  | w :: ws => Word.Concat w (ConcatWords ws)

def ReversePieces (pieces : List (Word alpha)) : List (Word alpha) :=
  pieces.reverse.map Word.Reverse

def Power (L : Language alpha) : Nat -> Language alpha
  | 0 => Singleton Word.Empty
  | n + 1 => Concat L (Power L n)

def Star (L : Language alpha) : Language alpha :=
  fun w =>
    exists pieces : List (Word alpha),
      (forall p, p ∈ pieces -> p ∈ L) ∧ ConcatWords pieces = w

def Finite (L : Language alpha) : Prop :=
  FSet.Finite L

/-!
# Membership laws

These lemmas expose the membership rules for the language constructors and
finite examples.
-/

theorem mem_union (w : Word alpha) (L M : Language alpha) :
    w ∈ Union L M <-> w ∈ L ∨ w ∈ M :=
  Iff.rfl

theorem mem_inter (w : Word alpha) (L M : Language alpha) :
    w ∈ Inter L M <-> w ∈ L ∧ w ∈ M :=
  Iff.rfl

theorem mem_compl (w : Word alpha) (L : Language alpha) :
    w ∈ Compl L <-> ¬ w ∈ L :=
  Iff.rfl

theorem mem_diff (w : Word alpha) (L M : Language alpha) :
    w ∈ Diff L M <-> w ∈ L ∧ ¬ w ∈ M :=
  Iff.rfl

theorem mem_concat (w : Word alpha) (L M : Language alpha) :
    w ∈ Concat L M <->
      exists x y, x ∈ L ∧ y ∈ M ∧ w = Word.Concat x y :=
  Iff.rfl

theorem singleton_finite (w : Word alpha) : Finite (Singleton w) :=
  FSet.singleton_finite w

/-!
# Extensional algebra

Language equality is pointwise logical equivalence. These facts provide the
set-algebra and concatenation laws used throughout the regular-language proofs.
-/

theorem equal_refl (L : Language alpha) : Equal L L :=
  FSet.equal_refl L

theorem equal_symm {L M : Language alpha} (h : Equal L M) : Equal M L :=
  FSet.equal_symm h

theorem equal_trans {L M N : Language alpha} (hLM : Equal L M) (hMN : Equal M N) :
  Equal L N :=
  FSet.equal_trans hLM hMN

theorem double_compl (L : Language alpha) :
  Equal (Compl (Compl L)) L :=
  FSet.double_compl L

theorem union_idempotent (L : Language alpha) : Equal (Union L L) L :=
  FSet.union_idempotent L

theorem inter_idempotent (L : Language alpha) : Equal (Inter L L) L :=
  FSet.inter_idempotent L

theorem union_absorption (L M : Language alpha) :
    Equal (Union L (Inter L M)) L :=
  FSet.union_absorption L M

theorem inter_absorption (L M : Language alpha) :
    Equal (Inter L (Union L M)) L :=
  FSet.inter_absorption L M

theorem diff_as_inter_compl (L M : Language alpha) :
    Equal (Diff L M) (Inter L (Compl M)) :=
  FSet.equal_refl _

theorem reverse_reverse (L : Language alpha) : Equal (Reverse (Reverse L)) L := by
  intro w
  constructor <;> intro hw
  · change Word.Reverse (Word.Reverse w) ∈ L at hw
    rw [show Word.Reverse (Word.Reverse w) = w by simp [Word.Reverse]] at hw
    exact hw
  · change Word.Reverse (Word.Reverse w) ∈ L
    rw [show Word.Reverse (Word.Reverse w) = w by simp [Word.Reverse]]
    exact hw

theorem concat_empty_language_left (L : Language alpha) :
  Equal (Concat Empty L) Empty := by
  intro w
  constructor
  · intro hw
    rcases hw with ⟨x, _y, hx, _hy, _hwEq⟩
    exact hx
  · intro hw
    cases hw

theorem concat_empty_language_right (L : Language alpha) :
    Equal (Concat L Empty) Empty := by
  intro w
  constructor
  · intro hw
    rcases hw with ⟨_x, y, _hx, hy, _hwEq⟩
    exact hy
  · intro hw
    cases hw

theorem concat_epsilon_left (L : Language alpha) :
    Equal (Concat (Singleton Word.Empty) L) L := by
  intro w
  constructor
  · intro hw
    rcases hw with ⟨x, y, hx, hy, hwEq⟩
    rw [hx, Word.concat_empty_left] at hwEq
    rw [hwEq]
    exact hy
  · intro hw
    exact ⟨Word.Empty, w, rfl, hw, by rw [Word.concat_empty_left]⟩

theorem concat_epsilon_right (L : Language alpha) :
    Equal (Concat L (Singleton Word.Empty)) L := by
  intro w
  constructor
  · intro hw
    rcases hw with ⟨x, y, hx, hy, hwEq⟩
    rw [hy, Word.concat_empty_right] at hwEq
    rw [hwEq]
    exact hx
  · intro hw
    exact ⟨w, Word.Empty, hw, rfl, by rw [Word.concat_empty_right]⟩

theorem reverse_concat (L M : Language alpha) :
    Equal (Reverse (Concat L M)) (Concat (Reverse M) (Reverse L)) := by
  intro w
  constructor
  · intro hw
    cases hw with
    | intro x hx =>
        cases hx with
        | intro y hy =>
            exists Word.Reverse y
            exists Word.Reverse x
            constructor
            · change Word.Reverse (Word.Reverse y) ∈ M
              simpa [Word.Reverse] using hy.right.left
            constructor
            · change Word.Reverse (Word.Reverse x) ∈ L
              simpa [Word.Reverse] using hy.left
            · have hwEq := congrArg Word.Reverse hy.right.right
              simpa [Word.Reverse, Word.Concat, List.reverse_append] using hwEq
  · intro hw
    cases hw with
    | intro yrev hyrev =>
        cases hyrev with
        | intro xrev hxrev =>
            exists Word.Reverse xrev
            exists Word.Reverse yrev
            constructor
            · exact hxrev.right.left
            constructor
            · exact hxrev.left
            · have hwEq := congrArg Word.Reverse hxrev.right.right
              simpa [Word.Reverse, Word.Concat, List.reverse_append] using hwEq

theorem concatWords_append (xs ys : List (Word alpha)) :
  ConcatWords (xs ++ ys) = Word.Concat (ConcatWords xs) (ConcatWords ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [ConcatWords, Word.Concat, ih, List.append_assoc]

theorem concatWords_reversePieces (pieces : List (Word alpha)) :
    ConcatWords (ReversePieces pieces) =
      Word.Reverse (ConcatWords pieces) := by
  induction pieces with
  | nil =>
      rfl
  | cons p rest ih =>
      rw [show ReversePieces (p :: rest) =
          ReversePieces rest ++ [Word.Reverse p] by
        simp [ReversePieces]]
      change ConcatWords (ReversePieces rest ++ [Word.Reverse p]) =
        Word.Reverse (Word.Concat p (ConcatWords rest))
      rw [concatWords_append, ih]
      simp [ConcatWords, Word.Reverse, Word.Concat, Word.Empty]

theorem reverse_star (L : Language alpha) :
    Equal (Reverse (Star L)) (Star (Reverse L)) := by
  intro w
  constructor
  · intro hw
    cases hw with
    | intro pieces hpieces =>
        exists ReversePieces pieces
        constructor
        · intro p hp
          unfold Reverse
          unfold ReversePieces at hp
          cases List.mem_map.mp hp with
          | intro original horiginal =>
              rw [← horiginal.right]
              change Word.Reverse (Word.Reverse original) ∈ L
              simpa [Word.Reverse] using
                hpieces.left original (List.mem_reverse.mp horiginal.left)
        · rw [concatWords_reversePieces, hpieces.right]
          simp [Word.Reverse]
  · intro hw
    cases hw with
    | intro pieces hpieces =>
        exists ReversePieces pieces
        constructor
        · intro p hp
          unfold ReversePieces at hp
          cases List.mem_map.mp hp with
          | intro original horiginal =>
              have horigRev : Word.Reverse original ∈ L :=
                hpieces.left original (List.mem_reverse.mp horiginal.left)
              rw [← horiginal.right]
              exact horigRev
        · rw [concatWords_reversePieces, hpieces.right]

theorem star_empty_word (L : Language alpha) : Word.Empty ∈ Star L := by
  exists []
  constructor
  · intro p hp
    cases hp
  · rfl

theorem star_of_mem (L : Language alpha) {w : Word alpha} (hw : w ∈ L) :
    w ∈ Star L := by
  exists [w]
  constructor
  · intro p hp
    cases hp with
    | head => exact hw
    | tail _ htail => cases htail
  · rw [ConcatWords]
    exact Word.concat_empty_right w

theorem star_concat {L : Language alpha} {x y : Word alpha}
    (hx : x ∈ Star L) (hy : y ∈ Star L) : Word.Concat x y ∈ Star L := by
  cases hx with
  | intro xs hxs =>
      cases hy with
      | intro ys hys =>
          exists xs ++ ys
          constructor
          · intro p hp
            have hpSplit := List.mem_append.mp hp
            cases hpSplit with
            | inl hpx => exact hxs.left p hpx
            | inr hpy => exact hys.left p hpy
          · rw [concatWords_append, hxs.right, hys.right]

end Language
end Languages
end FoC

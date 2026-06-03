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

theorem mem_empty (w : Word alpha) : w ∈ (Empty : Language alpha) <-> False :=
  Iff.rfl

theorem mem_universal (w : Word alpha) :
    w ∈ (Universal : Language alpha) <-> True :=
  Iff.rfl

theorem mem_singleton (w x : Word alpha) :
    w ∈ Singleton x <-> w = x :=
  Iff.rfl

theorem mem_union (w : Word alpha) (L M : Language alpha) :
    w ∈ Union L M <-> w ∈ L ∨ w ∈ M :=
  Iff.rfl

theorem mem_inter (w : Word alpha) (L M : Language alpha) :
    w ∈ Inter L M <-> w ∈ L ∧ w ∈ M :=
  Iff.rfl

theorem mem_compl (w : Word alpha) (L : Language alpha) :
    w ∈ Compl L <-> ¬ w ∈ L :=
  Iff.rfl

theorem mem_concat (w : Word alpha) (L M : Language alpha) :
    w ∈ Concat L M <->
      exists x y, x ∈ L ∧ y ∈ M ∧ w = Word.Concat x y :=
  Iff.rfl

theorem empty_finite : Finite (Empty : Language alpha) :=
  FSet.empty_finite

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

theorem compl_congr {L M : Language alpha} (h : Equal L M) :
    Equal (Compl L) (Compl M) := by
  intro w
  constructor
  · intro hw hM
    exact hw ((h w).mpr hM)
  · intro hw hL
    exact hw ((h w).mp hL)

theorem double_compl (L : Language alpha) :
    Equal (Compl (Compl L)) L :=
  FSet.double_compl L

theorem union_comm (L M : Language alpha) : Equal (Union L M) (Union M L) :=
  FSet.union_comm L M

theorem union_assoc (L M N : Language alpha) :
    Equal (Union L (Union M N)) (Union (Union L M) N) :=
  FSet.union_assoc L M N

theorem inter_comm (L M : Language alpha) : Equal (Inter L M) (Inter M L) :=
  FSet.inter_comm L M

theorem inter_assoc (L M N : Language alpha) :
    Equal (Inter L (Inter M N)) (Inter (Inter L M) N) :=
  FSet.inter_assoc L M N

theorem concat_empty_word_left (w : Word alpha) :
    w ∈ Singleton Word.Empty -> forall L : Language alpha,
      forall y, y ∈ L -> Word.Concat w y = y := by
  intro hw L y _hy
  rw [hw]
  exact Word.concat_empty_left y

theorem concat_assoc (L M N : Language alpha) :
    Equal (Concat (Concat L M) N) (Concat L (Concat M N)) := by
  intro w
  constructor
  · intro hw
    cases hw with
    | intro xy hxy =>
        cases hxy with
        | intro z hz =>
            cases hz with
            | intro hxyMem hrest =>
                cases hxyMem with
                | intro x hx =>
                    cases hx with
                    | intro y hy =>
                        cases hy with
                        | intro hxL hyrest =>
                            cases hyrest with
                            | intro hyM hxyEq =>
                                cases hrest with
                                | intro hzN hwEq =>
                                    exists x
                                    exists Word.Concat y z
                                    constructor
                                    · exact hxL
                                    constructor
                                    · exact Exists.intro y
                                        (Exists.intro z (And.intro hyM (And.intro hzN rfl)))
                                    · rw [hwEq, hxyEq, Word.concat_assoc]
  · intro hw
    cases hw with
    | intro x hx =>
        cases hx with
        | intro yz hyz =>
            cases hyz with
            | intro hxL hrest =>
                cases hrest with
                | intro hyzMem hwEq =>
                    cases hyzMem with
                    | intro y hy =>
                        cases hy with
                        | intro z hz =>
                            cases hz with
                            | intro hyM hzrest =>
                                cases hzrest with
                                | intro hzN hyzEq =>
                                    exists Word.Concat x y
                                    exists z
                                    constructor
                                    · exact Exists.intro x
                                        (Exists.intro y (And.intro hxL (And.intro hyM rfl)))
                                    constructor
                                    · exact hzN
                                    · rw [hwEq, hyzEq, Word.concat_assoc]

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
              simpa [Word.reverse_concat, Word.Reverse, Word.Concat] using hwEq
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
              simpa [Word.reverse_concat, Word.Reverse, Word.Concat] using hwEq

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

theorem power_zero (L : Language alpha) :
    Equal (Power L 0) (Singleton Word.Empty) :=
  equal_refl _

theorem power_succ (L : Language alpha) (n : Nat) :
    Equal (Power L (n + 1)) (Concat L (Power L n)) :=
  equal_refl _

end Language
end Languages
end FoC

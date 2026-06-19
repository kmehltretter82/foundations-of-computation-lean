import FoC.Book.Chapter03.Section02

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter03
namespace Section03

/-!
# Chapter 3, Section 3.3: Application - Using Regular Expressions

This section formalizes programming-language conveniences built on top of the
core regular-expression constructors from {module}`FoC.Languages.RegularExpression`.
The key point is that optional expressions, plus, and character classes are
notation for ordinary regular-expression combinations.

This is why those conveniences do not change the class of regular languages:
each convenience expands into the primitive regular-expression syntax already
formalized in Section 3.2.
-/

open Languages

/-!
## Derived Operators

Optional, plus, and character classes expand to union, concatenation, star,
and finite alternatives. Their canonical membership theorems are
{lit}`RegExp.optional_membership`, {lit}`RegExp.plus_membership`, and
{lit}`RegExp.charClass_denote`. The sample digit class demonstrates
character-class membership for a concrete one-symbol word.

The digit-class example is deliberately simple. It shows how a character class
is interpreted as "one of the listed symbols" rather than as a new matching
primitive.
-/

def digitClass : RegExp Nat :=
  RegExp.CharClass [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

theorem digit_class_accepts_7 :
    [7] ∈ RegExp.Denote digitClass := by
  exact (RegExp.charClass_denote _ _).mpr
    (Exists.intro 7 (And.intro (by simp) rfl))

def optionalA : RegExp Section01.AB :=
  RegExp.Optional (RegExp.sym Section01.AB.a)

theorem optionalA_membership (w : Word Section01.AB) :
    w ∈ RegExp.Denote optionalA <->
      w = [Section01.AB.a] ∨ w = Word.Empty :=
  RegExp.optional_membership (RegExp.sym Section01.AB.a) w

theorem optionalA_accepts_empty :
    Word.Empty ∈ RegExp.Denote optionalA := by
  exact Or.inr rfl

theorem optionalA_accepts_a :
    [Section01.AB.a] ∈ RegExp.Denote optionalA := by
  exact Or.inl rfl

def oneOrMoreBs : RegExp Section01.AB :=
  RegExp.Plus (RegExp.sym Section01.AB.b)

theorem oneOrMoreBs_membership (w : Word Section01.AB) :
    w ∈ RegExp.Denote oneOrMoreBs <->
      exists x y,
        x = [Section01.AB.b] ∧
        y ∈ Language.Star (RegExp.Denote (RegExp.sym Section01.AB.b)) ∧
        w = Word.Concat x y :=
  RegExp.plus_membership (RegExp.sym Section01.AB.b) w

theorem oneOrMoreBs_subset_bStar :
    Language.Subset (RegExp.Denote oneOrMoreBs)
      (RegExp.Denote (RegExp.star (RegExp.sym Section01.AB.b))) :=
  RegExp.plus_subset_star (RegExp.sym Section01.AB.b)

theorem oneOrMoreBs_accepts_bb :
    [Section01.AB.b, Section01.AB.b] ∈ RegExp.Denote oneOrMoreBs := by
  exists [Section01.AB.b]
  exists [Section01.AB.b]
  constructor
  · rfl
  constructor
  · exact Language.star_of_mem _ rfl
  · rfl

inductive TinyIdentifierChar where
  | upperA
  | upperB
  | lowerA
  | lowerB
  | digit0
deriving DecidableEq

def tinyUpperClass : RegExp TinyIdentifierChar :=
  RegExp.CharClass [TinyIdentifierChar.upperA, TinyIdentifierChar.upperB]

def tinyLetterClass : RegExp TinyIdentifierChar :=
  RegExp.CharClass
    [TinyIdentifierChar.upperA, TinyIdentifierChar.upperB,
      TinyIdentifierChar.lowerA, TinyIdentifierChar.lowerB]

def tinyIdentifierPattern : RegExp TinyIdentifierChar :=
  RegExp.seq tinyUpperClass (RegExp.star tinyLetterClass)

theorem tinyIdentifier_accepts_upper_lower_upper :
    [TinyIdentifierChar.upperA, TinyIdentifierChar.lowerB,
      TinyIdentifierChar.upperB] ∈ RegExp.Denote tinyIdentifierPattern := by
  exists [TinyIdentifierChar.upperA]
  exists [TinyIdentifierChar.lowerB, TinyIdentifierChar.upperB]
  constructor
  · exact (RegExp.charClass_denote _ _).mpr
      ⟨TinyIdentifierChar.upperA, by simp, rfl⟩
  constructor
  · exists [[TinyIdentifierChar.lowerB], [TinyIdentifierChar.upperB]]
    constructor
    · intro p hp
      cases hp with
      | head =>
          exact (RegExp.charClass_denote _ _).mpr
            ⟨TinyIdentifierChar.lowerB, by simp, rfl⟩
      | tail _ htail =>
          cases htail with
          | head =>
              exact (RegExp.charClass_denote _ _).mpr
                ⟨TinyIdentifierChar.upperB, by simp, rfl⟩
          | tail _ hnil =>
              cases hnil
    · rfl
  · rfl

theorem tinyIdentifier_rejects_initial_digit :
    ¬ [TinyIdentifierChar.digit0] ∈ RegExp.Denote tinyIdentifierPattern := by
  intro h
  rcases h with ⟨first, rest, hfirst, _hrest, hword⟩
  rcases (RegExp.charClass_denote _ _).mp hfirst with ⟨head, hhead, hfirstEq⟩
  rw [hfirstEq] at hword
  simp [Word.Concat, Word.Symbol] at hword
  cases head
  · cases hword
  · cases hword
  · simp at hhead
  · simp at hhead
  · simp at hhead

/-!
## Backreference Target Language

The book explains that backreferences add power beyond regular expressions.
The formalization records the target language {lit}`a^n b a^n` now, then
proves its non-regularity later in Section 3.7 after the Pumping Lemma is
available.

The definition {lit}`anbanWord left right` keeps the two blocks separate so later
proofs can talk about what happens when only the first block is shortened by a
pumping argument. The actual language requires the two block lengths to be
equal.
-/

def anbanWord (left right : Nat) : Word Section01.AB :=
  Word.Concat (Word.RepeatSymbol Section01.AB.a left)
    (Word.Concat (Word.Symbol Section01.AB.b)
      (Word.RepeatSymbol Section01.AB.a right))

def anbanLanguage : Language Section01.AB :=
  fun w => exists n, w = anbanWord n n

theorem anban_language_membership (w : Word Section01.AB) :
    w ∈ anbanLanguage <-> exists n, w = anbanWord n n :=
  Iff.rfl

theorem anban_word_mem (n : Nat) :
    anbanWord n n ∈ anbanLanguage := by
  exists n

end Section03
end Chapter03
end Book
end FoC

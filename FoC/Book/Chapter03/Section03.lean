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
and finite alternatives. Their canonical semantic theorems are
{lit}`RegExp.optional_denote`, {lit}`RegExp.plus_denote`, and
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

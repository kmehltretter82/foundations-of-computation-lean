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
-/

open Languages

/-!
## Derived Operators

Optional, plus, and character classes expand to union, concatenation, star,
and finite alternatives. The sample digit class demonstrates character-class
membership for a concrete one-symbol word.
-/

theorem optional_regular_expression (r : RegExp alpha) :
    Language.Equal (RegExp.Denote (RegExp.Optional r))
      (Language.Union (RegExp.Denote r) (Language.Singleton Word.Empty)) :=
  RegExp.optional_denote r

theorem plus_regular_expression (r : RegExp alpha) :
    Language.Equal (RegExp.Denote (RegExp.Plus r))
      (Language.Concat (RegExp.Denote r) (Language.Star (RegExp.Denote r))) :=
  RegExp.plus_denote r

theorem character_class_language (chars : List alpha) (w : Word alpha) :
    w ∈ RegExp.Denote (RegExp.CharClass chars) <->
      exists a, a ∈ chars ∧ w = Word.Symbol a :=
  RegExp.charClass_denote chars w

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

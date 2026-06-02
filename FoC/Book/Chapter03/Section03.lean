import FoC.Book.Chapter03.Section02

namespace FoC
namespace Book
namespace Chapter03
namespace Section03

/-!
Book: Chapter 3, Section 3.3, Application: Using Regular Expressions.
-/

open Languages

-- Book: Chapter 3, Section 3.3, `r?` is syntactic sugar for `r | epsilon`.
theorem optional_regular_expression (r : RegExp alpha) :
    Language.Equal (RegExp.Denote (RegExp.Optional r))
      (Language.Union (RegExp.Denote r) (Language.Singleton Word.Empty)) :=
  RegExp.optional_denote r

-- Book: Chapter 3, Section 3.3, `r+` is syntactic sugar for `rr*`.
theorem plus_regular_expression (r : RegExp alpha) :
    Language.Equal (RegExp.Denote (RegExp.Plus r))
      (Language.Concat (RegExp.Denote r) (Language.Star (RegExp.Denote r))) :=
  RegExp.plus_denote r

-- Book: Chapter 3, Section 3.3, character classes are finite alternatives.
theorem character_class_language (chars : List alpha) (w : Word alpha) :
    w ∈ RegExp.Denote (RegExp.CharClass chars) <->
      exists a, a ∈ chars ∧ w = Word.Symbol a :=
  RegExp.charClass_denote chars w

def digitClass : RegExp Nat :=
  RegExp.CharClass [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

-- Book: Chapter 3, Section 3.3, digit character class sample.
theorem digit_class_accepts_7 :
    [7] ∈ RegExp.Denote digitClass := by
  exact (RegExp.charClass_denote _ _).mpr
    (Exists.intro 7 (And.intro (by simp) rfl))

def anbanWord (left right : Nat) : Word Section01.AB :=
  Word.Concat (Word.RepeatSymbol Section01.AB.a left)
    (Word.Concat (Word.Symbol Section01.AB.b)
      (Word.RepeatSymbol Section01.AB.a right))

def anbanLanguage : Language Section01.AB :=
  fun w => exists n, w = anbanWord n n

-- Book: Chapter 3, Section 3.3, Exercise 4 backreference target language
-- `{ a^n b a^n | n >= 0 }`.
theorem anban_language_membership (w : Word Section01.AB) :
    w ∈ anbanLanguage <-> exists n, w = anbanWord n n :=
  Iff.rfl

-- Book: Chapter 3, Section 3.3, Exercise 4 witness word.
theorem anban_word_mem (n : Nat) :
    anbanWord n n ∈ anbanLanguage := by
  exists n

/-!
Backreferences in some programming-language "regular expressions" are noted in
the book as adding expressive power beyond regular expressions.  The exact
target language from the exercise is recorded here; its non-regularity is
proved later in Section 3.7, after the Pumping Lemma is available.
-/

end Section03
end Chapter03
end Book
end FoC

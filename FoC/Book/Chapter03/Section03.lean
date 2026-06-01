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

/-!
Backreferences in some programming-language "regular expressions" are noted in
the book as adding expressive power beyond regular expressions.  They are
classified as application syntax, not part of the formal `RegExp` grammar.
-/

end Section03
end Chapter03
end Book
end FoC

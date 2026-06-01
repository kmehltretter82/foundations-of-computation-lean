import FoC.Book.Chapter03.Section01
import FoC.Languages.Regular

namespace FoC
namespace Book
namespace Chapter03
namespace Section02

/-!
Book: Chapter 3, Section 3.2, Regular Expressions.
-/

open Languages

-- Book: Chapter 3, Section 3.2, Definition 3.2.
theorem regular_expression_empty_language (w : Word alpha) :
    w ∈ RegExp.Denote (RegExp.empty : RegExp alpha) <-> False :=
  RegExp.denote_empty w

-- Book: Chapter 3, Section 3.2, Definition 3.3.
theorem empty_string_expression_language (w : Word alpha) :
    w ∈ RegExp.Denote (RegExp.eps : RegExp alpha) <-> w = Word.Empty :=
  RegExp.denote_eps w

-- Book: Chapter 3, Section 3.2, Definition 3.3.
theorem symbol_expression_language (a : alpha) (w : Word alpha) :
    w ∈ RegExp.Denote (RegExp.sym a) <-> w = Word.Symbol a :=
  RegExp.denote_sym a w

-- Book: Chapter 3, Section 3.2, Definition 3.3.
theorem alternation_expression_language (r s : RegExp alpha) (w : Word alpha) :
    w ∈ RegExp.Denote (RegExp.alt r s) <->
      w ∈ RegExp.Denote r ∨ w ∈ RegExp.Denote s :=
  RegExp.denote_alt r s w

-- Book: Chapter 3, Section 3.2, Definition 3.3.
theorem concatenation_expression_language (r s : RegExp alpha) (w : Word alpha) :
    w ∈ RegExp.Denote (RegExp.seq r s) <->
      exists x y, x ∈ RegExp.Denote r ∧ y ∈ RegExp.Denote s ∧ w = Word.Concat x y :=
  RegExp.denote_seq r s w

-- Book: Chapter 3, Section 3.2, Definition 3.3.
theorem star_expression_language (r : RegExp alpha) (w : Word alpha) :
    w ∈ RegExp.Denote (RegExp.star r) <->
      w ∈ Language.Star (RegExp.Denote r) :=
  RegExp.denote_star r w

-- Book: Chapter 3, Section 3.2, Definition 3.4.
theorem regular_language_definition (L : Language alpha) :
    RegularLanguage.Regular L <-> exists r : RegExp alpha, RegExp.Generates r L :=
  Iff.rfl

-- Book: Chapter 3, Section 3.2, union of regular languages.
theorem union_of_regular_languages {L M : Language alpha}
    (hL : RegularLanguage.Regular L) (hM : RegularLanguage.Regular M) :
    RegularLanguage.Regular (Language.Union L M) :=
  RegularLanguage.union_regular hL hM

-- Book: Chapter 3, Section 3.2, concatenation of regular languages.
theorem concatenation_of_regular_languages {L M : Language alpha}
    (hL : RegularLanguage.Regular L) (hM : RegularLanguage.Regular M) :
    RegularLanguage.Regular (Language.Concat L M) :=
  RegularLanguage.concat_regular hL hM

-- Book: Chapter 3, Section 3.2, Kleene closure of a regular language.
theorem kleene_star_of_regular_language {L : Language alpha}
    (hL : RegularLanguage.Regular L) :
    RegularLanguage.Regular (Language.Star L) :=
  RegularLanguage.star_regular hL

-- Book: Chapter 3, Section 3.2, Exercise 3.
theorem finite_languages_are_regular (ws : List (Word alpha)) :
    RegularLanguage.Regular (fun w => w ∈ ws) :=
  RegularLanguage.finite_list_regular ws

def aStarBStar : RegExp Section01.AB :=
  RegExp.seq (RegExp.star (RegExp.sym Section01.AB.a))
    (RegExp.star (RegExp.sym Section01.AB.b))

-- Book: Chapter 3, Section 3.2, Example 3.7, sample membership.
theorem aStarBStar_accepts_aab :
    [Section01.AB.a, Section01.AB.a, Section01.AB.b] ∈ RegExp.Denote aStarBStar := by
  exists [Section01.AB.a, Section01.AB.a]
  exists [Section01.AB.b]
  constructor
  · exists [[Section01.AB.a], [Section01.AB.a]]
    constructor
    · intro p hp
      cases hp with
      | head =>
          rfl
      | tail _ htail =>
          cases htail with
          | head =>
              rfl
          | tail _ hnil =>
              cases hnil
    · rfl
  constructor
  · exists [[Section01.AB.b]]
    constructor
    · intro p hp
      cases hp with
      | head =>
          rfl
      | tail _ hnil =>
          cases hnil
    · rfl
  · rfl

end Section02
end Chapter03
end Book
end FoC

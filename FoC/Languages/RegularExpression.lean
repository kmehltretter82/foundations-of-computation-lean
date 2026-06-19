import FoC.Languages.Language

set_option doc.verso true

/-!
# Regular expressions

## Syntax and semantics

Regular expressions are represented as syntax trees.  Their meaning is a
language, defined by structural recursion: empty language, epsilon, symbols,
union, concatenation, and star.

## Book coordinates

Used by:
- Chapter 3, Section 3.2: definitions of regular expression and generated language
- Chapter 3, Section 3.3: application syntax sugar for {lit}`+` and {lit}`?`
- Chapter 3, Section 3.6: regular-language closure properties
-/

namespace FoC
namespace Languages

/-!
# Expression syntax

Regular expressions are syntax trees with constructors for the empty language,
epsilon, symbols, union, concatenation, and Kleene star.
-/

inductive RegExp (alpha : Type u) where
  | empty : RegExp alpha
  | eps : RegExp alpha
  | sym : alpha -> RegExp alpha
  | alt : RegExp alpha -> RegExp alpha -> RegExp alpha
  | seq : RegExp alpha -> RegExp alpha -> RegExp alpha
  | star : RegExp alpha -> RegExp alpha

namespace RegExp

/-!
# Denotational semantics

The meaning of an expression is a language, defined structurally by translating
each syntactic constructor to the corresponding language operation.
-/

def Denote : RegExp alpha -> Language alpha
  | empty => Language.Empty
  | eps => Language.Singleton Word.Empty
  | sym a => Language.Singleton (Word.Symbol a)
  | alt r s => Language.Union (Denote r) (Denote s)
  | seq r s => Language.Concat (Denote r) (Denote s)
  | star r => Language.Star (Denote r)

def Generates (r : RegExp alpha) (L : Language alpha) : Prop :=
  Language.Equal (Denote r) L

def Regular (L : Language alpha) : Prop :=
  exists r : RegExp alpha, Generates r L

/-!
# Derived expression forms

The textbook abbreviations such as optional, plus, character classes, finite
alternations, finite languages, and reversal are encoded as ordinary expression
transformations.
-/

def Optional (r : RegExp alpha) : RegExp alpha :=
  alt r eps

def Plus (r : RegExp alpha) : RegExp alpha :=
  seq r (star r)

def CharClass : List alpha -> RegExp alpha
  | [] => empty
  | a :: rest => alt (sym a) (CharClass rest)

def AltList : List (RegExp alpha) -> RegExp alpha
  | [] => empty
  | r :: rest => alt r (AltList rest)

def OfWord : Word alpha -> RegExp alpha
  | [] => eps
  | a :: w => seq (sym a) (OfWord w)

def OfFiniteLanguage : List (Word alpha) -> RegExp alpha
  | [] => empty
  | w :: ws => alt (OfWord w) (OfFiniteLanguage ws)

def Reverse : RegExp alpha -> RegExp alpha
  | empty => empty
  | eps => eps
  | sym a => sym a
  | alt r s => alt (Reverse r) (Reverse s)
  | seq r s => seq (Reverse s) (Reverse r)
  | star r => star (Reverse r)

/-!
# Semantic equations

These theorems expose the membership rules for each expression constructor and
register the base regular languages.
-/

/-!
# Closure constructions

The remaining theorems prove that the semantic language class is closed under
reversal, union, concatenation, star, and finite-language constructions.
-/

theorem reverse_denote (r : RegExp alpha) :
    Language.Equal (Denote (Reverse r)) (Language.Reverse (Denote r)) := by
  induction r with
  | empty =>
      intro w
      constructor <;> intro h <;> cases h
  | eps =>
      intro w
      constructor
      · intro hw
        rw [hw]
        rfl
      · intro hw
        have hrev := congrArg Word.Reverse hw
        simpa [Word.Reverse, Word.Empty] using hrev
  | sym a =>
      intro w
      constructor
      · intro hw
        rw [hw]
        rfl
      · intro hw
        have hrev := congrArg Word.Reverse hw
        simpa [Word.Reverse, Word.Symbol] using hrev
  | alt r s ihr ihs =>
      intro w
      constructor
      · intro hw
        cases hw with
        | inl hr => exact Or.inl ((ihr w).mp hr)
        | inr hs => exact Or.inr ((ihs w).mp hs)
      · intro hw
        cases hw with
        | inl hr => exact Or.inl ((ihr w).mpr hr)
        | inr hs => exact Or.inr ((ihs w).mpr hs)
  | seq r s ihr ihs =>
      intro w
      constructor
      · intro hw
        apply (Language.reverse_concat (Denote r) (Denote s) w).mpr
        cases hw with
        | intro x hx =>
            cases hx with
            | intro y hy =>
                exists x
                exists y
                constructor
                · exact (ihs x).mp hy.left
                constructor
                · exact (ihr y).mp hy.right.left
                · exact hy.right.right
      · intro hw
        have hconcat :=
          (Language.reverse_concat (Denote r) (Denote s) w).mp hw
        cases hconcat with
        | intro x hx =>
            cases hx with
            | intro y hy =>
                exists x
                exists y
                constructor
                · exact (ihs x).mpr hy.left
                constructor
                · exact (ihr y).mpr hy.right.left
                · exact hy.right.right
  | star r ih =>
      intro w
      constructor
      · intro hw
        have hstar :=
          (Language.reverse_star (Denote r) w).mpr
            (by
              cases hw with
              | intro pieces hpieces =>
                  exists pieces
                  constructor
                  · intro p hp
                    exact (ih p).mp (hpieces.left p hp)
                  · exact hpieces.right)
        exact hstar
      · intro hw
        have hstar :=
          (Language.reverse_star (Denote r) w).mp hw
        cases hstar with
        | intro pieces hpieces =>
            exists pieces
            constructor
            · intro p hp
              exact (ih p).mpr (hpieces.left p hp)
            · exact hpieces.right

theorem regular_reverse {L : Language alpha}
    (hL : Regular L) : Regular (Language.Reverse L) := by
  cases hL with
  | intro r hr =>
      exists Reverse r
      exact Language.equal_trans (reverse_denote r)
        (by
          intro w
          constructor
          · intro hw
            exact (hr (Word.Reverse w)).mp hw
          · intro hw
            exact (hr (Word.Reverse w)).mpr hw)

theorem regular_union {L M : Language alpha}
    (hL : Regular L) (hM : Regular M) : Regular (Language.Union L M) := by
  cases hL with
  | intro r hr =>
      cases hM with
      | intro s hs =>
          exists alt r s
          intro w
          constructor
          · intro hw
            cases hw with
            | inl hwr => exact Or.inl ((hr w).mp hwr)
            | inr hws => exact Or.inr ((hs w).mp hws)
          · intro hw
            cases hw with
            | inl hwL => exact Or.inl ((hr w).mpr hwL)
            | inr hwM => exact Or.inr ((hs w).mpr hwM)

theorem regular_concat {L M : Language alpha}
    (hL : Regular L) (hM : Regular M) : Regular (Language.Concat L M) := by
  cases hL with
  | intro r hr =>
      cases hM with
      | intro s hs =>
          exists seq r s
          intro w
          constructor
          · intro hw
            cases hw with
            | intro x hx =>
                cases hx with
                | intro y hy =>
                    cases hy with
                    | intro hxR hrest =>
                        cases hrest with
                        | intro hyS hwEq =>
                            exists x
                            exists y
                            exact And.intro ((hr x).mp hxR) (And.intro ((hs y).mp hyS) hwEq)
          · intro hw
            cases hw with
            | intro x hx =>
                cases hx with
                | intro y hy =>
                    cases hy with
                    | intro hxL hrest =>
                        cases hrest with
                        | intro hyM hwEq =>
                            exists x
                            exists y
                            exact And.intro ((hr x).mpr hxL) (And.intro ((hs y).mpr hyM) hwEq)

theorem regular_star {L : Language alpha} (hL : Regular L) :
    Regular (Language.Star L) := by
  cases hL with
  | intro r hr =>
      exists star r
      intro w
      constructor
      · intro hw
        cases hw with
        | intro pieces hpieces =>
            exists pieces
            constructor
            · intro p hp
              exact (hr p).mp (hpieces.left p hp)
            · exact hpieces.right
      · intro hw
        cases hw with
        | intro pieces hpieces =>
            exists pieces
            constructor
            · intro p hp
              exact (hr p).mpr (hpieces.left p hp)
            · exact hpieces.right

theorem optional_membership (r : RegExp alpha) (w : Word alpha) :
    w ∈ Denote (Optional r) <-> w ∈ Denote r ∨ w = Word.Empty :=
  Iff.rfl

theorem plus_membership (r : RegExp alpha) (w : Word alpha) :
    w ∈ Denote (Plus r) <->
      exists x y, x ∈ Denote r ∧ y ∈ Language.Star (Denote r) ∧
        w = Word.Concat x y :=
  Iff.rfl

theorem plus_subset_star (r : RegExp alpha) :
    Language.Subset (Denote (Plus r)) (Denote (star r)) := by
  intro w hw
  rcases hw with ⟨x, y, hx, hy, hwEq⟩
  rw [hwEq]
  exact Language.star_concat (Language.star_of_mem _ hx) hy

theorem charClass_denote (chars : List alpha) (w : Word alpha) :
    w ∈ Denote (CharClass chars) <->
      exists a, a ∈ chars ∧ w = Word.Symbol a := by
  induction chars with
  | nil =>
      constructor
      · intro hw
        cases hw
      · intro hw
        cases hw with
        | intro a ha =>
            cases ha.left
  | cons a rest ih =>
      constructor
      · intro hw
        cases hw with
        | inl hsym =>
            exists a
            constructor
            · exact List.Mem.head rest
            · exact hsym
        | inr hrest =>
            cases (ih.mp hrest) with
            | intro b hb =>
                exists b
                constructor
                · exact List.Mem.tail a hb.left
                · exact hb.right
      · intro hw
        cases hw with
        | intro b hb =>
            cases hb.left with
            | head =>
                exact Or.inl hb.right
            | tail _ htail =>
                exact Or.inr (ih.mpr (Exists.intro b (And.intro htail hb.right)))

theorem altList_denote (rs : List (RegExp alpha)) (w : Word alpha) :
    w ∈ Denote (AltList rs) <-> exists r, r ∈ rs ∧ w ∈ Denote r := by
  induction rs with
  | nil =>
      constructor
      · intro hw
        cases hw
      · intro hw
        cases hw with
        | intro r hr =>
            cases hr.left
  | cons r rest ih =>
      constructor
      · intro hw
        cases hw with
        | inl hwr =>
            exists r
            constructor
            · exact List.Mem.head rest
            · exact hwr
        | inr hwrest =>
            cases (ih.mp hwrest) with
            | intro s hs =>
                exists s
                constructor
                · exact List.Mem.tail r hs.left
                · exact hs.right
      · intro hw
        cases hw with
        | intro s hs =>
            cases hs.left with
            | head =>
                exact Or.inl hs.right
            | tail _ htail =>
                exact Or.inr (ih.mpr (Exists.intro s (And.intro htail hs.right)))

theorem denote_ofWord (w x : Word alpha) :
    x ∈ Denote (OfWord w) <-> x = w := by
  induction w generalizing x with
  | nil =>
      exact Iff.rfl
  | cons a rest ih =>
      constructor
      · intro hx
        cases hx with
        | intro y hy =>
            cases hy with
            | intro z hz =>
                cases hz with
                | intro hySym hrest =>
                    cases hrest with
                    | intro hzRest hxEq =>
                        have hyEq : y = [a] := hySym
                        have hzEq : z = rest := (ih z).mp hzRest
                        rw [hxEq, hyEq, hzEq]
                        rfl
      · intro hx
        rw [hx]
        exists [a]
        exists rest
        constructor
        · rfl
        constructor
        · exact (ih rest).mpr rfl
        · rfl

theorem ofWord_generates_singleton (w : Word alpha) :
    Generates (OfWord w) (Language.Singleton w) := by
  intro x
  exact denote_ofWord w x

theorem denote_ofFiniteLanguage (ws : List (Word alpha)) (w : Word alpha) :
    w ∈ Denote (OfFiniteLanguage ws) <-> w ∈ ws := by
  induction ws with
  | nil =>
      constructor
      · intro hw
        cases hw
      · intro hw
        cases hw
  | cons word rest ih =>
      constructor
      · intro hw
        cases hw with
        | inl hword =>
            have hwEq : w = word := (denote_ofWord word w).mp hword
            rw [hwEq]
            exact List.Mem.head rest
        | inr hrest =>
            exact List.Mem.tail word (ih.mp hrest)
      · intro hw
        cases hw with
        | head =>
            exact Or.inl ((denote_ofWord w w).mpr rfl)
        | tail _ htail =>
            exact Or.inr (ih.mpr htail)

theorem finite_language_regular (ws : List (Word alpha)) :
    Regular (fun w => w ∈ ws) := by
  exists OfFiniteLanguage ws
  intro w
  exact denote_ofFiniteLanguage ws w

theorem ofFiniteLanguage_generates (ws : List (Word alpha)) :
    Generates (OfFiniteLanguage ws) (fun w => w ∈ ws) := by
  intro w
  exact denote_ofFiniteLanguage ws w

end RegExp
end Languages
end FoC

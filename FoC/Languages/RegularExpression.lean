import FoC.Languages.Language

namespace FoC
namespace Languages

/-!
Regular expressions and their generated languages.

Used by:
- Chapter 3, Section 3.2: definitions of regular expression and generated language
- Chapter 3, Section 3.3: application syntax sugar for `+` and `?`
- Chapter 3, Section 3.6: regular-language closure properties
-/

inductive RegExp (alpha : Type u) where
  | empty : RegExp alpha
  | eps : RegExp alpha
  | sym : alpha -> RegExp alpha
  | alt : RegExp alpha -> RegExp alpha -> RegExp alpha
  | seq : RegExp alpha -> RegExp alpha -> RegExp alpha
  | star : RegExp alpha -> RegExp alpha

namespace RegExp

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

theorem denote_empty (w : Word alpha) : w ∈ Denote (empty : RegExp alpha) <-> False :=
  Iff.rfl

theorem denote_eps (w : Word alpha) : w ∈ Denote (eps : RegExp alpha) <-> w = Word.Empty :=
  Iff.rfl

theorem denote_sym (a : alpha) (w : Word alpha) : w ∈ Denote (sym a) <-> w = [a] :=
  Iff.rfl

theorem denote_alt (r s : RegExp alpha) (w : Word alpha) :
    w ∈ Denote (alt r s) <-> w ∈ Denote r ∨ w ∈ Denote s :=
  Iff.rfl

theorem denote_seq (r s : RegExp alpha) (w : Word alpha) :
    w ∈ Denote (seq r s) <->
      exists x y, x ∈ Denote r ∧ y ∈ Denote s ∧ w = Word.Concat x y :=
  Iff.rfl

theorem denote_star (r : RegExp alpha) (w : Word alpha) :
    w ∈ Denote (star r) <-> w ∈ Language.Star (Denote r) :=
  Iff.rfl

theorem regular_empty : Regular (Language.Empty : Language alpha) := by
  exists empty
  exact Language.equal_refl _

theorem regular_epsilon : Regular (Language.Singleton (Word.Empty : Word alpha)) := by
  exists eps
  exact Language.equal_refl _

theorem regular_symbol (a : alpha) : Regular (Language.Singleton (Word.Symbol a)) := by
  exists sym a
  exact Language.equal_refl _

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

theorem optional_denote (r : RegExp alpha) :
    Language.Equal (Denote (Optional r))
      (Language.Union (Denote r) (Language.Singleton Word.Empty)) :=
  Language.equal_refl _

theorem plus_denote (r : RegExp alpha) :
    Language.Equal (Denote (Plus r))
      (Language.Concat (Denote r) (Language.Star (Denote r))) :=
  Language.equal_refl _

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

end RegExp
end Languages
end FoC

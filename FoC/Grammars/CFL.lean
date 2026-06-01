import FoC.Grammars.CFG

namespace FoC
namespace Grammars

/-!
Context-free language vocabulary and construction lemmas.

Used by:
- Chapter 4, Section 4.1: context-free languages and closure constructions.
- Chapter 4, Section 4.5: pumping-lemma vocabulary for context-free languages.
-/

open Languages

namespace CFL

def ContextFreeLanguage (L : Language terminal) : Prop :=
  CFG.ContextFree L

theorem unionGrammar_generates_left (G : CFG terminal left) (H : CFG terminal right)
    {w : Word terminal} (hw : w ∈ CFG.GeneratedLanguage G) :
    w ∈ CFG.GeneratedLanguage (CFG.UnionGrammar G H) :=
  CFG.union_generates_left G H hw

theorem unionGrammar_generates_right (G : CFG terminal left) (H : CFG terminal right)
    {w : Word terminal} (hw : w ∈ CFG.GeneratedLanguage H) :
    w ∈ CFG.GeneratedLanguage (CFG.UnionGrammar G H) :=
  CFG.union_generates_right G H hw

theorem concatGrammar_generates (G : CFG terminal left) (H : CFG terminal right)
    {x y : Word terminal}
    (hx : x ∈ CFG.GeneratedLanguage G) (hy : y ∈ CFG.GeneratedLanguage H) :
    Word.Concat x y ∈ CFG.GeneratedLanguage (CFG.ConcatGrammar G H) :=
  CFG.concat_generates G H hx hy

theorem starGrammar_generates_empty (G : CFG terminal nt) :
    ([] : Word terminal) ∈ CFG.GeneratedLanguage (CFG.StarGrammar G) :=
  CFG.star_generates_empty G

theorem starGrammar_generates_cons (G : CFG terminal nt)
    {x y : Word terminal}
    (hx : x ∈ CFG.GeneratedLanguage G)
    (hy : y ∈ CFG.GeneratedLanguage (CFG.StarGrammar G)) :
    Word.Concat x y ∈ CFG.GeneratedLanguage (CFG.StarGrammar G) :=
  CFG.star_generates_cons G hx hy

def Concat3 (x y z : Word terminal) : Word terminal :=
  Word.Concat x (Word.Concat y z)

def Concat5 (u x y z v : Word terminal) : Word terminal :=
  Word.Concat u (Word.Concat x (Word.Concat y (Word.Concat z v)))

def Pumped (u x y z v : Word terminal) (n : Nat) : Word terminal :=
  Concat5 u (Word.RepeatWord x n) y (Word.RepeatWord z n) v

def PumpingDecomposition (L : Language terminal) (K : Nat) (w : Word terminal) : Prop :=
  exists u x y z v : Word terminal,
    w = Concat5 u x y z v ∧
    (x ≠ Word.Empty ∨ z ≠ Word.Empty) ∧
    Word.Length (Concat3 x y z) < K ∧
    forall n : Nat, Pumped u x y z v n ∈ L

def PumpingLength (L : Language terminal) (K : Nat) : Prop :=
  K > 0 ∧ forall w, w ∈ L -> K <= Word.Length w -> PumpingDecomposition L K w

def HasPumpingProperty (L : Language terminal) : Prop :=
  exists K, PumpingLength L K

def PumpingLemmaConclusion (L : Language terminal) : Prop :=
  ContextFreeLanguage L -> HasPumpingProperty L

theorem pumping_decomposition_original_word_mem {L : Language terminal}
    {K : Nat} {w : Word terminal}
    (h : PumpingDecomposition L K w) : w ∈ L := by
  cases h with
  | intro u hu =>
      cases hu with
      | intro x hx =>
          cases hx with
          | intro y hy =>
              cases hy with
              | intro z hz =>
                  cases hz with
                  | intro v hv =>
                      cases hv with
                      | intro hwEq hrest =>
                          have hpump := hrest.right.right 1
                          rw [hwEq]
                          simpa [Pumped, Concat5, Word.RepeatWord, Word.Concat] using hpump

theorem not_context_free_of_no_pumping_property {L : Language terminal}
    (pumpingLemma : PumpingLemmaConclusion L)
    (hNoPump : ¬ HasPumpingProperty L) :
    ¬ ContextFreeLanguage L := by
  intro hcf
  exact hNoPump (pumpingLemma hcf)

end CFL

end Grammars
end FoC

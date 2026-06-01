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

def FiniteProductionContextFreeLanguage (L : Language terminal) : Prop :=
  exists nonterminal : Type, exists G : CFG terminal nonterminal,
    CFG.HasFiniteProductions G ∧ Language.Equal (CFG.GeneratedLanguage G) L

theorem finiteProduction_contextFree {L : Language terminal}
    (hL : FiniteProductionContextFreeLanguage L) :
    ContextFreeLanguage L := by
  cases hL with
  | intro nonterminal hnt =>
      cases hnt with
      | intro G hG =>
          exists nonterminal
          exists G
          exact hG.right

theorem finiteProduction_rhs_length_bound {G : CFG terminal nonterminal}
    (hG : CFG.HasFiniteProductions G) :
    exists B : Nat,
      B > 0 ∧ forall A rhs, G.produces A rhs -> rhs.length < B :=
  CFG.finiteProductions_rhs_length_bound hG

theorem unionGrammar_generates_left (G : CFG terminal left) (H : CFG terminal right)
    {w : Word terminal} (hw : w ∈ CFG.GeneratedLanguage G) :
    w ∈ CFG.GeneratedLanguage (CFG.UnionGrammar G H) :=
  CFG.union_generates_left G H hw

theorem unionGrammar_generates_right (G : CFG terminal left) (H : CFG terminal right)
    {w : Word terminal} (hw : w ∈ CFG.GeneratedLanguage H) :
    w ∈ CFG.GeneratedLanguage (CFG.UnionGrammar G H) :=
  CFG.union_generates_right G H hw

theorem unionGrammar_generates_inv (G : CFG terminal left) (H : CFG terminal right)
    {w : Word terminal}
    (h : w ∈ CFG.GeneratedLanguage (CFG.UnionGrammar G H)) :
    w ∈ Language.Union (CFG.GeneratedLanguage G) (CFG.GeneratedLanguage H) :=
  CFG.union_generates_inv G H h

theorem unionGrammar_language_exact (G : CFG terminal left) (H : CFG terminal right)
    (w : Word terminal) :
    w ∈ CFG.GeneratedLanguage (CFG.UnionGrammar G H) <->
      w ∈ Language.Union (CFG.GeneratedLanguage G) (CFG.GeneratedLanguage H) :=
  CFG.union_generated_language_exact G H w

theorem union_context_free {L M : Language terminal}
    (hL : ContextFreeLanguage L) (hM : ContextFreeLanguage M) :
    ContextFreeLanguage (Language.Union L M) := by
  cases hL with
  | intro left hleft =>
      cases hleft with
      | intro G hG =>
          cases hM with
          | intro right hright =>
              cases hright with
              | intro H hH =>
                  exists CFG.SumStart left right
                  exists CFG.UnionGrammar G H
                  intro w
                  constructor
                  · intro hw
                    cases CFG.union_generates_inv G H hw with
                    | inl hwG => exact Or.inl ((hG w).mp hwG)
                    | inr hwH => exact Or.inr ((hH w).mp hwH)
                  · intro hw
                    cases hw with
                    | inl hwL => exact CFG.union_generates_left G H ((hG w).mpr hwL)
                    | inr hwM => exact CFG.union_generates_right G H ((hH w).mpr hwM)

theorem concatGrammar_generates (G : CFG terminal left) (H : CFG terminal right)
    {x y : Word terminal}
    (hx : x ∈ CFG.GeneratedLanguage G) (hy : y ∈ CFG.GeneratedLanguage H) :
    Word.Concat x y ∈ CFG.GeneratedLanguage (CFG.ConcatGrammar G H) :=
  CFG.concat_generates G H hx hy

theorem concatGrammar_generates_inv (G : CFG terminal left) (H : CFG terminal right)
    {w : Word terminal}
    (h : w ∈ CFG.GeneratedLanguage (CFG.ConcatGrammar G H)) :
    w ∈ Language.Concat (CFG.GeneratedLanguage G) (CFG.GeneratedLanguage H) :=
  CFG.concat_generates_inv G H h

theorem concatGrammar_language_exact (G : CFG terminal left) (H : CFG terminal right)
    (w : Word terminal) :
    w ∈ CFG.GeneratedLanguage (CFG.ConcatGrammar G H) <->
      w ∈ Language.Concat (CFG.GeneratedLanguage G) (CFG.GeneratedLanguage H) :=
  CFG.concat_generated_language_exact G H w

theorem concat_context_free {L M : Language terminal}
    (hL : ContextFreeLanguage L) (hM : ContextFreeLanguage M) :
    ContextFreeLanguage (Language.Concat L M) := by
  cases hL with
  | intro left hleft =>
      cases hleft with
      | intro G hG =>
          cases hM with
          | intro right hright =>
              cases hright with
              | intro H hH =>
                  exists CFG.SumStart left right
                  exists CFG.ConcatGrammar G H
                  intro w
                  constructor
                  · intro hw
                    cases CFG.concat_generates_inv G H hw with
                    | intro x hx =>
                        cases hx with
                        | intro y hy =>
                            exists x
                            exists y
                            constructor
                            · exact (hG x).mp hy.left
                            constructor
                            · exact (hH y).mp hy.right.left
                            · exact hy.right.right
                  · intro hw
                    cases hw with
                    | intro x hx =>
                        cases hx with
                        | intro y hy =>
                            rw [hy.right.right]
                            exact CFG.concat_generates G H
                              ((hG x).mpr hy.left) ((hH y).mpr hy.right.left)

theorem starGrammar_generates_empty (G : CFG terminal nt) :
    ([] : Word terminal) ∈ CFG.GeneratedLanguage (CFG.StarGrammar G) :=
  CFG.star_generates_empty G

theorem starGrammar_generates_cons (G : CFG terminal nt)
    {x y : Word terminal}
    (hx : x ∈ CFG.GeneratedLanguage G)
    (hy : y ∈ CFG.GeneratedLanguage (CFG.StarGrammar G)) :
    Word.Concat x y ∈ CFG.GeneratedLanguage (CFG.StarGrammar G) :=
  CFG.star_generates_cons G hx hy

theorem starGrammar_generates_inv (G : CFG terminal nt) {w : Word terminal}
    (h : w ∈ CFG.GeneratedLanguage (CFG.StarGrammar G)) :
    w ∈ Language.Star (CFG.GeneratedLanguage G) :=
  CFG.star_generates_inv G h

theorem starGrammar_language_exact (G : CFG terminal nt) (w : Word terminal) :
    w ∈ CFG.GeneratedLanguage (CFG.StarGrammar G) <->
      w ∈ Language.Star (CFG.GeneratedLanguage G) :=
  CFG.star_generated_language_exact G w

theorem star_context_free {L : Language terminal}
    (hL : ContextFreeLanguage L) :
    ContextFreeLanguage (Language.Star L) := by
  cases hL with
  | intro nt hnt =>
      cases hnt with
      | intro G hG =>
          exists CFG.StarNT nt
          exists CFG.StarGrammar G
          intro w
          constructor
          · intro hw
            cases CFG.star_generates_inv G hw with
            | intro pieces hpieces =>
                exists pieces
                constructor
                · intro p hp
                  exact (hG p).mp (hpieces.left p hp)
                · exact hpieces.right
          · intro hw
            cases hw with
            | intro pieces hpieces =>
                rw [← hpieces.right]
                exact CFG.star_generates_of_pieces G pieces (by
                  intro p hp
                  exact (hG p).mpr (hpieces.left p hp))

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

theorem pumping_decomposition_of_equal {L M : Language terminal} {K : Nat}
    {w : Word terminal}
    (hEq : Language.Equal L M) (h : PumpingDecomposition L K w) :
    PumpingDecomposition M K w := by
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
                      exists u
                      exists x
                      exists y
                      exists z
                      exists v
                      constructor
                      · exact hv.left
                      constructor
                      · exact hv.right.left
                      constructor
                      · exact hv.right.right.left
                      · intro n
                        exact (hEq _).mp (hv.right.right.right n)

theorem pumpingLength_of_equal {L M : Language terminal} {K : Nat}
    (hEq : Language.Equal L M) (h : PumpingLength L K) :
    PumpingLength M K := by
  constructor
  · exact h.left
  · intro w hw hlen
    exact pumping_decomposition_of_equal hEq
      (h.right w ((hEq w).mpr hw) hlen)

theorem hasPumpingProperty_of_equal {L M : Language terminal}
    (hEq : Language.Equal L M) (h : HasPumpingProperty L) :
    HasPumpingProperty M := by
  cases h with
  | intro K hK =>
      exists K
      exact pumpingLength_of_equal hEq hK

theorem pumpingLength_mono {L : Language terminal} {K M : Nat}
    (hKM : K <= M) (h : PumpingLength L K) :
    PumpingLength L M := by
  constructor
  · exact Nat.lt_of_lt_of_le h.left hKM
  · intro w hw hlen
    cases h.right w hw (Nat.le_trans hKM hlen) with
    | intro u hu =>
        cases hu with
        | intro x hx =>
            cases hx with
            | intro y hy =>
                cases hy with
                | intro z hz =>
                    cases hz with
                    | intro v hv =>
                        exists u
                        exists x
                        exists y
                        exists z
                        exists v
                        constructor
                        · exact hv.left
                        constructor
                        · exact hv.right.left
                        constructor
                        · exact Nat.lt_of_lt_of_le hv.right.right.left hKM
                        · exact hv.right.right.right

theorem not_pumpingLength_of_counterexample {L : Language terminal} {K : Nat}
    {w : Word terminal}
    (hw : w ∈ L) (hlen : K <= Word.Length w)
    (hbad :
      forall u x y z v : Word terminal,
        w = Concat5 u x y z v ->
        (x ≠ Word.Empty ∨ z ≠ Word.Empty) ->
        Word.Length (Concat3 x y z) < K ->
        exists n : Nat, ¬ Pumped u x y z v n ∈ L) :
    ¬ PumpingLength L K := by
  intro hpump
  cases hpump.right w hw hlen with
  | intro u hu =>
      cases hu with
      | intro x hx =>
          cases hx with
          | intro y hy =>
              cases hy with
              | intro z hz =>
                  cases hz with
                  | intro v hv =>
                      cases hbad u x y z v hv.left hv.right.left
                          hv.right.right.left with
                      | intro n hn =>
                          exact hn (hv.right.right.right n)

theorem not_hasPumpingProperty_of_counterexamples {L : Language terminal}
    (hbad :
      forall K : Nat, K > 0 ->
        exists w : Word terminal,
          w ∈ L ∧
          K <= Word.Length w ∧
          forall u x y z v : Word terminal,
            w = Concat5 u x y z v ->
            (x ≠ Word.Empty ∨ z ≠ Word.Empty) ->
            Word.Length (Concat3 x y z) < K ->
            exists n : Nat, ¬ Pumped u x y z v n ∈ L) :
    ¬ HasPumpingProperty L := by
  intro hpump
  cases hpump with
  | intro K hK =>
      cases hbad K hK.left with
      | intro w hw =>
          exact not_pumpingLength_of_counterexample hw.left hw.right.left
            hw.right.right hK

theorem not_context_free_of_no_pumping_property {L : Language terminal}
    (pumpingLemma : PumpingLemmaConclusion L)
    (hNoPump : ¬ HasPumpingProperty L) :
    ¬ ContextFreeLanguage L := by
  intro hcf
  exact hNoPump (pumpingLemma hcf)

end CFL

end Grammars
end FoC

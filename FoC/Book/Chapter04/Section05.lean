import FoC.Grammars.CFL

namespace FoC
namespace Book
namespace Chapter04
namespace Section05

/-!
Book: Chapter 4, Section 4.5, Non-context-free Languages.
-/

open Languages
open Grammars

inductive ABC where
  | a
  | b
  | c
deriving DecidableEq

def anbncnBlockWord (n : Nat) : Word ABC :=
  Word.Concat (Word.RepeatSymbol ABC.a n)
    (Word.Concat (Word.RepeatSymbol ABC.b n) (Word.RepeatSymbol ABC.c n))

def anbncnLanguage : Language ABC :=
  fun w => exists n, w = anbncnBlockWord n

-- Book: Chapter 4, Section 4.5, the finite-production boundary used by the
-- book's proof of the CFL Pumping Lemma.
def FiniteProductionContextFreeLanguage (L : Language terminal) : Prop :=
  CFL.FiniteProductionContextFreeLanguage L

-- Book: Chapter 4, Section 4.5, pumping-lemma decomposition vocabulary.
def CFLPumpingDecomposition (L : Language terminal) (K : Nat) (w : Word terminal) :
    Prop :=
  CFL.PumpingDecomposition L K w

-- Book: Chapter 4, Section 4.5, pumping length vocabulary.
def CFLPumpingLength (L : Language terminal) (K : Nat) : Prop :=
  CFL.PumpingLength L K

-- Book: Chapter 4, Section 4.5, pumping property vocabulary.
def CFLHasPumpingProperty (L : Language terminal) : Prop :=
  CFL.HasPumpingProperty L

-- Book: Chapter 4, Section 4.5, finite-production CFLs are CFLs under the
-- existing grammar-generated-language definition.
theorem finite_production_context_free {L : Language terminal}
    (hL : FiniteProductionContextFreeLanguage L) :
    CFL.ContextFreeLanguage L :=
  CFL.finiteProduction_contextFree hL

-- Book: Chapter 4, Section 4.5, finite production lists give a bound on
-- production right-hand-side lengths.
theorem finite_production_rhs_length_bound {G : CFG terminal nonterminal}
    (hG : CFG.HasFiniteProductions G) :
    exists B : Nat,
      B > 0 ∧ forall A rhs, G.produces A rhs -> rhs.length < B :=
  CFL.finiteProduction_rhs_length_bound hG

-- Book: Chapter 4, Section 4.5, every finite-production grammar satisfies
-- the CFL pumping property for its generated language.
theorem finite_production_grammar_pumping_property
    {terminal nonterminal : Type} {G : CFG terminal nonterminal}
    (hG : CFG.HasFiniteProductions G) :
    CFLHasPumpingProperty (CFG.GeneratedLanguage G) :=
  CFL.finiteProduction_generated_hasPumpingProperty hG

-- Book: Chapter 4, Section 4.5, the CFL Pumping Lemma for languages
-- presented by a finite-production grammar.
theorem finite_production_pumping_property {terminal : Type}
    {L : Language terminal}
    (hL : FiniteProductionContextFreeLanguage L) :
    CFLHasPumpingProperty L :=
  CFL.finiteProduction_hasPumpingProperty hL

-- Book: Chapter 4, Section 4.5, the original word is the n = 1 pumped word.
theorem pumping_decomposition_original_word_mem {L : Language terminal}
    {K : Nat} {w : Word terminal}
    (h : CFLPumpingDecomposition L K w) : w ∈ L :=
  CFL.pumping_decomposition_original_word_mem h

-- Book: Chapter 4, Section 4.5, pumping decompositions are extensional in the
-- language being pumped.
theorem pumping_decomposition_of_equal {L M : Language terminal} {K : Nat}
    {w : Word terminal}
    (hEq : Language.Equal L M) (h : CFLPumpingDecomposition L K w) :
    CFLPumpingDecomposition M K w :=
  CFL.pumping_decomposition_of_equal hEq h

-- Book: Chapter 4, Section 4.5, pumping lengths are extensional in the
-- language being pumped.
theorem pumping_length_of_equal {L M : Language terminal} {K : Nat}
    (hEq : Language.Equal L M) (h : CFLPumpingLength L K) :
    CFLPumpingLength M K :=
  CFL.pumpingLength_of_equal hEq h

-- Book: Chapter 4, Section 4.5, the pumping property is extensional in the
-- language being pumped.
theorem pumping_property_of_equal {L M : Language terminal}
    (hEq : Language.Equal L M) (h : CFLHasPumpingProperty L) :
    CFLHasPumpingProperty M :=
  CFL.hasPumpingProperty_of_equal hEq h

-- Book: Chapter 4, Section 4.5, a larger pumping length remains valid.
theorem pumping_length_monotone {L : Language terminal} {K M : Nat}
    (hKM : K <= M) (h : CFLPumpingLength L K) :
    CFLPumpingLength L M :=
  CFL.pumpingLength_mono hKM h

-- Book: Chapter 4, Section 4.5, one sufficiently long bad word refutes a
-- proposed CFL pumping length.
theorem not_pumping_length_of_counterexample {L : Language terminal} {K : Nat}
    {w : Word terminal}
    (hw : w ∈ L) (hlen : K <= Word.Length w)
    (hbad :
      forall u x y z v : Word terminal,
        w = CFL.Concat5 u x y z v ->
        (x ≠ Word.Empty ∨ z ≠ Word.Empty) ->
        Word.Length (CFL.Concat3 x y z) < K ->
        exists n : Nat, ¬ CFL.Pumped u x y z v n ∈ L) :
    ¬ CFLPumpingLength L K :=
  CFL.not_pumpingLength_of_counterexample hw hlen hbad

-- Book: Chapter 4, Section 4.5, a family of bad words refutes the CFL pumping
-- property.
theorem not_pumping_property_of_counterexamples {L : Language terminal}
    (hbad :
      forall K : Nat, K > 0 ->
        exists w : Word terminal,
          w ∈ L ∧
          K <= Word.Length w ∧
          forall u x y z v : Word terminal,
            w = CFL.Concat5 u x y z v ->
            (x ≠ Word.Empty ∨ z ≠ Word.Empty) ->
            Word.Length (CFL.Concat3 x y z) < K ->
            exists n : Nat, ¬ CFL.Pumped u x y z v n ∈ L) :
    ¬ CFLHasPumpingProperty L :=
  CFL.not_hasPumpingProperty_of_counterexamples hbad

-- Book: Chapter 4, Section 4.5, contrapositive schema for pumping arguments.
theorem not_context_free_of_no_pumping_property {L : Language terminal}
    (pumpingLemma : CFL.PumpingLemmaConclusion L)
    (hNoPump : ¬ CFLHasPumpingProperty L) :
    ¬ CFL.ContextFreeLanguage L :=
  CFL.not_context_free_of_no_pumping_property pumpingLemma hNoPump

-- Book: Chapter 4, Section 4.5, the language used in the first
-- non-context-free example.
theorem anbncn_membership (w : Word ABC) :
    w ∈ anbncnLanguage <-> exists n, w = anbncnBlockWord n :=
  Iff.rfl

theorem anbncn_block_count_a (n : Nat) :
    Word.Count ABC.a (anbncnBlockWord n) = n := by
  unfold anbncnBlockWord
  rw [Word.count_concat, Word.count_repeatSymbol_same]
  rw [Word.count_concat, Word.count_repeatSymbol_different,
    Word.count_repeatSymbol_different]
  · omega
  · intro h
    cases h
  · intro h
    cases h

theorem anbncn_block_count_b (n : Nat) :
    Word.Count ABC.b (anbncnBlockWord n) = n := by
  unfold anbncnBlockWord
  rw [Word.count_concat]
  rw [Word.count_repeatSymbol_different (a := ABC.b) (b := ABC.a)]
  rw [Word.count_concat, Word.count_repeatSymbol_same]
  rw [Word.count_repeatSymbol_different (a := ABC.b) (b := ABC.c)]
  · omega
  · intro h
    cases h
  · intro h
    cases h

theorem anbncn_block_count_c (n : Nat) :
    Word.Count ABC.c (anbncnBlockWord n) = n := by
  unfold anbncnBlockWord
  rw [Word.count_concat]
  rw [Word.count_repeatSymbol_different (a := ABC.c) (b := ABC.a)]
  rw [Word.count_concat]
  rw [Word.count_repeatSymbol_different (a := ABC.c) (b := ABC.b)]
  rw [Word.count_repeatSymbol_same]
  · omega
  · intro h
    cases h
  · intro h
    cases h

theorem anbncn_block_length (n : Nat) :
    Word.Length (anbncnBlockWord n) = 3 * n := by
  unfold anbncnBlockWord
  simp [Word.length_concat, Word.length_repeatSymbol]
  omega

theorem anbncn_members_have_equal_counts {w : Word ABC}
    (hw : w ∈ anbncnLanguage) :
    Word.Count ABC.a w = Word.Count ABC.b w ∧
      Word.Count ABC.b w = Word.Count ABC.c w := by
  cases hw with
  | intro n hn =>
      rw [hn, anbncn_block_count_a n, anbncn_block_count_b n,
        anbncn_block_count_c n]
      exact ⟨rfl, rfl⟩

theorem abc_count_sum_pos_of_nonempty {w : Word ABC}
    (h : w ≠ Word.Empty) :
    0 < Word.Count ABC.a w + Word.Count ABC.b w + Word.Count ABC.c w := by
  cases w with
  | nil =>
      exact False.elim (h rfl)
  | cons head tail =>
      cases head <;> simp [Word.Count] <;> omega

theorem anbncn_drop_after_a_count_a_zero (K l : Nat) (hl : K <= l) :
    Word.Count ABC.a (List.drop l (anbncnBlockWord K)) = 0 := by
  unfold anbncnBlockWord
  change Word.Count ABC.a
      (List.drop l
        (List.append (Word.RepeatSymbol ABC.a K)
          (Word.Concat (Word.RepeatSymbol ABC.b K) (Word.RepeatSymbol ABC.c K)))) = 0
  simp [List.drop_append, Word.RepeatSymbol, List.drop_replicate]
  have hzero : K - l = 0 := by omega
  rw [hzero]
  change Word.Count ABC.a
      (List.drop (l - K)
        (Word.Concat (Word.RepeatSymbol ABC.b K) (Word.RepeatSymbol ABC.c K))) = 0
  change Word.Count ABC.a
      (List.drop (l - K)
        (List.append (Word.RepeatSymbol ABC.b K) (Word.RepeatSymbol ABC.c K))) = 0
  simp [List.drop_append, Word.RepeatSymbol, List.drop_replicate]
  change Word.Count ABC.a
      (Word.Concat (Word.RepeatSymbol ABC.b (K - (l - K)))
        (Word.RepeatSymbol ABC.c (K - (l - K - K)))) = 0
  have hb :
      Word.Count ABC.a (Word.RepeatSymbol ABC.b (K - (l - K))) = 0 := by
    exact Word.count_repeatSymbol_different (a := ABC.a) (b := ABC.b)
      (by intro h; cases h) _
  have hc :
      Word.Count ABC.a (Word.RepeatSymbol ABC.c (K - (l - K - K))) = 0 := by
    exact Word.count_repeatSymbol_different (a := ABC.a) (b := ABC.c)
      (by intro h; cases h) _
  rw [Word.count_concat, hb, hc]

theorem anbncn_take_before_c_count_c_zero (K l : Nat)
    (hl : l <= 2 * K) :
    Word.Count ABC.c (List.take l (anbncnBlockWord K)) = 0 := by
  unfold anbncnBlockWord
  change Word.Count ABC.c
      (List.take l
        (List.append (Word.RepeatSymbol ABC.a K)
          (List.append (Word.RepeatSymbol ABC.b K) (Word.RepeatSymbol ABC.c K)))) = 0
  simp [List.take_append, Word.RepeatSymbol, List.take_replicate]
  have hzero : min (l - K - K) K = 0 := by omega
  rw [hzero]
  change Word.Count ABC.c
      (Word.Concat (Word.RepeatSymbol ABC.a (min l K))
        (Word.Concat (Word.RepeatSymbol ABC.b (min (l - K) K))
          (Word.RepeatSymbol ABC.c 0))) = 0
  rw [Word.count_concat, Word.count_concat]
  rw [Word.count_repeatSymbol_different (a := ABC.c) (b := ABC.a)]
  · rw [Word.count_repeatSymbol_different (a := ABC.c) (b := ABC.b)]
    · simp [Word.count_repeatSymbol_same]
    · intro h
      cases h
  · intro h
    cases h

theorem anbncn_middle_after_a_count_a_zero
    {u middle v : Word ABC} {K : Nat}
    (hword : anbncnBlockWord K = Word.Concat u (Word.Concat middle v))
    (hu : K <= Word.Length u) :
    Word.Count ABC.a middle = 0 := by
  have htail :
      Word.Concat middle v = List.drop (Word.Length u) (anbncnBlockWord K) := by
    calc
      Word.Concat middle v =
          List.drop (Word.Length u) (Word.Concat u (Word.Concat middle v)) := by
        change Word.Concat middle v =
          List.drop (List.length u) (List.append u (Word.Concat middle v))
        exact (List.drop_left (l₁ := u) (l₂ := Word.Concat middle v)).symm
      _ = List.drop (Word.Length u) (anbncnBlockWord K) := by
        rw [← hword]
  have hcountTail :
      Word.Count ABC.a (Word.Concat middle v) = 0 := by
    rw [htail]
    exact anbncn_drop_after_a_count_a_zero K (Word.Length u) hu
  rw [Word.count_concat] at hcountTail
  omega

theorem anbncn_middle_before_c_count_c_zero
    {u middle v : Word ABC} {K : Nat}
    (hword : anbncnBlockWord K = Word.Concat u (Word.Concat middle v))
    (hprefix : Word.Length (Word.Concat u middle) <= 2 * K) :
    Word.Count ABC.c middle = 0 := by
  have hprefixEq :
      Word.Concat u middle =
        List.take (Word.Length (Word.Concat u middle)) (anbncnBlockWord K) := by
    calc
      Word.Concat u middle =
          List.take (Word.Length (Word.Concat u middle))
            (Word.Concat (Word.Concat u middle) v) := by
        change Word.Concat u middle =
          List.take (List.length (Word.Concat u middle))
            (List.append (Word.Concat u middle) v)
        exact (List.take_left (l₁ := Word.Concat u middle) (l₂ := v)).symm
      _ = List.take (Word.Length (Word.Concat u middle))
            (Word.Concat u (Word.Concat middle v)) := by
        rw [Word.concat_assoc]
      _ = List.take (Word.Length (Word.Concat u middle)) (anbncnBlockWord K) := by
        rw [← hword]
  have hcountPrefix :
      Word.Count ABC.c (Word.Concat u middle) = 0 := by
    rw [hprefixEq]
    exact anbncn_take_before_c_count_c_zero K
      (Word.Length (Word.Concat u middle)) hprefix
  rw [Word.count_concat] at hcountPrefix
  omega

theorem anbncn_short_middle_count_a_or_c_zero
    {u middle v : Word ABC} {K : Nat}
    (hword : anbncnBlockWord K = Word.Concat u (Word.Concat middle v))
    (hmiddle : Word.Length middle < K) :
    Word.Count ABC.a middle = 0 ∨ Word.Count ABC.c middle = 0 := by
  by_cases hu : K <= Word.Length u
  · exact Or.inl (anbncn_middle_after_a_count_a_zero hword hu)
  · apply Or.inr
    have huLt : Word.Length u < K := by omega
    have hprefix : Word.Length (Word.Concat u middle) <= 2 * K := by
      rw [Word.length_concat]
      omega
    exact anbncn_middle_before_c_count_c_zero hword hprefix

theorem cfl_pumped_two_count (s : ABC) (u x y z v : Word ABC) :
    Word.Count s (CFL.Pumped u x y z v 2) =
      Word.Count s (CFL.Concat5 u x y z v) +
        Word.Count s (Word.Concat x z) := by
  unfold CFL.Pumped CFL.Concat5
  rw [show Word.RepeatWord x 2 = Word.Concat x x by simp [Word.RepeatWord, Word.Concat]]
  rw [show Word.RepeatWord z 2 = Word.Concat z z by simp [Word.RepeatWord, Word.Concat]]
  repeat rw [Word.count_concat]
  omega

theorem anbncn_xz_count_a_or_c_zero
    {u x y z v : Word ABC} {K : Nat}
    (hword : anbncnBlockWord K = CFL.Concat5 u x y z v)
    (hshort : Word.Length (CFL.Concat3 x y z) < K) :
    Word.Count ABC.a (Word.Concat x z) = 0 ∨
      Word.Count ABC.c (Word.Concat x z) = 0 := by
  have hmiddleWord :
      anbncnBlockWord K =
        Word.Concat u (Word.Concat (CFL.Concat3 x y z) v) := by
    rw [hword]
    simp [CFL.Concat5, CFL.Concat3, Word.Concat, List.append_assoc]
  cases anbncn_short_middle_count_a_or_c_zero hmiddleWord hshort with
  | inl ha =>
      apply Or.inl
      unfold CFL.Concat3 at ha
      rw [Word.count_concat, Word.count_concat] at ha
      rw [Word.count_concat]
      omega
  | inr hc =>
      apply Or.inr
      unfold CFL.Concat3 at hc
      rw [Word.count_concat, Word.count_concat] at hc
      rw [Word.count_concat]
      omega

theorem anbncn_xz_nonempty {x z : Word ABC}
    (h : x ≠ Word.Empty ∨ z ≠ Word.Empty) :
    Word.Concat x z ≠ Word.Empty := by
  intro hxz
  cases x with
  | nil =>
      cases h with
      | inl hx =>
          exact hx rfl
      | inr hz =>
          apply hz
          simpa [Word.Concat, Word.Empty] using hxz
  | cons _ _ =>
      cases hxz

theorem anbncn_pump_two_not_mem
    {u x y z v : Word ABC} {K : Nat}
    (hword : anbncnBlockWord K = CFL.Concat5 u x y z v)
    (hnonempty : x ≠ Word.Empty ∨ z ≠ Word.Empty)
    (hshort : Word.Length (CFL.Concat3 x y z) < K) :
    ¬ CFL.Pumped u x y z v 2 ∈ anbncnLanguage := by
  intro hpumped
  have hcounts := anbncn_members_have_equal_counts hpumped
  have hcountA :
      Word.Count ABC.a (CFL.Pumped u x y z v 2) =
        K + Word.Count ABC.a (Word.Concat x z) := by
    rw [cfl_pumped_two_count, ← hword, anbncn_block_count_a K]
  have hcountB :
      Word.Count ABC.b (CFL.Pumped u x y z v 2) =
        K + Word.Count ABC.b (Word.Concat x z) := by
    rw [cfl_pumped_two_count, ← hword, anbncn_block_count_b K]
  have hcountC :
      Word.Count ABC.c (CFL.Pumped u x y z v 2) =
        K + Word.Count ABC.c (Word.Concat x z) := by
    rw [cfl_pumped_two_count, ← hword, anbncn_block_count_c K]
  have hEqAB :
      K + Word.Count ABC.a (Word.Concat x z) =
        K + Word.Count ABC.b (Word.Concat x z) := by
    rw [← hcountA, ← hcountB]
    exact hcounts.left
  have hEqBC :
      K + Word.Count ABC.b (Word.Concat x z) =
        K + Word.Count ABC.c (Word.Concat x z) := by
    rw [← hcountB, ← hcountC]
    exact hcounts.right
  have hxzNonempty : Word.Concat x z ≠ Word.Empty :=
    anbncn_xz_nonempty hnonempty
  have hpos :
      0 < Word.Count ABC.a (Word.Concat x z) +
        Word.Count ABC.b (Word.Concat x z) +
        Word.Count ABC.c (Word.Concat x z) :=
    abc_count_sum_pos_of_nonempty hxzNonempty
  cases anbncn_xz_count_a_or_c_zero hword hshort with
  | inl ha0 =>
      have hb0 : Word.Count ABC.b (Word.Concat x z) = 0 := by omega
      have hc0 : Word.Count ABC.c (Word.Concat x z) = 0 := by omega
      omega
  | inr hc0 =>
      have hb0 : Word.Count ABC.b (Word.Concat x z) = 0 := by omega
      have ha0 : Word.Count ABC.a (Word.Concat x z) = 0 := by omega
      omega

-- Book: Chapter 4, Section 4.5, no pumping length works for
-- `{a^n b^n c^n | n >= 0}`.
theorem anbncn_no_pumping_property :
    ¬ CFLHasPumpingProperty anbncnLanguage := by
  intro hpump
  cases hpump with
  | intro K hK =>
      let w : Word ABC := anbncnBlockWord K
      have hwMem : w ∈ anbncnLanguage := by
        exists K
      have hwLength : K <= Word.Length w := by
        simp [w, anbncn_block_length]
        omega
      have hdec := hK.right w hwMem hwLength
      cases hdec with
      | intro u hu =>
          cases hu with
          | intro x hx =>
              cases hx with
              | intro y hy =>
                  cases hy with
                  | intro z hz =>
                      cases hz with
                      | intro v hv =>
                          exact anbncn_pump_two_not_mem hv.left
                            hv.right.left hv.right.right.left
                            (hv.right.right.right 2)

-- Book: Chapter 4, Section 4.5, `{a^n b^n c^n | n >= 0}` is not generated
-- by any finite-production context-free grammar.
theorem anbncn_not_finite_production_context_free :
    ¬ FiniteProductionContextFreeLanguage anbncnLanguage := by
  intro hcf
  exact anbncn_no_pumping_property
    (finite_production_pumping_property hcf)

-- Book: Chapter 4, Section 4.5, conditional non-context-freeness for
-- `{a^n b^n c^n | n >= 0}` from the CFL Pumping Lemma conclusion.
theorem anbncn_not_context_free_from_pumping_lemma
    (pumpingLemma : CFL.PumpingLemmaConclusion anbncnLanguage) :
    ¬ CFL.ContextFreeLanguage anbncnLanguage :=
  CFL.not_context_free_of_no_pumping_property pumpingLemma
    anbncn_no_pumping_property

/-!
The concrete contradiction for `{ a^n b^n c^n | n >= 0 }` is now formalized:
no pumping length can satisfy the book's quantified CFL pumping property for
this language, and the finite-production version of the CFL Pumping Lemma is
formalized.  The final `not context-free` theorem remains parameterized only for
the broader `ContextFreeLanguage` definition, which permits arbitrary production
relations rather than requiring a finite production presentation.
-/

end Section05
end Chapter04
end Book
end FoC

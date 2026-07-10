import FoC.Book.Chapter04.Section05.AnBnCn

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter04
namespace Section05

open Languages
open Grammars

/-!
# Context-Free Pumping and the Three-Block Counterexample

This module presents the book-facing pumping vocabulary and reusable
counterexample schemas, then proves that {lit}`a^n b^n c^n` has no
context-free pumping decomposition.
-/

/-!
## Finite-Production CFLs and Pumping Vocabulary

The book-facing context-free predicate requires a finite production list. The
CFL Pumping Lemma uses a five-part decomposition {lit}`u x y z v`, where pumping
repeats the two outer middle pieces {lit}`x` and {lit}`z` together. At least one of
{lit}`x` or {lit}`z` is nonempty, and the combined middle region {lit}`x y z` is bounded by
the pumping length.
-/

def FiniteProductionContextFreeLanguage (L : Language terminal) : Prop :=
  CFL.FiniteProductionContextFreeLanguage L

def CFLPumpingDecomposition (L : Language terminal) (K : Nat) (w : Word terminal) :
    Prop :=
  CFL.PumpingDecomposition L K w

def CFLPumpingLength (L : Language terminal) (K : Nat) : Prop :=
  CFL.PumpingLength L K

def CFLHasPumpingProperty (L : Language terminal) : Prop :=
  CFL.HasPumpingProperty L

def LanguageClassExtensional (C : Language terminal -> Prop) : Prop :=
  forall L M, Language.Equal L M -> C L -> C M

def ClosedUnderIntersection (C : Language terminal -> Prop) : Prop :=
  forall L M, C L -> C M -> C (Language.Inter L M)

def ClosedUnderUnion (C : Language terminal -> Prop) : Prop :=
  forall L M, C L -> C M -> C (Language.Union L M)

def ClosedUnderComplement (C : Language terminal -> Prop) : Prop :=
  forall L, C L -> C (Language.Compl L)

theorem finite_production_context_free {L : Language terminal}
    (hL : FiniteProductionContextFreeLanguage L) :
    CFL.ContextFreeLanguage L :=
  hL

theorem finite_production_context_free_of_equal {L M : Language terminal}
    (hEq : Language.Equal L M)
    (hL : FiniteProductionContextFreeLanguage L) :
    FiniteProductionContextFreeLanguage M := by
  cases hL with
  | intro nonterminal hnt =>
      cases hnt with
      | intro G hG =>
          exists nonterminal
          exists G
          constructor
          · exact hG.left
          · exact FoC.Foundation.FSet.equal_trans hG.right hEq

theorem finite_production_context_free_extensional :
    LanguageClassExtensional
      (FiniteProductionContextFreeLanguage (terminal := terminal)) := by
  intro L M hEq hL
  exact finite_production_context_free_of_equal hEq hL

theorem finite_production_cfls_closed_under_union :
    ClosedUnderUnion
      (FiniteProductionContextFreeLanguage (terminal := terminal)) := by
  intro L M hL hM
  exact CFL.union_context_free hL hM

theorem finite_production_rhs_length_bound {G : CFG terminal nonterminal}
    (hG : CFG.HasFiniteProductions G) :
    exists B : Nat,
      B > 0 ∧ forall A rhs, G.produces A rhs -> rhs.length < B :=
  CFG.finiteProductions_rhs_length_bound hG

theorem finite_production_grammar_pumping_property
    {terminal nonterminal : Type} {G : CFG terminal nonterminal}
    (hG : CFG.HasFiniteProductions G) :
    CFLHasPumpingProperty (CFG.GeneratedLanguage G) :=
  CFL.finiteProduction_generated_hasPumpingProperty
    (CFG.hasFinitePresentation_of_hasFiniteProductions hG)

theorem finite_production_pumping_property {terminal : Type}
    {L : Language terminal}
    (hL : FiniteProductionContextFreeLanguage L) :
    CFLHasPumpingProperty L :=
  CFL.finiteProduction_hasPumpingProperty hL

theorem pumping_decomposition_original_word_mem {L : Language terminal}
    {K : Nat} {w : Word terminal}
    (h : CFLPumpingDecomposition L K w) : w ∈ L :=
  CFL.pumping_decomposition_original_word_mem h

theorem pumping_decomposition_of_equal {L M : Language terminal} {K : Nat}
    {w : Word terminal}
    (hEq : Language.Equal L M) (h : CFLPumpingDecomposition L K w) :
    CFLPumpingDecomposition M K w :=
  CFL.pumping_decomposition_of_equal hEq h

theorem pumping_length_of_equal {L M : Language terminal} {K : Nat}
    (hEq : Language.Equal L M) (h : CFLPumpingLength L K) :
    CFLPumpingLength M K :=
  CFL.pumpingLength_of_equal hEq h

theorem pumping_property_of_equal {L M : Language terminal}
    (hEq : Language.Equal L M) (h : CFLHasPumpingProperty L) :
    CFLHasPumpingProperty M :=
  CFL.hasPumpingProperty_of_equal hEq h

theorem pumping_length_monotone {L : Language terminal} {K M : Nat}
    (hKM : K <= M) (h : CFLPumpingLength L K) :
    CFLPumpingLength L M :=
  CFL.pumpingLength_mono hKM h

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

/-!
These wrappers are the practical way to use the CFL Pumping Lemma on this page:
build a bad-word family for every proposed pumping length, then conclude that
the language is not context-free.
-/

theorem not_context_free_of_no_pumping_property {terminal : Type}
    {L : Language terminal}
    (hNoPump : ¬ CFLHasPumpingProperty L) :
    ¬ CFL.ContextFreeLanguage L :=
  CFL.not_context_free_of_no_pumping_property hNoPump

def CFLPumpingBadWordFamily (L : Language terminal) : Prop :=
  forall K : Nat, K > 0 ->
    exists w : Word terminal,
      w ∈ L ∧
      K <= Word.Length w ∧
      forall u x y z v : Word terminal,
        w = CFL.Concat5 u x y z v ->
        (x ≠ Word.Empty ∨ z ≠ Word.Empty) ->
        Word.Length (CFL.Concat3 x y z) < K ->
        exists n : Nat, ¬ CFL.Pumped u x y z v n ∈ L

theorem not_pumping_property_of_bad_word_family {L : Language terminal}
    (hbad : CFLPumpingBadWordFamily L) :
    ¬ CFLHasPumpingProperty L :=
  not_pumping_property_of_counterexamples hbad

theorem not_context_free_of_bad_word_family {terminal : Type}
    {L : Language terminal}
    (hbad : CFLPumpingBadWordFamily L) :
    ¬ CFL.ContextFreeLanguage L :=
  not_context_free_of_no_pumping_property
    (not_pumping_property_of_bad_word_family hbad)

theorem not_finite_production_context_free_of_bad_word_family
    {terminal : Type} {L : Language terminal}
    (hbad : CFLPumpingBadWordFamily L) :
    ¬ FiniteProductionContextFreeLanguage L := by
  intro hcf
  exact not_pumping_property_of_bad_word_family hbad
    (finite_production_pumping_property hcf)

theorem cfl_pumped_two_count_symbol [DecidableEq terminal]
    (s : terminal) (u x y z v : Word terminal) :
    Word.Count s (CFL.Pumped u x y z v 2) =
      Word.Count s (CFL.Concat5 u x y z v) +
        Word.Count s (Word.Concat x z) := by
  unfold CFL.Pumped CFL.Concat5
  rw [show Word.RepeatWord x 2 = Word.Concat x x by
    simp [Word.RepeatWord, Word.Concat]]
  rw [show Word.RepeatWord z 2 = Word.Concat z z by
    simp [Word.RepeatWord, Word.Concat]]
  repeat rw [Word.count_concat]
  lia

/-!
## Pumping {lit}`a^n b^n c^n`

For a proposed CFL pumping length {lit}`K`, choose {lit}`a^K b^K c^K`. The bounded
middle region {lit}`x y z` cannot cover all three block boundaries at once, so
pumping {lit}`x` and {lit}`z` with count {lit}`2` changes at most two of the three symbol
counts. The resulting word cannot still have equal numbers of {lit}`a`, {lit}`b`, and
{lit}`c`.
-/

theorem anbncn_membership (w : Word ABC) :
    w ∈ anbncnLanguage <-> exists n, w = anbncnBlockWord n :=
  Iff.rfl

theorem anbncn_block_count_a (n : Nat) :
    Word.Count ABC.a (anbncnBlockWord n) = n := by
  unfold anbncnBlockWord
  rw [Word.count_concat, Word.count_repeatSymbol_same]
  rw [Word.count_concat, Word.count_repeatSymbol_different,
    Word.count_repeatSymbol_different]
  · lia
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
  · lia
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
  · lia
  · intro h
    cases h
  · intro h
    cases h

theorem anbncn_block_length (n : Nat) :
    Word.Length (anbncnBlockWord n) = 3 * n := by
  unfold anbncnBlockWord
  simp [Word.length_concat, Word.length_repeatSymbol]
  lia

theorem anbncn_members_have_equal_counts {w : Word ABC}
    (hw : w ∈ anbncnLanguage) :
    Word.Count ABC.a w = Word.Count ABC.b w ∧
      Word.Count ABC.b w = Word.Count ABC.c w := by
  cases hw with
  | intro n hn =>
      rw [hn, anbncn_block_count_a n, anbncn_block_count_b n,
        anbncn_block_count_c n]
      exact ⟨rfl, rfl⟩

/-!
The pumping contradiction needs one combinatorial fact: because the pumpable
middle region is shorter than {lit}`K`, it cannot touch both the first
{lit}`a`-block and the final {lit}`c`-block of {lit}`a^K b^K c^K`.
-/

theorem abc_count_sum_pos_of_nonempty {w : Word ABC}
    (h : w ≠ Word.Empty) :
    0 < Word.Count ABC.a w + Word.Count ABC.b w + Word.Count ABC.c w := by
  cases w with
  | nil =>
      exact False.elim (h rfl)
  | cons head tail =>
      cases head <;> simp [Word.Count] <;> lia

theorem anbncn_drop_after_a_count_a_zero (K l : Nat) (hl : K <= l) :
    Word.Count ABC.a (List.drop l (anbncnBlockWord K)) = 0 := by
  unfold anbncnBlockWord
  change Word.Count ABC.a
      (List.drop l
        (List.append (Word.RepeatSymbol ABC.a K)
          (Word.Concat (Word.RepeatSymbol ABC.b K) (Word.RepeatSymbol ABC.c K)))) = 0
  simp [List.drop_append, Word.RepeatSymbol, List.drop_replicate]
  have hzero : K - l = 0 := by lia
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
  have hzero : min (l - K - K) K = 0 := by
    rw [Nat.min_eq_left (by lia)]
    lia
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
  lia

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
  lia

theorem anbncn_short_middle_count_a_or_c_zero
    {u middle v : Word ABC} {K : Nat}
    (hword : anbncnBlockWord K = Word.Concat u (Word.Concat middle v))
    (hmiddle : Word.Length middle < K) :
    Word.Count ABC.a middle = 0 ∨ Word.Count ABC.c middle = 0 := by
  by_cases hu : K <= Word.Length u
  · exact Or.inl (anbncn_middle_after_a_count_a_zero hword hu)
  · apply Or.inr
    have huLt : Word.Length u < K := by lia
    have hprefix : Word.Length (Word.Concat u middle) <= 2 * K := by
      rw [Word.length_concat]
      lia
    exact anbncn_middle_before_c_count_c_zero hword hprefix

/-!
Pumping with count {lit}`2` adds one extra copy of {lit}`x` and one extra copy
of {lit}`z`. Since {lit}`x ++ z` is nonempty but misses either all {lit}`a`s or
all {lit}`c`s, at least one of the three counts changes differently from the
others.
-/

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
      lia
  | inr hc =>
      apply Or.inr
      unfold CFL.Concat3 at hc
      rw [Word.count_concat, Word.count_concat] at hc
      rw [Word.count_concat]
      lia

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
    rw [cfl_pumped_two_count_symbol, ← hword, anbncn_block_count_a K]
  have hcountB :
      Word.Count ABC.b (CFL.Pumped u x y z v 2) =
        K + Word.Count ABC.b (Word.Concat x z) := by
    rw [cfl_pumped_two_count_symbol, ← hword, anbncn_block_count_b K]
  have hcountC :
      Word.Count ABC.c (CFL.Pumped u x y z v 2) =
        K + Word.Count ABC.c (Word.Concat x z) := by
    rw [cfl_pumped_two_count_symbol, ← hword, anbncn_block_count_c K]
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
      have hb0 : Word.Count ABC.b (Word.Concat x z) = 0 := by lia
      have hc0 : Word.Count ABC.c (Word.Concat x z) = 0 := by lia
      lia
  | inr hc0 =>
      have hb0 : Word.Count ABC.b (Word.Concat x z) = 0 := by lia
      have ha0 : Word.Count ABC.a (Word.Concat x z) = 0 := by lia
      lia

theorem anbncn_bad_word_family :
    CFLPumpingBadWordFamily anbncnLanguage := by
  intro K hK
  let w : Word ABC := anbncnBlockWord K
  have hwMem : w ∈ anbncnLanguage := by
    exists K
  have hwLength : K <= Word.Length w := by
    simp [w, anbncn_block_length]
    lia
  refine ⟨w, hwMem, hwLength, ?_⟩
  intro u x y z v hword hnonempty hshort
  exact ⟨2, anbncn_pump_two_not_mem hword hnonempty hshort⟩

theorem anbncn_no_pumping_property :
    ¬ CFLHasPumpingProperty anbncnLanguage :=
  not_pumping_property_of_bad_word_family anbncn_bad_word_family

theorem anbncn_not_finite_production_context_free :
    ¬ FiniteProductionContextFreeLanguage anbncnLanguage := by
  intro hcf
  exact anbncn_no_pumping_property
    (finite_production_pumping_property hcf)

theorem anbncn_not_context_free :
    ¬ CFL.ContextFreeLanguage anbncnLanguage :=
  not_context_free_of_no_pumping_property anbncn_no_pumping_property

end Section05
end Chapter04
end Book
end FoC


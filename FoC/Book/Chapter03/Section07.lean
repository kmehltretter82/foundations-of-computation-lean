import FoC.Book.Chapter03.Section06
import FoC.Languages.Pumping

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter03
namespace Section07

/-!
# Chapter 3, Section 3.7: Non-Regular Languages

This section formalizes the Pumping Lemma interface and its use for proving
languages non-regular. The reusable proof infrastructure lives in
{module}`FoC.Languages.Pumping`; this file applies it to the book's
{lit}`a^n b a^n` and {lit}`a^n b^n` examples.

Informally, the Pumping Lemma says that every regular language has a positive
number {lit}`n` such that every word in the language of length at least {lit}`n` can be
split as {lit}`x y z`, with {lit}`y` nonempty and {lit}`x y` near the front of the word, so
that repeating {lit}`y` any number of times keeps the word in the language. To prove
a language non-regular, we prove the opposite pumping behavior: every proposed
{lit}`n` has a long word for which every legal split can be broken by pumping.
-/

open Languages

/-!
## Pumping Lemma Vocabulary

The first theorems expose the quantified shape of pumping lengths,
decompositions, extensionality, monotonicity, and counterexample principles.
These are the tools used to turn a family of bad words into non-regularity.

{lit}`Pumping.PumpingLength L n` is the formal version of "n is a valid pumping
length for L". It contains three pieces of information: {lit}`n > 0`; every long
word {lit}`w` in {lit}`L` admits a decomposition; and that decomposition includes the
conditions {lit}`w = x y z`, `|x y| <= n`, `|y| > 0`, and membership of every pumped
word {lit}`x y^k z`.

{lit}`Pumping.HasPumpingProperty L` says that at least one such {lit}`n` exists. The
regular-language Pumping Lemma is the theorem that regular languages have this
property.
-/

theorem pumping_length_definition (L : Language alpha) (n : Nat) :
    Pumping.PumpingLength L n <->
      n > 0 ∧ forall w, w ∈ L -> n <= Word.Length w -> Pumping.Decomposition L n w :=
  Iff.rfl

theorem pumped_decomposition_original_word_mem
    {L : Language alpha} {n : Nat} {w : Word alpha}
    (h : Pumping.Decomposition L n w) : w ∈ L :=
  Pumping.decomposition_original_word_mem h

theorem pumped_decomposition_of_equal {L M : Language alpha} {n : Nat}
    {w : Word alpha}
    (hEq : Language.Equal L M) (h : Pumping.Decomposition L n w) :
    Pumping.Decomposition M n w :=
  Pumping.decomposition_of_equal hEq h

theorem pumping_length_of_equal {L M : Language alpha} {n : Nat}
    (hEq : Language.Equal L M) (h : Pumping.PumpingLength L n) :
    Pumping.PumpingLength M n :=
  Pumping.pumpingLength_of_equal hEq h

theorem pumping_property_of_equal {L M : Language alpha}
    (hEq : Language.Equal L M) (h : Pumping.HasPumpingProperty L) :
    Pumping.HasPumpingProperty M :=
  Pumping.hasPumpingProperty_of_equal hEq h

theorem pumping_length_monotone {L : Language alpha} {n m : Nat}
    (hnm : n <= m) (h : Pumping.PumpingLength L n) :
    Pumping.PumpingLength L m :=
  Pumping.pumpingLength_mono hnm h

/-!
The next two declarations are the reusable "bad word" principle. For a fixed
candidate pumping length {lit}`n`, it is enough to produce one long word {lit}`w` in the
language such that every legal split {lit}`w = x y z` fails after some pump count
{lit}`k`. If such a bad word exists for every positive {lit}`n`, then the language has no
pumping property at all.
-/

theorem not_pumping_length_of_counterexample {L : Language alpha} {n : Nat}
    {w : Word alpha}
    (hw : w ∈ L) (hlen : n <= Word.Length w)
    (hbad :
      forall x y z : Word alpha,
        w = Word.Concat x (Word.Concat y z) ->
        Word.Length (Word.Concat x y) <= n ->
        Word.Length y > 0 ->
        exists k : Nat,
          ¬ Word.Concat x (Word.Concat (Word.RepeatWord y k) z) ∈ L) :
    ¬ Pumping.PumpingLength L n :=
  Pumping.not_pumpingLength_of_counterexample hw hlen hbad

theorem not_pumping_property_of_counterexamples {L : Language alpha}
    (hbad :
      forall n : Nat, n > 0 ->
        exists w : Word alpha,
          w ∈ L ∧
          n <= Word.Length w ∧
          forall x y z : Word alpha,
            w = Word.Concat x (Word.Concat y z) ->
            Word.Length (Word.Concat x y) <= n ->
            Word.Length y > 0 ->
            exists k : Nat,
              ¬ Word.Concat x (Word.Concat (Word.RepeatWord y k) z) ∈ L) :
    ¬ Pumping.HasPumpingProperty L :=
  Pumping.not_hasPumpingProperty_of_counterexamples hbad

/-!
The final vocabulary statements connect the counterexample method to
regularity. If the regular-language Pumping Lemma is available for {lit}`L`, then
showing that {lit}`L` has no pumping property proves {lit}`L` is not regular.
-/

theorem not_regular_if_no_pumping_property {L : Language alpha}
    (pumpingLemma : Pumping.PumpingLemmaConclusion L)
    (hNoPump : ¬ Pumping.HasPumpingProperty L) :
    ¬ RegularLanguage.Regular L :=
  Pumping.not_regular_of_no_pumping_property pumpingLemma hNoPump

theorem not_regular_if_no_pumping_property_regular {L : Language alpha}
    (hNoPump : ¬ Pumping.HasPumpingProperty L) :
    ¬ RegularLanguage.Regular L :=
  Pumping.not_regular_of_no_pumping_property_regular hNoPump

theorem regular_languages_have_pumping_property {L : Language alpha}
    (hL : RegularLanguage.Regular L) :
    Pumping.HasPumpingProperty L :=
  Pumping.regular_hasPumpingProperty hL

theorem pumping_lemma_conclusion (L : Language alpha) :
    Pumping.PumpingLemmaConclusion L :=
  Pumping.regular_pumpingLemmaConclusion L

/-!
# Backreference Language

The language {lit}`a^n b a^n` was introduced in Section 3.3 as the target of
a backreference-style expression. The next lemmas establish the bookkeeping
needed to delete a pumped initial block of {lit}`a` symbols and derive a
contradiction.

The bad word for a proposed pumping length {lit}`n` is {lit}`a^n b a^n`. Because the
split must satisfy `|x y| <= n`, the pumped portion {lit}`y` lies entirely in the
first block of {lit}`a` symbols. Pumping with {lit}`k = 0` deletes at least one initial
{lit}`a`, leaving fewer {lit}`a`s before the middle {lit}`b` than after it. That word cannot
belong to `{ a^n b a^n | n >= 0 }`.
-/

theorem repeatSymbol_concat_same (a : alpha) (m n : Nat) :
    Word.Concat (Word.RepeatSymbol a m) (Word.RepeatSymbol a n) =
      Word.RepeatSymbol a (m + n) := by
  induction m with
  | zero => simp [Word.Concat, Word.RepeatSymbol]
  | succ _ _ => simp [Word.Concat, Word.RepeatSymbol]

theorem anbanWord_injective {p q r s : Nat}
    (h : Section03.anbanWord p q = Section03.anbanWord r s) :
    p = r ∧ q = s := by
  induction p generalizing r q s with
  | zero =>
      cases r with
      | zero =>
          constructor
          · rfl
          · unfold Section03.anbanWord at h
            simp [Word.Concat, Word.Symbol, Word.RepeatSymbol] at h
            have hlen := congrArg List.length h
            simpa using hlen
      | succ _ =>
          unfold Section03.anbanWord at h
          simp [Word.Concat, Word.Symbol, Word.RepeatSymbol, List.replicate_succ] at h
          cases h
  | succ p ih =>
      cases r with
      | zero =>
          unfold Section03.anbanWord at h
          simp [Word.Concat, Word.Symbol, Word.RepeatSymbol, List.replicate_succ] at h
          cases h
      | succ r =>
          unfold Section03.anbanWord at h
          simp [Word.Concat, Word.Symbol, Word.RepeatSymbol, List.replicate_succ] at h
          injection h with _ htail
          have htail' : Section03.anbanWord p q = Section03.anbanWord r s := by
            simpa [Section03.anbanWord, Word.Concat, Word.Symbol, Word.RepeatSymbol] using htail
          cases ih htail' with
          | intro hpr hqs =>
              constructor
              · omega
              · exact hqs

theorem anban_members_have_equal_blocks {p q : Nat}
    (h : Section03.anbanWord p q ∈ Section03.anbanLanguage) :
    p = q := by
  cases h with
  | intro n hn =>
      have hinj := anbanWord_injective hn
      rw [hinj.left, hinj.right]

theorem anbanWord_delete_initial_a
    {x y z : Word Section01.AB} {n : Nat}
    (hword : Section03.anbanWord n n = Word.Concat x (Word.Concat y z))
    (hxy : Word.Length (Word.Concat x y) <= n) :
    Word.Concat x z = Section03.anbanWord (n - Word.Length y) n := by
  let lenx := Word.Length x
  let leny := Word.Length y
  let lenxy := Word.Length (Word.Concat x y)
  have hlenxy : lenxy = lenx + leny := by
    simp [lenxy, lenx, leny, Word.length_concat]
  let suffix : Word Section01.AB :=
    Word.Concat (Word.Symbol Section01.AB.b) (Word.RepeatSymbol Section01.AB.a n)
  have hxyRep : Word.Concat x y = Word.RepeatSymbol Section01.AB.a lenxy := by
    have hprefix :
        Word.Concat x y = List.take lenxy (Section03.anbanWord n n) := by
      calc
        Word.Concat x y = List.take lenxy (Word.Concat (Word.Concat x y) z) := by
          change Word.Concat x y = List.take (List.length (Word.Concat x y))
            (List.append (Word.Concat x y) z)
          exact (List.take_left (l₁ := Word.Concat x y) (l₂ := z)).symm
        _ = List.take lenxy (Word.Concat x (Word.Concat y z)) := by
          rw [Word.concat_assoc]
        _ = List.take lenxy (Section03.anbanWord n n) := by
          rw [← hword]
    have htake : List.take lenxy (Section03.anbanWord n n) =
        Word.RepeatSymbol Section01.AB.a lenxy := by
      have hle : lenxy <= List.length (Word.RepeatSymbol Section01.AB.a n) := by
        simpa [lenxy, Word.Length, Word.Concat, Word.RepeatSymbol] using hxy
      have hleNat : lenxy <= n := by
        simpa [lenxy] using hxy
      unfold Section03.anbanWord
      change List.take lenxy
          (List.append (Word.RepeatSymbol Section01.AB.a n) suffix) =
        Word.RepeatSymbol Section01.AB.a lenxy
      have ht : List.take lenxy
          (List.append (Word.RepeatSymbol Section01.AB.a n) suffix) =
          List.take lenxy (Word.RepeatSymbol Section01.AB.a n) := by
        simpa [suffix, Word.Concat] using
          (List.take_append_of_le_length
            (l₁ := Word.RepeatSymbol Section01.AB.a n) (l₂ := suffix) hle)
      rw [ht]
      simp [Word.RepeatSymbol, Nat.min_eq_left hleNat]
    exact Eq.trans hprefix htake
  have hxRep : x = Word.RepeatSymbol Section01.AB.a lenx := by
    have htake : x = List.take lenx (Word.Concat x y) := by
      change x = List.take (List.length x) (List.append x y)
      exact (List.take_left (l₁ := x) (l₂ := y)).symm
    rw [htake, hxyRep]
    have hle : lenx <= lenxy := by
      simp [lenxy, lenx, Word.Length, Word.Concat]
    simp [Word.RepeatSymbol, Nat.min_eq_left hle]
  have hzRep : z = Word.Concat (Word.RepeatSymbol Section01.AB.a (n - lenxy)) suffix := by
    have hzDrop : z = List.drop lenxy (Section03.anbanWord n n) := by
      calc
        z = List.drop lenxy (Word.Concat (Word.Concat x y) z) := by
          change z = List.drop (List.length (Word.Concat x y))
            (List.append (Word.Concat x y) z)
          exact (List.drop_left (l₁ := Word.Concat x y) (l₂ := z)).symm
        _ = List.drop lenxy (Word.Concat x (Word.Concat y z)) := by
          rw [Word.concat_assoc]
        _ = List.drop lenxy (Section03.anbanWord n n) := by
          rw [← hword]
    rw [hzDrop]
    have hle : lenxy <= List.length (Word.RepeatSymbol Section01.AB.a n) := by
      simpa [lenxy, Word.Length, Word.Concat, Word.RepeatSymbol] using hxy
    unfold Section03.anbanWord
    change List.drop lenxy
        (List.append (Word.RepeatSymbol Section01.AB.a n) suffix) =
      Word.Concat (Word.RepeatSymbol Section01.AB.a (n - lenxy)) suffix
    have hd : List.drop lenxy
        (List.append (Word.RepeatSymbol Section01.AB.a n) suffix) =
        List.append (List.drop lenxy (Word.RepeatSymbol Section01.AB.a n)) suffix := by
      simpa [suffix, Word.Concat] using
        (List.drop_append_of_le_length
          (l₁ := Word.RepeatSymbol Section01.AB.a n) (l₂ := suffix) hle)
    rw [hd]
    simp [Word.Concat, Word.RepeatSymbol]
  rw [hxRep, hzRep]
  unfold Section03.anbanWord
  rw [← Word.concat_assoc]
  rw [repeatSymbol_concat_same]
  have harith : lenx + (n - lenxy) = n - leny := by omega
  rw [harith]

theorem anban_no_pumping_property :
    ¬ Pumping.HasPumpingProperty Section03.anbanLanguage := by
  intro hpump
  cases hpump with
  | intro n hn =>
      let w : Word Section01.AB := Section03.anbanWord n n
      have hwMem : w ∈ Section03.anbanLanguage := by
        exact Section03.anban_word_mem n
      have hwLength : n <= Word.Length w := by
        simp [w, Section03.anbanWord, Word.length_concat, Word.length_repeatSymbol,
          Word.Symbol]
      have hdec := hn.right w hwMem hwLength
      cases hdec with
      | intro x hx =>
          cases hx with
          | intro y hy =>
              cases hy with
              | intro z hz =>
                  cases hz with
                  | intro hword hrest =>
                      have hdeleted :
                          Word.Concat x z = Section03.anbanWord (n - Word.Length y) n :=
                        anbanWord_delete_initial_a hword hrest.left
                      have hpumpZero := hrest.right.right 0
                      have hmemDeleted :
                          Section03.anbanWord (n - Word.Length y) n ∈
                            Section03.anbanLanguage := by
                        rw [← hdeleted]
                        exact hpumpZero
                      have hEq := anban_members_have_equal_blocks hmemDeleted
                      have hyLe : Word.Length y <= n := by
                        have hyLeXY : Word.Length y <= Word.Length (Word.Concat x y) := by
                          simp [Word.length_concat]
                        omega
                      omega

theorem anban_not_regular_from_pumping_lemma
    (pumpingLemma : Pumping.PumpingLemmaConclusion Section03.anbanLanguage) :
    ¬ RegularLanguage.Regular Section03.anbanLanguage :=
  Pumping.not_regular_of_no_pumping_property pumpingLemma
    anban_no_pumping_property

theorem anban_not_regular :
    ¬ RegularLanguage.Regular Section03.anbanLanguage :=
  Pumping.not_regular_of_no_pumping_property_regular anban_no_pumping_property

/-!
# The {lit}`a^n b^n` Example

The final part of the section sets up and proves non-regularity for the
standard equal-block language. Counting lemmas identify how many {lit}`a` and
{lit}`b` symbols occur in block words, which is what pumping breaks.

The proof follows the same shape as the backreference language. For a proposed
pumping length {lit}`n`, choose {lit}`a^n b^n`. Any legal {lit}`y` lies inside the initial
{lit}`a` block. Pumping with {lit}`k = 0` removes at least one {lit}`a` and no {lit}`b`, so the
result has unequal symbol counts and cannot be another word of the form
{lit}`a^m b^m`.
-/

def anbnLanguage : Language Section01.AB :=
  fun w => exists n,
    w = Word.Concat (Word.RepeatSymbol Section01.AB.a n)
      (Word.RepeatSymbol Section01.AB.b n)

theorem anbn_membership (w : Word Section01.AB) :
    w ∈ anbnLanguage <->
      exists n,
        w = Word.Concat (Word.RepeatSymbol Section01.AB.a n)
          (Word.RepeatSymbol Section01.AB.b n) :=
  Iff.rfl

theorem ablock_word_count_a (aCount bCount : Nat) :
    Word.Count Section01.AB.a
      (Word.Concat (Word.RepeatSymbol Section01.AB.a aCount)
        (Word.RepeatSymbol Section01.AB.b bCount)) = aCount := by
  rw [Word.count_concat, Word.count_repeatSymbol_same]
  rw [Word.count_repeatSymbol_different]
  · omega
  · intro h
    cases h

theorem ablock_word_count_b (aCount bCount : Nat) :
    Word.Count Section01.AB.b
      (Word.Concat (Word.RepeatSymbol Section01.AB.a aCount)
        (Word.RepeatSymbol Section01.AB.b bCount)) = bCount := by
  rw [Word.count_concat, Word.count_repeatSymbol_same]
  rw [Word.count_repeatSymbol_different]
  · omega
  · intro h
    cases h

theorem anbn_word_count_a (n : Nat) :
    Word.Count Section01.AB.a
      (Word.Concat (Word.RepeatSymbol Section01.AB.a n)
        (Word.RepeatSymbol Section01.AB.b n)) = n := by
  exact ablock_word_count_a n n

theorem anbn_word_count_b (n : Nat) :
    Word.Count Section01.AB.b
      (Word.Concat (Word.RepeatSymbol Section01.AB.a n)
        (Word.RepeatSymbol Section01.AB.b n)) = n := by
  exact ablock_word_count_b n n

theorem anbn_members_have_equal_counts {w : Word Section01.AB}
    (hw : w ∈ anbnLanguage) :
    Word.Count Section01.AB.a w = Word.Count Section01.AB.b w := by
  cases hw with
  | intro n hn =>
      rw [hn, anbn_word_count_a n, anbn_word_count_b n]

theorem ab_count_a_pos_of_length_pos_count_b_zero {w : Word Section01.AB}
    (hlen : 0 < Word.Length w)
    (hb : Word.Count Section01.AB.b w = 0) :
    0 < Word.Count Section01.AB.a w := by
  cases w with
  | nil =>
      cases hlen
  | cons c rest =>
      cases c with
      | a =>
          simp [Word.Count]
          omega
      | b =>
          simp [Word.Count] at hb

theorem ablock_prefix_before_boundary_count_b_zero
    {x y z : Word Section01.AB} {aCount bCount : Nat}
    (hword :
      Word.Concat (Word.RepeatSymbol Section01.AB.a aCount)
        (Word.RepeatSymbol Section01.AB.b bCount) =
          Word.Concat x (Word.Concat y z))
    (hxy : Word.Length (Word.Concat x y) <= aCount) :
    Word.Count Section01.AB.b y = 0 := by
  have hprefix :
      Word.Concat x y =
        List.take (Word.Length (Word.Concat x y))
          (Word.Concat (Word.RepeatSymbol Section01.AB.a aCount)
            (Word.RepeatSymbol Section01.AB.b bCount)) := by
    calc
      Word.Concat x y =
          List.take (Word.Length (Word.Concat x y))
            (Word.Concat (Word.Concat x y) z) := by
            change Word.Concat x y =
              List.take (List.length (Word.Concat x y))
                (List.append (Word.Concat x y) z)
            have htleft :
                List.take (List.length (Word.Concat x y))
                  (List.append (Word.Concat x y) z) = Word.Concat x y := by
              simpa [Word.Concat] using
                (List.take_left (l₁ := Word.Concat x y) (l₂ := z))
            exact htleft.symm
      _ = List.take (Word.Length (Word.Concat x y))
          (Word.Concat x (Word.Concat y z)) := by
            rw [Word.concat_assoc]
      _ = List.take (Word.Length (Word.Concat x y))
          (Word.Concat (Word.RepeatSymbol Section01.AB.a aCount)
            (Word.RepeatSymbol Section01.AB.b bCount)) := by
            rw [← hword]
  have htake :
      List.take (Word.Length (Word.Concat x y))
        (Word.Concat (Word.RepeatSymbol Section01.AB.a aCount)
          (Word.RepeatSymbol Section01.AB.b bCount)) =
        Word.RepeatSymbol Section01.AB.a (Word.Length (Word.Concat x y)) := by
    have hxy' :
        List.length (Word.Concat x y) <=
          List.length (Word.RepeatSymbol Section01.AB.a aCount) := by
      simpa [Word.Length, Word.Concat, Word.RepeatSymbol] using hxy
    have hxyNat : List.length (Word.Concat x y) <= aCount := by
      simpa [Word.Length, Word.Concat] using hxy
    change List.take (List.length (Word.Concat x y))
        (List.append (Word.RepeatSymbol Section01.AB.a aCount)
          (Word.RepeatSymbol Section01.AB.b bCount)) =
      Word.RepeatSymbol Section01.AB.a (List.length (Word.Concat x y))
    have ht :
        List.take (List.length (Word.Concat x y))
          (List.append (Word.RepeatSymbol Section01.AB.a aCount)
            (Word.RepeatSymbol Section01.AB.b bCount)) =
          List.take (List.length (Word.Concat x y))
            (Word.RepeatSymbol Section01.AB.a aCount) := by
      simpa [Word.Concat] using
        (List.take_append_of_le_length
          (l₁ := Word.RepeatSymbol Section01.AB.a aCount)
          (l₂ := Word.RepeatSymbol Section01.AB.b bCount) hxy')
    rw [ht]
    simp [Word.RepeatSymbol, Nat.min_eq_left hxyNat]
  have hxyRep :
      Word.Concat x y =
        Word.RepeatSymbol Section01.AB.a (Word.Length (Word.Concat x y)) := by
    exact Eq.trans hprefix htake
  have hbxy : Word.Count Section01.AB.b (Word.Concat x y) = 0 := by
    rw [hxyRep]
    exact Word.count_repeatSymbol_different (by intro h; cases h)
      (Word.Length (Word.Concat x y))
  rw [Word.count_concat] at hbxy
  omega

theorem anbn_prefix_before_boundary_count_b_zero
    {x y z : Word Section01.AB} {n : Nat}
    (hword :
      Word.Concat (Word.RepeatSymbol Section01.AB.a n)
        (Word.RepeatSymbol Section01.AB.b n) =
          Word.Concat x (Word.Concat y z))
    (hxy : Word.Length (Word.Concat x y) <= n) :
    Word.Count Section01.AB.b y = 0 :=
  ablock_prefix_before_boundary_count_b_zero hword hxy

theorem anbn_pump_zero_unequal_counts
    {x y z : Word Section01.AB} {n : Nat}
    (hword :
      Word.Concat (Word.RepeatSymbol Section01.AB.a n)
        (Word.RepeatSymbol Section01.AB.b n) =
          Word.Concat x (Word.Concat y z))
    (hxy : Word.Length (Word.Concat x y) <= n)
    (hy : Word.Length y > 0) :
    Word.Count Section01.AB.a (Word.Concat x z) ≠
      Word.Count Section01.AB.b (Word.Concat x z) := by
  intro hcountsZero
  have hbY :
      Word.Count Section01.AB.b y = 0 :=
    anbn_prefix_before_boundary_count_b_zero hword hxy
  have haYPos :
      0 < Word.Count Section01.AB.a y :=
    ab_count_a_pos_of_length_pos_count_b_zero hy hbY
  have hcountAOriginal :
      Word.Count Section01.AB.a
        (Word.Concat x (Word.Concat y z)) = n := by
    rw [← hword]
    exact anbn_word_count_a n
  have hcountBOriginal :
      Word.Count Section01.AB.b
        (Word.Concat x (Word.Concat y z)) = n := by
    rw [← hword]
    exact anbn_word_count_b n
  rw [Word.count_concat, Word.count_concat] at hcountAOriginal
  rw [Word.count_concat, Word.count_concat] at hcountBOriginal
  rw [Word.count_concat, Word.count_concat] at hcountsZero
  omega

theorem anbn_no_pumping_property :
    ¬ Pumping.HasPumpingProperty anbnLanguage := by
  intro hpump
  cases hpump with
  | intro n hn =>
      let w : Word Section01.AB :=
        Word.Concat (Word.RepeatSymbol Section01.AB.a n)
          (Word.RepeatSymbol Section01.AB.b n)
      have hwMem : w ∈ anbnLanguage := by
        exists n
      have hwLength : n <= Word.Length w := by
        simp [w, Word.length_concat, Word.length_repeatSymbol]
      have hdec := hn.right w hwMem hwLength
      cases hdec with
      | intro x hx =>
          cases hx with
          | intro y hy =>
              cases hy with
              | intro z hz =>
                  cases hz with
                  | intro hword hrest =>
                      have hunequal :
                          Word.Count Section01.AB.a (Word.Concat x z) ≠
                            Word.Count Section01.AB.b (Word.Concat x z) :=
                        anbn_pump_zero_unequal_counts hword hrest.left
                          hrest.right.left
                      have hpumpZero := hrest.right.right 0
                      have hcountsZero :=
                        anbn_members_have_equal_counts hpumpZero
                      have hcountsZero' :
                        Word.Count Section01.AB.a (Word.Concat x z) =
                          Word.Count Section01.AB.b (Word.Concat x z) := by
                        simpa [Word.RepeatWord, Word.Concat] using hcountsZero
                      exact hunequal hcountsZero'

/-!
# Equal Counts Without Block Order

The language of all words with equally many {lit}`a` and {lit}`b` symbols is also
non-regular. The same bad word {lit}`a^n b^n` works: deleting a pumped piece from
the initial {lit}`a` block destroys equality of counts, even though this language
does not require all {lit}`a`s to come before all {lit}`b`s.
-/

def equalCountLanguage : Language Section01.AB :=
  fun w => Word.Count Section01.AB.a w = Word.Count Section01.AB.b w

theorem equal_count_language_membership (w : Word Section01.AB) :
    w ∈ equalCountLanguage <->
      Word.Count Section01.AB.a w = Word.Count Section01.AB.b w :=
  Iff.rfl

theorem equal_count_no_pumping_property :
    ¬ Pumping.HasPumpingProperty equalCountLanguage := by
  intro hpump
  cases hpump with
  | intro n hn =>
      let w : Word Section01.AB :=
        Word.Concat (Word.RepeatSymbol Section01.AB.a n)
          (Word.RepeatSymbol Section01.AB.b n)
      have hwMem : w ∈ equalCountLanguage := by
        change
          Word.Count Section01.AB.a
            (Word.Concat (Word.RepeatSymbol Section01.AB.a n)
              (Word.RepeatSymbol Section01.AB.b n)) =
            Word.Count Section01.AB.b
              (Word.Concat (Word.RepeatSymbol Section01.AB.a n)
                (Word.RepeatSymbol Section01.AB.b n))
        rw [anbn_word_count_a n, anbn_word_count_b n]
      have hwLength : n <= Word.Length w := by
        simp [w, Word.length_concat, Word.length_repeatSymbol]
      have hdec := hn.right w hwMem hwLength
      cases hdec with
      | intro x hx =>
          cases hx with
          | intro y hy =>
              cases hy with
              | intro z hz =>
                  cases hz with
                  | intro hword hrest =>
                      have hunequal :
                          Word.Count Section01.AB.a (Word.Concat x z) ≠
                            Word.Count Section01.AB.b (Word.Concat x z) :=
                        anbn_pump_zero_unequal_counts hword hrest.left
                          hrest.right.left
                      have hpumpZero := hrest.right.right 0
                      have hcountsZero :
                          Word.Count Section01.AB.a (Word.Concat x z) =
                            Word.Count Section01.AB.b (Word.Concat x z) := by
                        simpa [equalCountLanguage, Word.RepeatWord, Word.Concat]
                          using hpumpZero
                      exact hunequal hcountsZero

theorem equal_count_not_regular_from_pumping_lemma
    (pumpingLemma : Pumping.PumpingLemmaConclusion equalCountLanguage) :
    ¬ RegularLanguage.Regular equalCountLanguage :=
  Pumping.not_regular_of_no_pumping_property pumpingLemma
    equal_count_no_pumping_property

theorem equal_count_not_regular :
    ¬ RegularLanguage.Regular equalCountLanguage :=
  Pumping.not_regular_of_no_pumping_property_regular equal_count_no_pumping_property

/-!
# The {lit}`x x` Language

The language `{ x x | x in {a,b}* }` contains duplicated words. The bad family
uses words of the form `(a^n b)(a^n b)`. Pumping near the front changes only
the first {lit}`a` block. The supporting lemmas prove that a word with two {lit}`b`s of
this shape is a square only when the two {lit}`a` blocks have equal length.
-/

def squareBlockWord (p q : Nat) : Word Section01.AB :=
  Word.Concat (Word.RepeatSymbol Section01.AB.a p)
    (Word.Concat (Word.Symbol Section01.AB.b)
      (Word.Concat (Word.RepeatSymbol Section01.AB.a q) (Word.Symbol Section01.AB.b)))

def squareLanguage : Language Section01.AB :=
  fun w => exists u, w = Word.Concat u u

theorem square_language_membership (w : Word Section01.AB) :
    w ∈ squareLanguage <-> exists u, w = Word.Concat u u :=
  Iff.rfl

theorem squareBlock_count_b (p q : Nat) :
    Word.Count Section01.AB.b (squareBlockWord p q) = 2 := by
  unfold squareBlockWord
  rw [Word.count_concat, Word.count_concat, Word.count_concat]
  rw [Word.count_repeatSymbol_different, Word.count_repeatSymbol_different]
  · simp [Word.Count, Word.Symbol]
  · intro h
    cases h
  · intro h
    cases h

theorem squareBlock_length (p q : Nat) :
    Word.Length (squareBlockWord p q) = p + q + 2 := by
  unfold squareBlockWord
  simp [Word.Length, Word.Concat, Word.RepeatSymbol, Word.Symbol]
  omega

theorem squareBlock_take_before_first_b_count_b {p q l : Nat}
    (hl : l <= p) :
    Word.Count Section01.AB.b (List.take l (squareBlockWord p q)) = 0 := by
  unfold squareBlockWord
  have hle : l <= List.length (Word.RepeatSymbol Section01.AB.a p) := by
    simpa [Word.RepeatSymbol] using hl
  have ht : List.take l
      (List.append (Word.RepeatSymbol Section01.AB.a p)
        (Word.Concat (Word.Symbol Section01.AB.b)
          (Word.Concat (Word.RepeatSymbol Section01.AB.a q) (Word.Symbol Section01.AB.b)))) =
      List.take l (Word.RepeatSymbol Section01.AB.a p) := by
    simpa [Word.Concat] using
      (List.take_append_of_le_length
        (l₁ := Word.RepeatSymbol Section01.AB.a p)
        (l₂ := Word.Concat (Word.Symbol Section01.AB.b)
          (Word.Concat (Word.RepeatSymbol Section01.AB.a q) (Word.Symbol Section01.AB.b))) hle)
  change Word.Count Section01.AB.b
      (List.take l
        (List.append (Word.RepeatSymbol Section01.AB.a p)
          (Word.Concat (Word.Symbol Section01.AB.b)
            (Word.Concat (Word.RepeatSymbol Section01.AB.a q) (Word.Symbol Section01.AB.b))))) = 0
  rw [ht]
  have hmin : min l p = l := by omega
  rw [show List.take l (Word.RepeatSymbol Section01.AB.a p) =
      Word.RepeatSymbol Section01.AB.a l by
    simp [Word.RepeatSymbol, hmin]]
  exact Word.count_repeatSymbol_different (by intro h; cases h) l

theorem squareBlock_take_middle {p q l : Nat}
    (hp : p < l) (hl : l <= p + q + 1) :
    List.take l (squareBlockWord p q) =
      Word.Concat (Word.RepeatSymbol Section01.AB.a p)
        (Word.Concat (Word.Symbol Section01.AB.b)
          (Word.RepeatSymbol Section01.AB.a (l - p - 1))) := by
  unfold squareBlockWord
  simp [Word.Concat, Word.RepeatSymbol, Word.Symbol, List.take_append, List.take_replicate]
  have hmin1 : min l p = p := by omega
  rw [hmin1]
  have hpos : l - p = (l - p - 1) + 1 := by omega
  rw [hpos]
  simp [List.take_append, List.take_replicate]
  have hmin2 : min (l - p - 1) q = l - p - 1 := by omega
  rw [hmin2]
  have hzero : l - p - 1 - q = 0 := by omega
  rw [hzero]
  simp

theorem squareBlock_drop_middle {p q l : Nat}
    (hp : p < l) (hl : l <= p + q + 1) :
    List.drop l (squareBlockWord p q) =
      Word.Concat (Word.RepeatSymbol Section01.AB.a (p + q + 1 - l))
        (Word.Symbol Section01.AB.b) := by
  unfold squareBlockWord
  simp [Word.Concat, Word.RepeatSymbol, Word.Symbol, List.drop_append, List.drop_replicate]
  have hpzero : p - l = 0 := by omega
  rw [hpzero]
  have hdropP : l - p = (l - p - 1) + 1 := by omega
  rw [hdropP]
  simp [List.drop_append, List.drop_replicate]
  have harith : q - (l - p - 1) = p + q + 1 - l := by omega
  rw [harith]
  have hzero : l - p - 1 - q = 0 := by omega
  rw [hzero]
  simp

theorem single_b_block_eq_trailing_b {p r s : Nat}
    (h : Word.Concat (Word.RepeatSymbol Section01.AB.a p)
        (Word.Concat (Word.Symbol Section01.AB.b)
          (Word.RepeatSymbol Section01.AB.a r)) =
      Word.Concat (Word.RepeatSymbol Section01.AB.a s) (Word.Symbol Section01.AB.b)) :
    p = s ∧ r = 0 := by
  induction p generalizing r s with
  | zero =>
      cases s with
      | zero =>
          constructor
          · rfl
          · cases r with
            | zero => rfl
            | succ _ =>
                simp [Word.Concat, Word.RepeatSymbol, Word.Symbol, List.replicate_succ] at h
                cases h
      | succ _ =>
          simp [Word.Concat, Word.RepeatSymbol, Word.Symbol, List.replicate_succ] at h
          cases h
  | succ p ih =>
      cases s with
      | zero =>
          simp [Word.Concat, Word.RepeatSymbol, Word.Symbol, List.replicate_succ] at h
          cases h
      | succ s =>
          simp [Word.Concat, Word.RepeatSymbol, Word.Symbol, List.replicate_succ] at h
          injection h with _ htail
          have htail' :
              Word.Concat (Word.RepeatSymbol Section01.AB.a p)
                  (Word.Concat (Word.Symbol Section01.AB.b)
                    (Word.RepeatSymbol Section01.AB.a r)) =
                Word.Concat (Word.RepeatSymbol Section01.AB.a s) (Word.Symbol Section01.AB.b) := by
            simpa [Word.Concat, Word.RepeatSymbol, Word.Symbol] using htail
          cases ih htail' with
          | intro hps hr =>
              constructor
              · omega
              · exact hr

theorem square_block_members_have_equal_a_blocks {u : Word Section01.AB}
    {p q : Nat}
    (h : Word.Concat u u = squareBlockWord p q) :
    p = q := by
  let l := Word.Length u
  have huPrefix : u = List.take l (squareBlockWord p q) := by
    calc
      u = List.take l (Word.Concat u u) := by
        change u = List.take (List.length u) (List.append u u)
        exact (List.take_left (l₁ := u) (l₂ := u)).symm
      _ = List.take l (squareBlockWord p q) := by rw [h]
  have huSuffix : u = List.drop l (squareBlockWord p q) := by
    calc
      u = List.drop l (Word.Concat u u) := by
        change u = List.drop (List.length u) (List.append u u)
        exact (List.drop_left (l₁ := u) (l₂ := u)).symm
      _ = List.drop l (squareBlockWord p q) := by rw [h]
  have hcount : Word.Count Section01.AB.b u = 1 := by
    have hc := congrArg (Word.Count Section01.AB.b) h
    rw [Word.count_concat, squareBlock_count_b p q] at hc
    omega
  have hlen : p + q + 2 = 2 * l := by
    have hl := congrArg Word.Length h
    rw [Word.length_concat, squareBlock_length p q] at hl
    omega
  have hlpos : 0 < l := by
    cases u with
    | nil =>
        simp [Word.Count] at hcount
    | cons _ _ =>
        simp [l, Word.Length]
  have hp : p < l := by
    by_cases hplt : p < l
    · exact hplt
    · have hle : l <= p := by omega
      have hczero : Word.Count Section01.AB.b u = 0 := by
        rw [huPrefix]
        exact squareBlock_take_before_first_b_count_b hle
      omega
  have hlmid : l <= p + q + 1 := by omega
  have hshape :
      Word.Concat (Word.RepeatSymbol Section01.AB.a p)
          (Word.Concat (Word.Symbol Section01.AB.b)
            (Word.RepeatSymbol Section01.AB.a (l - p - 1))) =
        Word.Concat (Word.RepeatSymbol Section01.AB.a (p + q + 1 - l))
          (Word.Symbol Section01.AB.b) := by
    rw [← squareBlock_take_middle hp hlmid]
    rw [← squareBlock_drop_middle hp hlmid]
    rw [← huPrefix, ← huSuffix]
  cases single_b_block_eq_trailing_b hshape with
  | intro _ _ =>
      omega

theorem squareBlock_delete_initial_a
    {x y z : Word Section01.AB} {n : Nat}
    (hword : squareBlockWord n n = Word.Concat x (Word.Concat y z))
    (hxy : Word.Length (Word.Concat x y) <= n) :
    Word.Concat x z = squareBlockWord (n - Word.Length y) n := by
  let lenx := Word.Length x
  let leny := Word.Length y
  let lenxy := Word.Length (Word.Concat x y)
  have hlenxy : lenxy = lenx + leny := by
    simp [lenxy, lenx, leny, Word.length_concat]
  let suffix : Word Section01.AB :=
    Word.Concat (Word.Symbol Section01.AB.b)
      (Word.Concat (Word.RepeatSymbol Section01.AB.a n) (Word.Symbol Section01.AB.b))
  have hxyRep : Word.Concat x y = Word.RepeatSymbol Section01.AB.a lenxy := by
    have hprefix :
        Word.Concat x y = List.take lenxy (squareBlockWord n n) := by
      calc
        Word.Concat x y = List.take lenxy (Word.Concat (Word.Concat x y) z) := by
          change Word.Concat x y = List.take (List.length (Word.Concat x y))
            (List.append (Word.Concat x y) z)
          exact (List.take_left (l₁ := Word.Concat x y) (l₂ := z)).symm
        _ = List.take lenxy (Word.Concat x (Word.Concat y z)) := by
          rw [Word.concat_assoc]
        _ = List.take lenxy (squareBlockWord n n) := by
          rw [← hword]
    have htake : List.take lenxy (squareBlockWord n n) =
        Word.RepeatSymbol Section01.AB.a lenxy := by
      have hle : lenxy <= List.length (Word.RepeatSymbol Section01.AB.a n) := by
        simpa [lenxy, Word.Length, Word.Concat, Word.RepeatSymbol] using hxy
      have hleNat : lenxy <= n := by
        simpa [lenxy] using hxy
      unfold squareBlockWord
      change List.take lenxy
          (List.append (Word.RepeatSymbol Section01.AB.a n) suffix) =
        Word.RepeatSymbol Section01.AB.a lenxy
      have ht : List.take lenxy
          (List.append (Word.RepeatSymbol Section01.AB.a n) suffix) =
          List.take lenxy (Word.RepeatSymbol Section01.AB.a n) := by
        simpa [suffix, Word.Concat] using
          (List.take_append_of_le_length
            (l₁ := Word.RepeatSymbol Section01.AB.a n) (l₂ := suffix) hle)
      rw [ht]
      simp [Word.RepeatSymbol, Nat.min_eq_left hleNat]
    exact Eq.trans hprefix htake
  have hxRep : x = Word.RepeatSymbol Section01.AB.a lenx := by
    have htake : x = List.take lenx (Word.Concat x y) := by
      change x = List.take (List.length x) (List.append x y)
      exact (List.take_left (l₁ := x) (l₂ := y)).symm
    rw [htake, hxyRep]
    have hle : lenx <= lenxy := by
      simp [lenxy, lenx, Word.Length, Word.Concat]
    simp [Word.RepeatSymbol, Nat.min_eq_left hle]
  have hzRep : z = Word.Concat (Word.RepeatSymbol Section01.AB.a (n - lenxy)) suffix := by
    have hzDrop : z = List.drop lenxy (squareBlockWord n n) := by
      calc
        z = List.drop lenxy (Word.Concat (Word.Concat x y) z) := by
          change z = List.drop (List.length (Word.Concat x y))
            (List.append (Word.Concat x y) z)
          exact (List.drop_left (l₁ := Word.Concat x y) (l₂ := z)).symm
        _ = List.drop lenxy (Word.Concat x (Word.Concat y z)) := by
          rw [Word.concat_assoc]
        _ = List.drop lenxy (squareBlockWord n n) := by
          rw [← hword]
    rw [hzDrop]
    have hle : lenxy <= List.length (Word.RepeatSymbol Section01.AB.a n) := by
      simpa [lenxy, Word.Length, Word.Concat, Word.RepeatSymbol] using hxy
    unfold squareBlockWord
    change List.drop lenxy
        (List.append (Word.RepeatSymbol Section01.AB.a n) suffix) =
      Word.Concat (Word.RepeatSymbol Section01.AB.a (n - lenxy)) suffix
    have hd : List.drop lenxy
        (List.append (Word.RepeatSymbol Section01.AB.a n) suffix) =
        List.append (List.drop lenxy (Word.RepeatSymbol Section01.AB.a n)) suffix := by
      simpa [suffix, Word.Concat] using
        (List.drop_append_of_le_length
          (l₁ := Word.RepeatSymbol Section01.AB.a n) (l₂ := suffix) hle)
    rw [hd]
    simp [Word.Concat, Word.RepeatSymbol]
  rw [hxRep, hzRep]
  unfold squareBlockWord
  rw [← Word.concat_assoc]
  rw [repeatSymbol_concat_same]
  have harith : lenx + (n - lenxy) = n - leny := by omega
  rw [harith]

theorem square_no_pumping_property :
    ¬ Pumping.HasPumpingProperty squareLanguage := by
  intro hpump
  cases hpump with
  | intro n hn =>
      let half : Word Section01.AB :=
        Word.Concat (Word.RepeatSymbol Section01.AB.a n) (Word.Symbol Section01.AB.b)
      let w : Word Section01.AB := squareBlockWord n n
      have hwMem : w ∈ squareLanguage := by
        exists half
        change squareBlockWord n n = Word.Concat half half
        unfold half squareBlockWord Word.Concat Word.Symbol Word.RepeatSymbol
        simp [List.append_assoc]
      have hwLength : n <= Word.Length w := by
        simp [w, squareBlock_length]
        omega
      have hdec := hn.right w hwMem hwLength
      cases hdec with
      | intro x hx =>
          cases hx with
          | intro y hy =>
              cases hy with
              | intro z hz =>
                  cases hz with
                  | intro hword hrest =>
                      have hdeleted :
                          Word.Concat x z = squareBlockWord (n - Word.Length y) n :=
                        squareBlock_delete_initial_a hword hrest.left
                      have hpumpZero := hrest.right.right 0
                      cases hpumpZero with
                      | intro u hu =>
                          have hsquare :
                              Word.Concat u u = squareBlockWord (n - Word.Length y) n := by
                            rw [← hu]
                            exact hdeleted
                          have hEq := square_block_members_have_equal_a_blocks hsquare
                          have hyLe : Word.Length y <= n := by
                            have hyLeXY : Word.Length y <= Word.Length (Word.Concat x y) := by
                              simp [Word.length_concat]
                            omega
                          omega

theorem square_not_regular_from_pumping_lemma
    (pumpingLemma : Pumping.PumpingLemmaConclusion squareLanguage) :
    ¬ RegularLanguage.Regular squareLanguage :=
  Pumping.not_regular_of_no_pumping_property pumpingLemma
    square_no_pumping_property

theorem square_not_regular :
    ¬ RegularLanguage.Regular squareLanguage :=
  Pumping.not_regular_of_no_pumping_property_regular square_no_pumping_property

/-!
# The {lit}`x x^R` Language

The language `{ x reverse(x) | x in {a,b}* }` is handled by a mirror-image
variant of the square argument. The bad word is {lit}`a^n b b a^n`; deleting a
pumped piece from the first {lit}`a` block breaks the symmetry around the two
central {lit}`b` symbols.
-/

def doubleBWord : Word Section01.AB :=
  Word.Concat (Word.Symbol Section01.AB.b) (Word.Symbol Section01.AB.b)

def mirrorBlockWord (p q : Nat) : Word Section01.AB :=
  Word.Concat (Word.RepeatSymbol Section01.AB.a p)
    (Word.Concat doubleBWord (Word.RepeatSymbol Section01.AB.a q))

def reverseSquareLanguage : Language Section01.AB :=
  fun w => exists u, w = Word.Concat u (Word.Reverse u)

theorem reverse_square_language_membership (w : Word Section01.AB) :
    w ∈ reverseSquareLanguage <-> exists u, w = Word.Concat u (Word.Reverse u) :=
  Iff.rfl

theorem mirrorBlock_succ_succ (p q : Nat) :
    mirrorBlockWord (p + 1) (q + 1) =
      Section01.AB.a :: Word.Concat (mirrorBlockWord p q) (Word.Symbol Section01.AB.a) := by
  unfold mirrorBlockWord doubleBWord Word.Concat Word.RepeatSymbol Word.Symbol
  rw [List.replicate_succ]
  rw [List.replicate_succ']
  simp [List.append_assoc]

theorem mirrorBlock_succ_zero (p : Nat) :
    mirrorBlockWord (p + 1) 0 =
      Section01.AB.a :: Word.Concat
        (Word.Concat (Word.RepeatSymbol Section01.AB.a p) (Word.Symbol Section01.AB.b))
        (Word.Symbol Section01.AB.b) := by
  unfold mirrorBlockWord doubleBWord Word.Concat Word.RepeatSymbol Word.Symbol
  rw [List.replicate_succ]
  simp [List.append_assoc]

theorem mirrorBlock_zero_succ (q : Nat) :
    mirrorBlockWord 0 (q + 1) =
      Section01.AB.b :: Word.Concat
        (Word.Concat (Word.Symbol Section01.AB.b) (Word.RepeatSymbol Section01.AB.a q))
        (Word.Symbol Section01.AB.a) := by
  unfold mirrorBlockWord doubleBWord Word.Concat Word.RepeatSymbol Word.Symbol
  rw [List.replicate_succ']
  simp

theorem mirror_strip_a {u middle : Word Section01.AB}
    (h : Word.Concat u (Word.Reverse u) =
      Section01.AB.a :: Word.Concat middle (Word.Symbol Section01.AB.a)) :
    exists v, u = Section01.AB.a :: v ∧
      Word.Concat v (Word.Reverse v) = middle := by
  cases u with
  | nil =>
      simp [Word.Concat, Word.Reverse, Word.Symbol] at h
  | cons c v =>
      cases c with
      | a =>
          exists v
          constructor
          · rfl
          · simp [Word.Concat, Word.Reverse, Word.Symbol, List.reverse_cons] at h
            injection h with _ htail
            rw [← List.append_assoc] at htail
            exact List.append_cancel_right htail
      | b =>
          cases h

theorem mirror_not_a_to_b {u middle : Word Section01.AB} :
    Word.Concat u (Word.Reverse u) ≠
      Section01.AB.a :: Word.Concat middle (Word.Symbol Section01.AB.b) := by
  intro h
  cases u with
  | nil =>
      simp [Word.Concat, Word.Reverse, Word.Symbol] at h
  | cons c v =>
      cases c with
      | a =>
          simp [Word.Concat, Word.Reverse, Word.Symbol, List.reverse_cons] at h
          injection h with _ htail
          have hrev := congrArg List.reverse htail
          simp [List.reverse_append] at hrev
      | b =>
          cases h

theorem mirror_not_b_to_a {u middle : Word Section01.AB} :
    Word.Concat u (Word.Reverse u) ≠
      Section01.AB.b :: Word.Concat middle (Word.Symbol Section01.AB.a) := by
  intro h
  cases u with
  | nil =>
      simp [Word.Concat, Word.Reverse, Word.Symbol] at h
  | cons c v =>
      cases c with
      | a =>
          cases h
      | b =>
          simp [Word.Concat, Word.Reverse, Word.Symbol, List.reverse_cons] at h
          injection h with _ htail
          have hrev := congrArg List.reverse htail
          simp [List.reverse_append] at hrev

theorem mirror_block_members_have_equal_a_blocks {u : Word Section01.AB}
    {p q : Nat}
    (h : Word.Concat u (Word.Reverse u) = mirrorBlockWord p q) :
    p = q := by
  induction p generalizing q u with
  | zero =>
      cases q with
      | zero => rfl
      | succ q =>
          exfalso
          rw [mirrorBlock_zero_succ q] at h
          exact mirror_not_b_to_a h
  | succ p ih =>
      cases q with
      | zero =>
          exfalso
          rw [mirrorBlock_succ_zero p] at h
          exact mirror_not_a_to_b h
      | succ q =>
          rw [mirrorBlock_succ_succ p q] at h
          cases mirror_strip_a h with
          | intro _ hv =>
              have hpq := ih hv.right
              omega

theorem mirrorBlock_delete_initial_a
    {x y z : Word Section01.AB} {n : Nat}
    (hword : mirrorBlockWord n n = Word.Concat x (Word.Concat y z))
    (hxy : Word.Length (Word.Concat x y) <= n) :
    Word.Concat x z = mirrorBlockWord (n - Word.Length y) n := by
  let lenx := Word.Length x
  let leny := Word.Length y
  let lenxy := Word.Length (Word.Concat x y)
  have hlenxy : lenxy = lenx + leny := by
    simp [lenxy, lenx, leny, Word.length_concat]
  have hxyRep : Word.Concat x y = Word.RepeatSymbol Section01.AB.a lenxy := by
    have hprefix :
        Word.Concat x y = List.take lenxy (mirrorBlockWord n n) := by
      calc
        Word.Concat x y = List.take lenxy (Word.Concat (Word.Concat x y) z) := by
          change Word.Concat x y = List.take (List.length (Word.Concat x y))
            (List.append (Word.Concat x y) z)
          exact (List.take_left (l₁ := Word.Concat x y) (l₂ := z)).symm
        _ = List.take lenxy (Word.Concat x (Word.Concat y z)) := by
          rw [Word.concat_assoc]
        _ = List.take lenxy (mirrorBlockWord n n) := by
          rw [← hword]
    have htake : List.take lenxy (mirrorBlockWord n n) =
        Word.RepeatSymbol Section01.AB.a lenxy := by
      have hle : lenxy <= List.length (Word.RepeatSymbol Section01.AB.a n) := by
        simpa [lenxy, Word.Length, Word.Concat, Word.RepeatSymbol] using hxy
      have hleNat : lenxy <= n := by
        simpa [lenxy] using hxy
      unfold mirrorBlockWord
      change List.take lenxy
          (List.append (Word.RepeatSymbol Section01.AB.a n)
            (Word.Concat doubleBWord (Word.RepeatSymbol Section01.AB.a n))) =
        Word.RepeatSymbol Section01.AB.a lenxy
      have ht : List.take lenxy
          (List.append (Word.RepeatSymbol Section01.AB.a n)
            (Word.Concat doubleBWord (Word.RepeatSymbol Section01.AB.a n))) =
          List.take lenxy (Word.RepeatSymbol Section01.AB.a n) := by
        simpa [Word.Concat] using
          (List.take_append_of_le_length
            (l₁ := Word.RepeatSymbol Section01.AB.a n)
            (l₂ := Word.Concat doubleBWord (Word.RepeatSymbol Section01.AB.a n)) hle)
      rw [ht]
      simp [Word.RepeatSymbol, Nat.min_eq_left hleNat]
    exact Eq.trans hprefix htake
  have hxRep : x = Word.RepeatSymbol Section01.AB.a lenx := by
    have htake : x = List.take lenx (Word.Concat x y) := by
      change x = List.take (List.length x) (List.append x y)
      exact (List.take_left (l₁ := x) (l₂ := y)).symm
    rw [htake, hxyRep]
    have hle : lenx <= lenxy := by
      simp [lenxy, lenx, Word.Length, Word.Concat]
    simp [Word.RepeatSymbol, Nat.min_eq_left hle]
  have hzRep : z = Word.Concat (Word.RepeatSymbol Section01.AB.a (n - lenxy))
      (Word.Concat doubleBWord (Word.RepeatSymbol Section01.AB.a n)) := by
    have hzDrop : z = List.drop lenxy (mirrorBlockWord n n) := by
      calc
        z = List.drop lenxy (Word.Concat (Word.Concat x y) z) := by
          change z = List.drop (List.length (Word.Concat x y))
            (List.append (Word.Concat x y) z)
          exact (List.drop_left (l₁ := Word.Concat x y) (l₂ := z)).symm
        _ = List.drop lenxy (Word.Concat x (Word.Concat y z)) := by
          rw [Word.concat_assoc]
        _ = List.drop lenxy (mirrorBlockWord n n) := by
          rw [← hword]
    rw [hzDrop]
    have hle : lenxy <= List.length (Word.RepeatSymbol Section01.AB.a n) := by
      simpa [lenxy, Word.Length, Word.Concat, Word.RepeatSymbol] using hxy
    unfold mirrorBlockWord
    change List.drop lenxy
        (List.append (Word.RepeatSymbol Section01.AB.a n)
          (Word.Concat doubleBWord (Word.RepeatSymbol Section01.AB.a n))) =
      Word.Concat (Word.RepeatSymbol Section01.AB.a (n - lenxy))
        (Word.Concat doubleBWord (Word.RepeatSymbol Section01.AB.a n))
    have hd : List.drop lenxy
        (List.append (Word.RepeatSymbol Section01.AB.a n)
          (Word.Concat doubleBWord (Word.RepeatSymbol Section01.AB.a n))) =
        List.append (List.drop lenxy (Word.RepeatSymbol Section01.AB.a n))
          (Word.Concat doubleBWord (Word.RepeatSymbol Section01.AB.a n)) := by
      simpa [Word.Concat] using
        (List.drop_append_of_le_length
          (l₁ := Word.RepeatSymbol Section01.AB.a n)
          (l₂ := Word.Concat doubleBWord (Word.RepeatSymbol Section01.AB.a n)) hle)
    rw [hd]
    simp [Word.Concat, Word.RepeatSymbol]
  rw [hxRep, hzRep]
  unfold mirrorBlockWord
  rw [← Word.concat_assoc]
  rw [repeatSymbol_concat_same]
  have harith : lenx + (n - lenxy) = n - leny := by
    omega
  rw [harith]

theorem reverse_square_no_pumping_property :
    ¬ Pumping.HasPumpingProperty reverseSquareLanguage := by
  intro hpump
  cases hpump with
  | intro n hn =>
      let half : Word Section01.AB :=
        Word.Concat (Word.RepeatSymbol Section01.AB.a n) (Word.Symbol Section01.AB.b)
      let w : Word Section01.AB := mirrorBlockWord n n
      have hwMem : w ∈ reverseSquareLanguage := by
        exists half
        change mirrorBlockWord n n = Word.Concat half (Word.Reverse half)
        unfold half mirrorBlockWord doubleBWord Word.Concat Word.Reverse Word.Symbol Word.RepeatSymbol
        simp [List.reverse_append, List.reverse_replicate, List.append_assoc]
      have hwLength : n <= Word.Length w := by
        simp [w, mirrorBlockWord, doubleBWord, Word.length_concat, Word.length_repeatSymbol,
          Word.Symbol]
      have hdec := hn.right w hwMem hwLength
      cases hdec with
      | intro x hx =>
          cases hx with
          | intro y hy =>
              cases hy with
              | intro z hz =>
                  cases hz with
                  | intro hword hrest =>
                      have hdeleted :
                          Word.Concat x z = mirrorBlockWord (n - Word.Length y) n :=
                        mirrorBlock_delete_initial_a hword hrest.left
                      have hpumpZero := hrest.right.right 0
                      cases hpumpZero with
                      | intro u hu =>
                          have hmirror :
                              Word.Concat u (Word.Reverse u) =
                                mirrorBlockWord (n - Word.Length y) n := by
                            rw [← hu]
                            exact hdeleted
                          have hEq := mirror_block_members_have_equal_a_blocks hmirror
                          have hyLe : Word.Length y <= n := by
                            have hyLeXY : Word.Length y <= Word.Length (Word.Concat x y) := by
                              simp [Word.length_concat]
                            omega
                          omega

theorem reverse_square_not_regular_from_pumping_lemma
    (pumpingLemma : Pumping.PumpingLemmaConclusion reverseSquareLanguage) :
    ¬ RegularLanguage.Regular reverseSquareLanguage :=
  Pumping.not_regular_of_no_pumping_property pumpingLemma
    reverse_square_no_pumping_property

theorem reverse_square_not_regular :
    ¬ RegularLanguage.Regular reverseSquareLanguage :=
  Pumping.not_regular_of_no_pumping_property_regular reverse_square_no_pumping_property

/-!
# More {lit}`b`s Than {lit}`a`s in Blocks

For the block language `{ a^n b^m | n < m }`, the bad word is {lit}`a^n b^(n+1)`.
This time pumping with {lit}`k = 2` duplicates some initial {lit}`a`s. The result has at
least as many {lit}`a`s as {lit}`b`s, so it cannot remain in the language.
-/

def moreBsBlockLanguage : Language Section01.AB :=
  fun w => exists aCount bCount,
    aCount < bCount ∧
      w = Word.Concat (Word.RepeatSymbol Section01.AB.a aCount)
        (Word.RepeatSymbol Section01.AB.b bCount)

theorem more_bs_block_language_membership (w : Word Section01.AB) :
    w ∈ moreBsBlockLanguage <->
      exists aCount bCount,
        aCount < bCount ∧
          w = Word.Concat (Word.RepeatSymbol Section01.AB.a aCount)
            (Word.RepeatSymbol Section01.AB.b bCount) :=
  Iff.rfl

theorem more_bs_block_members_have_more_b_counts {w : Word Section01.AB}
    (hw : w ∈ moreBsBlockLanguage) :
    Word.Count Section01.AB.a w < Word.Count Section01.AB.b w := by
  cases hw with
  | intro aCount haCount =>
      cases haCount with
      | intro bCount hbCount =>
          rw [hbCount.right, ablock_word_count_a aCount bCount,
            ablock_word_count_b aCount bCount]
          exact hbCount.left

theorem more_bs_block_pump_two_not_mem
    {x y z : Word Section01.AB} {n : Nat}
    (hword :
      Word.Concat (Word.RepeatSymbol Section01.AB.a n)
        (Word.RepeatSymbol Section01.AB.b (n + 1)) =
          Word.Concat x (Word.Concat y z))
    (hxy : Word.Length (Word.Concat x y) <= n)
    (hy : Word.Length y > 0) :
    ¬ Word.Concat x (Word.Concat (Word.RepeatWord y 2) z) ∈
      moreBsBlockLanguage := by
  intro hmem
  have hcountLess := more_bs_block_members_have_more_b_counts hmem
  have hbY : Word.Count Section01.AB.b y = 0 :=
    ablock_prefix_before_boundary_count_b_zero hword hxy
  have haYPos : 0 < Word.Count Section01.AB.a y :=
    ab_count_a_pos_of_length_pos_count_b_zero hy hbY
  have hcountAOriginal :
      Word.Count Section01.AB.a
        (Word.Concat x (Word.Concat y z)) = n := by
    rw [← hword]
    exact ablock_word_count_a n (n + 1)
  have hcountBOriginal :
      Word.Count Section01.AB.b
        (Word.Concat x (Word.Concat y z)) = n + 1 := by
    rw [← hword]
    exact ablock_word_count_b n (n + 1)
  rw [show Word.RepeatWord y 2 = Word.Concat y y by
    simp [Word.RepeatWord, Word.Concat]] at hcountLess
  repeat rw [Word.count_concat] at hcountLess
  rw [Word.count_concat, Word.count_concat] at hcountAOriginal
  rw [Word.count_concat, Word.count_concat] at hcountBOriginal
  omega

theorem more_bs_block_no_pumping_property :
    ¬ Pumping.HasPumpingProperty moreBsBlockLanguage := by
  intro hpump
  cases hpump with
  | intro n hn =>
      let w : Word Section01.AB :=
        Word.Concat (Word.RepeatSymbol Section01.AB.a n)
          (Word.RepeatSymbol Section01.AB.b (n + 1))
      have hwMem : w ∈ moreBsBlockLanguage := by
        exists n
        exists n + 1
        constructor
        · omega
        · rfl
      have hwLength : n <= Word.Length w := by
        simp [w, Word.length_concat, Word.length_repeatSymbol]
      have hdec := hn.right w hwMem hwLength
      cases hdec with
      | intro x hx =>
          cases hx with
          | intro y hy =>
              cases hy with
              | intro z hz =>
                  cases hz with
                  | intro hword hrest =>
                      exact more_bs_block_pump_two_not_mem hword hrest.left
                        hrest.right.left (hrest.right.right 2)

theorem more_bs_block_not_regular_from_pumping_lemma
    (pumpingLemma : Pumping.PumpingLemmaConclusion moreBsBlockLanguage) :
    ¬ RegularLanguage.Regular moreBsBlockLanguage :=
  Pumping.not_regular_of_no_pumping_property pumpingLemma
    more_bs_block_no_pumping_property

theorem more_bs_block_not_regular :
    ¬ RegularLanguage.Regular moreBsBlockLanguage :=
  Pumping.not_regular_of_no_pumping_property_regular more_bs_block_no_pumping_property

/-!
The final two declarations return to the textbook's standard
`{ a^n b^n | n >= 0 }` example and package the contradiction into
book-facing non-regularity theorems.
-/

theorem anbn_not_regular_from_pumping_lemma
    (pumpingLemma : Pumping.PumpingLemmaConclusion anbnLanguage) :
    ¬ RegularLanguage.Regular anbnLanguage :=
  Pumping.not_regular_of_no_pumping_property pumpingLemma anbn_no_pumping_property

theorem anbn_not_regular :
    ¬ RegularLanguage.Regular anbnLanguage :=
  Pumping.not_regular_of_no_pumping_property_regular anbn_no_pumping_property

/-!
The concrete contradiction for `{ a^n b^n | n >= 0 }` is now formalized:
no pumping length can satisfy the book's quantified pumping property for this
language. The regular-language pumping lemma is proved in
{module}`FoC.Languages.Pumping`, so this file also derives the book-facing
unconditional non-regularity theorem.
-/

end Section07
end Chapter03
end Book
end FoC

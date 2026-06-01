import FoC.Book.Chapter03.Section06
import FoC.Languages.Pumping

namespace FoC
namespace Book
namespace Chapter03
namespace Section07

/-!
Book: Chapter 3, Section 3.7, Non-regular Languages.
-/

open Languages

-- Book: Chapter 3, Section 3.7, Pumping Lemma quantified conclusion.
theorem pumping_length_definition (L : Language alpha) (n : Nat) :
    Pumping.PumpingLength L n <->
      n > 0 ∧ forall w, w ∈ L -> n <= Word.Length w -> Pumping.Decomposition L n w :=
  Iff.rfl

-- Book: Chapter 3, Section 3.7, pumped decompositions keep the original word.
theorem pumped_decomposition_original_word_mem
    {L : Language alpha} {n : Nat} {w : Word alpha}
    (h : Pumping.Decomposition L n w) : w ∈ L :=
  Pumping.decomposition_original_word_mem h

-- Book: Chapter 3, Section 3.7, contrapositive use of the Pumping Lemma.
theorem not_regular_if_no_pumping_property {L : Language alpha}
    (pumpingLemma : Pumping.PumpingLemmaConclusion L)
    (hNoPump : ¬ Pumping.HasPumpingProperty L) :
    ¬ RegularLanguage.Regular L :=
  Pumping.not_regular_of_no_pumping_property pumpingLemma hNoPump

def anbnLanguage : Language Section01.AB :=
  fun w => exists n,
    w = Word.Concat (Word.RepeatSymbol Section01.AB.a n)
      (Word.RepeatSymbol Section01.AB.b n)

-- Book: Chapter 3, Section 3.7, the language used in Theorem 3.7.
theorem anbn_membership (w : Word Section01.AB) :
    w ∈ anbnLanguage <->
      exists n,
        w = Word.Concat (Word.RepeatSymbol Section01.AB.a n)
          (Word.RepeatSymbol Section01.AB.b n) :=
  Iff.rfl

-- Book: Chapter 3, Section 3.7, counting groundwork for the `a^n b^n` example.
theorem anbn_word_count_a (n : Nat) :
    Word.Count Section01.AB.a
      (Word.Concat (Word.RepeatSymbol Section01.AB.a n)
        (Word.RepeatSymbol Section01.AB.b n)) = n := by
  rw [Word.count_concat, Word.count_repeatSymbol_same]
  rw [Word.count_repeatSymbol_different]
  · omega
  · intro h
    cases h

-- Book: Chapter 3, Section 3.7, counting groundwork for the `a^n b^n` example.
theorem anbn_word_count_b (n : Nat) :
    Word.Count Section01.AB.b
      (Word.Concat (Word.RepeatSymbol Section01.AB.a n)
        (Word.RepeatSymbol Section01.AB.b n)) = n := by
  rw [Word.count_concat, Word.count_repeatSymbol_same]
  rw [Word.count_repeatSymbol_different]
  · omega
  · intro h
    cases h

-- Book: Chapter 3, Section 3.7, every word in `{a^n b^n}` has equal counts.
theorem anbn_members_have_equal_counts {w : Word Section01.AB}
    (hw : w ∈ anbnLanguage) :
    Word.Count Section01.AB.a w = Word.Count Section01.AB.b w := by
  cases hw with
  | intro n hn =>
      rw [hn, anbn_word_count_a n, anbn_word_count_b n]

/-!
The book's full proof that `{ a^n b^n | n >= 0 }` is not regular depends on the
Pumping Lemma.  This section formalizes the pumping property and its
contrapositive use without treating the Pumping Lemma itself as an unproved
global assumption.
-/

end Section07
end Chapter03
end Book
end FoC

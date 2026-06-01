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

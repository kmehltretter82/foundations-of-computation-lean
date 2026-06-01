import FoC.Languages.Regular

namespace FoC
namespace Languages

/-!
Pumping-lemma vocabulary for regular languages.

Used by:
- Chapter 3, Section 3.7: Non-regular Languages

This file records the precise quantified property used by the book's pumping
lemma.  It does not add the pumping lemma as a global premise; book-facing modules can
state and use the definition without counting the theorem as proved.
-/

namespace Pumping

def Decomposition (L : Language alpha) (n : Nat) (w : Word alpha) : Prop :=
  exists x y z : Word alpha,
    w = Word.Concat x (Word.Concat y z) ∧
    Word.Length (Word.Concat x y) <= n ∧
    Word.Length y > 0 ∧
    forall k : Nat, Word.Concat x (Word.Concat (Word.RepeatWord y k) z) ∈ L

def PumpingLength (L : Language alpha) (n : Nat) : Prop :=
  n > 0 ∧ forall w, w ∈ L -> n <= Word.Length w -> Decomposition L n w

def HasPumpingProperty (L : Language alpha) : Prop :=
  exists n, PumpingLength L n

def PumpingLemmaConclusion (L : Language alpha) : Prop :=
  RegularLanguage.Regular L -> HasPumpingProperty L

theorem decomposition_original_word_mem {L : Language alpha} {n : Nat} {w : Word alpha}
    (h : Decomposition L n w) : w ∈ L := by
  cases h with
  | intro x hx =>
      cases hx with
      | intro y hy =>
          cases hy with
          | intro z hz =>
              cases hz with
              | intro hwEq hrest =>
                  have hpump := hrest.right.right 1
                  rw [hwEq]
                  simpa [Word.RepeatWord, Word.Concat] using hpump

theorem not_regular_of_no_pumping_property {L : Language alpha}
    (pumpingLemma : PumpingLemmaConclusion L)
    (hNoPump : ¬ HasPumpingProperty L) :
    ¬ RegularLanguage.Regular L := by
  intro hreg
  exact hNoPump (pumpingLemma hreg)

end Pumping
end Languages
end FoC

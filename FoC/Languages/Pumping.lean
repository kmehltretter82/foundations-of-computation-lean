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

theorem decomposition_of_equal {L M : Language alpha} {n : Nat} {w : Word alpha}
    (hEq : Language.Equal L M) (h : Decomposition L n w) :
    Decomposition M n w := by
  cases h with
  | intro x hx =>
      cases hx with
      | intro y hy =>
          cases hy with
          | intro z hz =>
              cases hz with
              | intro hwEq hrest =>
                  exists x
                  exists y
                  exists z
                  constructor
                  · exact hwEq
                  constructor
                  · exact hrest.left
                  constructor
                  · exact hrest.right.left
                  · intro k
                    exact (hEq _).mp (hrest.right.right k)

theorem pumpingLength_of_equal {L M : Language alpha} {n : Nat}
    (hEq : Language.Equal L M) (h : PumpingLength L n) :
    PumpingLength M n := by
  constructor
  · exact h.left
  · intro w hw hlen
    exact decomposition_of_equal hEq
      (h.right w ((hEq w).mpr hw) hlen)

theorem hasPumpingProperty_of_equal {L M : Language alpha}
    (hEq : Language.Equal L M) (h : HasPumpingProperty L) :
    HasPumpingProperty M := by
  cases h with
  | intro n hn =>
      exists n
      exact pumpingLength_of_equal hEq hn

theorem pumpingLength_mono {L : Language alpha} {n m : Nat}
    (hnm : n <= m) (h : PumpingLength L n) :
    PumpingLength L m := by
  constructor
  · exact Nat.lt_of_lt_of_le h.left hnm
  · intro w hw hlen
    cases h.right w hw (Nat.le_trans hnm hlen) with
    | intro x hx =>
        cases hx with
        | intro y hy =>
            cases hy with
            | intro z hz =>
                cases hz with
                | intro hwEq hrest =>
                    exists x
                    exists y
                    exists z
                    constructor
                    · exact hwEq
                    constructor
                    · exact Nat.le_trans hrest.left hnm
                    exact hrest.right

theorem not_pumpingLength_of_counterexample {L : Language alpha} {n : Nat}
    {w : Word alpha}
    (hw : w ∈ L) (hlen : n <= Word.Length w)
    (hbad :
      forall x y z : Word alpha,
        w = Word.Concat x (Word.Concat y z) ->
        Word.Length (Word.Concat x y) <= n ->
        Word.Length y > 0 ->
        exists k : Nat,
          ¬ Word.Concat x (Word.Concat (Word.RepeatWord y k) z) ∈ L) :
    ¬ PumpingLength L n := by
  intro hpump
  cases hpump.right w hw hlen with
  | intro x hx =>
      cases hx with
      | intro y hy =>
          cases hy with
          | intro z hz =>
              cases hz with
              | intro hwEq hrest =>
                  cases hbad x y z hwEq hrest.left hrest.right.left with
                  | intro k hk =>
                      exact hk (hrest.right.right k)

theorem not_hasPumpingProperty_of_counterexamples {L : Language alpha}
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
    ¬ HasPumpingProperty L := by
  intro hpump
  cases hpump with
  | intro n hn =>
      cases hbad n hn.left with
      | intro w hw =>
          exact not_pumpingLength_of_counterexample hw.left hw.right.left
            hw.right.right hn

theorem not_regular_of_no_pumping_property {L : Language alpha}
    (pumpingLemma : PumpingLemmaConclusion L)
    (hNoPump : ¬ HasPumpingProperty L) :
    ¬ RegularLanguage.Regular L := by
  intro hreg
  exact hNoPump (pumpingLemma hreg)

end Pumping
end Languages
end FoC

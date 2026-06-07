import FoC.Foundation.DigitStreams
import FoC.Foundation.Reals

set_option doc.verso true

/-!
# Real uncountability

## Embedding streams into reals

Streams are interpreted as base-4 expansions with digits {lit}`0` and {lit}`2`.  The
larger digit gap gives a direct injectivity proof without ambiguous binary or
decimal-expansion endpoints.

## Book coordinates

Used by:
- Chapter 2, Section 2.6: real-number uncountability
- Irrational-real uncountability by removing the countable embedded rationals
-/

namespace FoC
namespace Foundation

namespace DigitStream

/-!
# Base-four stream approximations

Each Boolean digit becomes either {lit}`0` or {lit}`2`. Partial sums and probe
rationals then separate streams at the first coordinate where they differ.
-/

def cantorDigit (b : Bool) : Nat :=
  if b then 2 else 0

theorem cantorDigit_lt_four (b : Bool) : cantorDigit b < 4 := by
  cases b <;> decide

def cantorNumerator (s : DigitStream) : Nat -> Nat
  | 0 => 0
  | n + 1 => 4 * cantorNumerator s n + cantorDigit (s n)

theorem pow_four_pos (n : Nat) : 0 < 4 ^ n :=
  Nat.pow_pos (by decide : 0 < 4)

def streamPartial (s : DigitStream) (n : Nat) : QRat :=
  QRat.natFrac (cantorNumerator s n) (4 ^ n) (pow_four_pos n)

def streamProbe (pref m : Nat) : QRat :=
  QRat.natFrac (4 * pref + 1) (4 ^ (m + 1)) (pow_four_pos (m + 1))

theorem cantorNumerator_lt_pow_four (s : DigitStream) (n : Nat) :
    cantorNumerator s n < 4 ^ n := by
  induction n with
  | zero => simp [cantorNumerator]
  | succ n ih =>
      simp [cantorNumerator, Nat.pow_succ]
      have hd := cantorDigit_lt_four (s n)
      omega

theorem streamPartial_lt_one (s : DigitStream) (n : Nat) :
    streamPartial s n < (1 : QRat) := by
  exact QRat.one_gt_natFrac (pow_four_pos n) (cantorNumerator_lt_pow_four s n)

theorem neg_one_lt_streamPartial_zero (s : DigitStream) :
    QRat.ofInt (-1) < streamPartial s 0 := by
  unfold streamPartial QRat.natFrac QRat.ofInt
  apply QRat.lt_mk_of_rawLt
  unfold RatPair.RawLt RatPair.ofInt
  simp [cantorNumerator]

theorem cantorNumerator_suffix_lt (s : DigitStream) (m k : Nat) :
    cantorNumerator s (m + k) < cantorNumerator s m * 4 ^ k + 4 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.add_succ, cantorNumerator]
      have hd := cantorDigit_lt_four (s (m + k))
      have hmul : 4 * cantorNumerator s (m + k) <
          4 * (cantorNumerator s m * 4 ^ k + 4 ^ k) := by
        exact (Nat.mul_lt_mul_left (by decide : 0 < 4)).mpr ih
      calc
        4 * cantorNumerator s (m + k) + cantorDigit (s (m + k))
            < 4 * (cantorNumerator s m * 4 ^ k + 4 ^ k) := by
              omega
        _ = cantorNumerator s m * 4 ^ (k + 1) + 4 ^ (k + 1) := by
              simp [Nat.pow_succ, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm]

theorem cantorNumerator_prefix_scaled_le (s : DigitStream) (m k : Nat) :
    cantorNumerator s m * 4 ^ k ≤ cantorNumerator s (m + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show m + (k + 1) = (m + k) + 1 by omega]
      simp only [cantorNumerator]
      calc
        cantorNumerator s m * 4 ^ (k + 1)
            = 4 * (cantorNumerator s m * 4 ^ k) := by
              simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm]
        _ ≤ 4 * cantorNumerator s (m + k) := by
              exact Nat.mul_le_mul_left 4 ih
        _ ≤ 4 * cantorNumerator s (m + k) + cantorDigit (s (m + k)) := by
              exact Nat.le_add_right _ _

theorem cantorNumerator_succ_false {s : DigitStream} {m : Nat}
    (h : s m = false) :
    cantorNumerator s (m + 1) = 4 * cantorNumerator s m := by
  simp [cantorNumerator, cantorDigit, h]

theorem cantorNumerator_succ_true {s : DigitStream} {m : Nat}
    (h : s m = true) :
    cantorNumerator s (m + 1) = 4 * cantorNumerator s m + 2 := by
  simp [cantorNumerator, cantorDigit, h]

theorem cross_lt_probe_of_prefix_scaled_le {N P n k : Nat}
    (h : N * 4 ^ k ≤ P) :
    N * 4 ^ (n + k + 1) < (4 * P + 1) * 4 ^ n := by
  have hscale : 4 * (N * 4 ^ k) ≤ 4 * P := by
    exact Nat.mul_le_mul_left 4 h
  have hstrict : 4 * (N * 4 ^ k) < 4 * P + 1 := by
    omega
  have hpos : 0 < 4 ^ n := Nat.pow_pos (by decide : 0 < 4)
  have hmul := (Nat.mul_lt_mul_right hpos).mpr hstrict
  calc
    N * 4 ^ (n + k + 1)
        = (4 * (N * 4 ^ k)) * 4 ^ n := by
          simp [Nat.pow_add, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]
    _ < (4 * P + 1) * 4 ^ n := hmul

theorem cross_lt_probe_of_suffix_lt {N P m k : Nat}
    (h : N < (4 * P + 1) * 4 ^ k) :
    N * 4 ^ (m + 1) < (4 * P + 1) * 4 ^ (m + 1 + k) := by
  have hpos : 0 < 4 ^ (m + 1) := Nat.pow_pos (by decide : 0 < 4)
  have hmul := (Nat.mul_lt_mul_right hpos).mpr h
  calc
    N * 4 ^ (m + 1)
        < ((4 * P + 1) * 4 ^ k) * 4 ^ (m + 1) := hmul
    _ = (4 * P + 1) * 4 ^ (m + 1 + k) := by
          simp [Nat.pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem streamProbe_lt_partial_of_true {s : DigitStream} {m : Nat}
    (htrue : s m = true) :
    streamProbe (cantorNumerator s m) m < streamPartial s (m + 1) := by
  have hnum : cantorNumerator s (m + 1) = 4 * cantorNumerator s m + 2 :=
    cantorNumerator_succ_true htrue
  unfold streamProbe streamPartial
  rw [hnum]
  exact QRat.natFrac_lt_natFrac (pow_four_pos (m + 1)) (by omega)

theorem streamPartial_lt_probe_of_false {s : DigitStream} {m : Nat}
    (hfalse : s m = false) (n : Nat) :
    streamPartial s n < streamProbe (cantorNumerator s m) m := by
  by_cases hnm : n ≤ m
  · let k := m - n
    have hmk : n + k = m := by
      dsimp [k]
      exact Nat.add_sub_of_le hnm
    have hprefix := cantorNumerator_prefix_scaled_le s n k
    have hprefix' : cantorNumerator s n * 4 ^ k ≤ cantorNumerator s m := by
      simpa [hmk] using hprefix
    have hcross := cross_lt_probe_of_prefix_scaled_le (N := cantorNumerator s n)
      (P := cantorNumerator s m) (n := n) (k := k) hprefix'
    have hden : n + k + 1 = m + 1 := by omega
    exact QRat.natFrac_lt_of_cross (pow_four_pos n) (pow_four_pos (m + 1))
      (by simpa [hden] using hcross)
  · have hle : m + 1 ≤ n := by omega
    let k := n - (m + 1)
    have hnk : m + 1 + k = n := by
      dsimp [k]
      exact Nat.add_sub_of_le hle
    have hsuffix := cantorNumerator_suffix_lt s (m + 1) k
    have hstart : cantorNumerator s (m + 1) = 4 * cantorNumerator s m :=
      cantorNumerator_succ_false hfalse
    have hsuffix' : cantorNumerator s n < (4 * cantorNumerator s m + 1) * 4 ^ k := by
      rw [← hnk]
      calc
        cantorNumerator s (m + 1 + k)
            < cantorNumerator s (m + 1) * 4 ^ k + 4 ^ k := hsuffix
        _ = (4 * cantorNumerator s m + 1) * 4 ^ k := by
              rw [hstart]
              simp [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]
    have hcross := cross_lt_probe_of_suffix_lt (N := cantorNumerator s n)
      (P := cantorNumerator s m) (m := m) (k := k) hsuffix'
    have hden : m + 1 + k = n := hnk
    exact QRat.natFrac_lt_of_cross (pow_four_pos n) (pow_four_pos (m + 1))
      (by simpa [hden] using hcross)

/-!
# Embedding streams into reals

The stream is sent to the lower cut below some finite partial sum. The digit gap
proves injectivity because a probe rational lies on opposite sides of the two
cuts at the first differing digit.
-/

def streamToReal (s : DigitStream) : Real where
  lower q := exists n : Nat, q < streamPartial s n
  nonempty := by
    exists QRat.ofInt (-1)
    exists 0
    exact neg_one_lt_streamPartial_zero s
  proper := by
    exists (1 : QRat)
    intro h
    cases h with
    | intro n hn =>
        exact QRat.lt_asymm (streamPartial_lt_one s n) hn
  downward_closed := by
    intro q r hqr hr
    cases hr with
    | intro n hrn =>
        exists n
        exact QRat.lt_trans hqr hrn
  open_upward := by
    intro q hq
    cases hq with
    | intro n hqn =>
        cases QRat.density hqn with
        | intro r hr =>
            exists r
            exact And.intro hr.left (Exists.intro n hr.right)

theorem streamToReal_lower_iff (s : DigitStream) (q : QRat) :
    (streamToReal s).lower q <-> exists n : Nat, q < streamPartial s n :=
  Iff.rfl

theorem not_streamToReal_lower_probe_of_false {s : DigitStream} {m : Nat}
    (hfalse : s m = false) :
    ¬ (streamToReal s).lower (streamProbe (cantorNumerator s m) m) := by
  intro h
  cases h with
  | intro n hn =>
      exact QRat.lt_asymm (streamPartial_lt_probe_of_false hfalse n) hn

theorem streamToReal_bit_eq_of_prefix_eq {s t : DigitStream}
    (hreal : streamToReal s = streamToReal t) {m : Nat}
    (hpref : cantorNumerator s m = cantorNumerator t m) :
    s m = t m := by
  cases hs : s m <;> cases ht : t m
  · rfl
  · have hmemT : (streamToReal t).lower (streamProbe (cantorNumerator t m) m) := by
      exists m + 1
      exact streamProbe_lt_partial_of_true ht
    have hmemS : (streamToReal s).lower (streamProbe (cantorNumerator t m) m) :=
      (Real.lower_congr hreal (streamProbe (cantorNumerator t m) m)).mpr hmemT
    have hnotS : ¬ (streamToReal s).lower (streamProbe (cantorNumerator t m) m) := by
      simpa [← hpref] using not_streamToReal_lower_probe_of_false hs
    exact False.elim (hnotS hmemS)
  · have hmemS : (streamToReal s).lower (streamProbe (cantorNumerator s m) m) := by
      exists m + 1
      exact streamProbe_lt_partial_of_true hs
    have hmemT : (streamToReal t).lower (streamProbe (cantorNumerator s m) m) :=
      (Real.lower_congr hreal (streamProbe (cantorNumerator s m) m)).mp hmemS
    have hnotT : ¬ (streamToReal t).lower (streamProbe (cantorNumerator s m) m) := by
      simpa [hpref] using not_streamToReal_lower_probe_of_false ht
    exact False.elim (hnotT hmemT)
  · rfl

theorem streamToReal_injective : Fn.Injective streamToReal := by
  intro s t hreal
  funext n
  have hnum : forall k : Nat, cantorNumerator s k = cantorNumerator t k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        have hbit : s k = t k := streamToReal_bit_eq_of_prefix_eq hreal ih
        simp [cantorNumerator, ih, hbit]
  exact streamToReal_bit_eq_of_prefix_eq hreal (hnum n)

end DigitStream

namespace Real

/-!
# Countability transfer

The final section transports uncountability from digit streams to reals, then
removes the countable embedded rationals to get an irrational-real statement.
-/

def rationalSet : FSet Real :=
  fun x => Rational x

def irrationalSet : FSet Real :=
  fun x => Irrational x

theorem rationalSet_subset_univ : FSet.Subset rationalSet (FSet.Univ : FSet Real) := by
  intro x _
  exact True.intro

theorem rationalSet_countable : FSet.Countable rationalSet := by
  cases QRat.countable_univ with
  | intro f hf =>
      exists fun n =>
        match f n with
        | some q => some (qreal q)
        | none => none
      intro x
      constructor
      · intro hx
        cases hx with
        | intro q hq =>
            have hlisted := (hf q).mp True.intro
            cases hlisted with
            | intro n hn =>
                exists n
                simp [hn, hq]
      · intro hx
        cases hx with
        | intro n hn =>
            cases hfn : f n with
            | none =>
                simp [hfn] at hn
            | some q =>
                simp [hfn] at hn
                cases hn
                exact rational_qreal q

theorem uncountable_univ_of_digitStream_injective
    (embed : DigitStream -> Real) (hembed : Fn.Injective embed) :
    FSet.Uncountable (FSet.Univ : FSet Real) := by
  classical
  intro hRealCountable
  apply DigitStream.uncountable_univ
  cases hRealCountable with
  | intro f hf =>
      let preimage : Real -> Option DigitStream := fun x =>
        if h : exists s : DigitStream, embed s = x then
          some (Classical.choose h)
        else
          none
      let g : Nat -> Option DigitStream := fun n =>
        match f n with
        | some x => preimage x
        | none => none
      exists g
      intro s
      constructor
      · intro _
        have hlisted := (hf (embed s)).mp True.intro
        cases hlisted with
        | intro n hn =>
            have hex : exists t : DigitStream, embed t = embed s :=
              Exists.intro s rfl
            have hpre : preimage (embed s) = some s := by
              dsimp [preimage]
              rw [dif_pos hex]
              exact congrArg some (hembed (Classical.choose_spec hex))
            exists n
            simp [g, hn, hpre]
      · intro _
        exact True.intro

theorem uncountable_univ : FSet.Uncountable (FSet.Univ : FSet Real) :=
  uncountable_univ_of_digitStream_injective
    DigitStream.streamToReal DigitStream.streamToReal_injective

theorem irrationalSet_equal_univ_diff_rationalSet :
    FSet.Equal irrationalSet (FSet.Diff (FSet.Univ : FSet Real) rationalSet) := by
  intro x
  constructor
  · intro hx
    exact And.intro True.intro hx
  · intro hx
    exact hx.right

theorem irrationalSet_uncountable : FSet.Uncountable irrationalSet := by
  intro hcount
  have hdiff : FSet.Uncountable (FSet.Diff (FSet.Univ : FSet Real) rationalSet) :=
    FSet.uncountable_diff_countable_subset
      uncountable_univ rationalSet_countable rationalSet_subset_univ
  apply hdiff
  exact FSet.countable_of_equal irrationalSet_equal_univ_diff_rationalSet hcount

end Real

end Foundation
end FoC

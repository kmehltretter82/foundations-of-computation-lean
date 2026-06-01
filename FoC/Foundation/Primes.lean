import FoC.Foundation.Arithmetic

namespace FoC
namespace Foundation

/-!
Standalone prime-number infrastructure.

Used by:
- Chapter 1, Section 1.7: prime divisor existence
- Chapter 1, Section 1.8: product-of-primes induction example
- Later arithmetic and countability examples
-/

namespace NatPrime

def Prime (p : Nat) : Prop :=
  1 < p ∧ forall a b, p = a * b -> a = 1 ∨ b = 1

def Composite (n : Nat) : Prop :=
  1 < n ∧ ¬ Prime n

def Product : List Nat -> Nat
  | [] => 1
  | x :: xs => x * Product xs

def AllPrime : List Nat -> Prop
  | [] => True
  | x :: xs => Prime x ∧ AllPrime xs

def ProductOfPrimes (n : Nat) : Prop :=
  exists ps, AllPrime ps ∧ Product ps = n

theorem prime_gt_one {p : Nat} (hp : Prime p) : 1 < p :=
  hp.left

theorem not_composite_of_prime {n : Nat} (hp : Prime n) : ¬ Composite n := by
  intro hc
  exact hc.right hp

theorem divides_self (n : Nat) : NatPred.Divides n n := by
  exists 1
  rw [Nat.mul_one]

theorem divides_mul_right {a b : Nat} (h : NatPred.Divides a b) (c : Nat) :
    NatPred.Divides a (b * c) := by
  cases h with
  | intro k hk =>
      exists k * c
      rw [hk, Nat.mul_assoc]

theorem factor_lt_left {n a b : Nat}
    (hnab : n = a * b) (ha : 1 < a) (hb : 1 < b) : a < n := by
  have hapos : a > 0 := by
    omega
  have hmul : a * 1 < a * b := Nat.mul_lt_mul_of_pos_left hb hapos
  rw [Nat.mul_one] at hmul
  rw [hnab]
  exact hmul

theorem factor_lt_right {n a b : Nat}
    (hnab : n = a * b) (ha : 1 < a) (hb : 1 < b) : b < n := by
  have hbpos : b > 0 := by
    omega
  have hmul : 1 * b < a * b := Nat.mul_lt_mul_of_pos_right ha hbpos
  rw [Nat.one_mul] at hmul
  rw [hnab]
  exact hmul

theorem nonprime_factorization {n : Nat} (hn : 1 < n) (hnp : ¬ Prime n) :
    exists a b, n = a * b ∧ 1 < a ∧ 1 < b := by
  apply Classical.byContradiction
  intro hno
  apply hnp
  constructor
  · exact hn
  · intro a b hab
    by_cases ha : a = 1
    · exact Or.inl ha
    · by_cases hb : b = 1
      · exact Or.inr hb
      · have ha0 : a ≠ 0 := by
          intro h0
          rw [h0] at hab
          omega
        have hb0 : b ≠ 0 := by
          intro h0
          rw [h0] at hab
          omega
        have hapos : 1 < a := by
          omega
        have hbpos : 1 < b := by
          omega
        exfalso
        exact hno (Exists.intro a
          (Exists.intro b (And.intro hab (And.intro hapos hbpos))))

-- Book: Chapter 1, Section 1.7, prime divisor existence.
theorem prime_divisor_exists (n : Nat) (hn : 1 < n) :
    exists p, Prime p ∧ NatPred.Divides p n := by
  exact Nat.strongRecOn
    (motive := fun n => 1 < n -> exists p, Prime p ∧ NatPred.Divides p n)
    n
    (fun n ih hn => by
      by_cases hp : Prime n
      · exact Exists.intro n (And.intro hp (divides_self n))
      · cases nonprime_factorization hn hp with
        | intro a hrest =>
            cases hrest with
            | intro b hdata =>
                have hnab : n = a * b := hdata.left
                have ha : 1 < a := hdata.right.left
                have hb : 1 < b := hdata.right.right
                have halt : a < n := factor_lt_left hnab ha hb
                cases ih a halt ha with
                | intro p hpdata =>
                    exact Exists.intro p (And.intro hpdata.left (by
                      cases hpdata.right with
                      | intro k hk =>
                          exists k * b
                          rw [hnab, hk, Nat.mul_assoc])))
    hn

theorem product_append (xs ys : List Nat) :
    Product (xs ++ ys) = Product xs * Product ys := by
  induction xs with
  | nil =>
      simp [Product]
  | cons x xs ih =>
      simp [Product, ih, Nat.mul_assoc]

theorem allPrime_append {xs ys : List Nat}
    (hxs : AllPrime xs) (hys : AllPrime ys) : AllPrime (xs ++ ys) := by
  induction xs with
  | nil =>
      exact hys
  | cons x xs ih =>
      cases hxs with
      | intro hx hrest =>
          exact And.intro hx (ih hrest)

-- Book: Chapter 1, Section 1.8, product-of-primes induction example.
theorem product_of_primes_exists (n : Nat) (hn : 1 < n) : ProductOfPrimes n := by
  exact Nat.strongRecOn
    (motive := fun n => 1 < n -> ProductOfPrimes n)
    n
    (fun n ih hn => by
      by_cases hp : Prime n
      · exists [n]
        exact And.intro (And.intro hp True.intro) (Nat.mul_one n)
      · cases nonprime_factorization hn hp with
        | intro a hrest =>
            cases hrest with
            | intro b hdata =>
                have hnab : n = a * b := hdata.left
                have ha : 1 < a := hdata.right.left
                have hb : 1 < b := hdata.right.right
                have halt : a < n := factor_lt_left hnab ha hb
                have hblt : b < n := factor_lt_right hnab ha hb
                cases ih a halt ha with
                | intro aps hap =>
                    cases ih b hblt hb with
                    | intro bps hbp =>
                        exists aps ++ bps
                        constructor
                        · exact allPrime_append hap.left hbp.left
                        · rw [product_append, hap.right, hbp.right]
                          exact hnab.symm)
    hn

end NatPrime

end Foundation
end FoC

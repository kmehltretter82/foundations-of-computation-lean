import FoC.Computability.Compiler.DescriptionExecution

set_option doc.verso true

/-!
# Common search algebra

This module contains dependency-light witness reshaping lemmas for bounded
fuel and pair searches.
-/

namespace FoC
namespace Computability

namespace CommonGround

theorem exists_bounded_pair_iff_exists_pair
    (P : Nat -> Nat -> Prop) :
    (exists limit : Nat,
      exists m : Nat,
      exists n : Nat,
        m <= limit /\ n <= limit /\ P m n) <->
      exists m : Nat, exists n : Nat, P m n := by
  constructor
  · intro h
    rcases h with ⟨_limit, m, n, _hm, _hn, hp⟩
    exact ⟨m, n, hp⟩
  · intro h
    rcases h with ⟨m, n, hp⟩
    exact
      ⟨Nat.max m n, m, n,
        Nat.le_max_left m n, Nat.le_max_right m n, hp⟩

theorem exists_bounded_triple_iff_exists_triple
    (P : Nat -> Nat -> Nat -> Prop) :
    (exists limit : Nat,
      exists m : Nat,
      exists n : Nat,
      exists fuel : Nat,
        m <= limit /\ n <= limit /\ fuel <= limit /\ P m n fuel) <->
      exists m : Nat, exists n : Nat, exists fuel : Nat, P m n fuel := by
  constructor
  · intro h
    rcases h with ⟨_limit, m, n, fuel, _hm, _hn, _hfuel, hp⟩
    exact ⟨m, n, fuel, hp⟩
  · intro h
    rcases h with ⟨m, n, fuel, hp⟩
    let limit := Nat.max (Nat.max m n) fuel
    exact
      ⟨limit, m, n, fuel,
        Nat.le_trans (Nat.le_max_left m n)
          (Nat.le_max_left (Nat.max m n) fuel),
        Nat.le_trans (Nat.le_max_right m n)
          (Nat.le_max_left (Nat.max m n) fuel),
        Nat.le_max_right (Nat.max m n) fuel,
        hp⟩

theorem exists_bounded_fuel_iff_exists
    (P : Nat -> Prop) :
    (exists limit : Nat,
      exists fuel : Nat,
        fuel <= limit /\ P fuel) <->
      exists fuel : Nat, P fuel := by
  constructor
  · intro h
    rcases h with ⟨_limit, fuel, _hle, hp⟩
    exact ⟨fuel, hp⟩
  · intro h
    rcases h with ⟨fuel, hp⟩
    exact ⟨fuel, fuel, Nat.le_refl fuel, hp⟩

end CommonGround

end Computability
end FoC

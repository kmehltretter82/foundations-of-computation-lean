import FoC.Foundation.Countable
import FoC.Foundation.Functions

namespace FoC
namespace Book
namespace Chapter02
namespace Section06

/-!
Book: Chapter 2, Section 2.6, Counting Past Infinity.
-/

open Foundation

-- Book: Chapter 2, Section 2.6, finite sets by explicit enumeration.
theorem empty_set_is_finite : FSet.Finite (FSet.Empty : FSet alpha) :=
  FSet.empty_finite

-- Book: Chapter 2, Section 2.6, singleton sets are finite.
theorem singleton_set_is_finite (x : alpha) : FSet.Finite (FSet.Singleton x) :=
  FSet.singleton_finite x

-- Book: Chapter 2, Section 2.6, natural numbers are countable.
theorem natural_numbers_countable : FSet.Countable (FSet.Univ : FSet Nat) :=
  FSet.nat_univ_countable

-- Book: Chapter 2, Section 2.6, even natural numbers are countable.
theorem even_natural_numbers_countable : FSet.Countable FSet.EvenNaturals :=
  FSet.even_naturals_countable

-- Book: Chapter 2, Section 2.6, Theorem: no set has the cardinality of its powerset.
theorem cantor_no_one_to_one_correspondence_with_powerset
    (f : alpha -> FSet alpha) :
    ¬ (forall A : FSet alpha, exists x : alpha, FSet.Equal (f x) A) :=
  FSet.cantor_no_surjective_powerset f

-- Book: Chapter 2, Section 2.6, no bijective function reaches the powerset.
theorem cantor_no_bijection_with_powerset (f : alpha -> FSet alpha) :
    ¬ Fn.Bijective f := by
  intro hf
  apply FSet.cantor_no_surjective_powerset f
  intro A
  cases hf.right A with
  | intro x hx =>
      exists x
      rw [hx]
      exact FSet.equal_refl A

/-!
The section's finite-cardinality arithmetic laws, such as
`|A x B| = |A| * |B|`, require a numeric cardinality layer on top of the
current list-enumeration definition of finite sets. The present standalone
core records finite and countable objects directly and proves the diagonal
power-set theorem.
-/

end Section06
end Chapter02
end Book
end FoC

import FoC.Foundation.Sets

namespace FoC
namespace Book
namespace Chapter02
namespace Section08

/-!
Book: Chapter 2, Section 2.8, Application: Relational Databases.

The section explains relational databases as finite relations over product
types. The formal core below models table insertion as adding a row to a
relation.
-/

open Foundation

abbrev Table (row : Type u) : Type u :=
  FSet row

abbrev Insert (T : Table row) (r : row) : Table row :=
  FSet.Union T (FSet.Singleton r)

-- Book: Chapter 2, Section 2.8, inserted rows are present in the resulting table.
theorem inserted_row_present (T : Table row) (r : row) :
    r ∈ Insert T r := by
  exact Or.inr rfl

-- Book: Chapter 2, Section 2.8, old rows remain present after insertion.
theorem existing_row_present_after_insert {T : Table row} {old new : row}
    (h : old ∈ T) : old ∈ Insert T new := by
  exact Or.inl h

end Section08
end Chapter02
end Book
end FoC

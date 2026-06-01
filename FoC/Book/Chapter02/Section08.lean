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

abbrev Select (T : Table row) (P : row -> Prop) : Table row :=
  FSet.Inter T P

abbrev Delete (T : Table row) (P : row -> Prop) : Table row :=
  fun r => r ∈ T ∧ ¬ P r

abbrev Update (T : Table row) (P : row -> Prop) (u : row -> row) : Table row :=
  fun r' => (exists r, r ∈ T ∧ P r ∧ u r = r') ∨ (r' ∈ T ∧ ¬ P r')

def PrimaryKey (key : row -> keytype) (T : Table row) : Prop :=
  forall r1 r2, r1 ∈ T -> r2 ∈ T -> key r1 = key r2 -> r1 = r2

-- Book: Chapter 2, Section 2.8, inserted rows are present in the resulting table.
theorem inserted_row_present (T : Table row) (r : row) :
    r ∈ Insert T r := by
  exact Or.inr rfl

-- Book: Chapter 2, Section 2.8, old rows remain present after insertion.
theorem existing_row_present_after_insert {T : Table row} {old new : row}
    (h : old ∈ T) : old ∈ Insert T new := by
  exact Or.inl h

-- Book: Chapter 2, Section 2.8, selection is conjunction with a predicate.
theorem select_membership (T : Table row) (P : row -> Prop) (r : row) :
    r ∈ Select T P <-> r ∈ T ∧ P r :=
  Iff.rfl

-- Book: Chapter 2, Section 2.8, deletion removes rows satisfying a predicate.
theorem delete_membership (T : Table row) (P : row -> Prop) (r : row) :
    r ∈ Delete T P <-> r ∈ T ∧ ¬ P r :=
  Iff.rfl

-- Book: Chapter 2, Section 2.8, updated rows appear in the update result.
theorem updated_row_present {T : Table row} {P : row -> Prop} {u : row -> row} {r : row}
    (hT : r ∈ T) (hP : P r) : u r ∈ Update T P u := by
  exact Or.inl (Exists.intro r (And.intro hT (And.intro hP rfl)))

-- Book: Chapter 2, Section 2.8, inserting a fresh key preserves primary keys.
theorem insert_preserves_primary_key {key : row -> keytype} {T : Table row} {new : row}
    (hpk : PrimaryKey key T)
    (hfresh : forall old, old ∈ T -> key old ≠ key new) :
    PrimaryKey key (Insert T new) := by
  intro r1 r2 h1 h2 hkey
  cases h1 with
  | inl h1old =>
      cases h2 with
      | inl h2old => exact hpk r1 r2 h1old h2old hkey
      | inr h2new =>
          have hkeyNew : key r1 = key new := by
            rw [← h2new]
            exact hkey
          exfalso
          exact hfresh r1 h1old hkeyNew
  | inr h1new =>
      cases h2 with
      | inl h2old =>
          have hkeyNew : key r2 = key new := by
            rw [← h1new]
            exact hkey.symm
          exfalso
          exact hfresh r2 h2old hkeyNew
      | inr h2new =>
          rw [h1new, h2new]

end Section08
end Chapter02
end Book
end FoC

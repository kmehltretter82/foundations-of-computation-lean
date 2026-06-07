import FoC.Foundation.Sets

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter02
namespace Section08

/-!
# Chapter 2, Section 2.8: Application - Relational Databases

The section explains relational databases as finite relations over product
types. The formal core below models table insertion as adding a row to a
relation, selection and deletion as predicate filters, and updates as a
combination of transformed matching rows with unchanged nonmatching rows.

The page treats database operations by their effect on row membership. This is
close to SQL's declarative reading: an output table is specified by the rows
that belong to it, not by an implementation strategy for finding them.
-/

open Foundation

/-!
## Tables and Operations

A table is represented as a set of rows. Insertion adds a singleton row,
selection intersects the table with a predicate, deletion keeps rows that do
not satisfy a predicate, and update replaces rows satisfying the predicate by
their transformed versions.
-/

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

/-!
## Membership Properties

The first statements describe the observable behavior of the operations:
inserted rows are present, old rows remain after insertion, selection and
deletion have the expected membership tests, and updated rows appear in the
result.
-/

theorem inserted_row_present (T : Table row) (r : row) :
    r ∈ Insert T r := by
  exact Or.inr rfl

theorem existing_row_present_after_insert {T : Table row} {old new : row}
    (h : old ∈ T) : old ∈ Insert T new := by
  exact Or.inl h

theorem select_membership (T : Table row) (P : row -> Prop) (r : row) :
    r ∈ Select T P <-> r ∈ T ∧ P r :=
  Iff.rfl

theorem delete_membership (T : Table row) (P : row -> Prop) (r : row) :
    r ∈ Delete T P <-> r ∈ T ∧ ¬ P r :=
  Iff.rfl

theorem updated_row_present {T : Table row} {P : row -> Prop} {u : row -> row} {r : row}
    (hT : r ∈ T) (hP : P r) : u r ∈ Update T P u := by
  exact Or.inl (Exists.intro r (And.intro hT (And.intro hP rfl)))

theorem unchanged_row_present_after_update {T : Table row} {P : row -> Prop}
    {u : row -> row} {r : row} (hT : r ∈ T) (hP : ¬ P r) :
    r ∈ Update T P u := by
  exact Or.inr (And.intro hT hP)

theorem select_subset_table (T : Table row) (P : row -> Prop) :
    FSet.Subset (Select T P) T := by
  intro r hr
  exact hr.left

theorem delete_subset_table (T : Table row) (P : row -> Prop) :
    FSet.Subset (Delete T P) T := by
  intro r hr
  exact hr.left

theorem selected_rows_satisfy_predicate {T : Table row} {P : row -> Prop} {r : row}
    (hr : r ∈ Select T P) : P r :=
  hr.right

theorem deleted_rows_do_not_satisfy_predicate {T : Table row} {P : row -> Prop} {r : row}
    (hr : r ∈ Delete T P) : ¬ P r :=
  hr.right

theorem select_select_membership (T : Table row) (P Q : row -> Prop) (r : row) :
    r ∈ Select (Select T P) Q <-> r ∈ T ∧ P r ∧ Q r := by
  constructor
  · intro hr
    exact And.intro hr.left.left (And.intro hr.left.right hr.right)
  · intro hr
    exact And.intro (And.intro hr.left hr.right.left) hr.right.right

/-!
## Primary Keys

A primary key is modeled as injectivity of the key function on rows currently
in the table. Inserting a row with a key that is fresh relative to all old rows
preserves that invariant.

Freshness is the important side condition. If no old row has the new key, then
any two rows with the same key after insertion are either both old, both the
new row, or one old and one new; the mixed case is impossible by freshness.
-/

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

theorem select_preserves_primary_key {key : row -> keytype} {T : Table row}
    {P : row -> Prop} (hpk : PrimaryKey key T) :
    PrimaryKey key (Select T P) := by
  intro r1 r2 h1 h2 hkey
  exact hpk r1 r2 h1.left h2.left hkey

theorem delete_preserves_primary_key {key : row -> keytype} {T : Table row}
    {P : row -> Prop} (hpk : PrimaryKey key T) :
    PrimaryKey key (Delete T P) := by
  intro r1 r2 h1 h2 hkey
  exact hpk r1 r2 h1.left h2.left hkey

end Section08
end Chapter02
end Book
end FoC

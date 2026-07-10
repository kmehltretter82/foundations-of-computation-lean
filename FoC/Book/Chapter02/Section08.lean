import FoC.Foundation.Finite
import FoC.Foundation.Functions

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

{lit}`TableSpec` gives declarative set semantics. {lit}`FiniteTable` stores a
duplicate-free executable row list, and {lit}`FiniteTable.semantics`
interprets it as a specification. Insertion adds a singleton row, selection
and deletion filter, projection maps columns, products pair rows, and joins
retain pairs satisfying a condition.
-/

abbrev TableSpec (row : Type u) : Type u :=
  FSet row

abbrev Table := TableSpec

structure FiniteTable (row : Type u) where
  rows : List row
  nodup : rows.Nodup

def FiniteTable.semantics (T : FiniteTable row) : TableSpec row :=
  FSet.OfList T.rows

abbrev insert (T : Table row) (r : row) : Table row :=
  FSet.Union T (FSet.Singleton r)

abbrev select (T : Table row) (P : row -> Prop) : Table row :=
  FSet.Inter T P

abbrev delete (T : Table row) (P : row -> Prop) : Table row :=
  fun r => r ∈ T ∧ ¬ P r

abbrev update (T : Table row) (P : row -> Prop) (u : row -> row) : Table row :=
  fun r' => (exists r, r ∈ T ∧ P r ∧ u r = r') ∨ (r' ∈ T ∧ ¬ P r')

def project (T : TableSpec row) (column : row -> value) : TableSpec value :=
  Fn.Image column T

def tableProduct (T : TableSpec row) (U : TableSpec other) :
    TableSpec (row × other) :=
  FSet.Product T U

def join (T : TableSpec row) (U : TableSpec other)
    (condition : row -> other -> Prop) : TableSpec (row × other) :=
  fun p => p.1 ∈ T ∧ p.2 ∈ U ∧ condition p.1 p.2

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
    r ∈ insert T r := by
  exact Or.inr rfl

theorem existing_row_present_after_insert {T : Table row} {old new : row}
    (h : old ∈ T) : old ∈ insert T new := by
  exact Or.inl h

theorem select_membership (T : Table row) (P : row -> Prop) (r : row) :
    r ∈ select T P <-> r ∈ T ∧ P r :=
  Iff.rfl

theorem delete_membership (T : Table row) (P : row -> Prop) (r : row) :
    r ∈ delete T P <-> r ∈ T ∧ ¬ P r :=
  Iff.rfl

theorem updated_row_present {T : Table row} {P : row -> Prop} {u : row -> row} {r : row}
    (hT : r ∈ T) (hP : P r) : u r ∈ update T P u := by
  exact Or.inl (Exists.intro r (And.intro hT (And.intro hP rfl)))

theorem unchanged_row_present_after_update {T : Table row} {P : row -> Prop}
    {u : row -> row} {r : row} (hT : r ∈ T) (hP : ¬ P r) :
    r ∈ update T P u := by
  exact Or.inr (And.intro hT hP)

theorem select_subset_table (T : Table row) (P : row -> Prop) :
    FSet.Subset (select T P) T := by
  intro r hr
  exact hr.left

theorem delete_subset_table (T : Table row) (P : row -> Prop) :
    FSet.Subset (delete T P) T := by
  intro r hr
  exact hr.left

theorem selected_rows_satisfy_predicate {T : Table row} {P : row -> Prop} {r : row}
    (hr : r ∈ select T P) : P r :=
  hr.right

theorem deleted_rows_do_not_satisfy_predicate {T : Table row} {P : row -> Prop} {r : row}
    (hr : r ∈ delete T P) : ¬ P r :=
  hr.right

theorem select_select_membership (T : Table row) (P Q : row -> Prop) (r : row) :
    r ∈ select (select T P) Q <-> r ∈ T ∧ P r ∧ Q r := by
  constructor
  · intro hr
    exact And.intro hr.left.left (And.intro hr.left.right hr.right)
  · intro hr
    exact And.intro (And.intro hr.left hr.right.left) hr.right.right

/-!
## Primary Keys

A primary key is modeled as injectivity of the key function on rows currently
in the table. Insertion preserves it when every old row with the new key is
already the inserted row. This permits idempotent reinsertion while excluding
a genuinely different row with a colliding key.
-/

theorem project_membership (T : TableSpec row) (column : row -> value) (v : value) :
    v ∈ project T column <-> exists r, r ∈ T ∧ column r = v :=
  Iff.rfl

theorem tableProduct_membership (T : TableSpec row) (U : TableSpec other)
    (p : row × other) :
    p ∈ tableProduct T U <-> p.1 ∈ T ∧ p.2 ∈ U :=
  Iff.rfl

theorem join_membership (T : TableSpec row) (U : TableSpec other)
    (condition : row -> other -> Prop) (p : row × other) :
    p ∈ join T U condition <-> p.1 ∈ T ∧ p.2 ∈ U ∧ condition p.1 p.2 :=
  Iff.rfl

theorem finiteTable_semantics_finite (T : FiniteTable row) :
    FSet.Finite T.semantics := by
  exact ⟨T.rows, fun _ => Iff.rfl⟩

theorem insert_preserves_primary_key {key : row -> keytype} {T : Table row} {new : row}
    (hpk : PrimaryKey key T)
    (hcompatible : forall old, old ∈ T -> key old = key new -> old = new) :
    PrimaryKey key (insert T new) := by
  intro r1 r2 h1 h2 hkey
  cases h1 with
  | inl h1old =>
      cases h2 with
      | inl h2old => exact hpk r1 r2 h1old h2old hkey
      | inr h2new =>
          have holdNew : r1 = new := hcompatible r1 h1old (by
            rw [← h2new]
            exact hkey)
          exact holdNew.trans h2new.symm
  | inr h1new =>
      cases h2 with
      | inl h2old =>
          have holdNew : r2 = new := hcompatible r2 h2old (by
            rw [← h1new]
            exact hkey.symm)
          exact h1new.trans holdNew.symm
      | inr h2new =>
          rw [h1new, h2new]

theorem select_preserves_primary_key {key : row -> keytype} {T : Table row}
    {P : row -> Prop} (hpk : PrimaryKey key T) :
    PrimaryKey key (select T P) := by
  intro r1 r2 h1 h2 hkey
  exact hpk r1 r2 h1.left h2.left hkey

theorem delete_preserves_primary_key {key : row -> keytype} {T : Table row}
    {P : row -> Prop} (hpk : PrimaryKey key T) :
    PrimaryKey key (delete T P) := by
  intro r1 r2 h1 h2 hkey
  exact hpk r1 r2 h1.left h2.left hkey

end Section08
end Chapter02
end Book
end FoC

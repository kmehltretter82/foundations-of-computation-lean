import FoC.Foundation
import FoC.Book.Chapter01.Section01
import FoC.Book.Chapter01.Section02
import FoC.Book.Chapter01.Section03
import FoC.Book.Chapter01.Section04
import FoC.Book.Chapter01.Section05
import FoC.Book.Chapter01.Section06
import FoC.Book.Chapter01.Section07
import FoC.Book.Chapter01.Section08
import FoC.Book.Chapter01.Section09
import FoC.Book.Chapter01.Section10

set_option doc.verso true

/-!
# Chapter 1: Logic and Proof

Chapter 1 is where the companion establishes the habit that every later chapter
uses: informal mathematical claims are translated into precise Lean statements,
and proof techniques become reusable theorem patterns.

The reusable definitions are mostly in {module}`FoC.Foundation`. The section
modules keep statements close to the book coordinates, while still using Lean
definitions that later chapters can reuse.

## Story of the Chapter

The chapter begins with truth-table semantics for propositional formulas, then
uses those semantics to explain Boolean algebra and deduction rules. The middle
sections shift from symbolic logic to proof patterns: direct proof,
contradiction, induction, and recursive definitions. The final sections use the
same methods on small mathematical objects such as parity predicates, rational
representations, finite sums, Fibonacci numbers, and binary trees.

## What to Inspect

Start with {module}`FoC.Book.Chapter01.Section01` and
{module}`FoC.Foundation.Logic` for the logic syntax and semantics. Then compare
the proof-method sections with the arithmetic support files:
{module}`FoC.Foundation.Arithmetic`, {module}`FoC.Foundation.Integers`,
{module}`FoC.Foundation.Primes`, and {module}`FoC.Foundation.Summation`.

Many short proofs are truth-table splits or induction, so the important content
is often the theorem type itself. It tells which informal statement has been
formalized, while the proof shows that Lean can check the required cases.

## Status Notes

The formal core of the chapter is covered. The propositional-logic and Boolean
algebra sections include truth-table equivalences, substitution laws, NOR
expressibility, and circuit/formula bridges. The circuit section now also links
the full-adder DNF tables to compact XOR and carry formulas, so the table,
formula, and gate-reading presentations are checked against one another.

The proof sections cover parity, divisibility, rational closure, irrational
real examples, contradiction, pigeonhole, induction, finite sums, recursive
definitions, Hanoi move counts, and binary-tree recursions. Recent cleanup
adds explicit odd-plus-odd, odd-times-odd, and even-sum induction wrappers.

Theorem 1.9, the induction proof that {lit}`n` propositional variables admit
exactly {lit}`2 ^ n` truth assignments, is formalized below as a counting
statement about the enumeration {lit}`truthAssignments` defined below.

Remaining deferrals are intentionally presentational: drawn circuit layouts,
long exercise lists whose Lean counterparts are already represented by more
general theorem schemas, and informal prose about proof-writing style.
-/

namespace FoC
namespace Book
namespace Chapter01

/-!
# Theorem 1.9: Counting Truth Assignments

Theorem 1.9 states that if a compound proposition contains exactly {lit}`n`
propositional variables, there are exactly {lit}`2 ^ n` ways of assigning
truth values to those variables. With the variables listed in a fixed order,
a truth assignment is a length-{lit}`n` list of Boolean values, one entry per
variable. The enumeration below doubles at each step, mirroring the book's
induction: every assignment for {lit}`n` variables extends to exactly two
assignments for {lit}`n + 1` variables, one per truth value of the new
variable.
-/

def truthAssignments : Nat -> List (List Bool)
  | 0 => [[]]
  | n + 1 =>
      (truthAssignments n).map (fun row => true :: row) ++
        (truthAssignments n).map (fun row => false :: row)

/-! The enumeration has exactly {lit}`2 ^ n` entries. -/
theorem truthAssignments_length (n : Nat) :
    (truthAssignments n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [truthAssignments, ih, Nat.pow_succ]
      lia

/-! Every entry of the enumeration assigns a truth value to exactly the
{lit}`n` listed variables. -/
theorem length_of_mem_truthAssignments {assignment : List Bool} {n : Nat}
    (h : assignment ∈ truthAssignments n) : assignment.length = n := by
  induction n generalizing assignment with
  | zero =>
      simp [truthAssignments] at h
      simp [h]
  | succ n ih =>
      simp [truthAssignments, List.mem_append, List.mem_map] at h
      cases h with
      | inl h =>
          cases h with
          | intro row hrow =>
              rw [← hrow.right]
              simp [ih hrow.left]
      | inr h =>
          cases h with
          | intro row hrow =>
              rw [← hrow.right]
              simp [ih hrow.left]

/-! The enumeration is complete: every truth assignment to the {lit}`n`
listed variables occurs in it. -/
theorem mem_truthAssignments_of_length {assignment : List Bool} {n : Nat}
    (h : assignment.length = n) : assignment ∈ truthAssignments n := by
  induction assignment generalizing n with
  | nil =>
      rw [← h]
      simp [truthAssignments]
  | cons b rest ih =>
      rw [← h]
      cases b
      · simp [truthAssignments, List.mem_append, List.mem_map]
        exact ih rfl
      · simp [truthAssignments, List.mem_append, List.mem_map]
        exact ih rfl

/-! The enumeration lists no assignment twice, so its length counts the
assignments exactly. The two halves of the doubling step are separately
duplicate-free, and they are disjoint because their entries disagree on the
newly added variable. -/
theorem truthAssignments_nodup (n : Nat) : (truthAssignments n).Nodup := by
  induction n with
  | zero => simp [truthAssignments]
  | succ n ih =>
      rw [truthAssignments, List.nodup_append]
      apply And.intro
      · rw [List.Nodup, List.pairwise_map]
        exact List.Pairwise.imp (fun hne heq => hne (List.cons.inj heq).right) ih
      apply And.intro
      · rw [List.Nodup, List.pairwise_map]
        exact List.Pairwise.imp (fun hne heq => hne (List.cons.inj heq).right) ih
      · intro a ha b hb
        rw [List.mem_map] at ha hb
        cases ha with
        | intro rowa hrowa =>
            cases hb with
            | intro rowb hrowb =>
                rw [← hrowa.right, ← hrowb.right]
                intro heq
                exact Bool.noConfusion (List.cons.inj heq).left

/-! Theorem 1.9 packaged: the enumeration of truth assignments on {lit}`n`
variables has exactly {lit}`2 ^ n` entries, contains no duplicates, and
contains precisely the length-{lit}`n` truth-value lists. -/
theorem truth_assignment_count (n : Nat) :
    (truthAssignments n).length = 2 ^ n ∧
      (truthAssignments n).Nodup ∧
      forall assignment : List Bool,
        assignment ∈ truthAssignments n <-> assignment.length = n := by
  apply And.intro (truthAssignments_length n)
  apply And.intro (truthAssignments_nodup n)
  intro assignment
  exact Iff.intro length_of_mem_truthAssignments mem_truthAssignments_of_length

end Chapter01
end Book
end FoC

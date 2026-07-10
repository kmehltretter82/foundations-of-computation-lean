import FoC.Book.Chapter01.Section08

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter01
namespace Section09

/-!
# Chapter 1, Section 1.9: Recursion and Induction Applications

This section formalizes the recursive kernels behind the book's application
examples. The source text discusses Java subroutines and data-structure
arguments; this file keeps the executable mathematics: Tower of Hanoi move
counts and structural recursion over binary trees.

The declarations show two faces of recursion. For Hanoi, recursion describes a
process; the proofs establish its legality, final configuration, and closed
form for its length. For trees,
recursion describes how a value is computed from subtrees, and induction over
the tree proves that two computations agree.
-/

/-! The factorial example belongs to the recursion application in this
section. Its equations are definitional. -/
def factorial : Nat -> Nat
  | 0 => 1
  | n + 1 => factorial n * (n + 1)

theorem factorial_succ (n : Nat) : factorial (n + 1) = factorial n * (n + 1) :=
  rfl

theorem factorial_zero : factorial 0 = 1 :=
  rfl

theorem factorial_one : factorial 1 = 1 :=
  rfl

theorem factorial_five : factorial 5 = 120 :=
  rfl

/-- The recursive move-count equation for the Tower of Hanoi puzzle. -/
def hanoiMoveCount : Nat -> Nat
  | 0 => 0
  | n + 1 => 2 * hanoiMoveCount n + 1

theorem hanoiMoveCount_succ (n : Nat) :
    hanoiMoveCount (n + 1) = 2 * hanoiMoveCount n + 1 :=
  rfl

theorem hanoiMoveCount_closed_form (n : Nat) :
    hanoiMoveCount n = 2 ^ n - 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [hanoiMoveCount, ih]
      rw [Nat.pow_succ]
      have hpos : 0 < 2 ^ n := Nat.pow_pos (by decide : 0 < 2)
      lia

/-!
The move list itself is also recursive: move the top stack to the spare peg,
move the bottom disk, and then move the saved stack to the target peg.

The theorem {lit}`hanoiMoves_length` connects the concrete list of moves to the
earlier recurrence for move counts, so the algorithm and the counting formula
are not separate stories.
-/

inductive Peg where
  | left : Peg
  | middle : Peg
  | right : Peg
deriving DecidableEq, Repr

def hanoiMoves : Nat -> Peg -> Peg -> Peg -> List (Peg × Peg)
  | 0, _, _, _ => []
  | n + 1, source, target, spare =>
      hanoiMoves n source spare target ++ [(source, target)] ++
        hanoiMoves n spare target source

theorem hanoiMoves_one (source target spare : Peg) :
    hanoiMoves 1 source target spare = [(source, target)] :=
  rfl

theorem hanoiMoves_two (source target spare : Peg) :
    hanoiMoves 2 source target spare =
      [(source, spare), (source, target), (spare, target)] :=
  rfl

theorem hanoiMoves_length (n : Nat) (source target spare : Peg) :
    (hanoiMoves n source target spare).length = hanoiMoveCount n := by
  induction n generalizing source target spare with
  | zero => rfl
  | succ n ih =>
      simp [hanoiMoves, hanoiMoveCount, ih]
      lia

/-!
**Legal Hanoi execution.** The source text's principal theorem concerns the
execution, not only its length. Disks are numbered from {lit}`0` (smallest)
upward. A move is legal when its disk is on the named source peg and every
smaller disk is on neither the source nor the target peg. Thus the moved disk
is exposed and is placed on no smaller disk.
-/

structure DiskMove where
  disk : Nat
  source : Peg
  target : Peg
deriving DecidableEq, Repr

abbrev HanoiConfig := Nat -> Peg

def LegalMove (config : HanoiConfig) (move : DiskMove) : Prop :=
  config move.disk = move.source ∧
    forall smaller, smaller < move.disk ->
      config smaller ≠ move.source ∧ config smaller ≠ move.target

def applyMove (config : HanoiConfig) (move : DiskMove) : HanoiConfig :=
  fun disk => if disk = move.disk then move.target else config disk

def legalMoveBool (config : HanoiConfig) (move : DiskMove) : Bool :=
  config move.disk == move.source &&
    (List.range move.disk).all fun smaller =>
      config smaller != move.source && config smaller != move.target

theorem legalMoveBool_eq_true (config : HanoiConfig) (move : DiskMove) :
    legalMoveBool config move = true <-> LegalMove config move := by
  simp [legalMoveBool, LegalMove, List.all_eq_true]

/-! Execute a list of moves, returning {lit}`none` at the first illegal move. -/
def runMoves : HanoiConfig -> List DiskMove -> Option HanoiConfig
  | config, [] => some config
  | config, move :: moves =>
      if legalMoveBool config move then
        runMoves (applyMove config move) moves
      else
        none

inductive Executes : HanoiConfig -> List DiskMove -> HanoiConfig -> Prop where
  | nil (config) : Executes config [] config
  | cons {config final : HanoiConfig} {move : DiskMove} {moves : List DiskMove} :
      LegalMove config move ->
      Executes (applyMove config move) moves final ->
      Executes config (move :: moves) final

theorem executes_iff_runMoves_eq_some (initial final : HanoiConfig) :
    forall moves, Executes initial moves final <-> runMoves initial moves = some final := by
  intro moves
  constructor
  · intro hexec
    induction hexec with
    | nil => rfl
    | cons hlegal _ ih =>
        simp [runMoves, (legalMoveBool_eq_true _ _).mpr hlegal, ih]
  · intro hrun
    induction moves generalizing initial with
    | nil =>
        simp [runMoves] at hrun
        subst final
        exact Executes.nil initial
    | cons move moves ih =>
        simp only [runMoves] at hrun
        by_cases hlegal : legalMoveBool initial move = true
        · rw [if_pos hlegal] at hrun
          exact Executes.cons ((legalMoveBool_eq_true _ _).mp hlegal)
            (ih (applyMove initial move) hrun)
        · rw [if_neg hlegal] at hrun
          contradiction

def hanoiDiskMoves : Nat -> Peg -> Peg -> Peg -> List DiskMove
  | 0, _, _, _ => []
  | n + 1, source, target, spare =>
      hanoiDiskMoves n source spare target ++
        [{ disk := n, source := source, target := target }] ++
        hanoiDiskMoves n spare target source

def DiskMove.erase (move : DiskMove) : Peg × Peg :=
  (move.source, move.target)

/-! Forgetting disk labels recovers the original textbook move list. -/
theorem hanoiDiskMoves_erase (n : Nat) (source target spare : Peg) :
    (hanoiDiskMoves n source target spare).map DiskMove.erase =
      hanoiMoves n source target spare := by
  induction n generalizing source target spare with
  | zero => rfl
  | succ n ih =>
      simp [hanoiDiskMoves, hanoiMoves, DiskMove.erase, ih]

theorem executes_append {initial middle final : HanoiConfig}
    {first second : List DiskMove}
    (hfirst : Executes initial first middle)
    (hsecond : Executes middle second final) :
    Executes initial (first ++ second) final := by
  induction hfirst with
  | nil => exact hsecond
  | cons hlegal hexec ih =>
      exact Executes.cons hlegal (ih hsecond)

def DistinctPegs (source target spare : Peg) : Prop :=
  source ≠ target ∧ source ≠ spare ∧ target ≠ spare

/-! The recursive algorithm's induction invariant. All relevant disks finish
on the target, larger disks are unchanged, and every step is legal. -/
theorem hanoiDiskMoves_solve : forall (n : Nat) (config : HanoiConfig)
    (source target spare : Peg),
    DistinctPegs source target spare ->
    (forall disk, disk < n -> config disk = source) ->
    exists final,
      Executes config (hanoiDiskMoves n source target spare) final ∧
        (forall disk, disk < n -> final disk = target) ∧
        (forall disk, n <= disk -> final disk = config disk) := by
  intro n
  induction n with
  | zero =>
      intro config source target spare _ _
      exact ⟨config, Executes.nil config, by simp, by simp⟩
  | succ n ih =>
      intro config source target spare hdistinct hsource
      rcases hdistinct with ⟨hst, hsa, hta⟩
      obtain ⟨afterFirst, hfirstExec, hfirstAtSpare, hfirstUnchanged⟩ :=
        ih config source spare target
          ⟨hsa, hst, Ne.symm hta⟩
          (fun disk hd => hsource disk (Nat.lt_succ_of_lt hd))
      let largest : DiskMove := { disk := n, source := source, target := target }
      let afterLargest := applyMove afterFirst largest
      have hlargestLegal : LegalMove afterFirst largest := by
        constructor
        · rw [hfirstUnchanged n (Nat.le_refl n)]
          exact hsource n (Nat.lt_succ_self n)
        · intro smaller hsmaller
          rw [hfirstAtSpare smaller hsmaller]
          exact ⟨Ne.symm hsa, Ne.symm hta⟩
      have hlargestExec : Executes afterFirst [largest] afterLargest :=
        Executes.cons hlargestLegal (Executes.nil afterLargest)
      obtain ⟨final, hsecondExec, hfinalAtTarget, hsecondUnchanged⟩ :=
        ih afterLargest spare target source
          ⟨Ne.symm hta, Ne.symm hsa, Ne.symm hst⟩
          (by
            intro disk hd
            simp [afterLargest, applyMove, largest, Nat.ne_of_lt hd,
              hfirstAtSpare disk hd])
      refine ⟨final, ?_, ?_, ?_⟩
      · simpa [hanoiDiskMoves, largest] using
          executes_append (executes_append hfirstExec hlargestExec) hsecondExec
      · intro disk hd
        by_cases heq : disk = n
        · rw [heq, hsecondUnchanged n (Nat.le_refl n)]
          simp [afterLargest, applyMove, largest]
        · apply hfinalAtTarget disk
          lia
      · intro disk hd
        rw [hsecondUnchanged disk (by lia)]
        simp [afterLargest, applyMove, largest, show disk ≠ n by lia]
        exact hfirstUnchanged disk (by lia)

def initialHanoiConfig (source : Peg) : HanoiConfig :=
  fun _ => source

/-! The principal Tower-of-Hanoi theorem: from the standard initial
configuration, the generated moves execute legally and put every puzzle disk
on the target peg. -/
theorem hanoiMoves_legally_solve (n : Nat) (source target spare : Peg)
    (hdistinct : DistinctPegs source target spare) :
    exists final,
      Executes (initialHanoiConfig source)
        (hanoiDiskMoves n source target spare) final ∧
      forall disk, disk < n -> final disk = target := by
  obtain ⟨final, hexec, htarget, _⟩ :=
    hanoiDiskMoves_solve n (initialHanoiConfig source) source target spare
      hdistinct (by simp [initialHanoiConfig])
  exact ⟨final, hexec, htarget⟩

theorem hanoiMoves_run_succeeds (n : Nat) (source target spare : Peg)
    (hdistinct : DistinctPegs source target spare) :
    exists final,
      runMoves (initialHanoiConfig source)
        (hanoiDiskMoves n source target spare) = some final ∧
      forall disk, disk < n -> final disk = target := by
  obtain ⟨final, hexec, htarget⟩ :=
    hanoiMoves_legally_solve n source target spare hdistinct
  exact ⟨final, (executes_iff_runMoves_eq_some _ _ _).mp hexec, htarget⟩

/-!
**Binary trees.**

The binary-tree definitions show structural recursion: every computation over a
tree is determined by the empty-tree case and the node case. The final theorem
connects the recursive tree sum with the sum of the list obtained by an inorder
traversal.

The point of the final equality is representation independence. Summing by
following the tree shape and summing after flattening by inorder traversal give
the same integer.
-/

inductive BinaryTree where
  | empty : BinaryTree
  | node : BinaryTree -> Int -> BinaryTree -> BinaryTree

def treeSum : BinaryTree -> Int
  | BinaryTree.empty => 0
  | BinaryTree.node left value right => treeSum left + value + treeSum right

def nodeCount : BinaryTree -> Nat
  | BinaryTree.empty => 0
  | BinaryTree.node left _ right => nodeCount left + 1 + nodeCount right

def leafCount : BinaryTree -> Nat
  | BinaryTree.empty => 0
  | BinaryTree.node BinaryTree.empty _ BinaryTree.empty => 1
  | BinaryTree.node left _ right => leafCount left + leafCount right

def intListSum : List Int -> Int
  | [] => 0
  | x :: xs => x + intListSum xs

def treeValues : BinaryTree -> List Int
  | BinaryTree.empty => []
  | BinaryTree.node left value right => treeValues left ++ [value] ++ treeValues right

def leafValues : BinaryTree -> List Int
  | BinaryTree.empty => []
  | BinaryTree.node BinaryTree.empty value BinaryTree.empty => [value]
  | BinaryTree.node left _ right => leafValues left ++ leafValues right

theorem treeSum_empty : treeSum BinaryTree.empty = 0 :=
  rfl

theorem treeSum_node (left right : BinaryTree) (value : Int) :
    treeSum (BinaryTree.node left value right) = treeSum left + value + treeSum right :=
  rfl

theorem intListSum_append (xs ys : List Int) :
    intListSum (xs ++ ys) = intListSum xs + intListSum ys := by
  induction xs with
  | nil => simp [intListSum]
  | cons x xs ih => simp [intListSum, ih, Int.add_assoc]

theorem treeSum_eq_intListSum (t : BinaryTree) :
    treeSum t = intListSum (treeValues t) := by
  induction t with
  | empty => rfl
  | node left value right ihl ihr =>
      simp [treeSum, treeValues, intListSum_append, intListSum, ihl, ihr]
      lia

theorem nodeCount_empty : nodeCount BinaryTree.empty = 0 :=
  rfl

theorem nodeCount_node (left right : BinaryTree) (value : Int) :
    nodeCount (BinaryTree.node left value right) = nodeCount left + 1 + nodeCount right :=
  rfl

theorem leafCount_empty : leafCount BinaryTree.empty = 0 :=
  rfl

theorem leafCount_singleton (value : Int) :
    leafCount (BinaryTree.node BinaryTree.empty value BinaryTree.empty) = 1 :=
  rfl

/-!
The leaf-count exercise is represented by an independent leaf enumeration. The
recursive counter agrees with the length of that enumeration for every tree.
-/
theorem leafCount_eq_leafValues_length (t : BinaryTree) :
    leafCount t = (leafValues t).length := by
  induction t with
  | empty =>
      rfl
  | node left value right ihLeft ihRight =>
      cases left <;> cases right <;>
        simp [leafCount, leafValues, ihLeft, ihRight]

end Section09
end Chapter01
end Book
end FoC

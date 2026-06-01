import FoC.Book.Chapter01.Section08

namespace FoC
namespace Book
namespace Chapter01
namespace Section09

/-!
Book: Chapter 1, Section 1.9, Application: Recursion and Induction.

The Java subroutines and data-structure proofs are classified in coverage as
application material. This file formalizes the recursive mathematical kernels.
-/

def hanoiMoveCount : Nat -> Nat
  | 0 => 0
  | n + 1 => 2 * hanoiMoveCount n + 1

-- Book: Chapter 1, Section 1.9, Hanoi recurrence
theorem hanoiMoveCount_succ (n : Nat) :
    hanoiMoveCount (n + 1) = 2 * hanoiMoveCount n + 1 :=
  rfl

-- Book: Chapter 1, Section 1.9, Hanoi closed-form move count.
theorem hanoiMoveCount_closed_form (n : Nat) :
    hanoiMoveCount n = 2 ^ n - 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [hanoiMoveCount, ih]
      rw [Nat.pow_succ]
      have hpos : 0 < 2 ^ n := Nat.pow_pos (by decide : 0 < 2)
      omega

inductive Peg where
  | left : Peg
  | middle : Peg
  | right : Peg

def hanoiMoves : Nat -> Peg -> Peg -> Peg -> List (Peg × Peg)
  | 0, _, _, _ => []
  | n + 1, source, target, spare =>
      hanoiMoves n source spare target ++ [(source, target)] ++
        hanoiMoves n spare target source

-- Book: Chapter 1, Section 1.9, the recursive Hanoi program has the expected length.
theorem hanoiMoves_length (n : Nat) (source target spare : Peg) :
    (hanoiMoves n source target spare).length = hanoiMoveCount n := by
  induction n generalizing source target spare with
  | zero => rfl
  | succ n ih =>
      simp [hanoiMoves, hanoiMoveCount, ih]
      omega

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

-- Book: Chapter 1, Section 1.9, TreeSum base case
theorem treeSum_empty : treeSum BinaryTree.empty = 0 :=
  rfl

-- Book: Chapter 1, Section 1.9, TreeSum recursive case
theorem treeSum_node (left right : BinaryTree) (value : Int) :
    treeSum (BinaryTree.node left value right) = treeSum left + value + treeSum right :=
  rfl

theorem intListSum_append (xs ys : List Int) :
    intListSum (xs ++ ys) = intListSum xs + intListSum ys := by
  induction xs with
  | nil => simp [intListSum]
  | cons x xs ih => simp [intListSum, ih, Int.add_assoc]

-- Book: Chapter 1, Section 1.9, TreeSum equals a traversal sum.
theorem treeSum_eq_intListSum (t : BinaryTree) :
    treeSum t = intListSum (treeValues t) := by
  induction t with
  | empty => rfl
  | node left value right ihl ihr =>
      simp [treeSum, treeValues, intListSum_append, intListSum, ihl, ihr]
      omega

-- Book: Chapter 1, Section 1.9, NodeCount base case
theorem nodeCount_empty : nodeCount BinaryTree.empty = 0 :=
  rfl

-- Book: Chapter 1, Section 1.9, NodeCount recursive case
theorem nodeCount_node (left right : BinaryTree) (value : Int) :
    nodeCount (BinaryTree.node left value right) = nodeCount left + 1 + nodeCount right :=
  rfl

-- Book: Chapter 1, Section 1.9, LeafCount base case
theorem leafCount_empty : leafCount BinaryTree.empty = 0 :=
  rfl

-- Book: Chapter 1, Section 1.9, a one-node tree has one leaf.
theorem leafCount_singleton (value : Int) :
    leafCount (BinaryTree.node BinaryTree.empty value BinaryTree.empty) = 1 :=
  rfl

end Section09
end Chapter01
end Book
end FoC

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

-- Book: Chapter 1, Section 1.9, TreeSum base case
theorem treeSum_empty : treeSum BinaryTree.empty = 0 :=
  rfl

-- Book: Chapter 1, Section 1.9, LeafCount base case
theorem leafCount_empty : leafCount BinaryTree.empty = 0 :=
  rfl

end Section09
end Chapter01
end Book
end FoC


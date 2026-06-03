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
process and the proof extracts a closed form for its length. For trees,
recursion describes how a value is computed from subtrees, and induction over
the tree proves that two computations agree.
-/

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
      omega

/-!
The move list itself is also recursive: move the top stack to the spare peg,
move the bottom disk, and then move the saved stack to the target peg.

The theorem `hanoiMoves_length` connects the concrete list of moves to the
earlier recurrence for move counts, so the algorithm and the counting formula
are not separate stories.
-/

inductive Peg where
  | left : Peg
  | middle : Peg
  | right : Peg

def hanoiMoves : Nat -> Peg -> Peg -> Peg -> List (Peg × Peg)
  | 0, _, _, _ => []
  | n + 1, source, target, spare =>
      hanoiMoves n source spare target ++ [(source, target)] ++
        hanoiMoves n spare target source

theorem hanoiMoves_length (n : Nat) (source target spare : Peg) :
    (hanoiMoves n source target spare).length = hanoiMoveCount n := by
  induction n generalizing source target spare with
  | zero => rfl
  | succ n ih =>
      simp [hanoiMoves, hanoiMoveCount, ih]
      omega

/-!
# Binary Trees

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
      omega

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

end Section09
end Chapter01
end Book
end FoC

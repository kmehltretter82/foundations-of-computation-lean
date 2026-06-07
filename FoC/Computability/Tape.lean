import FoC.Languages.Words

set_option doc.verso true

/-!
# Tapes

## Finite tape windows

The book's tape is infinite in both directions and blank except for finitely
many cells.  We represent the finite visible window by a left context, current
cell, and right context.  Cells outside the stored lists are blank, represented
by {lit}`none`.

## Book coordinates

Used by:
- Chapter 5, Section 5.1: Turing-machine tapes, reading, writing, and moving.
-/

namespace FoC
namespace Computability

open Languages

/-!
# Directions and tape representation

The tape stores only a finite window around the head. Moving beyond the stored
window exposes a blank cell.
-/

inductive Direction where
  | left : Direction
  | right : Direction
deriving DecidableEq

structure Tape (symbol : Type u) where
  left : List (Option symbol)
  head : Option symbol
  right : List (Option symbol)
deriving DecidableEq

namespace Tape

/-!
# Basic tape operations

Input and output words are loaded into the visible window; reading, writing,
and moving update only the local head and neighboring contexts.
-/

def blank : Tape symbol where
  left := []
  head := none
  right := []

def input : Word symbol -> Tape symbol
  | [] => blank
  | a :: rest =>
      { left := [], head := some a, right := rest.map some }

def read (T : Tape symbol) : Option symbol :=
  T.head

def write (cell : Option symbol) (T : Tape symbol) : Tape symbol :=
  { T with head := cell }

def moveLeft (T : Tape symbol) : Tape symbol :=
  match T.left with
  | [] => { left := [], head := none, right := T.head :: T.right }
  | cell :: rest => { left := rest, head := cell, right := T.head :: T.right }

def moveRight (T : Tape symbol) : Tape symbol :=
  match T.right with
  | [] => { left := T.head :: T.left, head := none, right := [] }
  | cell :: rest => { left := T.head :: T.left, head := cell, right := rest }

def move : Direction -> Tape symbol -> Tape symbol
  | Direction.left, T => moveLeft T
  | Direction.right, T => moveRight T

def output (w : Word symbol) : Tape symbol :=
  input w

def cells (T : Tape symbol) : List (Option symbol) :=
  T.left.reverse ++ T.head :: T.right

def normalizedOutput (T : Tape symbol) : Word symbol :=
  (cells T).filterMap (fun cell => cell)

def contextLength (T : Tape symbol) : Nat :=
  T.left.length + T.right.length

/-!
# Operation laws

These small equations and injectivity facts are the reusable interface for the
Turing-machine configuration layer.
-/

theorem read_write (cell : Option symbol) (T : Tape symbol) :
    read (write cell T) = cell :=
  rfl

theorem input_empty : input ([] : Word symbol) = blank :=
  rfl

theorem output_empty : output ([] : Word symbol) = blank :=
  rfl

theorem normalizedOutput_empty :
    normalizedOutput (blank : Tape symbol) = [] :=
  rfl

theorem contextLength_blank : contextLength (blank : Tape symbol) = 0 :=
  rfl

theorem contextLength_output_single (a : symbol) :
    contextLength (output [a]) = 0 :=
  rfl

theorem input_cons (a : symbol) (rest : Word symbol) :
    input (a :: rest) = { left := [], head := some a, right := rest.map some } :=
  rfl

theorem filterMap_id_map_some (w : Word symbol) :
    (w.map (fun a => some a)).filterMap (fun cell => cell) = w := by
  induction w with
  | nil => rfl
  | cons a rest ih =>
      simp [ih]

theorem normalizedOutput_output (w : Word symbol) :
    normalizedOutput (output w) = w := by
  cases w with
  | nil => rfl
  | cons a rest =>
      change
        a :: ((rest.map (fun a => some a)).filterMap (fun cell => cell)) =
          a :: rest
      rw [filterMap_id_map_some]

theorem normalizedOutput_of_eq_output {T : Tape symbol} {w : Word symbol}
    (h : T = output w) :
    normalizedOutput T = w := by
  rw [h, normalizedOutput_output]

theorem list_map_some_injective {xs ys : List symbol}
    (h : xs.map some = ys.map some) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons _ _ => simp at h
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          simp at h
          cases h.left
          rw [ih h.right]

theorem input_injective : Function.Injective (input : Word symbol -> Tape symbol) := by
  intro x y h
  cases x with
  | nil =>
      cases y with
      | nil => rfl
      | cons _ _ =>
          have hhead := congrArg Tape.head h
          simp [input, blank] at hhead
  | cons _ _ =>
      cases y with
      | nil =>
          have hhead := congrArg Tape.head h
          simp [input, blank] at hhead
      | cons _ _ =>
          have hhead := congrArg Tape.head h
          have hright := congrArg Tape.right h
          simp [input] at hhead hright
          cases hhead
          rw [list_map_some_injective hright]

theorem output_injective : Function.Injective (output : Word symbol -> Tape symbol) := by
  intro x y h
  exact input_injective h

theorem contextLength_move_write_ge (dir : Direction) (cell : Option symbol)
    (T : Tape symbol) :
    contextLength T ≤ contextLength (move dir (write cell T)) := by
  cases T with
  | mk left head right =>
      cases dir with
      | left =>
          cases left with
          | nil =>
              simp [contextLength, move, moveLeft, write]
          | cons leftHead leftTail =>
              simp [contextLength, move, moveLeft, write]
              omega
      | right =>
          cases right with
          | nil =>
              simp [contextLength, move, moveRight, write]
          | cons rightHead rightTail =>
              simp [contextLength, move, moveRight, write]
              omega

theorem read_input_cons (a : symbol) (rest : Word symbol) :
    read (input (a :: rest)) = some a :=
  rfl

theorem move_left_after_write (cell : Option symbol) (T : Tape symbol) :
    move Direction.left (write cell T) = moveLeft (write cell T) :=
  rfl

theorem move_right_after_write (cell : Option symbol) (T : Tape symbol) :
    move Direction.right (write cell T) = moveRight (write cell T) :=
  rfl

end Tape

end Computability
end FoC

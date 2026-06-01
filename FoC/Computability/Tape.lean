import FoC.Languages.Words

namespace FoC
namespace Computability

/-!
Finite-window tapes for Turing machines.

The book's tape is infinite in both directions and blank except for finitely
many cells.  We represent the finite visible window by a left context, current
cell, and right context.  Cells outside the stored lists are blank, represented
by `none`.

Used by:
- Chapter 5, Section 5.1: Turing-machine tapes, reading, writing, and moving.
-/

open Languages

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

theorem read_write (cell : Option symbol) (T : Tape symbol) :
    read (write cell T) = cell :=
  rfl

theorem input_empty : input ([] : Word symbol) = blank :=
  rfl

theorem output_empty : output ([] : Word symbol) = blank :=
  rfl

theorem input_cons (a : symbol) (rest : Word symbol) :
    input (a :: rest) = { left := [], head := some a, right := rest.map some } :=
  rfl

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

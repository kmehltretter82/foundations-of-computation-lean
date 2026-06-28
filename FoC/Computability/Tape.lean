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

theorem normalizedOutput_moveLeft (T : Tape symbol) :
    normalizedOutput (moveLeft T) = normalizedOutput T := by
  cases T with
  | mk left head right =>
      cases left with
      | nil =>
          simp [moveLeft, normalizedOutput, cells]
      | cons leftHead leftTail =>
          simp [moveLeft, normalizedOutput, cells, List.reverse_cons,
            List.append_assoc]

theorem normalizedOutput_moveRight (T : Tape symbol) :
    normalizedOutput (moveRight T) = normalizedOutput T := by
  cases T with
  | mk left head right =>
      cases right with
      | nil =>
          cases head <;>
            simp [moveRight, normalizedOutput, cells, List.reverse_cons,
              List.append_assoc]
      | cons rightHead rightTail =>
          simp [moveRight, normalizedOutput, cells, List.reverse_cons,
            List.append_assoc]

theorem normalizedOutput_move (dir : Direction) (T : Tape symbol) :
    normalizedOutput (move dir T) = normalizedOutput T := by
  cases dir with
  | left => exact normalizedOutput_moveLeft T
  | right => exact normalizedOutput_moveRight T

theorem move_left_move_right_eq_self_of_right_cons
    (T : Tape symbol) {cell : Option symbol} {right : List (Option symbol)}
    (h : T.right = cell :: right) :
    move Direction.left (move Direction.right T) = T := by
  cases T with
  | mk left head rightCells =>
      cases h
      simp [move, moveLeft, moveRight]

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

/-!
# Tape Equivalence

We define `Tape.Equiv` to ignore trailing blanks (none) on both ends of the tape.
-/

def dropTrailingNone {symbol} : List (Option symbol) -> List (Option symbol)
  | [] => []
  | none :: xs =>
      let rest := dropTrailingNone xs
      if rest = [] then [] else none :: rest
  | some x :: xs => some x :: dropTrailingNone xs

def Equiv {symbol} (T1 T2 : Tape symbol) : Prop :=
  dropTrailingNone T1.left = dropTrailingNone T2.left ∧
  T1.head = T2.head ∧
  dropTrailingNone T1.right = dropTrailingNone T2.right

theorem Equiv.refl {symbol} (T : Tape symbol) :
  Equiv T T :=
⟨rfl, rfl, rfl⟩

theorem Equiv.symm {symbol} {T U : Tape symbol} :
  Equiv T U -> Equiv U T :=
fun ⟨hl, hh, hr⟩ => ⟨hl.symm, hh.symm, hr.symm⟩

theorem Equiv.trans {symbol} {T U V : Tape symbol} :
  Equiv T U -> Equiv U V -> Equiv T V :=
fun ⟨hl1, hh1, hr1⟩ ⟨hl2, hh2, hr2⟩ => ⟨hl1.trans hl2, hh1.trans hh2, hr1.trans hr2⟩

theorem Equiv.read_eq {symbol} {T U : Tape symbol} :
  Equiv T U -> Tape.read T = Tape.read U :=
fun ⟨_, hh, _⟩ => hh

theorem Equiv.write {symbol} {T U : Tape symbol}
    (h : Equiv T U) (cell : Option symbol) :
  Equiv (Tape.write cell T) (Tape.write cell U) :=
⟨h.1, rfl, h.2.2⟩

/-!
# Equivalence helpers
-/

theorem dropTrailingNone_cons {symbol} (x : Option symbol) (xs : List (Option symbol)) :
    dropTrailingNone (x :: xs) =
      if x = none ∧ dropTrailingNone xs = [] then [] else x :: dropTrailingNone xs := by
  cases x <;> simp [dropTrailingNone]

def getHead {symbol} (xs : List (Option symbol)) : Option symbol :=
  match xs with | [] => none | x :: _ => x

def getTail {symbol} (xs : List (Option symbol)) : List (Option symbol) :=
  match xs with | [] => [] | _ :: rest => rest

theorem getHead_dropTrailingNone {symbol} (xs : List (Option symbol)) :
    getHead (dropTrailingNone xs) = getHead xs := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    rw [dropTrailingNone_cons]
    split
    · next h =>
      rcases h with ⟨hx, hxs⟩
      rw [hx]
      rfl
    · rfl

theorem dropTrailingNone_idem {symbol} (xs : List (Option symbol)) :
    dropTrailingNone (dropTrailingNone xs) = dropTrailingNone xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [dropTrailingNone_cons]
    split
    · next h =>
      rcases h with ⟨hx, hxs⟩
      rfl
    · next h =>
      rw [dropTrailingNone_cons]
      rw [ih]
      split
      · next h' =>
        rcases h' with ⟨hx', hxs'⟩
        exact False.elim (h ⟨hx', hxs'⟩)
      · rfl

theorem getTail_dropTrailingNone {symbol} (xs : List (Option symbol)) :
    dropTrailingNone (getTail (dropTrailingNone xs)) = dropTrailingNone (getTail xs) := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    rw [dropTrailingNone_cons]
    split
    · next h =>
      rcases h with ⟨hx, hxs⟩
      simp [getTail]
      rw [hxs]
      rfl
    · simp [getTail, dropTrailingNone_idem]

theorem getHead_eq_of_dropTrailingNone_eq {symbol} {xs ys : List (Option symbol)}
    (h : dropTrailingNone xs = dropTrailingNone ys) : getHead xs = getHead ys := by
  rw [← getHead_dropTrailingNone xs, h, getHead_dropTrailingNone]

theorem getTail_eq_of_dropTrailingNone_eq {symbol} {xs ys : List (Option symbol)}
    (h : dropTrailingNone xs = dropTrailingNone ys) :
    dropTrailingNone (getTail xs) = dropTrailingNone (getTail ys) := by
  rw [← getTail_dropTrailingNone xs, h, getTail_dropTrailingNone]

theorem dropTrailingNone_cons_eq {symbol} {x y : Option symbol} {xs ys : List (Option symbol)}
    (hx : x = y) (hxs : dropTrailingNone xs = dropTrailingNone ys) :
    dropTrailingNone (x :: xs) = dropTrailingNone (y :: ys) := by
  rw [hx, dropTrailingNone_cons, dropTrailingNone_cons, hxs]

theorem moveLeft_left {symbol} (T : Tape symbol) : (Tape.moveLeft T).left = getTail T.left := by
  cases T with | mk left head right => cases left <;> rfl
theorem moveLeft_head {symbol} (T : Tape symbol) : (Tape.moveLeft T).head = getHead T.left := by
  cases T with | mk left head right => cases left <;> rfl
theorem moveLeft_right {symbol} (T : Tape symbol) : (Tape.moveLeft T).right = T.head :: T.right := by
  cases T with | mk left head right => cases left <;> rfl

theorem moveRight_left {symbol} (T : Tape symbol) : (Tape.moveRight T).left = T.head :: T.left := by
  cases T with | mk left head right => cases right <;> rfl
theorem moveRight_head {symbol} (T : Tape symbol) : (Tape.moveRight T).head = getHead T.right := by
  cases T with | mk left head right => cases right <;> rfl
theorem moveRight_right {symbol} (T : Tape symbol) : (Tape.moveRight T).right = getTail T.right := by
  cases T with | mk left head right => cases right <;> rfl

/-!
# Main Equiv Proofs
-/

theorem Equiv.moveLeft {symbol} {T1 T2 : Tape symbol}
    (h : Equiv T1 T2) : Equiv (Tape.moveLeft T1) (Tape.moveLeft T2) := by
  have h_left : dropTrailingNone T1.left = dropTrailingNone T2.left := h.1
  have h_head : T1.head = T2.head := h.2.1
  have h_right : dropTrailingNone T1.right = dropTrailingNone T2.right := h.2.2
  
  constructor
  · rw [moveLeft_left, moveLeft_left]
    exact getTail_eq_of_dropTrailingNone_eq h_left
  · constructor
    · rw [moveLeft_head, moveLeft_head]
      exact getHead_eq_of_dropTrailingNone_eq h_left
    · rw [moveLeft_right, moveLeft_right]
      exact dropTrailingNone_cons_eq h_head h_right

theorem Equiv.moveRight {symbol} {T1 T2 : Tape symbol}
    (h : Equiv T1 T2) : Equiv (Tape.moveRight T1) (Tape.moveRight T2) := by
  have h_left : dropTrailingNone T1.left = dropTrailingNone T2.left := h.1
  have h_head : T1.head = T2.head := h.2.1
  have h_right : dropTrailingNone T1.right = dropTrailingNone T2.right := h.2.2
  
  constructor
  · rw [moveRight_left, moveRight_left]
    exact dropTrailingNone_cons_eq h_head h_left
  · constructor
    · rw [moveRight_head, moveRight_head]
      exact getHead_eq_of_dropTrailingNone_eq h_right
    · rw [moveRight_right, moveRight_right]
      exact getTail_eq_of_dropTrailingNone_eq h_right

theorem Equiv.move {symbol} {T1 T2 : Tape symbol}
    (h : Equiv T1 T2) (dir : Direction) : Equiv (Tape.move dir T1) (Tape.move dir T2) := by
  cases dir
  · exact Equiv.moveLeft h
  · exact Equiv.moveRight h

/-!
# Normalized Output helpers
-/

theorem filterMap_dropTrailingNone {symbol} (xs : List (Option symbol)) :
    (dropTrailingNone xs).filterMap (fun x => x) = xs.filterMap (fun x => x) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [dropTrailingNone_cons]
    split
    · next h =>
      rcases h with ⟨hx, hxs⟩
      have h1 : xs.filterMap (fun x => x) = [] := by
        rw [← ih, hxs]
        rfl
      rw [hx]
      simp [h1]
    · cases x
      · simp [ih]
      · simp [ih]

theorem filterMap_reverse {symbol} (xs : List (Option symbol)) :
    xs.reverse.filterMap (fun x => x) = (xs.filterMap (fun x => x)).reverse := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [ih]
    cases x
    · simp
    · simp

theorem filterMap_append_lemma {symbol} (xs ys : List (Option symbol)) :
    (xs ++ ys).filterMap (fun x => x) = xs.filterMap (fun x => x) ++ ys.filterMap (fun x => x) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases x <;> simp [ih]

theorem filterMap_cons_eq {symbol} (x : Option symbol) (xs ys : List (Option symbol))
    (h : xs.filterMap (fun c => c) = ys.filterMap (fun c => c)) :
    (x :: xs).filterMap (fun c => c) = (x :: ys).filterMap (fun c => c) := by
  cases x <;> simp [h]

theorem Equiv.normalizedOutput_eq {symbol} {T1 T2 : Tape symbol}
    (h : Equiv T1 T2) : normalizedOutput T1 = normalizedOutput T2 := by
  have h_left : dropTrailingNone T1.left = dropTrailingNone T2.left := h.1
  have h_head : T1.head = T2.head := h.2.1
  have h_right : dropTrailingNone T1.right = dropTrailingNone T2.right := h.2.2

  have h_filter_left : T1.left.filterMap (fun cell => cell) = T2.left.filterMap (fun cell => cell) := by
    rw [← filterMap_dropTrailingNone T1.left, ← filterMap_dropTrailingNone T2.left, h_left]
  
  have h_filter_right : T1.right.filterMap (fun cell => cell) = T2.right.filterMap (fun cell => cell) := by
    rw [← filterMap_dropTrailingNone T1.right, ← filterMap_dropTrailingNone T2.right, h_right]

  unfold normalizedOutput cells
  rw [filterMap_append_lemma, filterMap_append_lemma]
  rw [filterMap_reverse, filterMap_reverse, h_filter_left]
  have h_filter_right_cons : List.filterMap (fun cell => cell) (T1.head :: T1.right) = List.filterMap (fun cell => cell) (T2.head :: T2.right) := by
    rw [h_head]
    exact filterMap_cons_eq _ _ _ h_filter_right
  rw [h_filter_right_cons]

end Tape

end Computability
end FoC

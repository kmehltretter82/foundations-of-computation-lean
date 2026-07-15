import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.Compaction
import FoC.Computability.Compiler.Structured.Lowering.Projection

set_option doc.verso true

/-!
# Pair-encoded option-cell ingress shapes

Shared pair encoding and guarded-ingress shapes used by the live
marker-delimited selected-footprint compactor and its contract guardrails.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering
namespace PairEncodedOptionCellCompactor

def markerCell : Option Bool := some true

@[simp] theorem replicate_markerCell_add_one (n : Nat) :
    List.replicate (n + 1) markerCell =
      markerCell :: List.replicate n markerCell := by
  simp [markerCell, List.replicate_succ]

@[simp] theorem replicate_some_true_add_one (n : Nat) :
    List.replicate (n + 1) (some true : Option Bool) =
      some true :: List.replicate n (some true : Option Bool) := by
  simpa [markerCell] using replicate_markerCell_add_one n

def encodedCells (cells : List (Option Bool)) : List (Option Bool) :=
  (cells.map selectedSegmentLogicalTapeDecoderCellCells).flatten

@[simp] theorem selectedSegmentLogicalTapeDecoderCellCells_eq_pair
    (cell : Option Bool) :
    selectedSegmentLogicalTapeDecoderCellCells cell = [none, cell] := by
  cases cell with
  | none =>
      rfl
  | some bit =>
      rfl

@[simp] theorem encodedCells_nil :
    encodedCells [] = [] := by
  rfl

@[simp] theorem encodedCells_cons
    (cell : Option Bool) (rest : List (Option Bool)) :
    encodedCells (cell :: rest) = none :: cell :: encodedCells rest := by
  simp [encodedCells]

theorem encodedCells_append
    (left right : List (Option Bool)) :
    encodedCells (left ++ right) = encodedCells left ++ encodedCells right := by
  induction left with
  | nil =>
      rfl
  | cons cell rest ih =>
      simp [ih]

theorem encodedCells_append_singleton
    (cells : List (Option Bool)) (boundary : Option Bool) :
    encodedCells (cells ++ [boundary]) =
      encodedCells cells ++ [none, boundary] := by
  simp [encodedCells_append]

@[simp] theorem encodedCells_eq_nil_iff
    (cells : List (Option Bool)) :
    encodedCells cells = [] ↔ cells = [] := by
  cases cells <;> simp

theorem encodedCells_inj
    {xs ys : List (Option Bool)}
    (h : encodedCells xs = encodedCells ys) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys =>
          simp at h
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp at h
      | cons y ys =>
          simp only [encodedCells_cons] at h
          injection h with _ hrest
          injection hrest with hxy htail
          subst y
          rw [ih htail]

@[simp] theorem mappedSelectedCells_flatten_eq_nil_iff
    (cells : List (Option Bool)) :
    (List.map selectedSegmentLogicalTapeDecoderCellCells cells).flatten = [] ↔
      cells = [] := by
  simpa [encodedCells] using encodedCells_eq_nil_iff cells

@[simp] theorem forall_not_mem_option_bool_iff_eq_nil
    (cells : List (Option Bool)) :
    (forall cell : Option Bool, ¬ cell ∈ cells) ↔ cells = [] := by
  constructor
  · intro h
    cases cells with
    | nil =>
        rfl
    | cons cell rest =>
        exact False.elim (h cell (by simp))
  · intro h cell hmem
    simp [h] at hmem

def sourceTapeAt
    (consumed remaining : List (Option Bool)) : Tape Bool :=
  tapeAtCells (encodedCells consumed).reverse (encodedCells remaining)

def sourceTape (cells : List (Option Bool)) : Tape Bool :=
  sourceTapeAt [] cells

def markerTapeAt (used remaining : Nat) : Tape Bool :=
  tapeAtCells
    (List.replicate used markerCell)
    (List.replicate remaining markerCell)

def markerTape (count : Nat) : Tape Bool :=
  markerTapeAt 0 count

def outputTape (out : List (Option Bool)) : Tape Bool :=
  tapeAtCells out.reverse []

/-!
## Pair-encoded payload ingress

These names isolate the shared one-tape-to-guarded-three-tape ingress shape for
payloads encoded as pairs of physical cells. The source tape has a fixed
left-side prefix followed by pair-encoded payload cells and a right boundary;
the guarded target exposes the payload as the compactor's source tape, a marker
tape with one marker per payload cell, and an initially blank output tape.
-/

def fixedPrefixPayloadIngressSourceTape
    (fixedPrefix payload : List (Option Bool)) : Tape Bool :=
  rightEndCompactionSourceTape
    (none ::
      List.append (List.append fixedPrefix (encodedCells payload)) [none])

def payloadIngressTargetTape
    (payload : List (Option Bool)) : Tape Bool :=
  encodedGuardedStructured3Tapes
    (sourceTape payload)
    (markerTape payload.length)
    (outputTape [])

end PairEncodedOptionCellCompactor
end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC

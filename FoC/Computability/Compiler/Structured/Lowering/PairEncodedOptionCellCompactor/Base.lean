import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.Compaction
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredInputMaterializer
import FoC.Computability.Compiler.Structured.Lowering.Projection
import FoC.Computability.Compiler.Structured.Lowering.ConcreteRefresh
import FoC.Computability.Compiler.Structured.Lowering.ThreeTapeTactic
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTableChecks

set_option doc.verso true

/-!
# Pair-encoded option-cell compactor

This module contains a small lowerer-facing three-tape component for the
selected-footprint compaction route.  Tape 0 carries cells encoded as
{lit}`[none, cell]`, tape 1 carries one marker per decoded cell, and tape 2 receives
all decoded cells except the final pending boundary cell.
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

def dropLastWithPending
    (pending : Option Bool) : List (Option Bool) -> List (Option Bool)
  | [] => []
  | cell :: rest => pending :: dropLastWithPending cell rest

def dropFinalCell : List (Option Bool) -> List (Option Bool)
  | [] => []
  | cell :: rest => dropLastWithPending cell rest

private theorem dropLastWithPending_append_singleton
    (pending : Option Bool) (cells : List (Option Bool))
    (last : Option Bool) :
    dropLastWithPending pending (cells ++ [last]) =
      pending :: cells := by
  induction cells generalizing pending with
  | nil =>
      rfl
  | cons cell rest ih =>
      simp [dropLastWithPending, ih]

theorem dropFinalCell_append_singleton
    (cells : List (Option Bool)) (last : Option Bool) :
    dropFinalCell (cells ++ [last]) = cells := by
  cases cells with
  | nil =>
      rfl
  | cons cell rest =>
      exact dropLastWithPending_append_singleton cell rest last

def sourceTapeAt
    (consumed remaining : List (Option Bool)) : Tape Bool :=
  tapeAtCells (encodedCells consumed).reverse (encodedCells remaining)

def sourceTape (cells : List (Option Bool)) : Tape Bool :=
  sourceTapeAt [] cells

theorem sourceTapeAt_append_singleton
    (consumed remaining : List (Option Bool)) (boundary : Option Bool) :
    sourceTapeAt consumed (remaining ++ [boundary]) =
      tapeAtCells (encodedCells consumed).reverse
        (encodedCells remaining ++ [none, boundary]) := by
  simp [sourceTapeAt, encodedCells_append_singleton]

def markerTapeAt (used remaining : Nat) : Tape Bool :=
  tapeAtCells
    (List.replicate used markerCell)
    (List.replicate remaining markerCell)

def markerTape (count : Nat) : Tape Bool :=
  markerTapeAt 0 count

theorem markerTapeAt_succ (used n : Nat) :
    markerTapeAt used (n + 1) =
      tapeAtCells
        (List.replicate used markerCell)
        (markerCell :: List.replicate n markerCell) := by
  simp [markerTapeAt, List.replicate_succ]

@[simp] theorem markerTapeAt_preserveRight_succ
    (used n : Nat) :
    (TapeAction.preserveMove HeadMove.right).apply
        (markerTapeAt used (n + 1)) =
      markerTapeAt (used + 1) n := by
  cases n <;>
    simp [markerTapeAt, tapeAtCells, List.replicate_succ, TapeAction.apply,
      HeadMove.apply, Tape.move, Tape.moveRight, markerCell]

@[simp] theorem markerTapeAt_stay
    (used remaining : Nat) :
    TapeAction.stay.apply (markerTapeAt used remaining) =
      markerTapeAt used remaining := by
  rfl

def outputTape (out : List (Option Bool)) : Tape Bool :=
  tapeAtCells out.reverse []

/-!
## Pair-encoded payload ingress

These names isolate the shared one-tape-to-guarded-three-tape ingress shape for
payloads encoded as pairs of physical cells.  The source tape has a fixed
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

def PayloadIngressTargetFamilySpec {ι : Type}
    (source : ι -> Tape Bool)
    (payload : ι -> List (Option Bool))
    (initializer : MachineDescription) : Prop :=
  Structured3InputTargetFamilySpec
    source
    (fun input => payloadIngressTargetTape (payload input))
    initializer

def PayloadIngressTargetFamilyConstruction {ι : Type}
    (source : ι -> Tape Bool)
    (payload : ι -> List (Option Bool)) : Prop :=
  exists initializer : MachineDescription,
    PayloadIngressTargetFamilySpec source payload initializer

def FixedPrefixPayloadIngressTargetFamilyConstruction
    (fixedPrefix : List (Option Bool)) : Prop :=
  PayloadIngressTargetFamilyConstruction
    (fixedPrefixPayloadIngressSourceTape fixedPrefix)
    (fun payload : List (Option Bool) => payload)

theorem payloadIngressTargetFamilySpec_subroutineReady
    {ι : Type} {source : ι -> Tape Bool}
    {payload : ι -> List (Option Bool)}
    {initializer : MachineDescription}
    (hspec :
      PayloadIngressTargetFamilySpec source payload initializer) :
    initializer.SubroutineReady :=
  hspec.left

theorem payloadIngressTargetFamilySpec_haltsFromTapeEquiv
    {ι : Type} {source : ι -> Tape Bool}
    {payload : ι -> List (Option Bool)}
    {initializer : MachineDescription}
    (hspec :
      PayloadIngressTargetFamilySpec source payload initializer)
    (input : ι) :
    initializer.HaltsFromTapeEquiv
      (source input)
      (payloadIngressTargetTape (payload input)) :=
  hspec.right input

/-!
## Split-target separator focus route

The compactor output tape is right-positioned after the full target payload.
For payloads of the form {lit}`bits.map some ++ none :: padding`, downstream
selected-footprint endpoints need the output logical tape focused back at the
semantic separator.  This route keeps the full structured source and marker
tapes available, so it is not the ambiguous tape-2-only rewind.
-/

def splitTargetPayloadCells
    (bits : Word Bool) (padding : List (Option Bool)) :
    List (Option Bool) :=
  List.append (bits.map some) (none :: padding)

def splitSourcePayloadCells
    (bits : Word Bool) (padding : List (Option Bool)) :
    List (Option Bool) :=
  List.append (splitTargetPayloadCells bits padding) [none]

theorem splitSourcePayloadCells_eq_target_append_boundary
    (bits : Word Bool) (padding : List (Option Bool)) :
    splitSourcePayloadCells bits padding =
      List.append (splitTargetPayloadCells bits padding) [none] := by
  rfl

def splitTargetOutput0
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape Bool :=
  sourceTapeAt (splitSourcePayloadCells bits padding) []

def splitTargetOutput1
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape Bool :=
  markerTapeAt (splitSourcePayloadCells bits padding).length 0

def splitTargetOutput2
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape Bool :=
  outputTape (splitTargetPayloadCells bits padding)

def splitTargetFocusedOutput2
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape Bool :=
  tapeAtCells (bits.reverse.map some) (none :: padding)

theorem splitTargetFocusedOutput2_eq_rightEdgeRewindSourceTape
    (bits : Word Bool) (padding : List (Option Bool)) :
    splitTargetFocusedOutput2 bits padding =
      rightEdgeRewindSourceTape bits padding := by
  rfl

def splitTargetOutputTape
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape Bool :=
  encodedGuardedStructured3Tapes
    (splitTargetOutput0 bits padding)
    (splitTargetOutput1 bits padding)
    (splitTargetOutput2 bits padding)

def splitTargetFocusedOutputTape
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape Bool :=
  encodedGuardedStructured3Tapes
    (splitTargetOutput0 bits padding)
    (splitTargetOutput1 bits padding)
    (splitTargetFocusedOutput2 bits padding)

def splitTargetRightEdgeRewindOutputTape
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape Bool :=
  encodedGuardedStructured3Tapes
    (splitTargetOutput0 bits padding)
    (splitTargetOutput1 bits padding)
    (rightEdgeRewindSourceTape bits padding)

theorem splitTargetFocusedOutputTape_eq_rightEdgeRewindOutputTape
    (bits : Word Bool) (padding : List (Option Bool)) :
    splitTargetFocusedOutputTape bits padding =
      splitTargetRightEdgeRewindOutputTape bits padding := by
  simp [
    splitTargetFocusedOutputTape,
    splitTargetRightEdgeRewindOutputTape,
    splitTargetFocusedOutput2_eq_rightEdgeRewindSourceTape]

def SplitTargetSeparatorFocusSpec
    (focus : MachineDescription) : Prop :=
  focus.SubroutineReady ∧
    forall (bits : Word Bool) (padding : List (Option Bool)),
      focus.HaltsFromTapeEquiv
        (splitTargetOutputTape bits padding)
        (splitTargetFocusedOutputTape bits padding)

def SplitTargetSeparatorFocusConstruction : Prop :=
  exists focus : MachineDescription,
    SplitTargetSeparatorFocusSpec focus

def SplitTargetRightEdgeRewindOutputSpec
    (focus : MachineDescription) : Prop :=
  focus.SubroutineReady ∧
    forall (bits : Word Bool) (padding : List (Option Bool)),
      focus.HaltsFromTapeEquiv
        (splitTargetOutputTape bits padding)
        (splitTargetRightEdgeRewindOutputTape bits padding)

def SplitTargetRightEdgeRewindOutputConstruction : Prop :=
  exists focus : MachineDescription,
    SplitTargetRightEdgeRewindOutputSpec focus

def SplitTargetRightEdgeRewindOutputNilPadSymbolCaseSpec
    (focus : MachineDescription) : Prop :=
  focus.SubroutineReady ∧
    focus.HaltsFromTapeEquiv
      (splitTargetOutputTape [] [])
      (splitTargetRightEdgeRewindOutputTape [] []) ∧
    (forall padding : List (Option Bool),
      focus.HaltsFromTapeEquiv
        (splitTargetOutputTape [] (none :: padding))
        (splitTargetRightEdgeRewindOutputTape [] (none :: padding))) ∧
    forall (padBit : Bool) (padding : List (Option Bool)),
      focus.HaltsFromTapeEquiv
        (splitTargetOutputTape [] (some padBit :: padding))
        (splitTargetRightEdgeRewindOutputTape [] (some padBit :: padding))

def SplitTargetRightEdgeRewindOutputConsPadSymbolCaseSpec
    (focus : MachineDescription) : Prop :=
  focus.SubroutineReady ∧
    (forall (bit : Bool) (rest : Word Bool),
      focus.HaltsFromTapeEquiv
        (splitTargetOutputTape (bit :: rest) [])
        (splitTargetRightEdgeRewindOutputTape (bit :: rest) [])) ∧
    (forall (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      focus.HaltsFromTapeEquiv
        (splitTargetOutputTape (bit :: rest) (none :: padding))
        (splitTargetRightEdgeRewindOutputTape
          (bit :: rest) (none :: padding))) ∧
    forall (bit : Bool) (rest : Word Bool)
      (padBit : Bool) (padding : List (Option Bool)),
      focus.HaltsFromTapeEquiv
        (splitTargetOutputTape (bit :: rest) (some padBit :: padding))
        (splitTargetRightEdgeRewindOutputTape
          (bit :: rest) (some padBit :: padding))

def SplitTargetRightEdgeRewindOutputSplitPadSymbolCaseSpec
    (focus : MachineDescription) : Prop :=
  SplitTargetRightEdgeRewindOutputNilPadSymbolCaseSpec focus ∧
    SplitTargetRightEdgeRewindOutputConsPadSymbolCaseSpec focus

def SplitTargetRightEdgeRewindOutputSplitPadSymbolCaseConstruction :
    Prop :=
  exists focus : MachineDescription,
    SplitTargetRightEdgeRewindOutputSplitPadSymbolCaseSpec focus

theorem splitTargetRightEdgeRewindOutputSplitPadSymbolCaseSpec_of_spec
    {focus : MachineDescription}
    (hfocus : SplitTargetRightEdgeRewindOutputSpec focus) :
    SplitTargetRightEdgeRewindOutputSplitPadSymbolCaseSpec focus := by
  rcases hfocus with ⟨hready, hrun⟩
  refine ⟨?_, ?_⟩
  · refine ⟨hready, ?_, ?_, ?_⟩
    · exact hrun [] []
    · intro padding
      exact hrun [] (none :: padding)
    · intro padBit padding
      exact hrun [] (some padBit :: padding)
  · refine ⟨hready, ?_, ?_, ?_⟩
    · intro bit rest
      exact hrun (bit :: rest) []
    · intro bit rest padding
      exact hrun (bit :: rest) (none :: padding)
    · intro bit rest padBit padding
      exact hrun (bit :: rest) (some padBit :: padding)

theorem splitTargetRightEdgeRewindOutputSpec_of_splitPadSymbolCaseSpec
    {focus : MachineDescription}
    (hsplit :
      SplitTargetRightEdgeRewindOutputSplitPadSymbolCaseSpec focus) :
    SplitTargetRightEdgeRewindOutputSpec focus := by
  rcases hsplit with ⟨hnil, hcons⟩
  rcases hnil with ⟨hready, hnilNil, hnilNone, hnilSome⟩
  rcases hcons with
    ⟨_hreadyCons, hconsNil, hconsNone, hconsSome⟩
  refine ⟨hready, ?_⟩
  intro bits padding
  cases bits with
  | nil =>
      cases padding with
      | nil =>
          exact hnilNil
      | cons pad padding =>
          cases pad with
          | none =>
              exact hnilNone padding
          | some padBit =>
              exact hnilSome padBit padding
  | cons bit rest =>
      cases padding with
      | nil =>
          exact hconsNil bit rest
      | cons pad padding =>
          cases pad with
          | none =>
              exact hconsNone bit rest padding
          | some padBit =>
              exact hconsSome bit rest padBit padding

theorem splitTargetRightEdgeRewindOutputConstruction_of_splitPadSymbolCases
    (hsplit :
      SplitTargetRightEdgeRewindOutputSplitPadSymbolCaseConstruction) :
    SplitTargetRightEdgeRewindOutputConstruction := by
  rcases hsplit with ⟨focus, hspec⟩
  exact
    ⟨focus,
      splitTargetRightEdgeRewindOutputSpec_of_splitPadSymbolCaseSpec
        hspec⟩

def SplitTargetProjectableRightEdgeRewindOutputSpec
    (focus : MachineDescription) : Prop :=
  focus.SubroutineReady ∧
    forall (bits : Word Bool) (padding : List (Option Bool)),
      exists source marker target : Tape Bool,
        Tape.Equiv target (rightEdgeRewindSourceTape bits padding) ∧
        focus.HaltsFromTapeEquiv
          (splitTargetOutputTape bits padding)
          (encodedGuardedStructured3Tapes
            source marker target)

def SplitTargetProjectableRightEdgeRewindOutputConstruction : Prop :=
  exists focus : MachineDescription,
    SplitTargetProjectableRightEdgeRewindOutputSpec focus

def SplitTargetProjectableRightEdgeRewindOutputNilPadSymbolCaseSpec
    (focus : MachineDescription) : Prop :=
  focus.SubroutineReady ∧
    (exists source marker target : Tape Bool,
      Tape.Equiv target (rightEdgeRewindSourceTape [] []) ∧
      focus.HaltsFromTapeEquiv
        (splitTargetOutputTape [] [])
        (encodedGuardedStructured3Tapes
          source marker target)) ∧
    (forall padding : List (Option Bool),
      exists source marker target : Tape Bool,
        Tape.Equiv target
          (rightEdgeRewindSourceTape [] (none :: padding)) ∧
        focus.HaltsFromTapeEquiv
          (splitTargetOutputTape [] (none :: padding))
          (encodedGuardedStructured3Tapes
            source marker target)) ∧
    forall (padBit : Bool) (padding : List (Option Bool)),
      exists source marker target : Tape Bool,
        Tape.Equiv target
          (rightEdgeRewindSourceTape [] (some padBit :: padding)) ∧
        focus.HaltsFromTapeEquiv
          (splitTargetOutputTape [] (some padBit :: padding))
          (encodedGuardedStructured3Tapes
            source marker target)

def SplitTargetProjectableRightEdgeRewindOutputConsPadSymbolCaseSpec
    (focus : MachineDescription) : Prop :=
  focus.SubroutineReady ∧
    (forall (bit : Bool) (rest : Word Bool),
      exists source marker target : Tape Bool,
        Tape.Equiv target
          (rightEdgeRewindSourceTape (bit :: rest) []) ∧
        focus.HaltsFromTapeEquiv
          (splitTargetOutputTape (bit :: rest) [])
          (encodedGuardedStructured3Tapes
            source marker target)) ∧
    (forall (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      exists source marker target : Tape Bool,
        Tape.Equiv target
          (rightEdgeRewindSourceTape
            (bit :: rest) (none :: padding)) ∧
        focus.HaltsFromTapeEquiv
          (splitTargetOutputTape (bit :: rest) (none :: padding))
          (encodedGuardedStructured3Tapes
            source marker target)) ∧
    forall (bit : Bool) (rest : Word Bool)
      (padBit : Bool) (padding : List (Option Bool)),
      exists source marker target : Tape Bool,
        Tape.Equiv target
          (rightEdgeRewindSourceTape
            (bit :: rest) (some padBit :: padding)) ∧
        focus.HaltsFromTapeEquiv
          (splitTargetOutputTape (bit :: rest) (some padBit :: padding))
          (encodedGuardedStructured3Tapes
            source marker target)

def SplitTargetProjectableRightEdgeRewindOutputSplitPadSymbolCaseSpec
    (focus : MachineDescription) : Prop :=
  SplitTargetProjectableRightEdgeRewindOutputNilPadSymbolCaseSpec focus ∧
    SplitTargetProjectableRightEdgeRewindOutputConsPadSymbolCaseSpec focus

def SplitTargetProjectableRightEdgeRewindOutputSplitPadSymbolCaseConstruction :
    Prop :=
  exists focus : MachineDescription,
    SplitTargetProjectableRightEdgeRewindOutputSplitPadSymbolCaseSpec focus

theorem splitTargetProjectableRightEdgeRewindOutputSplitPadSymbolCaseSpec_of_spec
    {focus : MachineDescription}
    (hfocus :
      SplitTargetProjectableRightEdgeRewindOutputSpec focus) :
    SplitTargetProjectableRightEdgeRewindOutputSplitPadSymbolCaseSpec
      focus := by
  rcases hfocus with ⟨hready, hrun⟩
  refine ⟨?_, ?_⟩
  · refine ⟨hready, ?_, ?_, ?_⟩
    · exact hrun [] []
    · intro padding
      exact hrun [] (none :: padding)
    · intro padBit padding
      exact hrun [] (some padBit :: padding)
  · refine ⟨hready, ?_, ?_, ?_⟩
    · intro bit rest
      exact hrun (bit :: rest) []
    · intro bit rest padding
      exact hrun (bit :: rest) (none :: padding)
    · intro bit rest padBit padding
      exact hrun (bit :: rest) (some padBit :: padding)

theorem splitTargetProjectableRightEdgeRewindOutputSpec_of_splitPadSymbolCaseSpec
    {focus : MachineDescription}
    (hsplit :
      SplitTargetProjectableRightEdgeRewindOutputSplitPadSymbolCaseSpec
        focus) :
    SplitTargetProjectableRightEdgeRewindOutputSpec focus := by
  rcases hsplit with ⟨hnil, hcons⟩
  rcases hnil with ⟨hready, hnilNil, hnilNone, hnilSome⟩
  rcases hcons with
    ⟨_hreadyCons, hconsNil, hconsNone, hconsSome⟩
  refine ⟨hready, ?_⟩
  intro bits padding
  cases bits with
  | nil =>
      cases padding with
      | nil =>
          exact hnilNil
      | cons pad padding =>
          cases pad with
          | none =>
              exact hnilNone padding
          | some padBit =>
              exact hnilSome padBit padding
  | cons bit rest =>
      cases padding with
      | nil =>
          exact hconsNil bit rest
      | cons pad padding =>
          cases pad with
          | none =>
              exact hconsNone bit rest padding
          | some padBit =>
              exact hconsSome bit rest padBit padding

theorem splitTargetProjectableRightEdgeRewindOutputConstruction_of_splitPadSymbolCases
    (hsplit :
      SplitTargetProjectableRightEdgeRewindOutputSplitPadSymbolCaseConstruction) :
    SplitTargetProjectableRightEdgeRewindOutputConstruction := by
  rcases hsplit with ⟨focus, hspec⟩
  exact
    ⟨focus,
      splitTargetProjectableRightEdgeRewindOutputSpec_of_splitPadSymbolCaseSpec
        hspec⟩

theorem splitTargetProjectableRightEdgeRewindOutputSpec_of_rightEdgeRewindOutputSpec
    {focus : MachineDescription}
    (hfocus : SplitTargetRightEdgeRewindOutputSpec focus) :
    SplitTargetProjectableRightEdgeRewindOutputSpec focus := by
  rcases hfocus with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro bits padding
  refine
    ⟨splitTargetOutput0 bits padding,
      splitTargetOutput1 bits padding,
      rightEdgeRewindSourceTape bits padding,
      Tape.Equiv.refl _, ?_⟩
  simpa [splitTargetRightEdgeRewindOutputTape] using hrun bits padding

theorem splitTargetProjectableRightEdgeRewindOutputConstruction_of_rightEdgeRewindOutput
    (hfocus : SplitTargetRightEdgeRewindOutputConstruction) :
    SplitTargetProjectableRightEdgeRewindOutputConstruction := by
  rcases hfocus with ⟨focus, hspec⟩
  exact
    ⟨focus,
      splitTargetProjectableRightEdgeRewindOutputSpec_of_rightEdgeRewindOutputSpec
        hspec⟩

theorem splitTargetProjectableRightEdgeRewindOutputSplitPadSymbolCaseSpec_of_rightEdgeRewindOutputSpec
    {focus : MachineDescription}
    (hfocus : SplitTargetRightEdgeRewindOutputSpec focus) :
    SplitTargetProjectableRightEdgeRewindOutputSplitPadSymbolCaseSpec
      focus :=
  splitTargetProjectableRightEdgeRewindOutputSplitPadSymbolCaseSpec_of_spec
    (splitTargetProjectableRightEdgeRewindOutputSpec_of_rightEdgeRewindOutputSpec
      hfocus)

theorem splitTargetProjectableRightEdgeRewindOutputSplitPadSymbolCaseConstruction_of_rightEdgeRewindOutput
    (hfocus : SplitTargetRightEdgeRewindOutputConstruction) :
    SplitTargetProjectableRightEdgeRewindOutputSplitPadSymbolCaseConstruction := by
  rcases hfocus with ⟨focus, hspec⟩
  exact
    ⟨focus,
      splitTargetProjectableRightEdgeRewindOutputSplitPadSymbolCaseSpec_of_rightEdgeRewindOutputSpec
        hspec⟩

theorem splitTargetProjectableRightEdgeRewindOutputNilPadSymbolCaseSpec_of_rightEdgeRewindOutputNilPadSymbolCaseSpec
    {focus : MachineDescription}
    (hfocus :
      SplitTargetRightEdgeRewindOutputNilPadSymbolCaseSpec focus) :
    SplitTargetProjectableRightEdgeRewindOutputNilPadSymbolCaseSpec
      focus := by
  rcases hfocus with ⟨hready, hnilNil, hnilNone, hnilSome⟩
  refine ⟨hready, ?_, ?_, ?_⟩
  · refine
      ⟨splitTargetOutput0 [] [],
        splitTargetOutput1 [] [],
        rightEdgeRewindSourceTape [] [],
        Tape.Equiv.refl _, ?_⟩
    simpa [splitTargetRightEdgeRewindOutputTape] using hnilNil
  · intro padding
    refine
      ⟨splitTargetOutput0 [] (none :: padding),
        splitTargetOutput1 [] (none :: padding),
        rightEdgeRewindSourceTape [] (none :: padding),
        Tape.Equiv.refl _, ?_⟩
    simpa [splitTargetRightEdgeRewindOutputTape] using
      hnilNone padding
  · intro padBit padding
    refine
      ⟨splitTargetOutput0 [] (some padBit :: padding),
        splitTargetOutput1 [] (some padBit :: padding),
        rightEdgeRewindSourceTape [] (some padBit :: padding),
        Tape.Equiv.refl _, ?_⟩
    simpa [splitTargetRightEdgeRewindOutputTape] using
      hnilSome padBit padding

theorem splitTargetProjectableRightEdgeRewindOutputConsPadSymbolCaseSpec_of_rightEdgeRewindOutputConsPadSymbolCaseSpec
    {focus : MachineDescription}
    (hfocus :
      SplitTargetRightEdgeRewindOutputConsPadSymbolCaseSpec focus) :
    SplitTargetProjectableRightEdgeRewindOutputConsPadSymbolCaseSpec
      focus := by
  rcases hfocus with ⟨hready, hconsNil, hconsNone, hconsSome⟩
  refine ⟨hready, ?_, ?_, ?_⟩
  · intro bit rest
    refine
      ⟨splitTargetOutput0 (bit :: rest) [],
        splitTargetOutput1 (bit :: rest) [],
        rightEdgeRewindSourceTape (bit :: rest) [],
        Tape.Equiv.refl _, ?_⟩
    simpa [splitTargetRightEdgeRewindOutputTape] using
      hconsNil bit rest
  · intro bit rest padding
    refine
      ⟨splitTargetOutput0 (bit :: rest) (none :: padding),
        splitTargetOutput1 (bit :: rest) (none :: padding),
        rightEdgeRewindSourceTape (bit :: rest) (none :: padding),
        Tape.Equiv.refl _, ?_⟩
    simpa [splitTargetRightEdgeRewindOutputTape] using
      hconsNone bit rest padding
  · intro bit rest padBit padding
    refine
      ⟨splitTargetOutput0 (bit :: rest) (some padBit :: padding),
        splitTargetOutput1 (bit :: rest) (some padBit :: padding),
        rightEdgeRewindSourceTape (bit :: rest) (some padBit :: padding),
        Tape.Equiv.refl _, ?_⟩
    simpa [splitTargetRightEdgeRewindOutputTape] using
      hconsSome bit rest padBit padding

theorem splitTargetProjectableRightEdgeRewindOutputSplitPadSymbolCaseSpec_of_rightEdgeRewindOutputSplitPadSymbolCaseSpec
    {focus : MachineDescription}
    (hsplit :
      SplitTargetRightEdgeRewindOutputSplitPadSymbolCaseSpec focus) :
    SplitTargetProjectableRightEdgeRewindOutputSplitPadSymbolCaseSpec
      focus := by
  exact
    ⟨splitTargetProjectableRightEdgeRewindOutputNilPadSymbolCaseSpec_of_rightEdgeRewindOutputNilPadSymbolCaseSpec
        hsplit.left,
      splitTargetProjectableRightEdgeRewindOutputConsPadSymbolCaseSpec_of_rightEdgeRewindOutputConsPadSymbolCaseSpec
        hsplit.right⟩

theorem splitTargetProjectableRightEdgeRewindOutputSplitPadSymbolCaseConstruction_of_rightEdgeRewindOutputSplitPadSymbolCases
    (hsplit :
      SplitTargetRightEdgeRewindOutputSplitPadSymbolCaseConstruction) :
    SplitTargetProjectableRightEdgeRewindOutputSplitPadSymbolCaseConstruction := by
  rcases hsplit with ⟨focus, hspec⟩
  exact
    ⟨focus,
      splitTargetProjectableRightEdgeRewindOutputSplitPadSymbolCaseSpec_of_rightEdgeRewindOutputSplitPadSymbolCaseSpec
        hspec⟩

theorem splitTargetProjectableRightEdgeRewindOutputConstruction_of_rightEdgeRewindOutputSplitPadSymbolCases
    (hsplit :
      SplitTargetRightEdgeRewindOutputSplitPadSymbolCaseConstruction) :
    SplitTargetProjectableRightEdgeRewindOutputConstruction :=
  splitTargetProjectableRightEdgeRewindOutputConstruction_of_splitPadSymbolCases
    (splitTargetProjectableRightEdgeRewindOutputSplitPadSymbolCaseConstruction_of_rightEdgeRewindOutputSplitPadSymbolCases
      hsplit)

theorem splitTargetSeparatorFocusSpec_of_rightEdgeRewindOutputSpec
    {focus : MachineDescription}
    (hfocus : SplitTargetRightEdgeRewindOutputSpec focus) :
    SplitTargetSeparatorFocusSpec focus := by
  rcases hfocus with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro bits padding
  simpa [splitTargetFocusedOutputTape_eq_rightEdgeRewindOutputTape] using
    hrun bits padding

theorem splitTargetSeparatorFocusConstruction_of_rightEdgeRewindOutput
    (hfocus : SplitTargetRightEdgeRewindOutputConstruction) :
    SplitTargetSeparatorFocusConstruction := by
  rcases hfocus with ⟨focus, hspec⟩
  exact
    ⟨focus,
      splitTargetSeparatorFocusSpec_of_rightEdgeRewindOutputSpec hspec⟩

def SplitTargetSeparatorFocusNilPadSymbolCaseSpec
    (focus : MachineDescription) : Prop :=
  focus.SubroutineReady ∧
    focus.HaltsFromTapeEquiv
      (splitTargetOutputTape [] [])
      (splitTargetFocusedOutputTape [] []) ∧
    (forall padding : List (Option Bool),
      focus.HaltsFromTapeEquiv
        (splitTargetOutputTape [] (none :: padding))
        (splitTargetFocusedOutputTape [] (none :: padding))) ∧
    forall (padBit : Bool) (padding : List (Option Bool)),
      focus.HaltsFromTapeEquiv
        (splitTargetOutputTape [] (some padBit :: padding))
        (splitTargetFocusedOutputTape [] (some padBit :: padding))

def SplitTargetSeparatorFocusConsPadSymbolCaseSpec
    (focus : MachineDescription) : Prop :=
  focus.SubroutineReady ∧
    (forall (bit : Bool) (rest : Word Bool),
      focus.HaltsFromTapeEquiv
        (splitTargetOutputTape (bit :: rest) [])
        (splitTargetFocusedOutputTape (bit :: rest) [])) ∧
    (forall (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      focus.HaltsFromTapeEquiv
        (splitTargetOutputTape (bit :: rest) (none :: padding))
        (splitTargetFocusedOutputTape (bit :: rest) (none :: padding))) ∧
    forall (bit : Bool) (rest : Word Bool)
      (padBit : Bool) (padding : List (Option Bool)),
      focus.HaltsFromTapeEquiv
        (splitTargetOutputTape (bit :: rest) (some padBit :: padding))
        (splitTargetFocusedOutputTape
          (bit :: rest) (some padBit :: padding))

def SplitTargetSeparatorFocusSplitPadSymbolCaseSpec
    (focus : MachineDescription) : Prop :=
  SplitTargetSeparatorFocusNilPadSymbolCaseSpec focus ∧
    SplitTargetSeparatorFocusConsPadSymbolCaseSpec focus

def SplitTargetSeparatorFocusSplitPadSymbolCaseConstruction : Prop :=
  exists focus : MachineDescription,
    SplitTargetSeparatorFocusSplitPadSymbolCaseSpec focus

theorem splitTargetSeparatorFocusSplitPadSymbolCaseSpec_of_spec
    {focus : MachineDescription}
    (hfocus : SplitTargetSeparatorFocusSpec focus) :
    SplitTargetSeparatorFocusSplitPadSymbolCaseSpec focus := by
  rcases hfocus with ⟨hready, hrun⟩
  refine ⟨?_, ?_⟩
  · refine ⟨hready, ?_, ?_, ?_⟩
    · exact hrun [] []
    · intro padding
      exact hrun [] (none :: padding)
    · intro padBit padding
      exact hrun [] (some padBit :: padding)
  · refine ⟨hready, ?_, ?_, ?_⟩
    · intro bit rest
      exact hrun (bit :: rest) []
    · intro bit rest padding
      exact hrun (bit :: rest) (none :: padding)
    · intro bit rest padBit padding
      exact hrun (bit :: rest) (some padBit :: padding)

theorem splitTargetSeparatorFocusSpec_of_splitPadSymbolCaseSpec
    {focus : MachineDescription}
    (hsplit : SplitTargetSeparatorFocusSplitPadSymbolCaseSpec focus) :
    SplitTargetSeparatorFocusSpec focus := by
  rcases hsplit with ⟨hnil, hcons⟩
  rcases hnil with ⟨hready, hnilNil, hnilNone, hnilSome⟩
  rcases hcons with
    ⟨_hreadyCons, hconsNil, hconsNone, hconsSome⟩
  refine ⟨hready, ?_⟩
  intro bits padding
  cases bits with
  | nil =>
      cases padding with
      | nil =>
          exact hnilNil
      | cons pad padding =>
          cases pad with
          | none =>
              exact hnilNone padding
          | some padBit =>
              exact hnilSome padBit padding
  | cons bit rest =>
      cases padding with
      | nil =>
          exact hconsNil bit rest
      | cons pad padding =>
          cases pad with
          | none =>
              exact hconsNone bit rest padding
          | some padBit =>
              exact hconsSome bit rest padBit padding

theorem splitTargetSeparatorFocusConstruction_of_splitPadSymbolCases
    (hsplit : SplitTargetSeparatorFocusSplitPadSymbolCaseConstruction) :
    SplitTargetSeparatorFocusConstruction := by
  rcases hsplit with ⟨focus, hspec⟩
  exact
    ⟨focus,
      splitTargetSeparatorFocusSpec_of_splitPadSymbolCaseSpec hspec⟩

theorem splitTargetSeparatorFocusSplitPadSymbolCaseConstruction_of_rightEdgeRewindOutput
    (hfocus : SplitTargetRightEdgeRewindOutputConstruction) :
    SplitTargetSeparatorFocusSplitPadSymbolCaseConstruction := by
  rcases hfocus with ⟨focus, hspec⟩
  exact
    ⟨focus,
      splitTargetSeparatorFocusSplitPadSymbolCaseSpec_of_spec
        (splitTargetSeparatorFocusSpec_of_rightEdgeRewindOutputSpec
          hspec)⟩


end PairEncodedOptionCellCompactor
end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC

import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorDeterminismGate.Basic

set_option doc.verso true

/-!
# Exact-code validator: determinism-gate run foundations

This module fixes the symbolic row layout used by the leaf-5 run proof and
packages the generic aligned-block scan combinators for the concrete table.
The later pair and outer-loop modules work only with these layouts; they do not
unfold the generated 102-state table.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer
namespace ValidatorDeterminismGate

open Languages
open MachineDescription

/-- Compact logical configuration notation for leaf-5 proofs. -/
def configuration
    (state : Nat)
    (left right : Word ValidatorBlockSymbol) :
    ValidatorBlockDescription.Configuration :=
  ValidatorBlockDescription.blockConfiguration state left right

/-- One row after its transition boundary and before its final target
terminator. -/
def rowInteriorBlocks (row : TransitionDescription) :
    Word ValidatorBlockSymbol :=
  List.append (List.replicate row.source .tick)
    (.done ::
      ValidatorCountedRows.cellBlock row.read ::
      ValidatorCountedRows.cellBlock row.write ::
      ValidatorCountedRows.directionBlock row.move ::
      List.replicate row.target .tick)

/-- The existing boundary-free row body is a transition block followed by the
leaf-5 interior. -/
theorem rowBodyBlocks_eq_transition_cons_interior
    (row : TransitionDescription) :
    ValidatorCountedRows.rowBodyBlocks row =
      .transition :: rowInteriorBlocks row := by
  simp [ValidatorCountedRows.rowBodyBlocks, rowInteriorBlocks,
    ValidatorHeaderBounds.natBlocks]

/-- A canonical row is its transition, interior, and final terminator. -/
theorem rowBlocks_eq_transition_cons_interior_append_done
    (row : TransitionDescription) :
    ValidatorCountedRows.rowBlocks row =
      .transition :: List.append (rowInteriorBlocks row) [.done] := by
  rw [ValidatorCountedRows.rowBlocks_eq_body_append_done,
    rowBodyBlocks_eq_transition_cons_interior]
  simp

/-- A row whose transition boundary remains selected. -/
def selectedRowBlocks (row : TransitionDescription) :
    Word ValidatorBlockSymbol :=
  .marker001 :: List.append (rowInteriorBlocks row) [.done]

/-- A row already passed by the outer selector remains selected until the
single final restoration sweep. -/
def selectedRowsBlocks : List TransitionDescription ->
    Word ValidatorBlockSymbol
  | [] => []
  | row :: rest =>
      List.append (selectedRowBlocks row) (selectedRowsBlocks rest)

/-- Every row-interior symbol is a canonical non-header corridor symbol. -/
theorem rowInteriorBlocks_mem_canonicalCorridor
    (row : TransitionDescription) (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈
      (show List ValidatorBlockSymbol from rowInteriorBlocks row)) :
    symbol ∈ ValidatorCountedRows.canonicalCorridorSymbols := by
  have hrow : symbol ∈
      (show List ValidatorBlockSymbol from
        ValidatorCountedRows.rowBlocks row) := by
    rw [rowBlocks_eq_transition_cons_interior_append_done]
    simp only [List.mem_cons]
    exact Or.inr (List.mem_append_left [.done] hmem)
  exact ValidatorCountedRows.canonicalCorridor_rowBlocks row symbol hrow

/-- One logical right step for the concrete determinism table. -/
theorem reaches_one_right
    {state target : Nat} {read write : ValidatorBlockSymbol}
    (hlookup :
      blockDescription.lookup state read =
        some
          { source := state
            read := read
            write := write
            move := Direction.right
            target := target })
    (left rest : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration state left (read :: rest))
        (configuration target (List.append left [write]) rest) := by
  exact ValidatorBlockDescription.reaches_one_right hlookup left rest

/-- One logical left step for the concrete determinism table. -/
theorem reaches_one_left
    {state target : Nat} {read write : ValidatorBlockSymbol}
    (hlookup :
      blockDescription.lookup state read =
        some
          { source := state
            read := read
            write := write
            move := Direction.left
            target := target })
    (left rest : Word ValidatorBlockSymbol)
    (previous : ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration state
          (List.append left [previous]) (read :: rest))
        (configuration target left (previous :: write :: rest)) := by
  exact ValidatorBlockDescription.reaches_one_left
    hlookup left rest previous

/-- Scan a heterogeneous right word while preserving every block. -/
theorem reaches_scan_right_list
    {state : Nat} (symbols : List ValidatorBlockSymbol)
    (hlookup : forall symbol : ValidatorBlockSymbol,
      symbol ∈ symbols ->
        blockDescription.lookup state symbol =
          some
            { source := state
              read := symbol
              write := symbol
              move := Direction.right
              target := state })
    (left rest : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration state left (List.append symbols rest))
        (configuration state (List.append left symbols) rest) := by
  exact ValidatorBlockDescription.reaches_scan_right_list
    symbols hlookup left rest

/-- Cross a right-to-left corridor and stop on its boundary.  The corridor is
written in ordinary tape order rather than head-first encounter order. -/
theorem reaches_cross_scan_left_word
    {entry scan : Nat}
    {entryRead entryWrite boundary : ValidatorBlockSymbol}
    (corridor : List ValidatorBlockSymbol)
    (hentry :
      blockDescription.lookup entry entryRead =
        some
          { source := entry
            read := entryRead
            write := entryWrite
            move := Direction.left
            target := scan })
    (hscan : forall symbol : ValidatorBlockSymbol,
      symbol ∈ corridor ->
        blockDescription.lookup scan symbol =
          some
            { source := scan
              read := symbol
              write := symbol
              move := Direction.left
              target := scan })
    (before after : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration entry
          (List.append (List.append before [boundary]) corridor)
          (entryRead :: after))
        (configuration scan before
          (boundary :: List.append corridor (entryWrite :: after))) := by
  have hrun := ValidatorBlockDescription.reaches_cross_scan_left_list
    (boundary := boundary) corridor.reverse hentry
    (fun symbol hsymbol => hscan symbol (by simpa using hsymbol))
    before after
  simpa [configuration, ValidatorBlockDescription.blockConfiguration,
    List.append_assoc] using hrun

private theorem reaches_cross_rewrite_left_encountered
    {entry scan : Nat}
    {entryRead entryWrite boundary : ValidatorBlockSymbol}
    (encountered : List ValidatorBlockSymbol)
    (rewrite : ValidatorBlockSymbol -> ValidatorBlockSymbol)
    (hentry :
      blockDescription.lookup entry entryRead =
        some
          { source := entry
            read := entryRead
            write := entryWrite
            move := Direction.left
            target := scan })
    (hscan : forall symbol : ValidatorBlockSymbol,
      symbol ∈ encountered ->
        blockDescription.lookup scan symbol =
          some
            { source := scan
              read := symbol
              write := rewrite symbol
              move := Direction.left
              target := scan })
    (before after : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration entry
          (List.append
            (List.append before [boundary]) encountered.reverse)
          (entryRead :: after))
        (configuration scan before
          (boundary ::
            List.append (List.map rewrite encountered).reverse
              (entryWrite :: after))) := by
  induction encountered generalizing entry entryRead entryWrite after with
  | nil =>
      have hrun := reaches_one_left hentry before after boundary
      simpa [configuration] using hrun
  | cons first rest ih =>
      have hfirst := reaches_one_left hentry
        (List.append (List.append before [boundary]) rest.reverse)
        after first
      have htail := ih
        (entry := scan) (entryRead := first)
        (entryWrite := rewrite first)
        (hentry := hscan first List.mem_cons_self)
        (hscan := fun symbol hsymbol =>
          hscan symbol (List.mem_cons_of_mem first hsymbol))
        (after := entryWrite :: after)
      simpa [configuration, List.reverse_cons, List.append_assoc] using
        hfirst.trans htail

/-- Cross a right-to-left corridor while rewriting each logical symbol.  The
corridor is stated in ordinary tape order; the output retains that order. -/
theorem reaches_cross_rewrite_left_word
    {entry scan : Nat}
    {entryRead entryWrite boundary : ValidatorBlockSymbol}
    (corridor : List ValidatorBlockSymbol)
    (rewrite : ValidatorBlockSymbol -> ValidatorBlockSymbol)
    (hentry :
      blockDescription.lookup entry entryRead =
        some
          { source := entry
            read := entryRead
            write := entryWrite
            move := Direction.left
            target := scan })
    (hscan : forall symbol : ValidatorBlockSymbol,
      symbol ∈ corridor ->
        blockDescription.lookup scan symbol =
          some
            { source := scan
              read := symbol
              write := rewrite symbol
              move := Direction.left
              target := scan })
    (before after : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration entry
          (List.append (List.append before [boundary]) corridor)
          (entryRead :: after))
        (configuration scan before
          (boundary ::
            List.append (List.map rewrite corridor) (entryWrite :: after))) := by
  have hrun := reaches_cross_rewrite_left_encountered
    (boundary := boundary) corridor.reverse rewrite
    hentry
    (fun symbol hsymbol => hscan symbol (by simpa using hsymbol))
    before after
  simpa [configuration, List.append_assoc] using hrun

/-- Scan a homogeneous run of paired-tick markers to the right. -/
theorem reaches_scan_right_markers
    {state : Nat}
    (hlookup :
      blockDescription.lookup state .marker010 =
        some
          { source := state
            read := .marker010
            write := .marker010
            move := Direction.right
            target := state })
    (count : Nat) (left rest : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration state left
          (List.append (List.replicate count .marker010) rest))
        (configuration state
          (List.append left (List.replicate count .marker010)) rest) := by
  apply reaches_scan_right_list
  intro symbol hsymbol
  have heq : symbol = .marker010 :=
    (List.mem_replicate.mp hsymbol).2
  subst symbol
  exact hlookup

end ValidatorDeterminismGate
end SelfHaltingRecognizer
end Computability
end FoC

import FoC.Computability.Encoding
import FoC.Computability.Program

set_option doc.verso true

/-!
# Machine-description construction tools

This module collects the low-level ingredients needed for the remaining
Chapter 5 Section 5.2 finite compiler constructions.  The definitions here are
still ordinary first-order data over {lit}`MachineDescription`: state offsets,
finite tape/configuration codes, and executable bounded searches over the
interpreter.

The bounded search layer is not yet a one-tape transition table.  It is the
checked executable specification that such a transition table must implement:
for fixed recognizer descriptions, it computes exactly the same finite-stage
answers as the staged dovetailer.
-/

namespace FoC
namespace Computability

open Languages

namespace TransitionDescription

/-!
## State offsets

State offsets are the basic operation behind disjoint unions and larger machine
builders.  They rename source and target states while preserving the read/write
action.
-/

def offsetStates (offset : Nat) (t : TransitionDescription) :
    TransitionDescription where
  source := offset + t.source
  read := t.read
  write := t.write
  move := t.move
  target := offset + t.target

theorem offsetStates_sameAction
    (offset : Nat) (t u : TransitionDescription)
    (h : SameAction t u) :
    SameAction (offsetStates offset t) (offsetStates offset u) := by
  rcases h with ⟨hwrite, hmove, htarget⟩
  simp [SameAction, offsetStates, hwrite, hmove, htarget]

theorem sameKey_of_offsetStates_sameKey
    {offset : Nat} {t u : TransitionDescription}
    (h : SameKey (offsetStates offset t) (offsetStates offset u)) :
    SameKey t u := by
  constructor
  · exact Nat.add_left_cancel h.left
  · exact h.right

theorem wellFormed_offsetStates
    {stateCount offset : Nat} {t : TransitionDescription}
    (h : WellFormed stateCount t) :
    WellFormed (offset + stateCount) (offsetStates offset t) := by
  constructor
  · exact Nat.add_lt_add_left h.left offset
  · exact Nat.add_lt_add_left h.right offset

end TransitionDescription

namespace MachineDescription

/-!
## Description-level state extension

The first builder keeps a transition table unchanged while reserving extra
states above it.  This is useful for adding controller states around an existing
machine without changing the old state numbers.
-/

def extendStates (extra : Nat) (D : MachineDescription) :
    MachineDescription where
  stateCount := D.stateCount + extra
  start := D.start
  halt := D.halt
  transitions := D.transitions

theorem extendStates_wellFormed
    {extra : Nat} {D : MachineDescription}
    (hD : D.WellFormed) :
    (extendStates extra D).WellFormed := by
  constructor
  · have hpos : 0 < D.stateCount := hD.left
    change 0 < D.stateCount + extra
    omega
  constructor
  · exact Nat.lt_add_right extra hD.right.left
  constructor
  · exact Nat.lt_add_right extra hD.right.right.left
  constructor
  · intro t ht
    have htD := hD.right.right.right.left t ht
    constructor
    · exact Nat.lt_add_right extra htD.left
    · exact Nat.lt_add_right extra htD.right
  · intro t u ht hu hkey
    exact hD.right.right.right.right t u ht hu hkey

/-!
## State-block offsets

The second builder moves a whole description into a higher state block.  The
proof preserves well-formedness and determinism, so later compiler code can
reuse a recognizer table inside a larger controller table.
-/

def offsetStates (offset : Nat) (D : MachineDescription) :
    MachineDescription where
  stateCount := offset + D.stateCount
  start := offset + D.start
  halt := offset + D.halt
  transitions := D.transitions.map
    (TransitionDescription.offsetStates offset)

theorem offsetStates_wellFormed
    {offset : Nat} {D : MachineDescription}
    (hD : D.WellFormed) :
    (offsetStates offset D).WellFormed := by
  constructor
  · have hpos : 0 < D.stateCount := hD.left
    change 0 < offset + D.stateCount
    omega
  constructor
  · exact Nat.add_lt_add_left hD.right.left offset
  constructor
  · exact Nat.add_lt_add_left hD.right.right.left offset
  constructor
  · intro t ht
    simp [offsetStates] at ht
    rcases ht with ⟨base, hbase, rfl⟩
    exact TransitionDescription.wellFormed_offsetStates
      (hD.right.right.right.left base hbase)
  · intro t u ht hu hkey
    simp [offsetStates] at ht hu
    rcases ht with ⟨baseT, hbaseT, rfl⟩
    rcases hu with ⟨baseU, hbaseU, rfl⟩
    exact TransitionDescription.offsetStates_sameAction offset baseT baseU
      (hD.right.right.right.right baseT baseU hbaseT hbaseU
        (TransitionDescription.sameKey_of_offsetStates_sameKey hkey))

/-!
## Disjoint table unions

Disjoint union places a second transition table above the state range of the
first.  The constructor does not add controller edges; it is the checked
renaming/combination primitive that later sequencing and branching builders can
use.
-/

def disjointUnion (A B : MachineDescription) :
    MachineDescription where
  stateCount := A.stateCount + B.stateCount
  start := A.start
  halt := A.halt
  transitions :=
    A.transitions ++
      B.transitions.map
        (TransitionDescription.offsetStates A.stateCount)

theorem disjointUnion_wellFormed
    {A B : MachineDescription}
    (hA : A.WellFormed) (hB : B.WellFormed) :
    (disjointUnion A B).WellFormed := by
  constructor
  · have hpos : 0 < A.stateCount := hA.left
    change 0 < A.stateCount + B.stateCount
    omega
  constructor
  · exact Nat.lt_add_right B.stateCount hA.right.left
  constructor
  · exact Nat.lt_add_right B.stateCount hA.right.right.left
  constructor
  · intro t ht
    simp [disjointUnion] at ht
    cases ht with
    | inl hleft =>
        have htA := hA.right.right.right.left t hleft
        constructor
        · exact Nat.lt_add_right B.stateCount htA.left
        · exact Nat.lt_add_right B.stateCount htA.right
    | inr hright =>
        rcases hright with ⟨base, hbase, rfl⟩
        exact TransitionDescription.wellFormed_offsetStates
          (hB.right.right.right.left base hbase)
  · intro t u ht hu hkey
    simp [disjointUnion] at ht hu
    cases ht with
    | inl htA =>
        cases hu with
        | inl huA =>
            exact hA.right.right.right.right t u htA huA hkey
        | inr huB =>
            rcases huB with ⟨baseU, hbaseU, rfl⟩
            have htBound := (hA.right.right.right.left t htA).left
            have hsource : t.source = A.stateCount + baseU.source :=
              hkey.left
            omega
    | inr htB =>
        rcases htB with ⟨baseT, hbaseT, rfl⟩
        cases hu with
        | inl huA =>
            have huBound := (hA.right.right.right.left u huA).left
            have hsource : A.stateCount + baseT.source = u.source :=
              hkey.left
            omega
        | inr huB =>
            rcases huB with ⟨baseU, hbaseU, rfl⟩
            exact
              TransitionDescription.offsetStates_sameAction
                A.stateCount baseT baseU
                (hB.right.right.right.right baseT baseU
                  hbaseT hbaseU
                  (TransitionDescription.sameKey_of_offsetStates_sameKey
                    hkey))

/-!
## Tape and configuration codes

These encodings are over the existing {name}`MachineCodeSymbol` alphabet.  They
are not yet the tape layout used by a universal machine, but they give the
finite simulator target a precise, checked representation of configurations.
-/

def encodeCellsAppend (cells : List (Option Bool))
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  match cells with
  | [] => suffix
  | cell :: rest =>
      encodeCellAppend cell (encodeCellsAppend rest suffix)

def encodeCells (cells : List (Option Bool)) :
    Word MachineCodeSymbol :=
  encodeCellsAppend cells []

def decodeCells : Nat -> Word MachineCodeSymbol ->
    Option (List (Option Bool) × Word MachineCodeSymbol)
  | 0, tokens => some ([], tokens)
  | n + 1, tokens =>
      match decodeCell tokens with
      | none => none
      | some (cell, rest) =>
          match decodeCells n rest with
          | none => none
          | some (cells, suffix) => some (cell :: cells, suffix)

theorem decodeCells_encodeCellsAppend
    (cells : List (Option Bool)) (suffix : Word MachineCodeSymbol) :
    decodeCells cells.length (encodeCellsAppend cells suffix) =
      some (cells, suffix) := by
  induction cells with
  | nil =>
      rfl
  | cons cell rest ih =>
      simp [encodeCellsAppend, decodeCells, decodeCell_encodeCellAppend, ih]

def encodeCellListAppend (cells : List (Option Bool))
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  encodeNatAppend cells.length (encodeCellsAppend cells suffix)

def decodeCellList (tokens : Word MachineCodeSymbol) :
    Option (List (Option Bool) × Word MachineCodeSymbol) :=
  match decodeNat tokens with
  | none => none
  | some (len, rest) => decodeCells len rest

theorem decodeCellList_encodeCellListAppend
    (cells : List (Option Bool)) (suffix : Word MachineCodeSymbol) :
    decodeCellList (encodeCellListAppend cells suffix) =
      some (cells, suffix) := by
  simp [decodeCellList, encodeCellListAppend, decodeNat_encodeNatAppend,
    decodeCells_encodeCellsAppend]

def encodeTapeAppend (T : Tape Bool)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  encodeCellListAppend T.left
    (encodeCellAppend T.head
      (encodeCellListAppend T.right suffix))

def encodeTape (T : Tape Bool) : Word MachineCodeSymbol :=
  encodeTapeAppend T []

def decodeTape (tokens : Word MachineCodeSymbol) :
    Option (Tape Bool × Word MachineCodeSymbol) :=
  match decodeCellList tokens with
  | none => none
  | some (left, rest) =>
      match decodeCell rest with
      | none => none
      | some (head, rest) =>
          match decodeCellList rest with
          | none => none
          | some (right, suffix) =>
              some ({ left := left, head := head, right := right }, suffix)

theorem decodeTape_encodeTapeAppend
    (T : Tape Bool) (suffix : Word MachineCodeSymbol) :
    decodeTape (encodeTapeAppend T suffix) = some (T, suffix) := by
  cases T
  simp [encodeTapeAppend, decodeTape, decodeCellList_encodeCellListAppend,
    decodeCell_encodeCellAppend]

theorem decodeTape_encodeTape (T : Tape Bool) :
    decodeTape (encodeTape T) = some (T, []) :=
  decodeTape_encodeTapeAppend T []

def encodeConfigurationAppend (c : Configuration)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  encodeNatAppend c.state (encodeTapeAppend c.tape suffix)

def encodeConfiguration (c : Configuration) :
    Word MachineCodeSymbol :=
  encodeConfigurationAppend c []

def decodeConfiguration (tokens : Word MachineCodeSymbol) :
    Option (Configuration × Word MachineCodeSymbol) :=
  match decodeNat tokens with
  | none => none
  | some (state, rest) =>
      match decodeTape rest with
      | none => none
      | some (tape, suffix) =>
          some ({ state := state, tape := tape }, suffix)

theorem decodeConfiguration_encodeConfigurationAppend
    (c : Configuration) (suffix : Word MachineCodeSymbol) :
    decodeConfiguration (encodeConfigurationAppend c suffix) =
      some (c, suffix) := by
  cases c
  simp [encodeConfigurationAppend, decodeConfiguration,
    decodeNat_encodeNatAppend, decodeTape_encodeTapeAppend]

theorem decodeConfiguration_encodeConfiguration (c : Configuration) :
    decodeConfiguration (encodeConfiguration c) = some (c, []) :=
  decodeConfiguration_encodeConfigurationAppend c []

def runEncodedConfiguration
    (D : MachineDescription) (steps : Nat)
    (tokens : Word MachineCodeSymbol) :
    Option (Configuration × Word MachineCodeSymbol) :=
  match decodeConfiguration tokens with
  | none => none
  | some (c, suffix) => some (D.runConfig steps c, suffix)

theorem runEncodedConfiguration_encodeConfigurationAppend
    (D : MachineDescription) (steps : Nat)
    (c : Configuration) (suffix : Word MachineCodeSymbol) :
    runEncodedConfiguration D steps
        (encodeConfigurationAppend c suffix) =
      some (D.runConfig steps c, suffix) := by
  simp [runEncodedConfiguration,
    decodeConfiguration_encodeConfigurationAppend]

theorem runEncodedConfiguration_encodeConfiguration
    (D : MachineDescription) (steps : Nat)
    (c : Configuration) :
    runEncodedConfiguration D steps (encodeConfiguration c) =
      some (D.runConfig steps c, []) :=
  runEncodedConfiguration_encodeConfigurationAppend D steps c []

/-!
## Executable bounded simulation

The following Boolean search is the executable core of the textbook dovetailing
argument.  It searches the concrete interpreter up to a stage bound and is
proved equivalent to the trace-level search used by {name}`DovetailProgram`.
-/

def haltsInBool (D : MachineDescription) (n : Nat)
    (w : Word Bool) : Bool :=
  (D.runConfig n (D.initial w)).state == D.halt

theorem haltsInBool_eq_true_iff
    (D : MachineDescription) (n : Nat) (w : Word Bool) :
    haltsInBool D n w = true <-> D.HaltsIn n w := by
  simp [haltsInBool, HaltsIn]

def hitsByBool (D : MachineDescription) (w : Word Bool) :
    Nat -> Bool
  | 0 => haltsInBool D 0 w
  | limit + 1 =>
      hitsByBool D w limit || haltsInBool D (limit + 1) w

theorem hitsByBool_eq_true_iff
    (D : MachineDescription) (w : Word Bool) (limit : Nat) :
    hitsByBool D w limit = true <->
      exists n : Nat, n ≤ limit ∧ D.HaltsIn n w := by
  induction limit with
  | zero =>
      constructor
      · intro h
        exact ⟨0, Nat.le_refl 0,
          (haltsInBool_eq_true_iff D 0 w).mp h⟩
      · intro h
        rcases h with ⟨n, hnle, hhalt⟩
        have hn : n = 0 := by omega
        cases hn
        exact (haltsInBool_eq_true_iff D 0 w).mpr hhalt
  | succ limit ih =>
      constructor
      · intro h
        have hcases :
            hitsByBool D w limit = true ∨
              haltsInBool D (limit + 1) w = true := by
          simpa [hitsByBool] using h
        cases hcases with
        | inl hprev =>
            rcases ih.mp hprev with ⟨n, hnle, hhalt⟩
            exact ⟨n, Nat.le_trans hnle (Nat.le_succ limit), hhalt⟩
        | inr hnow =>
            exact ⟨limit + 1, Nat.le_refl (limit + 1),
              (haltsInBool_eq_true_iff D (limit + 1) w).mp hnow⟩
      · intro h
        rcases h with ⟨n, hnle, hhalt⟩
        by_cases hn : n ≤ limit
        · have hprev : hitsByBool D w limit = true :=
            ih.mpr ⟨n, hn, hhalt⟩
          simp [hitsByBool, hprev]
        · have hnEq : n = limit + 1 := by omega
          cases hnEq
          have hnow : haltsInBool D (limit + 1) w = true :=
            (haltsInBool_eq_true_iff D (limit + 1) w).mpr hhalt
          simp [hitsByBool, hnow]

def boundedDovetailOutput
    (accept reject : MachineDescription)
    (w : Word Bool) (limit : Nat) : Option (Word Bool) :=
  if hitsByBool accept w limit = true then
    some [true]
  else if hitsByBool reject w limit = true then
    some [false]
  else
    none

theorem boundedDovetailOutput_eq_dovetailProgram_run
    (accept reject : MachineDescription)
    (w : Word Bool) (limit : Nat) :
    boundedDovetailOutput accept reject w limit =
      (DovetailProgram
        (fun w n => accept.HaltsIn n w)
        (fun w n => reject.HaltsIn n w)).run w limit := by
  classical
  by_cases haccept : hitsByBool accept w limit = true
  · have hacceptTrace :
      TraceHitsBy (fun w n => accept.HaltsIn n w) w limit :=
        (hitsByBool_eq_true_iff accept w limit).mp haccept
    simp [boundedDovetailOutput, DovetailProgram, haccept, hacceptTrace]
  · have hacceptTrace :
      ¬ TraceHitsBy (fun w n => accept.HaltsIn n w) w limit := by
        intro h
        exact haccept ((hitsByBool_eq_true_iff accept w limit).mpr h)
    by_cases hreject : hitsByBool reject w limit = true
    · have hrejectTrace :
        TraceHitsBy (fun w n => reject.HaltsIn n w) w limit :=
          (hitsByBool_eq_true_iff reject w limit).mp hreject
      simp [boundedDovetailOutput, DovetailProgram, haccept, hacceptTrace,
        hreject, hrejectTrace]
    · have hrejectTrace :
        ¬ TraceHitsBy (fun w n => reject.HaltsIn n w) w limit := by
          intro h
          exact hreject ((hitsByBool_eq_true_iff reject w limit).mpr h)
      simp [boundedDovetailOutput, DovetailProgram, haccept, hacceptTrace,
        hreject, hrejectTrace]

end MachineDescription

end Computability
end FoC

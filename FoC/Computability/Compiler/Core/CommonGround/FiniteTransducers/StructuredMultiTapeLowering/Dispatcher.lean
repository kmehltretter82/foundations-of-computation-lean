import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.Runs

set_option doc.verso true

/-!
# Static dispatcher scaffolding

This module collects the finite-control data used by a future static
three-tape dispatcher.  The physical dispatcher first has to read the three
logical head cells into finite control; only then can it select the structured
row and run the corresponding row machine.
-/

namespace FoC
namespace Computability

open Languages

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

/-- The three logical head-cell reads used by the MVP lowerer. -/
structure ReadTuple3 where
  read0 : Option Bool
  read1 : Option Bool
  read2 : Option Bool
deriving Repr, DecidableEq

namespace ReadTuple3

def toList (r : ReadTuple3) : List (Option Bool) :=
  [r.read0, r.read1, r.read2]

def ofTapes (tapes : List (Tape Bool)) : ReadTuple3 where
  read0 := Tape.read (Description.tapeAt tapes 0)
  read1 := Tape.read (Description.tapeAt tapes 1)
  read2 := Tape.read (Description.tapeAt tapes 2)

def ofConfig (c : Configuration) : ReadTuple3 :=
  ofTapes c.tapes

@[simp] theorem toList_mk
    (read0 read1 read2 : Option Bool) :
    (ReadTuple3.mk read0 read1 read2).toList =
      [read0, read1, read2] := by
  rfl

theorem currentReads_eq_toList_ofTapes
    (D : Description) (hD : D.tapeCount = 3)
    (state : Nat) (tapes : List (Tape Bool)) :
    D.currentReads { state := state, tapes := tapes } =
      (ofTapes tapes).toList := by
  cases D
  cases hD
  rfl

theorem currentReads_eq_toList_ofConfig
    (D : Description) (hD : D.tapeCount = 3)
    (c : Configuration) :
    D.currentReads c = (ofConfig c).toList := by
  cases c with
  | mk state tapes =>
      exact currentReads_eq_toList_ofTapes D hD state tapes

/-- A compact finite-control code for one logical read. -/
def readCode : Option Bool -> Nat
  | none => 0
  | some false => 1
  | some true => 2

theorem readCode_lt_three
    (cell : Option Bool) :
    readCode cell < 3 := by
  cases cell with
  | none => decide
  | some bit =>
      cases bit <;> decide

/-- A compact finite-control code for a three-read tuple. -/
def code (r : ReadTuple3) : Nat :=
  readCode r.read0 + 3 * readCode r.read1 + 9 * readCode r.read2

theorem code_lt_twentySeven
    (r : ReadTuple3) :
    r.code < 27 := by
  cases r with
  | mk read0 read1 read2 =>
      cases read0 with
      | none =>
          cases read1 with
          | none =>
              cases read2 with
              | none => simp [code, readCode]
              | some bit => cases bit <;> simp [code, readCode]
          | some bit1 =>
              cases bit1 <;>
                cases read2 with
                | none => simp [code, readCode]
                | some bit2 => cases bit2 <;> simp [code, readCode]
      | some bit0 =>
          cases bit0 <;>
            cases read1 with
            | none =>
                cases read2 with
                | none => simp [code, readCode]
                | some bit2 => cases bit2 <;> simp [code, readCode]
            | some bit1 =>
                cases bit1 <;>
                  cases read2 with
                  | none => simp [code, readCode]
                  | some bit2 => cases bit2 <;> simp [code, readCode]

end ReadTuple3

/-!
## Branching head-cell readers

The check-only cursor reader used by row machines assumes the expected logical
read is already known.  A static dispatcher needs the dual primitive: read the
encoded logical head-cell code and branch in finite control according to the
discovered value.

The first fragment below starts at the first bit of an encoded logical cell
code.  It preserves the tape, moves right to inspect the second bit, returns
left to the first bit, and exits in one of three caller-supplied target states.
The separator-to-separator dispatcher reader can wrap this fragment after the
finite-table embedding/retargeting utilities are in place.
-/

def branchingReadHeadCellCodeTargetCeiling
    (noneTarget falseTarget trueTarget : Nat) : Nat :=
  Nat.max noneTarget (Nat.max falseTarget trueTarget)

def branchingReadHeadCellCodeStateCount
    (noneTarget falseTarget trueTarget : Nat) : Nat :=
  branchingReadHeadCellCodeTargetCeiling
    noneTarget falseTarget trueTarget + 4

def branchingReadHeadCellCodeHalt
    (noneTarget falseTarget trueTarget : Nat) : Nat :=
  branchingReadHeadCellCodeTargetCeiling
    noneTarget falseTarget trueTarget + 3

def branchingReadHeadCellCodeTarget
    (noneTarget falseTarget trueTarget : Nat) :
    Option Bool -> Nat
  | none => noneTarget
  | some false => falseTarget
  | some true => trueTarget

private theorem branchingReadHeadCellCode_state0_lt
    (noneTarget falseTarget trueTarget : Nat) :
    0 <
      branchingReadHeadCellCodeStateCount
        noneTarget falseTarget trueTarget := by
  unfold branchingReadHeadCellCodeStateCount
  lia

private theorem branchingReadHeadCellCode_state1_lt
    (noneTarget falseTarget trueTarget : Nat) :
    1 <
      branchingReadHeadCellCodeStateCount
        noneTarget falseTarget trueTarget := by
  unfold branchingReadHeadCellCodeStateCount
  lia

private theorem branchingReadHeadCellCode_state2_lt
    (noneTarget falseTarget trueTarget : Nat) :
    2 <
      branchingReadHeadCellCodeStateCount
        noneTarget falseTarget trueTarget := by
  unfold branchingReadHeadCellCodeStateCount
  lia

private theorem branchingReadHeadCellCode_halt_lt
    (noneTarget falseTarget trueTarget : Nat) :
    branchingReadHeadCellCodeHalt noneTarget falseTarget trueTarget <
      branchingReadHeadCellCodeStateCount
        noneTarget falseTarget trueTarget := by
  unfold branchingReadHeadCellCodeHalt
    branchingReadHeadCellCodeStateCount
  lia

private theorem branchingReadHeadCellCode_noneTarget_lt
    (noneTarget falseTarget trueTarget : Nat) :
    noneTarget <
      branchingReadHeadCellCodeStateCount
        noneTarget falseTarget trueTarget := by
  have hle :
      noneTarget ≤
        branchingReadHeadCellCodeTargetCeiling
          noneTarget falseTarget trueTarget := by
    unfold branchingReadHeadCellCodeTargetCeiling
    exact Nat.le_max_left _ _
  unfold branchingReadHeadCellCodeStateCount
  lia

private theorem branchingReadHeadCellCode_falseTarget_lt
    (noneTarget falseTarget trueTarget : Nat) :
    falseTarget <
      branchingReadHeadCellCodeStateCount
        noneTarget falseTarget trueTarget := by
  have hle :
      falseTarget ≤
        branchingReadHeadCellCodeTargetCeiling
          noneTarget falseTarget trueTarget := by
    unfold branchingReadHeadCellCodeTargetCeiling
    exact Nat.le_trans (Nat.le_max_left _ _)
      (Nat.le_max_right _ _)
  unfold branchingReadHeadCellCodeStateCount
  lia

private theorem branchingReadHeadCellCode_trueTarget_lt
    (noneTarget falseTarget trueTarget : Nat) :
    trueTarget <
      branchingReadHeadCellCodeStateCount
        noneTarget falseTarget trueTarget := by
  have hle :
      trueTarget ≤
        branchingReadHeadCellCodeTargetCeiling
          noneTarget falseTarget trueTarget := by
    unfold branchingReadHeadCellCodeTargetCeiling
    exact Nat.le_trans (Nat.le_max_right _ _)
      (Nat.le_max_right _ _)
  unfold branchingReadHeadCellCodeStateCount
  lia

private theorem branchingReadHeadCellCode_source_ne_halt
    {noneTarget falseTarget trueTarget source : Nat}
    (hsource : source ≤ 2) :
    source ≠
      branchingReadHeadCellCodeHalt
        noneTarget falseTarget trueTarget := by
  intro h
  have hlt :
      source <
        branchingReadHeadCellCodeHalt
          noneTarget falseTarget trueTarget := by
    unfold branchingReadHeadCellCodeHalt
    lia
  rw [← h] at hlt
  exact Nat.lt_irrefl source hlt

/--
Branch on the encoded logical head-cell code.

The machine starts on the first bit of the two-bit
{name}`logicalCellCode`.  Normal inputs are:

* {lit}`00` for a blank logical cell;
* {lit}`01` for a false logical cell;
* {lit}`10` for a true logical cell.

The invalid marker-like pattern {lit}`11` intentionally has no normal branch.
-/
def branchingReadHeadCellCodeDescription
    (noneTarget falseTarget trueTarget : Nat) :
    MachineDescription where
  stateCount :=
    branchingReadHeadCellCodeStateCount
      noneTarget falseTarget trueTarget
  start := 0
  halt :=
    branchingReadHeadCellCodeHalt
      noneTarget falseTarget trueTarget
  transitions :=
    [ { source := 0
        read := some false
        write := some false
        move := Direction.right
        target := 1 }
    , { source := 0
        read := some true
        write := some true
        move := Direction.right
        target := 2 }
    , { source := 1
        read := some false
        write := some false
        move := Direction.left
        target := noneTarget }
    , { source := 1
        read := some true
        write := some true
        move := Direction.left
        target := falseTarget }
    , { source := 2
        read := some false
        write := some false
        move := Direction.left
        target := trueTarget } ]

theorem branchingReadHeadCellCodeDescription_wellFormed
    (noneTarget falseTarget trueTarget : Nat) :
    (branchingReadHeadCellCodeDescription
      noneTarget falseTarget trueTarget).WellFormed := by
  refine ⟨
    branchingReadHeadCellCode_state0_lt
      noneTarget falseTarget trueTarget,
    branchingReadHeadCellCode_state0_lt
      noneTarget falseTarget trueTarget,
    branchingReadHeadCellCode_halt_lt
      noneTarget falseTarget trueTarget,
    ?_,
    ?_⟩
  · intro t ht
    simp [branchingReadHeadCellCodeDescription] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact ⟨
        branchingReadHeadCellCode_state0_lt
          noneTarget falseTarget trueTarget,
        branchingReadHeadCellCode_state1_lt
          noneTarget falseTarget trueTarget⟩
    · exact ⟨
        branchingReadHeadCellCode_state0_lt
          noneTarget falseTarget trueTarget,
        branchingReadHeadCellCode_state2_lt
          noneTarget falseTarget trueTarget⟩
    · exact ⟨
        branchingReadHeadCellCode_state1_lt
          noneTarget falseTarget trueTarget,
        branchingReadHeadCellCode_noneTarget_lt
          noneTarget falseTarget trueTarget⟩
    · exact ⟨
        branchingReadHeadCellCode_state1_lt
          noneTarget falseTarget trueTarget,
        branchingReadHeadCellCode_falseTarget_lt
          noneTarget falseTarget trueTarget⟩
    · exact ⟨
        branchingReadHeadCellCode_state2_lt
          noneTarget falseTarget trueTarget,
        branchingReadHeadCellCode_trueTarget_lt
          noneTarget falseTarget trueTarget⟩
  · intro t u ht hu hkey
    simp [branchingReadHeadCellCodeDescription] at ht hu
    rcases ht with rfl | rfl | rfl | rfl | rfl <;>
      rcases hu with rfl | rfl | rfl | rfl | rfl <;>
        simp [TransitionDescription.SameKey] at hkey <;>
        simp [TransitionDescription.SameAction]

theorem branchingReadHeadCellCodeDescription_haltTransitionFree
    (noneTarget falseTarget trueTarget : Nat) :
    (branchingReadHeadCellCodeDescription
      noneTarget falseTarget trueTarget).HaltTransitionFree := by
  intro t ht
  simp [branchingReadHeadCellCodeDescription] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact branchingReadHeadCellCode_source_ne_halt
      (noneTarget := noneTarget)
      (falseTarget := falseTarget)
      (trueTarget := trueTarget)
      (source := 0)
      (by decide)
  · exact branchingReadHeadCellCode_source_ne_halt
      (noneTarget := noneTarget)
      (falseTarget := falseTarget)
      (trueTarget := trueTarget)
      (source := 0)
      (by decide)
  · exact branchingReadHeadCellCode_source_ne_halt
      (noneTarget := noneTarget)
      (falseTarget := falseTarget)
      (trueTarget := trueTarget)
      (source := 1)
      (by decide)
  · exact branchingReadHeadCellCode_source_ne_halt
      (noneTarget := noneTarget)
      (falseTarget := falseTarget)
      (trueTarget := trueTarget)
      (source := 1)
      (by decide)
  · exact branchingReadHeadCellCode_source_ne_halt
      (noneTarget := noneTarget)
      (falseTarget := falseTarget)
      (trueTarget := trueTarget)
      (source := 2)
      (by decide)

theorem branchingReadHeadCellCodeDescription_subroutineReady
    (noneTarget falseTarget trueTarget : Nat) :
    (branchingReadHeadCellCodeDescription
      noneTarget falseTarget trueTarget).SubroutineReady :=
  ⟨branchingReadHeadCellCodeDescription_wellFormed
      noneTarget falseTarget trueTarget,
    branchingReadHeadCellCodeDescription_haltTransitionFree
      noneTarget falseTarget trueTarget⟩

theorem branchingReadHeadCellCodeDescription_runs_none
    (noneTarget falseTarget trueTarget : Nat)
    (left suffix : List (Option Bool)) :
    (branchingReadHeadCellCodeDescription
      noneTarget falseTarget trueTarget).runConfig 2
        { state :=
            (branchingReadHeadCellCodeDescription
              noneTarget falseTarget trueTarget).start
          tape :=
            tapeAtCells left
              (List.append (logicalCellCode none) suffix) } =
      { state := noneTarget
        tape :=
          tapeAtCells left
            (List.append (logicalCellCode none) suffix) } := by
  cases suffix <;>
    simp [branchingReadHeadCellCodeDescription,
      logicalCellCode, MachineDescription.runConfig,
      MachineDescription.stepConfig,
      MachineDescription.lookupTransition,
      MachineDescription.Matches, tapeAtCells, Tape.read,
      Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem branchingReadHeadCellCodeDescription_runs_false
    (noneTarget falseTarget trueTarget : Nat)
    (left suffix : List (Option Bool)) :
    (branchingReadHeadCellCodeDescription
      noneTarget falseTarget trueTarget).runConfig 2
        { state :=
            (branchingReadHeadCellCodeDescription
              noneTarget falseTarget trueTarget).start
          tape :=
            tapeAtCells left
              (List.append (logicalCellCode (some false)) suffix) } =
      { state := falseTarget
        tape :=
          tapeAtCells left
            (List.append (logicalCellCode (some false)) suffix) } := by
  cases suffix <;>
    simp [branchingReadHeadCellCodeDescription,
      logicalCellCode, MachineDescription.runConfig,
      MachineDescription.stepConfig,
      MachineDescription.lookupTransition,
      MachineDescription.Matches, tapeAtCells, Tape.read,
      Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem branchingReadHeadCellCodeDescription_runs_true
    (noneTarget falseTarget trueTarget : Nat)
    (left suffix : List (Option Bool)) :
    (branchingReadHeadCellCodeDescription
      noneTarget falseTarget trueTarget).runConfig 2
        { state :=
            (branchingReadHeadCellCodeDescription
              noneTarget falseTarget trueTarget).start
          tape :=
            tapeAtCells left
              (List.append (logicalCellCode (some true)) suffix) } =
      { state := trueTarget
        tape :=
          tapeAtCells left
            (List.append (logicalCellCode (some true)) suffix) } := by
  cases suffix <;>
    simp [branchingReadHeadCellCodeDescription,
      logicalCellCode, MachineDescription.runConfig,
      MachineDescription.stepConfig,
      MachineDescription.lookupTransition,
      MachineDescription.Matches, tapeAtCells, Tape.read,
      Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem branchingReadHeadCellCodeDescription_runs_cell
    (noneTarget falseTarget trueTarget : Nat)
    (cell : Option Bool)
    (left suffix : List (Option Bool)) :
    (branchingReadHeadCellCodeDescription
      noneTarget falseTarget trueTarget).runConfig 2
        { state :=
            (branchingReadHeadCellCodeDescription
              noneTarget falseTarget trueTarget).start
          tape :=
            tapeAtCells left
              (List.append (logicalCellCode cell) suffix) } =
      { state :=
          branchingReadHeadCellCodeTarget
            noneTarget falseTarget trueTarget cell
        tape :=
          tapeAtCells left
            (List.append (logicalCellCode cell) suffix) } := by
  cases cell with
  | none =>
      simpa [branchingReadHeadCellCodeTarget] using
        branchingReadHeadCellCodeDescription_runs_none
          noneTarget falseTarget trueTarget left suffix
  | some bit =>
      cases bit
      · simpa [branchingReadHeadCellCodeTarget] using
          branchingReadHeadCellCodeDescription_runs_false
            noneTarget falseTarget trueTarget left suffix
      · simpa [branchingReadHeadCellCodeTarget] using
          branchingReadHeadCellCodeDescription_runs_true
            noneTarget falseTarget trueTarget left suffix

theorem branchingReadHeadCellCodeDescription_runsFromHeadCellCode
    (noneTarget falseTarget trueTarget : Nat)
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    {physical : Tape Bool}
    (hcell : AtTapeHeadCellCode logical tapeIndex physical) :
    RunsFromStateTapeEquiv
      (branchingReadHeadCellCodeDescription
        noneTarget falseTarget trueTarget)
      (branchingReadHeadCellCodeDescription
        noneTarget falseTarget trueTarget).start
      (branchingReadHeadCellCodeTarget
        noneTarget falseTarget trueTarget
        (Tape.read (Description.tapeAt logical tapeIndex)))
      physical
      physical := by
  rcases hcell with ⟨T, rest, hdrop, hphysical⟩
  have htapeAt : Description.tapeAt logical tapeIndex = T :=
    description_tapeAt_eq_of_drop_eq_cons hdrop
  let pre :=
    List.append
      (encodedPrefixBeforeTape logical tapeIndex)
      (List.append tapeSeparatorCells
        (List.append (logicalCellListCode T.left.reverse)
          headMarkerCells))
  let suffix :=
    List.append (logicalCellListCode T.right)
      (encodedStructuredTapeCells rest)
  have hrun :=
    branchingReadHeadCellCodeDescription_runs_cell
      noneTarget falseTarget trueTarget T.head
      pre.reverse suffix
  refine ⟨2, physical, ?_, Tape.Equiv.refl physical⟩
  rw [hphysical]
  simpa [pre, suffix, tapeAtEncodedSplit, htapeAt, Tape.read,
    List.append_assoc] using hrun

/--
Lookup a structured row after the static dispatcher has read the three logical
head cells into finite control.
-/
def lookupTransitionFromReadTuple3
    (D : Description) (state : Nat) (reads : ReadTuple3) :
    Option Transition :=
  D.transitions.find? (Description.Matches state reads.toList)

theorem lookupTransitionFromReadTuple3_eq_lookupTransition
    (D : Description) (hD : D.tapeCount = 3)
    (c : Configuration) :
    lookupTransitionFromReadTuple3 D c.state (ReadTuple3.ofConfig c) =
      D.lookupTransition c := by
  simp [lookupTransitionFromReadTuple3, Description.lookupTransition,
    ReadTuple3.currentReads_eq_toList_ofConfig D hD c]

theorem lookupTransitionFromReadTuple3_mem
    {D : Description} {state : Nat} {reads : ReadTuple3}
    {t : Transition}
    (hlookup :
      lookupTransitionFromReadTuple3 D state reads = some t) :
    t ∈ D.transitions := by
  unfold lookupTransitionFromReadTuple3 at hlookup
  let p := Description.Matches state reads.toList
  have hmem :
      forall rows : List Transition,
        rows.find? p = some t -> t ∈ rows := by
    intro rows
    induction rows with
    | nil =>
        intro hnil
        simp at hnil
    | cons row rest ih =>
        intro hfind
        rw [List.find?_cons] at hfind
        cases hm : p row
        · simp [hm] at hfind
          have ht : t ∈ rest := ih hfind
          simp [ht]
        · simp [hm] at hfind
          cases hfind
          simp
  exact hmem D.transitions hlookup

theorem lookupTransitionFromReadTuple3_match
    {D : Description} {state : Nat} {reads : ReadTuple3}
    {t : Transition}
    (hlookup :
      lookupTransitionFromReadTuple3 D state reads = some t) :
    t.source = state ∧ t.reads = reads.toList := by
  unfold lookupTransitionFromReadTuple3 at hlookup
  have hpred :
      Description.Matches state reads.toList t = true :=
    List.find?_some hlookup
  simpa [Description.Matches] using hpred

theorem SupportsReadWriteRows3.lookupFromReadTuple_lowersGuardedTransitionEquiv_withRefresh
    {D : Description} (hD : SupportsReadWriteRows3 D)
    {state : Nat} {reads : ReadTuple3} {t : Transition}
    (hlookup :
      lookupTransitionFromReadTuple3 D state reads = some t)
    {refresh : MachineDescription}
    (hrefresh : LogicalEquivGuardRefreshContract refresh) :
    LowersGuardedTransitionEquiv D t
      (readWriteRow3DescriptionOfRowWithRefresh t refresh) :=
  hD.row_lowersGuardedTransitionEquiv_withRefresh
    (lookupTransitionFromReadTuple3_mem hlookup) hrefresh

namespace StaticDispatcherState

/-- Canonical physical ready state for a represented structured state. -/
def ready (state : Nat) : Nat :=
  state

/--
Finite-control state after collecting a three-read tuple for a structured
state.  This is only a state-layout convention; the concrete scanner machine
will prove it reaches these states.
-/
def afterRead (D : Description) (state : Nat) (reads : ReadTuple3) :
    Nat :=
  D.stateCount + 27 * state + reads.code

theorem ready_start
    (D : Description) :
    ready D.start = D.start := by
  rfl

theorem ready_halt
    (D : Description) :
    ready D.halt = D.halt := by
  rfl

end StaticDispatcherState

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC

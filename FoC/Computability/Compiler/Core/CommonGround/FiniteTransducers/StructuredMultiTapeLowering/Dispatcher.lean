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

theorem ofTapes_guardLogicalTapes
    (tapes : List (Tape Bool)) :
    ofTapes (guardLogicalTapes tapes) = ofTapes tapes := by
  cases tapes with
  | nil =>
      rfl
  | cons T rest =>
      cases rest with
      | nil =>
          rfl
      | cons U rest =>
          cases rest with
          | nil =>
              rfl
          | cons V rest =>
              simp [ofTapes, tapeAt_guardLogicalTapes_read]

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

def code01 (read0 read1 : Option Bool) : Nat :=
  readCode read0 + 3 * readCode read1

theorem code01_lt_nine
    (read0 read1 : Option Bool) :
    code01 read0 read1 < 9 := by
  have h0 := readCode_lt_three read0
  have h1 := readCode_lt_three read1
  unfold code01
  lia

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

theorem branchingReadHeadCellCodeDescription_runFromHeadCellCode
    (noneTarget falseTarget trueTarget : Nat)
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    {physical : Tape Bool}
    (hcell : AtTapeHeadCellCode logical tapeIndex physical) :
    (branchingReadHeadCellCodeDescription
      noneTarget falseTarget trueTarget).runConfig 2
        { state :=
            (branchingReadHeadCellCodeDescription
              noneTarget falseTarget trueTarget).start
          tape := physical } =
      { state :=
          branchingReadHeadCellCodeTarget
            noneTarget falseTarget trueTarget
            (Tape.read (Description.tapeAt logical tapeIndex))
        tape := physical } := by
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
  rw [hphysical]
  simpa [pre, suffix, tapeAtEncodedSplit, htapeAt, Tape.read,
    List.append_assoc] using hrun

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
  refine ⟨2, physical, ?_, Tape.Equiv.refl physical⟩
  exact
    branchingReadHeadCellCodeDescription_runFromHeadCellCode
      noneTarget falseTarget trueTarget hcell

namespace BranchingHeadCellReturn

def noneStart : Nat := 3
def falseStart : Nat := 6
def trueStart : Nat := 9

def noneExit : Nat := noneStart + returnToOpeningSeparatorDescription.halt
def falseExit : Nat := falseStart + returnToOpeningSeparatorDescription.halt
def trueExit : Nat := trueStart + returnToOpeningSeparatorDescription.halt

def stateCount : Nat := 13
def halt : Nat := 12

def startForRead : Option Bool -> Nat
  | none => noneStart
  | some false => falseStart
  | some true => trueStart

def targetForRead : Option Bool -> Nat
  | none => noneExit
  | some false => falseExit
  | some true => trueExit

def returnCopyTransitions (offset : Nat) :
    List TransitionDescription :=
  returnToOpeningSeparatorDescription.transitions.map
    (TransitionDescription.offsetStates offset)

end BranchingHeadCellReturn

/--
Branch on the encoded head-cell code and then return to the selected tape's
separator, preserving the read value in the final finite-control state.

This table has three disjoint copies of
{name}`returnToOpeningSeparatorDescription`, one for each logical read value.
-/
def branchingReadHeadCellAndReturnToSeparatorDescription :
    MachineDescription where
  stateCount := BranchingHeadCellReturn.stateCount
  start := 0
  halt := BranchingHeadCellReturn.halt
  transitions :=
    (branchingReadHeadCellCodeDescription
      BranchingHeadCellReturn.noneStart
      BranchingHeadCellReturn.falseStart
      BranchingHeadCellReturn.trueStart).transitions ++
    BranchingHeadCellReturn.returnCopyTransitions
      BranchingHeadCellReturn.noneStart ++
    BranchingHeadCellReturn.returnCopyTransitions
      BranchingHeadCellReturn.falseStart ++
    BranchingHeadCellReturn.returnCopyTransitions
      BranchingHeadCellReturn.trueStart

theorem branchingReadHeadCellAndReturnToSeparatorDescription_wellFormed :
    branchingReadHeadCellAndReturnToSeparatorDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := branchingReadHeadCellAndReturnToSeparatorDescription.transitions)
      (stateCount :=
        branchingReadHeadCellAndReturnToSeparatorDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := branchingReadHeadCellAndReturnToSeparatorDescription.transitions)
      (by decide)

theorem
    branchingReadHeadCellAndReturnToSeparatorDescription_haltTransitionFree :
    branchingReadHeadCellAndReturnToSeparatorDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := branchingReadHeadCellAndReturnToSeparatorDescription.transitions)
    (state := branchingReadHeadCellAndReturnToSeparatorDescription.halt)
    (by decide)

theorem branchingReadHeadCellAndReturnToSeparatorDescription_subroutineReady :
    branchingReadHeadCellAndReturnToSeparatorDescription.SubroutineReady :=
  ⟨branchingReadHeadCellAndReturnToSeparatorDescription_wellFormed,
    branchingReadHeadCellAndReturnToSeparatorDescription_haltTransitionFree⟩

theorem branchingReadHeadCellAndReturnToSeparatorDescription_run_branch
    (cell : Option Bool)
    (left suffix : List (Option Bool)) :
    branchingReadHeadCellAndReturnToSeparatorDescription.runConfig 2
        { state :=
            branchingReadHeadCellAndReturnToSeparatorDescription.start
          tape :=
            tapeAtCells left
              (List.append (logicalCellCode cell) suffix) } =
      { state := BranchingHeadCellReturn.startForRead cell
        tape :=
          tapeAtCells left
            (List.append (logicalCellCode cell) suffix) } := by
  cases cell with
  | none =>
      cases suffix <;>
        simp [branchingReadHeadCellAndReturnToSeparatorDescription,
          branchingReadHeadCellCodeDescription,
          BranchingHeadCellReturn.noneStart,
          BranchingHeadCellReturn.falseStart,
          BranchingHeadCellReturn.trueStart,
          BranchingHeadCellReturn.startForRead,
          BranchingHeadCellReturn.returnCopyTransitions,
          returnToOpeningSeparatorDescription,
          logicalCellCode, MachineDescription.runConfig,
          MachineDescription.stepConfig,
          MachineDescription.lookupTransition,
          MachineDescription.Matches, tapeAtCells, Tape.read,
          Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
  | some bit =>
      cases bit <;> cases suffix <;>
        simp [branchingReadHeadCellAndReturnToSeparatorDescription,
          branchingReadHeadCellCodeDescription,
          BranchingHeadCellReturn.noneStart,
          BranchingHeadCellReturn.falseStart,
          BranchingHeadCellReturn.trueStart,
          BranchingHeadCellReturn.startForRead,
          BranchingHeadCellReturn.returnCopyTransitions,
          returnToOpeningSeparatorDescription,
          logicalCellCode, MachineDescription.runConfig,
          MachineDescription.stepConfig,
          MachineDescription.lookupTransition,
          MachineDescription.Matches, tapeAtCells, Tape.read,
          Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

private theorem
    branchingReadHeadCellAndReturnToSeparatorDescription_return_step_bit
    (read : Option Bool)
    (left right : List (Option Bool)) (previous current : Bool) :
    branchingReadHeadCellAndReturnToSeparatorDescription.runConfig 1
        { state := BranchingHeadCellReturn.startForRead read
          tape := tapeAtCells (some previous :: left)
            (some current :: right) } =
      { state := BranchingHeadCellReturn.startForRead read
        tape := tapeAtCells left
          (some previous :: some current :: right) } := by
  cases read with
  | none =>
      cases previous <;> cases current <;> cases right <;>
        simp [branchingReadHeadCellAndReturnToSeparatorDescription,
          branchingReadHeadCellCodeDescription,
          BranchingHeadCellReturn.noneStart,
          BranchingHeadCellReturn.falseStart,
          BranchingHeadCellReturn.trueStart,
          BranchingHeadCellReturn.startForRead,
          BranchingHeadCellReturn.returnCopyTransitions,
          TransitionDescription.offsetStates,
          returnToOpeningSeparatorDescription,
          MachineDescription.runConfig,
          MachineDescription.stepConfig,
          MachineDescription.lookupTransition,
          MachineDescription.Matches, tapeAtCells, Tape.read,
          Tape.write, Tape.move, Tape.moveLeft]
  | some bit =>
      cases bit <;> cases previous <;> cases current <;>
        cases right <;>
          simp [branchingReadHeadCellAndReturnToSeparatorDescription,
            branchingReadHeadCellCodeDescription,
            BranchingHeadCellReturn.noneStart,
            BranchingHeadCellReturn.falseStart,
            BranchingHeadCellReturn.trueStart,
            BranchingHeadCellReturn.startForRead,
            BranchingHeadCellReturn.returnCopyTransitions,
            TransitionDescription.offsetStates,
            returnToOpeningSeparatorDescription,
            MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition,
            MachineDescription.Matches, tapeAtCells, Tape.read,
            Tape.write, Tape.move, Tape.moveLeft]

private theorem
    branchingReadHeadCellAndReturnToSeparatorDescription_return_step_current
    (read : Option Bool)
    (left right : List (Option Bool)) (current : Bool) :
    branchingReadHeadCellAndReturnToSeparatorDescription.runConfig 1
        { state := BranchingHeadCellReturn.startForRead read
          tape := tapeAtCells (none :: left) (some current :: right) } =
      { state := BranchingHeadCellReturn.startForRead read
        tape := tapeAtCells left (none :: some current :: right) } := by
  cases read with
  | none =>
      cases current <;> cases right <;>
        simp [branchingReadHeadCellAndReturnToSeparatorDescription,
          branchingReadHeadCellCodeDescription,
          BranchingHeadCellReturn.noneStart,
          BranchingHeadCellReturn.falseStart,
          BranchingHeadCellReturn.trueStart,
          BranchingHeadCellReturn.startForRead,
          BranchingHeadCellReturn.returnCopyTransitions,
          TransitionDescription.offsetStates,
          returnToOpeningSeparatorDescription,
          MachineDescription.runConfig,
          MachineDescription.stepConfig,
          MachineDescription.lookupTransition,
          MachineDescription.Matches, tapeAtCells, Tape.read,
          Tape.write, Tape.move, Tape.moveLeft]
  | some bit =>
      cases bit <;> cases current <;> cases right <;>
        simp [branchingReadHeadCellAndReturnToSeparatorDescription,
          branchingReadHeadCellCodeDescription,
          BranchingHeadCellReturn.noneStart,
          BranchingHeadCellReturn.falseStart,
          BranchingHeadCellReturn.trueStart,
          BranchingHeadCellReturn.startForRead,
          BranchingHeadCellReturn.returnCopyTransitions,
          TransitionDescription.offsetStates,
          returnToOpeningSeparatorDescription,
          MachineDescription.runConfig,
          MachineDescription.stepConfig,
          MachineDescription.lookupTransition,
          MachineDescription.Matches, tapeAtCells, Tape.read,
          Tape.write, Tape.move, Tape.moveLeft]

private theorem
    branchingReadHeadCellAndReturnToSeparatorDescription_return_finish
    (read : Option Bool)
    (left right : List (Option Bool)) (current : Bool) :
    branchingReadHeadCellAndReturnToSeparatorDescription.runConfig 2
        { state := BranchingHeadCellReturn.startForRead read
          tape := tapeAtCells left (none :: some current :: right) } =
      { state := BranchingHeadCellReturn.targetForRead read
        tape := tapeAtCells left (none :: some current :: right) } := by
  cases read with
  | none =>
      cases current <;> cases left <;> cases right <;>
        simp [branchingReadHeadCellAndReturnToSeparatorDescription,
          branchingReadHeadCellCodeDescription,
          BranchingHeadCellReturn.noneStart,
          BranchingHeadCellReturn.falseStart,
          BranchingHeadCellReturn.trueStart,
          BranchingHeadCellReturn.startForRead,
          BranchingHeadCellReturn.targetForRead,
          BranchingHeadCellReturn.noneExit,
          BranchingHeadCellReturn.returnCopyTransitions,
          TransitionDescription.offsetStates,
          returnToOpeningSeparatorDescription,
          MachineDescription.runConfig,
          MachineDescription.stepConfig,
          MachineDescription.lookupTransition,
          MachineDescription.Matches, tapeAtCells, Tape.read,
          Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
  | some bit =>
      cases bit <;> cases current <;> cases left <;>
        cases right <;>
          simp [branchingReadHeadCellAndReturnToSeparatorDescription,
            branchingReadHeadCellCodeDescription,
            BranchingHeadCellReturn.noneStart,
            BranchingHeadCellReturn.falseStart,
            BranchingHeadCellReturn.trueStart,
            BranchingHeadCellReturn.startForRead,
            BranchingHeadCellReturn.targetForRead,
            BranchingHeadCellReturn.falseExit,
            BranchingHeadCellReturn.trueExit,
            BranchingHeadCellReturn.returnCopyTransitions,
            TransitionDescription.offsetStates,
            returnToOpeningSeparatorDescription,
            MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition,
            MachineDescription.Matches, tapeAtCells, Tape.read,
            Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem branchingReadHeadCellAndReturnToSeparatorDescription_run_return
    (read : Option Bool)
    (scanStack : Word Bool) (current : Bool)
    (leftBase right : List (Option Bool)) :
    branchingReadHeadCellAndReturnToSeparatorDescription.runConfig
        (scanStack.length + 3)
        { state := BranchingHeadCellReturn.startForRead read
          tape :=
            tapeAtCells
              (List.append (scanStack.map some) (none :: leftBase))
              (some current :: right) } =
      { state := BranchingHeadCellReturn.targetForRead read
        tape :=
          tapeAtCells leftBase
            (none ::
              List.append (scanStack.reverse.map some)
                (some current :: right)) } := by
  induction scanStack generalizing current right with
  | nil =>
      simp only [List.length_nil, Nat.zero_add, List.map_nil,
        List.reverse_nil]
      rw [show 3 = 1 + 2 by rfl]
      rw [MachineDescription.runConfig_add]
      change
        branchingReadHeadCellAndReturnToSeparatorDescription.runConfig 2
            (branchingReadHeadCellAndReturnToSeparatorDescription.runConfig 1
              { state := BranchingHeadCellReturn.startForRead read
                tape := tapeAtCells (none :: leftBase)
                  (some current :: right) }) =
          { state := BranchingHeadCellReturn.targetForRead read
            tape := tapeAtCells leftBase
              (none :: some current :: right) }
      rw [branchingReadHeadCellAndReturnToSeparatorDescription_return_step_current]
      exact
        branchingReadHeadCellAndReturnToSeparatorDescription_return_finish
          read leftBase right current
  | cons bit rest ih =>
      have hlen :
          (bit :: rest).length + 3 = 1 + (rest.length + 3) := by
        simp
        lia
      rw [hlen]
      rw [MachineDescription.runConfig_add]
      simp only [List.map_cons]
      change
        branchingReadHeadCellAndReturnToSeparatorDescription.runConfig
            (rest.length + 3)
            (branchingReadHeadCellAndReturnToSeparatorDescription.runConfig 1
              { state := BranchingHeadCellReturn.startForRead read
                tape :=
                  tapeAtCells
                    (some bit ::
                      List.append (List.map some rest)
                        (none :: leftBase))
                    (some current :: right) }) =
          { state := BranchingHeadCellReturn.targetForRead read
            tape :=
              tapeAtCells leftBase
                (none ::
                  List.append (List.map some (bit :: rest).reverse)
                    (some current :: right)) }
      rw [branchingReadHeadCellAndReturnToSeparatorDescription_return_step_bit]
      have htail :=
        ih bit (some current :: right)
      simpa [List.reverse_cons, List.map_append, List.append_assoc]
        using htail

private theorem list_index_le_length_of_drop_eq_cons
    {α : Type} {xs : List α} {index : Nat}
    {x : α} {rest : List α}
    (hdrop : xs.drop index = x :: rest) :
    index ≤ xs.length := by
  induction index generalizing xs with
  | zero =>
      exact Nat.zero_le xs.length
  | succ index ih =>
      cases xs with
      | nil =>
          simp at hdrop
      | cons y ys =>
          simp at hdrop
          exact Nat.succ_le_succ (ih hdrop)

theorem
    branchingReadHeadCellAndReturnToSeparatorDescription_runsFromHeadCellCode
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    {physical : Tape Bool}
    (hcell : AtTapeHeadCellCode logical tapeIndex physical) :
    exists separatorPhysical : Tape Bool,
      AtTapeSeparator logical tapeIndex separatorPhysical ∧
        RunsFromStateTapeEquiv
          branchingReadHeadCellAndReturnToSeparatorDescription
          branchingReadHeadCellAndReturnToSeparatorDescription.start
          (BranchingHeadCellReturn.targetForRead
            (Tape.read (Description.tapeAt logical tapeIndex)))
          physical
          separatorPhysical := by
  rcases hcell with ⟨T, rest, hdrop, hTin⟩
  have htapeAt : Description.tapeAt logical tapeIndex = T :=
    description_tapeAt_eq_of_drop_eq_cons hdrop
  rcases logicalCellBits_exists_cons T.head with
    ⟨headBit, headRest, hheadBits⟩
  let leftBits := logicalCellListBits T.left.reverse
  let scanStack := List.append [true, true] leftBits.reverse
  let suffix :=
    List.append (logicalCellListCode T.right)
      (encodedStructuredTapeCells rest)
  let pre :=
    List.append
      (encodedPrefixBeforeTape logical tapeIndex)
      (List.append tapeSeparatorCells
        (List.append (logicalCellListCode T.left.reverse)
          headMarkerCells))
  let Tout :=
    tapeAtEncodedSplit
      (encodedPrefixBeforeTape logical tapeIndex)
      (List.append tapeSeparatorCells
        (List.append (logicalTapeCode T)
          (encodedStructuredTapeCells rest)))
  have hrun :
      branchingReadHeadCellAndReturnToSeparatorDescription.runConfig
          (2 + (scanStack.length + 3))
          { state :=
              branchingReadHeadCellAndReturnToSeparatorDescription.start
            tape := physical } =
        { state := BranchingHeadCellReturn.targetForRead T.head
          tape := Tout } := by
    rw [hTin]
    rw [MachineDescription.runConfig_add]
    have hbranch :=
      branchingReadHeadCellAndReturnToSeparatorDescription_run_branch
        T.head pre.reverse suffix
    change
      branchingReadHeadCellAndReturnToSeparatorDescription.runConfig
          (scanStack.length + 3)
          (branchingReadHeadCellAndReturnToSeparatorDescription.runConfig 2
            { state :=
                branchingReadHeadCellAndReturnToSeparatorDescription.start
              tape :=
                tapeAtCells pre.reverse
                  (List.append (logicalCellCode T.head) suffix) }) =
        { state := BranchingHeadCellReturn.targetForRead T.head
          tape := Tout }
    rw [hbranch]
    have hreturn :=
      branchingReadHeadCellAndReturnToSeparatorDescription_run_return
        T.head scanStack headBit
        (encodedPrefixBeforeTape logical tapeIndex).reverse
        (List.append (headRest.map some) suffix)
    simpa [Tout, pre, scanStack, leftBits, suffix,
      tapeAtEncodedSplit, logicalTapeCode, hheadBits,
      headMarkerCells, tapeSeparatorCells, List.reverse_append,
      List.map_reverse, List.map_append, List.append_assoc] using hreturn
  refine ⟨Tout, ?_, ?_⟩
  · constructor
    · exact list_index_le_length_of_drop_eq_cons hdrop
    · simp [Tout, tapeAtEncodedSplit, encodedSuffixFromTape, hdrop,
        tapeSeparatorCells]
  · refine ⟨2 + (scanStack.length + 3), Tout, ?_, Tape.Equiv.refl Tout⟩
    simpa [htapeAt, Tape.read] using hrun

def branchingEnterReadHeadCellDescription
    (noneTarget falseTarget trueTarget : Nat) :
    MachineDescription :=
  canonicalPrimitiveSeqDescription
    cursorEnterAndMoveToHeadCellDescription
    (branchingReadHeadCellCodeDescription
      noneTarget falseTarget trueTarget)

def branchingEnterReadHeadCellTarget
    (noneTarget falseTarget trueTarget : Nat) :
    Option Bool -> Nat :=
  fun cell =>
    canonicalPrimitiveSeqRightStateOffset
        cursorEnterAndMoveToHeadCellDescription +
      branchingReadHeadCellCodeTarget
        noneTarget falseTarget trueTarget cell

theorem branchingEnterReadHeadCellDescription_subroutineReady
    (noneTarget falseTarget trueTarget : Nat) :
    (branchingEnterReadHeadCellDescription
      noneTarget falseTarget trueTarget).SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    (cursorEnterAndMoveToHeadCellDescription_contract 0).subroutineReady
    (branchingReadHeadCellCodeDescription_subroutineReady
      noneTarget falseTarget trueTarget)

theorem branchingEnterReadHeadCellDescription_runsFromSeparator
    (noneTarget falseTarget trueTarget : Nat)
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    {physical : Tape Bool}
    (hseparator : AtExistingTapeSeparator logical tapeIndex physical) :
    exists headPhysical : Tape Bool,
      AtTapeHeadCellCode logical tapeIndex headPhysical ∧
        RunsFromStateTapeEquiv
          (branchingEnterReadHeadCellDescription
            noneTarget falseTarget trueTarget)
          (branchingEnterReadHeadCellDescription
            noneTarget falseTarget trueTarget).start
          (branchingEnterReadHeadCellTarget
            noneTarget falseTarget trueTarget
            (Tape.read (Description.tapeAt logical tapeIndex)))
          physical
          headPhysical := by
  rcases
      (cursorEnterAndMoveToHeadCellDescription_contract
        tapeIndex).realizes logical physical hseparator with
    ⟨headPhysical, henter, hcell⟩
  have hmove :
      Tape.move Direction.left
          (Tape.move Direction.right headPhysical) =
        headPhysical :=
    atTapeHeadCellCode_moveLeft_moveRight hcell
  have hbranch :
      exists nB : Nat,
        (branchingReadHeadCellCodeDescription
          noneTarget falseTarget trueTarget).runConfig nB
            { state :=
                (branchingReadHeadCellCodeDescription
                  noneTarget falseTarget trueTarget).start
              tape :=
                Tape.move Direction.left
                  (Tape.move Direction.right headPhysical) } =
          { state :=
              branchingReadHeadCellCodeTarget
                noneTarget falseTarget trueTarget
                (Tape.read (Description.tapeAt logical tapeIndex))
            tape := headPhysical } := by
    refine ⟨2, ?_⟩
    rw [hmove]
    exact
      branchingReadHeadCellCodeDescription_runFromHeadCellCode
        noneTarget falseTarget trueTarget hcell
  rcases
      canonicalPrimitiveSeqDescription_reaches_right_state
        (A := cursorEnterAndMoveToHeadCellDescription)
        (B :=
          branchingReadHeadCellCodeDescription
            noneTarget falseTarget trueTarget)
        (cursorEnterAndMoveToHeadCellDescription_contract
          tapeIndex).subroutineReady
        (branchingReadHeadCellCodeDescription_subroutineReady
          noneTarget falseTarget trueTarget)
        henter hbranch with
    ⟨n, hrun⟩
  exact
    ⟨headPhysical, hcell,
      ⟨n, headPhysical, by
        simpa [branchingEnterReadHeadCellDescription,
          branchingEnterReadHeadCellTarget] using hrun,
        Tape.Equiv.refl headPhysical⟩⟩

def branchingSeparatorReadHeadCellDescription :
    MachineDescription :=
  canonicalPrimitiveSeqDescription
    cursorEnterAndMoveToHeadCellDescription
    branchingReadHeadCellAndReturnToSeparatorDescription

def branchingSeparatorReadHeadCellTarget :
    Option Bool -> Nat :=
  fun cell =>
    canonicalPrimitiveSeqRightStateOffset
        cursorEnterAndMoveToHeadCellDescription +
      BranchingHeadCellReturn.targetForRead cell

theorem branchingSeparatorReadHeadCellDescription_subroutineReady :
    branchingSeparatorReadHeadCellDescription.SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    (cursorEnterAndMoveToHeadCellDescription_contract 0).subroutineReady
    branchingReadHeadCellAndReturnToSeparatorDescription_subroutineReady

theorem branchingSeparatorReadHeadCellDescription_runsFromSeparator
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    {physical : Tape Bool}
    (hseparator : AtExistingTapeSeparator logical tapeIndex physical) :
    exists separatorPhysical : Tape Bool,
      AtTapeSeparator logical tapeIndex separatorPhysical ∧
        RunsFromStateTapeEquiv
          branchingSeparatorReadHeadCellDescription
          branchingSeparatorReadHeadCellDescription.start
          (branchingSeparatorReadHeadCellTarget
            (Tape.read (Description.tapeAt logical tapeIndex)))
          physical
          separatorPhysical := by
  rcases
      (cursorEnterAndMoveToHeadCellDescription_contract
        tapeIndex).realizes logical physical hseparator with
    ⟨headPhysical, henter, hcell⟩
  have hmove :
      Tape.move Direction.left
          (Tape.move Direction.right headPhysical) =
        headPhysical :=
    atTapeHeadCellCode_moveLeft_moveRight hcell
  rcases
      branchingReadHeadCellAndReturnToSeparatorDescription_runsFromHeadCellCode
        hcell with
    ⟨separatorPhysical, hsep, hbranchReturn⟩
  rcases hbranchReturn with
    ⟨nB, actualSeparator, hbranchReturnRun, hactual⟩
  have hBReach :
      exists nB : Nat,
        branchingReadHeadCellAndReturnToSeparatorDescription.runConfig nB
            { state :=
                branchingReadHeadCellAndReturnToSeparatorDescription.start
              tape :=
                Tape.move Direction.left
                  (Tape.move Direction.right headPhysical) } =
          { state :=
              BranchingHeadCellReturn.targetForRead
                (Tape.read (Description.tapeAt logical tapeIndex))
            tape := actualSeparator } := by
    refine ⟨nB, ?_⟩
    rw [hmove]
    exact hbranchReturnRun
  rcases
      canonicalPrimitiveSeqDescription_reaches_right_state
        (A := cursorEnterAndMoveToHeadCellDescription)
        (B := branchingReadHeadCellAndReturnToSeparatorDescription)
        (cursorEnterAndMoveToHeadCellDescription_contract
          tapeIndex).subroutineReady
        branchingReadHeadCellAndReturnToSeparatorDescription_subroutineReady
        henter hBReach with
    ⟨n, hrun⟩
  exact
    ⟨separatorPhysical, hsep,
      ⟨n, actualSeparator, by
        simpa [branchingSeparatorReadHeadCellDescription,
          branchingSeparatorReadHeadCellTarget] using hrun,
        hactual⟩⟩

/-!
## Branching readers from the canonical block start

These wrappers reuse the existing seek routines and the one-head branching
separator reader above.  They deliberately stop at the selected tape separator:
the later static dispatcher assembly will add the finite-control copies needed
to return to the block start while preserving the accumulated read tuple.
-/

private theorem HasAtLeastThreeTapes_drop_two_exists
    {logical : List (Tape Bool)}
    (hshape : HasAtLeastThreeTapes logical) :
    exists T : Tape Bool, exists rest : List (Tape Bool),
      logical.drop 2 = T :: rest := by
  rcases hshape with ⟨T, U, V, rest, hlogical⟩
  subst hlogical
  exact ⟨V, rest, rfl⟩

private theorem HasAtLeastThreeTapes_drop_one_exists
    {logical : List (Tape Bool)}
    (hshape : HasAtLeastThreeTapes logical) :
    exists T : Tape Bool, exists rest : List (Tape Bool),
      logical.drop 1 = T :: rest := by
  rcases hshape with ⟨T, U, V, rest, hlogical⟩
  subst hlogical
  exact ⟨U, V :: rest, rfl⟩

private theorem guardedAtExistingTapeSeparator_zero_of_length_three
    {logical : List (Tape Bool)}
    (hlength : logical.length = 3) :
    AtExistingTapeSeparator (guardLogicalTapes logical) 0
      (encodedGuardedStructuredTapes logical) := by
  cases logical with
  | nil =>
      simp at hlength
  | cons T rest =>
      exact
        ⟨by
          simpa [encodedGuardedStructuredTapes] using
            atTapeSeparator_zero_self (guardLogicalTapes (T :: rest)),
          guardLogicalTape T, guardLogicalTapes rest,
          by simp [guardLogicalTapes]⟩

private theorem guarded_drop_one_exists_of_length_three
    {logical : List (Tape Bool)}
    (hlength : logical.length = 3) :
    exists T : Tape Bool, exists rest : List (Tape Bool),
      (guardLogicalTapes logical).drop 1 = T :: rest := by
  cases logical with
  | nil =>
      simp at hlength
  | cons T rest =>
      cases rest with
      | nil =>
          simp at hlength
      | cons U rest =>
          exact
            ⟨guardLogicalTape U, guardLogicalTapes rest,
              by simp [guardLogicalTapes]⟩

private theorem guarded_hasAtLeastThreeTapes_of_length_three
    {logical : List (Tape Bool)}
    (hlength : logical.length = 3) :
    HasAtLeastThreeTapes (guardLogicalTapes logical) := by
  cases logical with
  | nil =>
      simp at hlength
  | cons T rest =>
      cases rest with
      | nil =>
          simp at hlength
      | cons U rest =>
          cases rest with
          | nil =>
              simp at hlength
          | cons V rest =>
              exact
                ⟨guardLogicalTape T, guardLogicalTape U,
                  guardLogicalTape V, guardLogicalTapes rest,
                  by simp [guardLogicalTapes]⟩

theorem returnFromTape1SeparatorToBlockStartDescription_runsFromTape1Separator
    {logical : List (Tape Bool)} {physical : Tape Bool}
    (hseparator : AtTapeSeparator logical 1 physical) :
    exists blockStartPhysical : Tape Bool,
      AtTapeSeparator logical 0 blockStartPhysical ∧
        RunsFromStateTapeEquiv
          returnFromTape1SeparatorToBlockStartDescription
          returnFromTape1SeparatorToBlockStartDescription.start
          returnFromTape1SeparatorToBlockStartDescription.halt
          physical
          blockStartPhysical := by
  rcases
      returnFromTape1SeparatorToBlockStartDescription_contract.realizes
        logical physical hseparator with
    ⟨blockStartPhysical, hhalts, hblockStart⟩
  rcases MachineDescription.runConfig_eq_halt_of_haltsFromTape hhalts with
    ⟨n, hrun⟩
  exact
    ⟨blockStartPhysical, hblockStart,
      ⟨n, blockStartPhysical, hrun,
        Tape.Equiv.refl blockStartPhysical⟩⟩

def returnFromTape2SeparatorToBlockStartDescription :
    MachineDescription :=
  canonicalPrimitiveSeqDescription
    returnFromNextSeparatorToCurrentSeparatorDescription
    returnFromTape1SeparatorToBlockStartDescription

theorem returnFromTape2SeparatorToBlockStartDescription_subroutineReady :
    returnFromTape2SeparatorToBlockStartDescription.SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    (returnFromNextSeparatorToCurrentSeparatorDescription_contract
      1).subroutineReady
    returnFromTape1SeparatorToBlockStartDescription_contract.subroutineReady

theorem returnFromTape2SeparatorToBlockStartDescription_contract :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator logical 2 physical ∧
          HasAtLeastThreeTapes logical)
      (fun logical physical =>
        AtTapeSeparator logical 0 physical)
      returnFromTape2SeparatorToBlockStartDescription := by
  let source := fun logical physical =>
    AtExistingTapeSeparator logical 2 physical ∧
      HasAtLeastThreeTapes logical
  let middle := fun logical physical =>
    AtExistingTapeSeparator logical 1 physical
  have hfirst :
      CursorRoutineContract source middle
        returnFromNextSeparatorToCurrentSeparatorDescription := by
    exact
      { subroutineReady :=
          (returnFromNextSeparatorToCurrentSeparatorDescription_contract
            1).subroutineReady
        realizes := by
          intro logical Tin hsource
          rcases hsource with ⟨hseparator, hshape⟩
          rcases
              (returnFromNextSeparatorToCurrentSeparatorDescription_contract
                1).realizes logical Tin
                ⟨hseparator.left,
                  HasAtLeastThreeTapes_drop_one_exists hshape⟩ with
            ⟨Tout, hhalts, hsep⟩
          exact
            ⟨Tout, hhalts,
              ⟨hsep, HasAtLeastThreeTapes_drop_one_exists hshape⟩⟩ }
  have hsecond :
      CursorRoutineContract middle
        (fun logical physical =>
          AtTapeSeparator logical 0 physical)
        returnFromTape1SeparatorToBlockStartDescription := by
    exact
      { subroutineReady :=
          returnFromTape1SeparatorToBlockStartDescription_contract
            |>.subroutineReady
        realizes := by
          intro logical Tin hmiddle
          exact
            returnFromTape1SeparatorToBlockStartDescription_contract
              |>.realizes logical Tin hmiddle.left }
  exact
    cursorRoutineContract_canonicalSeq_self hfirst hsecond
      (by
        intro logical physical hmiddle
        rw [atExistingTapeSeparator_moveLeft_moveRight hmiddle])

theorem returnFromTape2SeparatorToBlockStartDescription_runsFromTape2Separator
    {logical : List (Tape Bool)} {physical : Tape Bool}
    (hseparator : AtExistingTapeSeparator logical 2 physical)
    (hshape : HasAtLeastThreeTapes logical) :
    exists blockStartPhysical : Tape Bool,
      AtTapeSeparator logical 0 blockStartPhysical ∧
        RunsFromStateTapeEquiv
          returnFromTape2SeparatorToBlockStartDescription
          returnFromTape2SeparatorToBlockStartDescription.start
          returnFromTape2SeparatorToBlockStartDescription.halt
          physical
          blockStartPhysical := by
  rcases
      returnFromTape2SeparatorToBlockStartDescription_contract.realizes
        logical physical ⟨hseparator, hshape⟩ with
    ⟨blockStartPhysical, hhalts, hblockStart⟩
  rcases MachineDescription.runConfig_eq_halt_of_haltsFromTape hhalts with
    ⟨n, hrun⟩
  exact
    ⟨blockStartPhysical, hblockStart,
      ⟨n, blockStartPhysical, hrun,
        Tape.Equiv.refl blockStartPhysical⟩⟩

/--
Lift an arbitrary-state run through a plain copied submachine block.
-/
theorem runsFromStateTapeEquiv_offsetDescription
    (offset : Nat)
    {D : MachineDescription}
    {sourceState targetState : Nat} {Tin Tout : Tape Bool}
    (hrun : RunsFromStateTapeEquiv D sourceState targetState Tin Tout) :
    RunsFromStateTapeEquiv
      (MachineDescription.offsetDescription offset D)
      (offset + sourceState)
      (offset + targetState)
      Tin Tout := by
  rcases hrun with ⟨n, Tactual, hrun, hout⟩
  exact
    ⟨n, Tactual,
      MachineDescription.offsetDescription_runConfig_eq
        (offset := offset) hrun,
      hout⟩

/--
Lift an arbitrary-state run through a copied submachine whose local halt has
been redirected to a caller continuation state.
-/
theorem runsFromStateTapeEquiv_offsetRetargetDescription
    {offset target : Nat} (htarget : target < offset)
    {D : MachineDescription} (hD : D.HaltTransitionFree)
    {sourceState : Nat} {Tin Tout : Tape Bool}
    (hrun : RunsFromStateTapeEquiv D sourceState D.halt Tin Tout) :
    RunsFromStateTapeEquiv
      (MachineDescription.offsetRetargetDescription offset target D)
      (if sourceState = D.halt then target else offset + sourceState)
      target Tin Tout := by
  rcases hrun with ⟨n, Tactual, hrun, hout⟩
  refine ⟨n, Tactual, ?_, hout⟩
  have hretarget :=
    MachineDescription.offsetRetargetDescription_runConfig_eq
      (offset := offset) (target := target)
      htarget hD hrun
  simpa [MachineDescription.sharedExitRetargetConfiguration] using hretarget

/--
Lift an arbitrary-state run through a copied submachine whose chosen local exit
state has been redirected to a caller continuation state.
-/
theorem runsFromStateTapeEquiv_offsetExitRetargetDescription
    {offset localExit target : Nat} (htarget : target < offset)
    {D : MachineDescription} (hD : D.TransitionFreeAt localExit)
    {sourceState : Nat} {Tin Tout : Tape Bool}
    (hrun : RunsFromStateTapeEquiv D sourceState localExit Tin Tout) :
    RunsFromStateTapeEquiv
      (MachineDescription.offsetExitRetargetDescription
        offset localExit target D)
      (if sourceState = localExit then target else offset + sourceState)
      target Tin Tout := by
  rcases hrun with ⟨n, Tactual, hrun, hout⟩
  refine ⟨n, Tactual, ?_, hout⟩
  have hretarget :=
    MachineDescription.offsetExitRetargetDescription_runConfig_eq
      (offset := offset) (localExit := localExit) (target := target)
      htarget hD hrun
  simpa [MachineDescription.sharedExitRetargetConfiguration] using hretarget

/--
Copied return routine for the tape-1 branch of the dispatcher.  Its local halt
is redirected to a caller-specified continuation state below the copied block.
-/
def retargetedReturnFromTape1SeparatorToBlockStartDescription
    (offset target : Nat) : MachineDescription :=
  MachineDescription.offsetRetargetDescription offset target
    returnFromTape1SeparatorToBlockStartDescription

theorem
    retargetedReturnFromTape1SeparatorToBlockStartDescription_subroutineReady
    {offset target : Nat} (htarget : target < offset) :
    (retargetedReturnFromTape1SeparatorToBlockStartDescription
      offset target).SubroutineReady :=
  MachineDescription.offsetRetargetDescription_subroutineReady
    htarget
    returnFromTape1SeparatorToBlockStartDescription_contract.subroutineReady.left

theorem
    retargetedReturnFromTape1SeparatorToBlockStartDescription_runsFromTape1Separator
    {offset target : Nat} (htarget : target < offset)
    {logical : List (Tape Bool)} {physical : Tape Bool}
    (hseparator : AtTapeSeparator logical 1 physical) :
    exists blockStartPhysical : Tape Bool,
      AtTapeSeparator logical 0 blockStartPhysical ∧
        RunsFromStateTapeEquiv
          (retargetedReturnFromTape1SeparatorToBlockStartDescription
            offset target)
          (retargetedReturnFromTape1SeparatorToBlockStartDescription
            offset target).start
          target
          physical
          blockStartPhysical := by
  rcases
      returnFromTape1SeparatorToBlockStartDescription_runsFromTape1Separator
        hseparator with
    ⟨blockStartPhysical, hblockStart, hrun⟩
  have hcopy :=
    runsFromStateTapeEquiv_offsetRetargetDescription
      (offset := offset) (target := target)
      htarget
      returnFromTape1SeparatorToBlockStartDescription_contract.subroutineReady.right
      hrun
  exact
    ⟨blockStartPhysical, hblockStart, by
      simpa [retargetedReturnFromTape1SeparatorToBlockStartDescription,
        MachineDescription.offsetRetargetDescription] using hcopy⟩

/--
Copied return routine for the tape-2 branch of the dispatcher.  Its local halt
is redirected to a caller-specified continuation state, so branch assembly can
return to the canonical block start and immediately continue in finite control.
-/
def retargetedReturnFromTape2SeparatorToBlockStartDescription
    (offset target : Nat) : MachineDescription :=
  MachineDescription.offsetRetargetDescription offset target
    returnFromTape2SeparatorToBlockStartDescription

theorem
    retargetedReturnFromTape2SeparatorToBlockStartDescription_subroutineReady
    {offset target : Nat} (htarget : target < offset) :
    (retargetedReturnFromTape2SeparatorToBlockStartDescription
      offset target).SubroutineReady :=
  MachineDescription.offsetRetargetDescription_subroutineReady
    htarget
    returnFromTape2SeparatorToBlockStartDescription_subroutineReady.left

theorem
    retargetedReturnFromTape2SeparatorToBlockStartDescription_runsFromTape2Separator
    {offset target : Nat} (htarget : target < offset)
    {logical : List (Tape Bool)} {physical : Tape Bool}
    (hseparator : AtExistingTapeSeparator logical 2 physical)
    (hshape : HasAtLeastThreeTapes logical) :
    exists blockStartPhysical : Tape Bool,
      AtTapeSeparator logical 0 blockStartPhysical ∧
        RunsFromStateTapeEquiv
          (retargetedReturnFromTape2SeparatorToBlockStartDescription
            offset target)
          (retargetedReturnFromTape2SeparatorToBlockStartDescription
            offset target).start
          target
          physical
          blockStartPhysical := by
  rcases
      returnFromTape2SeparatorToBlockStartDescription_runsFromTape2Separator
        hseparator hshape with
    ⟨blockStartPhysical, hblockStart, hrun⟩
  have hcopy :=
    runsFromStateTapeEquiv_offsetRetargetDescription
      (offset := offset) (target := target)
      htarget
      returnFromTape2SeparatorToBlockStartDescription_subroutineReady.right
      hrun
  exact
    ⟨blockStartPhysical, hblockStart, by
      simpa [retargetedReturnFromTape2SeparatorToBlockStartDescription,
        MachineDescription.offsetRetargetDescription] using hcopy⟩

def branchingTape0ReadHeadCellAndReturnToSeparatorDescription :
    MachineDescription :=
  branchingSeparatorReadHeadCellDescription

def branchingTape0ReadHeadCellAndReturnToSeparatorTarget :
    Option Bool -> Nat :=
  branchingSeparatorReadHeadCellTarget

theorem
    branchingTape0ReadHeadCellAndReturnToSeparatorDescription_subroutineReady :
    branchingTape0ReadHeadCellAndReturnToSeparatorDescription.SubroutineReady :=
  branchingSeparatorReadHeadCellDescription_subroutineReady

theorem
    branchingTape0ReadHeadCellAndReturnToSeparatorDescription_transitionFreeAt
    (cell : Option Bool) :
    branchingTape0ReadHeadCellAndReturnToSeparatorDescription
        |>.TransitionFreeAt
          (branchingTape0ReadHeadCellAndReturnToSeparatorTarget cell) := by
  intro t ht
  cases cell with
  | none =>
      exact
        transition_notFrom_of_all
          (l := branchingTape0ReadHeadCellAndReturnToSeparatorDescription
            |>.transitions)
          (state :=
            branchingTape0ReadHeadCellAndReturnToSeparatorTarget none)
          (by decide) t ht
  | some bit =>
      cases bit with
      | false =>
        exact
          transition_notFrom_of_all
            (l := branchingTape0ReadHeadCellAndReturnToSeparatorDescription
              |>.transitions)
            (state :=
              branchingTape0ReadHeadCellAndReturnToSeparatorTarget
                (some false))
            (by decide) t ht
      | true =>
        exact
          transition_notFrom_of_all
            (l := branchingTape0ReadHeadCellAndReturnToSeparatorDescription
              |>.transitions)
            (state :=
              branchingTape0ReadHeadCellAndReturnToSeparatorTarget
                (some true))
            (by decide) t ht

def retargetedBranchingTape0ReadHeadCellAndReturnToSeparatorDescription
    (offset target : Nat) (cell : Option Bool) :
    MachineDescription :=
  MachineDescription.offsetExitRetargetDescription offset
    (branchingTape0ReadHeadCellAndReturnToSeparatorTarget cell)
    target
    branchingTape0ReadHeadCellAndReturnToSeparatorDescription

theorem
    retargetedBranchingTape0ReadHeadCellAndReturnToSeparatorDescription_subroutineReady
    {offset target : Nat} (htarget : target < offset)
    (cell : Option Bool) :
    (retargetedBranchingTape0ReadHeadCellAndReturnToSeparatorDescription
      offset target cell).SubroutineReady :=
  MachineDescription.offsetExitRetargetDescription_subroutineReady
    htarget
    branchingTape0ReadHeadCellAndReturnToSeparatorDescription_subroutineReady.left

theorem
    branchingTape0ReadHeadCellAndReturnToSeparatorDescription_runsFromBlockStart
    {logical : List (Tape Bool)} {physical : Tape Bool}
    (hstart : AtExistingTapeSeparator logical 0 physical) :
    exists separatorPhysical : Tape Bool,
      AtExistingTapeSeparator logical 0 separatorPhysical ∧
        RunsFromStateTapeEquiv
          branchingTape0ReadHeadCellAndReturnToSeparatorDescription
          branchingTape0ReadHeadCellAndReturnToSeparatorDescription.start
          (branchingTape0ReadHeadCellAndReturnToSeparatorTarget
            (Tape.read (Description.tapeAt logical 0)))
          physical
          separatorPhysical := by
  rcases
      branchingSeparatorReadHeadCellDescription_runsFromSeparator hstart with
    ⟨separatorPhysical, hsep, hrun⟩
  exact
    ⟨separatorPhysical, ⟨hsep, hstart.right⟩, by
      simpa [branchingTape0ReadHeadCellAndReturnToSeparatorDescription,
        branchingTape0ReadHeadCellAndReturnToSeparatorTarget] using hrun⟩

theorem
    branchingTape0ReadHeadCellAndReturnToSeparatorDescription_runsFromGuardedBlockStart
    {logical : List (Tape Bool)}
    (hlength : logical.length = 3) :
    exists separatorPhysical : Tape Bool,
      AtExistingTapeSeparator (guardLogicalTapes logical) 0
        separatorPhysical ∧
        RunsFromStateTapeEquiv
          branchingTape0ReadHeadCellAndReturnToSeparatorDescription
          branchingTape0ReadHeadCellAndReturnToSeparatorDescription.start
          (branchingTape0ReadHeadCellAndReturnToSeparatorTarget
            (Tape.read (Description.tapeAt logical 0)))
          (encodedGuardedStructuredTapes logical)
          separatorPhysical := by
  have hrun :=
    branchingTape0ReadHeadCellAndReturnToSeparatorDescription_runsFromBlockStart
      (guardedAtExistingTapeSeparator_zero_of_length_three hlength)
  simpa [tapeAt_guardLogicalTapes_read] using hrun

theorem
    retargetedBranchingTape0ReadHeadCellAndReturnToSeparatorDescription_runsFromGuardedBlockStart
    {offset target : Nat} (htarget : target < offset)
    {logical : List (Tape Bool)}
    (hlength : logical.length = 3) :
    exists separatorPhysical : Tape Bool,
      AtExistingTapeSeparator (guardLogicalTapes logical) 0
        separatorPhysical ∧
        RunsFromStateTapeEquiv
          (retargetedBranchingTape0ReadHeadCellAndReturnToSeparatorDescription
            offset target (Tape.read (Description.tapeAt logical 0)))
          (retargetedBranchingTape0ReadHeadCellAndReturnToSeparatorDescription
            offset target (Tape.read (Description.tapeAt logical 0))).start
          target
          (encodedGuardedStructuredTapes logical)
          separatorPhysical := by
  rcases
      branchingTape0ReadHeadCellAndReturnToSeparatorDescription_runsFromGuardedBlockStart
        hlength with
    ⟨separatorPhysical, hseparator, hrun⟩
  have hcopy :=
    runsFromStateTapeEquiv_offsetExitRetargetDescription
      (offset := offset)
      (localExit :=
        branchingTape0ReadHeadCellAndReturnToSeparatorTarget
          (Tape.read (Description.tapeAt logical 0)))
      (target := target)
      htarget
      (branchingTape0ReadHeadCellAndReturnToSeparatorDescription_transitionFreeAt
        (Tape.read (Description.tapeAt logical 0)))
      hrun
  exact
    ⟨separatorPhysical, hseparator, by
      simpa
        [retargetedBranchingTape0ReadHeadCellAndReturnToSeparatorDescription,
          MachineDescription.offsetExitRetargetDescription] using hcopy⟩

def branchingTape1ReadHeadCellAndReturnToSeparatorDescription :
    MachineDescription :=
  canonicalPrimitiveSeqDescription
    seekTape1Description
    branchingSeparatorReadHeadCellDescription

def branchingTape1ReadHeadCellAndReturnToSeparatorTarget :
    Option Bool -> Nat :=
  fun cell =>
    canonicalPrimitiveSeqRightStateOffset seekTape1Description +
      branchingSeparatorReadHeadCellTarget cell

theorem
    branchingTape1ReadHeadCellAndReturnToSeparatorDescription_subroutineReady :
    branchingTape1ReadHeadCellAndReturnToSeparatorDescription.SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    seekTape1Description_contract.subroutineReady
    branchingSeparatorReadHeadCellDescription_subroutineReady

theorem
    branchingTape1ReadHeadCellAndReturnToSeparatorDescription_transitionFreeAt
    (cell : Option Bool) :
    branchingTape1ReadHeadCellAndReturnToSeparatorDescription
        |>.TransitionFreeAt
          (branchingTape1ReadHeadCellAndReturnToSeparatorTarget cell) := by
  intro t ht
  cases cell with
  | none =>
      exact
        transition_notFrom_of_all
          (l := branchingTape1ReadHeadCellAndReturnToSeparatorDescription
            |>.transitions)
          (state :=
            branchingTape1ReadHeadCellAndReturnToSeparatorTarget none)
          (by decide) t ht
  | some bit =>
      cases bit with
      | false =>
        exact
          transition_notFrom_of_all
            (l := branchingTape1ReadHeadCellAndReturnToSeparatorDescription
              |>.transitions)
            (state :=
              branchingTape1ReadHeadCellAndReturnToSeparatorTarget
                (some false))
            (by decide) t ht
      | true =>
        exact
          transition_notFrom_of_all
            (l := branchingTape1ReadHeadCellAndReturnToSeparatorDescription
              |>.transitions)
            (state :=
              branchingTape1ReadHeadCellAndReturnToSeparatorTarget
                (some true))
            (by decide) t ht

def retargetedBranchingTape1ReadHeadCellAndReturnToSeparatorDescription
    (offset target : Nat) (cell : Option Bool) :
    MachineDescription :=
  MachineDescription.offsetExitRetargetDescription offset
    (branchingTape1ReadHeadCellAndReturnToSeparatorTarget cell)
    target
    branchingTape1ReadHeadCellAndReturnToSeparatorDescription

theorem
    retargetedBranchingTape1ReadHeadCellAndReturnToSeparatorDescription_subroutineReady
    {offset target : Nat} (htarget : target < offset)
    (cell : Option Bool) :
    (retargetedBranchingTape1ReadHeadCellAndReturnToSeparatorDescription
      offset target cell).SubroutineReady :=
  MachineDescription.offsetExitRetargetDescription_subroutineReady
    htarget
    branchingTape1ReadHeadCellAndReturnToSeparatorDescription_subroutineReady.left

theorem
    branchingTape1ReadHeadCellAndReturnToSeparatorDescription_runsFromBlockStart
    {logical : List (Tape Bool)} {physical : Tape Bool}
    (hstart : AtExistingTapeSeparator logical 0 physical)
    (hexists :
      exists T : Tape Bool, exists rest : List (Tape Bool),
        logical.drop 1 = T :: rest) :
    exists separatorPhysical : Tape Bool,
      AtExistingTapeSeparator logical 1 separatorPhysical ∧
        RunsFromStateTapeEquiv
          branchingTape1ReadHeadCellAndReturnToSeparatorDescription
          branchingTape1ReadHeadCellAndReturnToSeparatorDescription.start
          (branchingTape1ReadHeadCellAndReturnToSeparatorTarget
            (Tape.read (Description.tapeAt logical 1)))
          physical
          separatorPhysical := by
  rcases
      seekTape1Description_contract.realizes
        logical physical hstart with
    ⟨mid, hseek, hseparator⟩
  let hmid :
      AtExistingTapeSeparator logical 1 mid :=
    ⟨hseparator, hexists⟩
  rcases
      branchingSeparatorReadHeadCellDescription_runsFromSeparator hmid with
    ⟨separatorPhysical, hsep, hread⟩
  rcases hread with ⟨nRead, actual, hreadRun, hactual⟩
  have hreadReach :
      exists nRead : Nat,
        branchingSeparatorReadHeadCellDescription.runConfig nRead
            { state := branchingSeparatorReadHeadCellDescription.start
              tape :=
                Tape.move Direction.left
                  (Tape.move Direction.right mid) } =
          { state :=
              branchingSeparatorReadHeadCellTarget
                (Tape.read (Description.tapeAt logical 1))
            tape := actual } := by
    refine ⟨nRead, ?_⟩
    rw [atExistingTapeSeparator_moveLeft_moveRight hmid]
    exact hreadRun
  rcases
      canonicalPrimitiveSeqDescription_reaches_right_state
        (A := seekTape1Description)
        (B := branchingSeparatorReadHeadCellDescription)
        seekTape1Description_contract.subroutineReady
        branchingSeparatorReadHeadCellDescription_subroutineReady
        hseek hreadReach with
    ⟨n, hrun⟩
  exact
    ⟨separatorPhysical, ⟨hsep, hexists⟩,
      ⟨n, actual, by
        simpa [branchingTape1ReadHeadCellAndReturnToSeparatorDescription,
          branchingTape1ReadHeadCellAndReturnToSeparatorTarget] using hrun,
        hactual⟩⟩

theorem
    branchingTape1ReadHeadCellAndReturnToSeparatorDescription_runsFromGuardedBlockStart
    {logical : List (Tape Bool)}
    (hlength : logical.length = 3) :
    exists separatorPhysical : Tape Bool,
      AtExistingTapeSeparator (guardLogicalTapes logical) 1
        separatorPhysical ∧
        RunsFromStateTapeEquiv
          branchingTape1ReadHeadCellAndReturnToSeparatorDescription
          branchingTape1ReadHeadCellAndReturnToSeparatorDescription.start
          (branchingTape1ReadHeadCellAndReturnToSeparatorTarget
            (Tape.read (Description.tapeAt logical 1)))
          (encodedGuardedStructuredTapes logical)
          separatorPhysical := by
  have hrun :=
    branchingTape1ReadHeadCellAndReturnToSeparatorDescription_runsFromBlockStart
      (guardedAtExistingTapeSeparator_zero_of_length_three hlength)
      (guarded_drop_one_exists_of_length_three hlength)
  simpa [tapeAt_guardLogicalTapes_read] using hrun

theorem
    retargetedBranchingTape1ReadHeadCellAndReturnToSeparatorDescription_runsFromGuardedBlockStart
    {offset target : Nat} (htarget : target < offset)
    {logical : List (Tape Bool)}
    (hlength : logical.length = 3) :
    exists separatorPhysical : Tape Bool,
      AtExistingTapeSeparator (guardLogicalTapes logical) 1
        separatorPhysical ∧
        RunsFromStateTapeEquiv
          (retargetedBranchingTape1ReadHeadCellAndReturnToSeparatorDescription
            offset target (Tape.read (Description.tapeAt logical 1)))
          (retargetedBranchingTape1ReadHeadCellAndReturnToSeparatorDescription
            offset target (Tape.read (Description.tapeAt logical 1))).start
          target
          (encodedGuardedStructuredTapes logical)
          separatorPhysical := by
  rcases
      branchingTape1ReadHeadCellAndReturnToSeparatorDescription_runsFromGuardedBlockStart
        hlength with
    ⟨separatorPhysical, hseparator, hrun⟩
  have hcopy :=
    runsFromStateTapeEquiv_offsetExitRetargetDescription
      (offset := offset)
      (localExit :=
        branchingTape1ReadHeadCellAndReturnToSeparatorTarget
          (Tape.read (Description.tapeAt logical 1)))
      (target := target)
      htarget
      (branchingTape1ReadHeadCellAndReturnToSeparatorDescription_transitionFreeAt
        (Tape.read (Description.tapeAt logical 1)))
      hrun
  exact
    ⟨separatorPhysical, hseparator, by
      simpa
        [retargetedBranchingTape1ReadHeadCellAndReturnToSeparatorDescription,
          MachineDescription.offsetExitRetargetDescription] using hcopy⟩

def branchingTape2ReadHeadCellAndReturnToSeparatorDescription :
    MachineDescription :=
  canonicalPrimitiveSeqDescription
    seekTape2Description
    branchingSeparatorReadHeadCellDescription

def branchingTape2ReadHeadCellAndReturnToSeparatorTarget :
    Option Bool -> Nat :=
  fun cell =>
    canonicalPrimitiveSeqRightStateOffset seekTape2Description +
      branchingSeparatorReadHeadCellTarget cell

theorem
    branchingTape2ReadHeadCellAndReturnToSeparatorDescription_subroutineReady :
    branchingTape2ReadHeadCellAndReturnToSeparatorDescription.SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    seekTape2Description_contract.subroutineReady
    branchingSeparatorReadHeadCellDescription_subroutineReady

theorem
    branchingTape2ReadHeadCellAndReturnToSeparatorDescription_transitionFreeAt
    (cell : Option Bool) :
    branchingTape2ReadHeadCellAndReturnToSeparatorDescription
        |>.TransitionFreeAt
          (branchingTape2ReadHeadCellAndReturnToSeparatorTarget cell) := by
  intro t ht
  cases cell with
  | none =>
      exact
        transition_notFrom_of_all
          (l := branchingTape2ReadHeadCellAndReturnToSeparatorDescription
            |>.transitions)
          (state :=
            branchingTape2ReadHeadCellAndReturnToSeparatorTarget none)
          (by decide) t ht
  | some bit =>
      cases bit with
      | false =>
        exact
          transition_notFrom_of_all
            (l := branchingTape2ReadHeadCellAndReturnToSeparatorDescription
              |>.transitions)
            (state :=
              branchingTape2ReadHeadCellAndReturnToSeparatorTarget
                (some false))
            (by decide) t ht
      | true =>
        exact
          transition_notFrom_of_all
            (l := branchingTape2ReadHeadCellAndReturnToSeparatorDescription
              |>.transitions)
            (state :=
              branchingTape2ReadHeadCellAndReturnToSeparatorTarget
                (some true))
            (by decide) t ht

def retargetedBranchingTape2ReadHeadCellAndReturnToSeparatorDescription
    (offset target : Nat) (cell : Option Bool) :
    MachineDescription :=
  MachineDescription.offsetExitRetargetDescription offset
    (branchingTape2ReadHeadCellAndReturnToSeparatorTarget cell)
    target
    branchingTape2ReadHeadCellAndReturnToSeparatorDescription

theorem
    retargetedBranchingTape2ReadHeadCellAndReturnToSeparatorDescription_subroutineReady
    {offset target : Nat} (htarget : target < offset)
    (cell : Option Bool) :
    (retargetedBranchingTape2ReadHeadCellAndReturnToSeparatorDescription
      offset target cell).SubroutineReady :=
  MachineDescription.offsetExitRetargetDescription_subroutineReady
    htarget
    branchingTape2ReadHeadCellAndReturnToSeparatorDescription_subroutineReady.left

theorem
    branchingTape2ReadHeadCellAndReturnToSeparatorDescription_runsFromBlockStart
    {logical : List (Tape Bool)} {physical : Tape Bool}
    (hstart : AtExistingTapeSeparator logical 0 physical)
    (hshape : HasAtLeastThreeTapes logical) :
    exists separatorPhysical : Tape Bool,
      AtExistingTapeSeparator logical 2 separatorPhysical ∧
        RunsFromStateTapeEquiv
          branchingTape2ReadHeadCellAndReturnToSeparatorDescription
          branchingTape2ReadHeadCellAndReturnToSeparatorDescription.start
          (branchingTape2ReadHeadCellAndReturnToSeparatorTarget
            (Tape.read (Description.tapeAt logical 2)))
          physical
          separatorPhysical := by
  rcases hshape with ⟨T, U, V, rest, hlogical⟩
  have hshape' : HasAtLeastThreeTapes logical :=
    ⟨T, U, V, rest, hlogical⟩
  rcases
      seekTape2Description_contract.realizes
        logical physical
        ⟨T, U, V :: rest, hlogical, hstart.left⟩ with
    ⟨mid, hseek, hseparator⟩
  let hmid :
      AtExistingTapeSeparator logical 2 mid :=
    ⟨hseparator, HasAtLeastThreeTapes_drop_two_exists hshape'⟩
  rcases
      branchingSeparatorReadHeadCellDescription_runsFromSeparator hmid with
    ⟨separatorPhysical, hsep, hread⟩
  rcases hread with ⟨nRead, actual, hreadRun, hactual⟩
  have hreadReach :
      exists nRead : Nat,
        branchingSeparatorReadHeadCellDescription.runConfig nRead
            { state := branchingSeparatorReadHeadCellDescription.start
              tape :=
                Tape.move Direction.left
                  (Tape.move Direction.right mid) } =
          { state :=
              branchingSeparatorReadHeadCellTarget
                (Tape.read (Description.tapeAt logical 2))
            tape := actual } := by
    refine ⟨nRead, ?_⟩
    rw [atExistingTapeSeparator_moveLeft_moveRight hmid]
    exact hreadRun
  rcases
      canonicalPrimitiveSeqDescription_reaches_right_state
        (A := seekTape2Description)
        (B := branchingSeparatorReadHeadCellDescription)
        seekTape2Description_contract.subroutineReady
        branchingSeparatorReadHeadCellDescription_subroutineReady
        hseek hreadReach with
    ⟨n, hrun⟩
  exact
    ⟨separatorPhysical,
      ⟨hsep, HasAtLeastThreeTapes_drop_two_exists hshape'⟩,
      ⟨n, actual, by
        simpa [branchingTape2ReadHeadCellAndReturnToSeparatorDescription,
          branchingTape2ReadHeadCellAndReturnToSeparatorTarget] using hrun,
        hactual⟩⟩

theorem
    branchingTape2ReadHeadCellAndReturnToSeparatorDescription_runsFromGuardedBlockStart
    {logical : List (Tape Bool)}
    (hlength : logical.length = 3) :
    exists separatorPhysical : Tape Bool,
      AtExistingTapeSeparator (guardLogicalTapes logical) 2
        separatorPhysical ∧
        RunsFromStateTapeEquiv
          branchingTape2ReadHeadCellAndReturnToSeparatorDescription
          branchingTape2ReadHeadCellAndReturnToSeparatorDescription.start
          (branchingTape2ReadHeadCellAndReturnToSeparatorTarget
            (Tape.read (Description.tapeAt logical 2)))
          (encodedGuardedStructuredTapes logical)
          separatorPhysical := by
  have hrun :=
    branchingTape2ReadHeadCellAndReturnToSeparatorDescription_runsFromBlockStart
      (guardedAtExistingTapeSeparator_zero_of_length_three hlength)
      (guarded_hasAtLeastThreeTapes_of_length_three hlength)
  simpa [tapeAt_guardLogicalTapes_read] using hrun

theorem
    retargetedBranchingTape2ReadHeadCellAndReturnToSeparatorDescription_runsFromGuardedBlockStart
    {offset target : Nat} (htarget : target < offset)
    {logical : List (Tape Bool)}
    (hlength : logical.length = 3) :
    exists separatorPhysical : Tape Bool,
      AtExistingTapeSeparator (guardLogicalTapes logical) 2
        separatorPhysical ∧
        RunsFromStateTapeEquiv
          (retargetedBranchingTape2ReadHeadCellAndReturnToSeparatorDescription
            offset target (Tape.read (Description.tapeAt logical 2)))
          (retargetedBranchingTape2ReadHeadCellAndReturnToSeparatorDescription
            offset target (Tape.read (Description.tapeAt logical 2))).start
          target
          (encodedGuardedStructuredTapes logical)
          separatorPhysical := by
  rcases
      branchingTape2ReadHeadCellAndReturnToSeparatorDescription_runsFromGuardedBlockStart
        hlength with
    ⟨separatorPhysical, hseparator, hrun⟩
  have hcopy :=
    runsFromStateTapeEquiv_offsetExitRetargetDescription
      (offset := offset)
      (localExit :=
        branchingTape2ReadHeadCellAndReturnToSeparatorTarget
          (Tape.read (Description.tapeAt logical 2)))
      (target := target)
      htarget
      (branchingTape2ReadHeadCellAndReturnToSeparatorDescription_transitionFreeAt
        (Tape.read (Description.tapeAt logical 2)))
      hrun
  exact
    ⟨separatorPhysical, hseparator, by
      simpa
        [retargetedBranchingTape2ReadHeadCellAndReturnToSeparatorDescription,
          MachineDescription.offsetExitRetargetDescription] using hcopy⟩

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

def afterRead0Base (D : Description) : Nat :=
  D.stateCount + 27 * D.stateCount

def afterRead0 (D : Description) (state : Nat)
    (read0 : Option Bool) : Nat :=
  afterRead0Base D + 3 * state + ReadTuple3.readCode read0

def afterRead1Base (D : Description) : Nat :=
  afterRead0Base D + 3 * D.stateCount

def afterRead1 (D : Description) (state : Nat)
    (read0 read1 : Option Bool) : Nat :=
  afterRead1Base D + 9 * state + ReadTuple3.code01 read0 read1

def readerStateLimit (D : Description) : Nat :=
  afterRead1Base D + 9 * D.stateCount

def tape0ReaderTarget (D : Description) (state : Nat)
    (read0 : Option Bool) : Nat :=
  afterRead0 D state read0

def tape1ReaderTarget (D : Description) (state : Nat)
    (read0 read1 : Option Bool) : Nat :=
  afterRead1 D state read0 read1

def tape2ReaderTarget (D : Description) (state : Nat)
    (reads : ReadTuple3) : Nat :=
  afterRead D state reads

theorem ready_lt_afterRead0Base
    (D : Description) {state : Nat}
    (hstate : state < D.stateCount) :
    ready state < afterRead0Base D := by
  unfold ready afterRead0Base
  lia

theorem afterRead0Base_le_afterRead0
    (D : Description) (state : Nat) (read0 : Option Bool) :
    afterRead0Base D ≤ afterRead0 D state read0 := by
  unfold afterRead0
  lia

theorem afterRead1Base_le_afterRead1
    (D : Description) (state : Nat)
    (read0 read1 : Option Bool) :
    afterRead1Base D ≤ afterRead1 D state read0 read1 := by
  unfold afterRead1
  lia

theorem afterRead_lt_afterRead0Base
    (D : Description) {state : Nat} (reads : ReadTuple3)
    (hstate : state < D.stateCount) :
    afterRead D state reads < afterRead0Base D := by
  have hcode := ReadTuple3.code_lt_twentySeven reads
  unfold afterRead afterRead0Base
  lia

theorem afterRead0_lt_afterRead1Base
    (D : Description) {state : Nat} (read0 : Option Bool)
    (hstate : state < D.stateCount) :
    afterRead0 D state read0 < afterRead1Base D := by
  have hcode := ReadTuple3.readCode_lt_three read0
  simp [afterRead0, afterRead0Base, afterRead1Base]
  lia

theorem afterRead1_lt_readerStateLimit
    (D : Description) {state : Nat} (read0 read1 : Option Bool)
    (hstate : state < D.stateCount) :
    afterRead1 D state read0 read1 < readerStateLimit D := by
  have hcode := ReadTuple3.code01_lt_nine read0 read1
  simp [afterRead1, afterRead0Base, afterRead1Base, readerStateLimit]
  lia

theorem tape0ReaderTarget_lt_afterRead1Base
    (D : Description) {state : Nat} (read0 : Option Bool)
    (hstate : state < D.stateCount) :
    tape0ReaderTarget D state read0 < afterRead1Base D := by
  simpa [tape0ReaderTarget] using
    afterRead0_lt_afterRead1Base D read0 hstate

theorem tape1ReaderTarget_lt_readerStateLimit
    (D : Description) {state : Nat}
    (read0 read1 : Option Bool)
    (hstate : state < D.stateCount) :
    tape1ReaderTarget D state read0 read1 < readerStateLimit D := by
  simpa [tape1ReaderTarget] using
    afterRead1_lt_readerStateLimit D read0 read1 hstate

theorem tape2ReaderTarget_lt_afterRead0Base
    (D : Description) {state : Nat} (reads : ReadTuple3)
    (hstate : state < D.stateCount) :
    tape2ReaderTarget D state reads < afterRead0Base D := by
  simpa [tape2ReaderTarget] using
    afterRead_lt_afterRead0Base D reads hstate

theorem afterRead_lt_tape0ReaderTarget
    (D : Description) {state targetState : Nat}
    (reads : ReadTuple3) (read0 : Option Bool)
    (hstate : state < D.stateCount) :
    afterRead D state reads <
      tape0ReaderTarget D targetState read0 := by
  have hfinal := afterRead_lt_afterRead0Base D reads hstate
  have htarget :=
    afterRead0Base_le_afterRead0 D targetState read0
  unfold tape0ReaderTarget
  lia

theorem tape0ReaderTarget_lt_tape1ReaderTarget
    (D : Description) {state targetState : Nat}
    (read0 read0' read1 : Option Bool)
    (hstate : state < D.stateCount) :
    tape0ReaderTarget D state read0 <
      tape1ReaderTarget D targetState read0' read1 := by
  have hleft :=
    tape0ReaderTarget_lt_afterRead1Base D read0 hstate
  have hright :=
    afterRead1Base_le_afterRead1 D targetState read0' read1
  unfold tape1ReaderTarget
  lia

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

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

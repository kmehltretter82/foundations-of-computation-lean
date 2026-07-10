import FoC.Computability.Compiler.Core.StructuredConstructionTargets.OptionCellExpandAppendSpec

set_option doc.verso true

/-!
# Option-cell expansion emitter implementation

This module provides the concrete finite table
{lit}`optionCellExpandAppendDescription` for the option-cell expansion
primitive and proves its exact run contract
{lit}`optionCellExpandAppendDescription_runSpec`.

The machine expands a public input word {lit}`Tape.input bits` in place into
the guarded three-logical-tape input layout
{lit}`optionCellExpandAppendTargetCells` and halts with the head back on the
left boundary separator.  The construction never visits a cell left of the
start position and its rightmost visited cell is the target's final
separator, so the halting tape record equals the target record exactly.

Phases (states in parentheses):

- dispatch (1): an empty input branches to the fixed writer chain (66-73);
  a nonempty input starts shift pass 1.
- shift passes 1-6 (1-24): each pass moves the word one cell to the right,
  vacating one more prefix scratch cell; after pass 6 the word sits at
  positions 6..n+5 with positions 0..5 blank.
- expansion loop (25-38): each iteration consumes the leftmost remaining
  input bit, shifts the remaining tail one cell right, and writes the
  two-cell logical code of the consumed bit; the loop head re-enters on the
  boundary blank.
- right guard and fixed suffix (39-59): writes the right guard, the two
  guarded blank tapes, and the three separators, turning around on the final
  separator.
- rewind (60-62) and backward prefix write (63-65): counts two separator
  blanks leftwards, crosses the blank-free code block, then writes the head
  marker and left guard backwards, arriving into the halt state (0) on the
  left boundary separator.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace StructuredConstructionTargets

open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

/--
Concrete finite table for the stream expansion and left rewind.

State plan: 0 halt; 1 dispatch and pass-1 start; passes 1-6 use
(carryFalse, carryTrue, walkBack) blocks {lit}`(2,3,4) (6,7,8) (10,11,12)
(14,15,16) (18,19,20) (22,23,24)` with pass starts {lit}`5 9 13 17 21`;
loop states {lit}`25`-{lit}`38`; suffix writers {lit}`39`-{lit}`59`; rewind
{lit}`60`-{lit}`62`; backward prefix writers {lit}`63`-{lit}`65`; empty-input
branch {lit}`66`-{lit}`73`.
-/
def optionCellExpandAppendDescription : MachineDescription where
  stateCount := 74
  start := 1
  halt := 0
  transitions :=
    [ -- dispatch / pass-1 vacate
      transition 1 none none Direction.right 66
    , transition 1 (some false) none Direction.right 2
    , transition 1 (some true) none Direction.right 3
      -- pass 1 carry/walkback (next pass start: 5)
    , transition 2 (some false) (some false) Direction.right 2
    , transition 2 (some true) (some false) Direction.right 3
    , transition 2 none (some false) Direction.left 4
    , transition 3 (some false) (some true) Direction.right 2
    , transition 3 (some true) (some true) Direction.right 3
    , transition 3 none (some true) Direction.left 4
    , transition 4 (some false) (some false) Direction.left 4
    , transition 4 (some true) (some true) Direction.left 4
    , transition 4 none none Direction.right 5
      -- pass 2
    , transition 5 (some false) none Direction.right 6
    , transition 5 (some true) none Direction.right 7
    , transition 6 (some false) (some false) Direction.right 6
    , transition 6 (some true) (some false) Direction.right 7
    , transition 6 none (some false) Direction.left 8
    , transition 7 (some false) (some true) Direction.right 6
    , transition 7 (some true) (some true) Direction.right 7
    , transition 7 none (some true) Direction.left 8
    , transition 8 (some false) (some false) Direction.left 8
    , transition 8 (some true) (some true) Direction.left 8
    , transition 8 none none Direction.right 9
      -- pass 3
    , transition 9 (some false) none Direction.right 10
    , transition 9 (some true) none Direction.right 11
    , transition 10 (some false) (some false) Direction.right 10
    , transition 10 (some true) (some false) Direction.right 11
    , transition 10 none (some false) Direction.left 12
    , transition 11 (some false) (some true) Direction.right 10
    , transition 11 (some true) (some true) Direction.right 11
    , transition 11 none (some true) Direction.left 12
    , transition 12 (some false) (some false) Direction.left 12
    , transition 12 (some true) (some true) Direction.left 12
    , transition 12 none none Direction.right 13
      -- pass 4
    , transition 13 (some false) none Direction.right 14
    , transition 13 (some true) none Direction.right 15
    , transition 14 (some false) (some false) Direction.right 14
    , transition 14 (some true) (some false) Direction.right 15
    , transition 14 none (some false) Direction.left 16
    , transition 15 (some false) (some true) Direction.right 14
    , transition 15 (some true) (some true) Direction.right 15
    , transition 15 none (some true) Direction.left 16
    , transition 16 (some false) (some false) Direction.left 16
    , transition 16 (some true) (some true) Direction.left 16
    , transition 16 none none Direction.right 17
      -- pass 5
    , transition 17 (some false) none Direction.right 18
    , transition 17 (some true) none Direction.right 19
    , transition 18 (some false) (some false) Direction.right 18
    , transition 18 (some true) (some false) Direction.right 19
    , transition 18 none (some false) Direction.left 20
    , transition 19 (some false) (some true) Direction.right 18
    , transition 19 (some true) (some true) Direction.right 19
    , transition 19 none (some true) Direction.left 20
    , transition 20 (some false) (some false) Direction.left 20
    , transition 20 (some true) (some true) Direction.left 20
    , transition 20 none none Direction.right 21
      -- pass 6 (the walkback exits directly into the loop head read)
    , transition 21 (some false) none Direction.right 22
    , transition 21 (some true) none Direction.right 23
    , transition 22 (some false) (some false) Direction.right 22
    , transition 22 (some true) (some false) Direction.right 23
    , transition 22 none (some false) Direction.left 24
    , transition 23 (some false) (some true) Direction.right 22
    , transition 23 (some true) (some true) Direction.right 23
    , transition 23 none (some true) Direction.left 24
    , transition 24 (some false) (some false) Direction.left 24
    , transition 24 (some true) (some true) Direction.left 24
    , transition 24 none none Direction.right 25
      -- expansion loop: 25 consumes the next bit or exits to the suffix
    , transition 25 (some false) none Direction.right 26
    , transition 25 (some true) none Direction.right 27
    , transition 25 none (some false) Direction.left 39
      -- 26/27: vacate the tail head and start the tail shift, or tail-empty
    , transition 26 (some false) none Direction.right 28
    , transition 26 (some true) none Direction.right 29
    , transition 26 none none Direction.left 34
    , transition 27 (some false) none Direction.right 30
    , transition 27 (some true) none Direction.right 31
    , transition 27 none none Direction.left 35
      -- 28-31: tail shift carry, consumed bit latched
    , transition 28 (some false) (some false) Direction.right 28
    , transition 28 (some true) (some false) Direction.right 29
    , transition 28 none (some false) Direction.left 32
    , transition 29 (some false) (some true) Direction.right 28
    , transition 29 (some true) (some true) Direction.right 29
    , transition 29 none (some true) Direction.left 32
    , transition 30 (some false) (some false) Direction.right 30
    , transition 30 (some true) (some false) Direction.right 31
    , transition 30 none (some false) Direction.left 33
    , transition 31 (some false) (some true) Direction.right 30
    , transition 31 (some true) (some true) Direction.right 31
    , transition 31 none (some true) Direction.left 33
      -- 32/33: walk back left to the vacated boundary
    , transition 32 (some false) (some false) Direction.left 32
    , transition 32 (some true) (some true) Direction.left 32
    , transition 32 none none Direction.left 34
    , transition 33 (some false) (some false) Direction.left 33
    , transition 33 (some true) (some true) Direction.left 33
    , transition 33 none none Direction.left 35
      -- 34-37: write the two-cell logical code of the consumed bit backwards
    , transition 34 none (some true) Direction.left 36
    , transition 35 none (some false) Direction.left 37
    , transition 36 none (some false) Direction.right 38
    , transition 37 none (some true) Direction.right 38
      -- 38: walk right over the fresh code to the new boundary
    , transition 38 (some false) (some false) Direction.right 38
    , transition 38 (some true) (some true) Direction.right 38
    , transition 38 none none Direction.right 25
      -- 39/40: finish the right guard, then fixed suffix writers 41-59
    , transition 39 none (some false) Direction.right 40
    , transition 40 (some false) (some false) Direction.right 41
    , transition 41 none none Direction.right 42
    , transition 42 none (some false) Direction.right 43
    , transition 43 none (some false) Direction.right 44
    , transition 44 none (some true) Direction.right 45
    , transition 45 none (some true) Direction.right 46
    , transition 46 none (some false) Direction.right 47
    , transition 47 none (some false) Direction.right 48
    , transition 48 none (some false) Direction.right 49
    , transition 49 none (some false) Direction.right 50
    , transition 50 none none Direction.right 51
    , transition 51 none (some false) Direction.right 52
    , transition 52 none (some false) Direction.right 53
    , transition 53 none (some true) Direction.right 54
    , transition 54 none (some true) Direction.right 55
    , transition 55 none (some false) Direction.right 56
    , transition 56 none (some false) Direction.right 57
    , transition 57 none (some false) Direction.right 58
    , transition 58 none (some false) Direction.right 59
    , transition 59 none none Direction.left 60
      -- 60-62: count two separators leftwards, cross the blank-free block
    , transition 60 (some false) (some false) Direction.left 60
    , transition 60 (some true) (some true) Direction.left 60
    , transition 60 none none Direction.left 61
    , transition 61 (some false) (some false) Direction.left 61
    , transition 61 (some true) (some true) Direction.left 61
    , transition 61 none none Direction.left 62
    , transition 62 (some false) (some false) Direction.left 62
    , transition 62 (some true) (some true) Direction.left 62
    , transition 62 none (some true) Direction.left 63
      -- 63-65: backward prefix write, arriving into the halt state at 0
    , transition 63 none (some true) Direction.left 64
    , transition 64 none (some false) Direction.left 65
    , transition 65 none (some false) Direction.left 0
      -- 66-73: empty-input branch
    , transition 66 none none Direction.right 67
    , transition 67 none none Direction.right 68
    , transition 68 none none Direction.right 69
    , transition 69 none none Direction.right 70
    , transition 70 none (some false) Direction.right 71
    , transition 71 none (some false) Direction.right 72
    , transition 72 none (some false) Direction.right 73
    , transition 73 none (some false) Direction.right 41 ]

set_option maxRecDepth 8192 in
theorem optionCellExpandAppendDescription_wellFormed :
    optionCellExpandAppendDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := optionCellExpandAppendDescription.transitions)
      (stateCount := optionCellExpandAppendDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := optionCellExpandAppendDescription.transitions)
      (by decide)

set_option maxRecDepth 8192 in
theorem optionCellExpandAppendDescription_haltTransitionFree :
    optionCellExpandAppendDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := optionCellExpandAppendDescription.transitions)
    (state := optionCellExpandAppendDescription.halt)
    (by decide)

theorem optionCellExpandAppendDescription_subroutineReady :
    optionCellExpandAppendDescription.SubroutineReady :=
  ⟨optionCellExpandAppendDescription_wellFormed,
    optionCellExpandAppendDescription_haltTransitionFree⟩

/-!
## Generic single-step and scan lemmas

The machine table is large, so per-phase lemmas never unfold the transition
list.  Every step goes through one lookup-driven step lemma; scans and the
shift carry are proved once, parameterized over the participating states and
their lookup equations, and instantiated per phase with {lit}`rfl` lookups.
-/

theorem optionCellExpand_runConfig_one_of_lookup
    {D : MachineDescription} {s s' : Nat} {r w : Option Bool}
    {d : Direction}
    (h : D.lookupTransition s r = some (transition s r w d s'))
    (T : Tape Bool) (hr : Tape.read T = r) :
    D.runConfig 1 { state := s, tape := T } =
      { state := s', tape := Tape.move d (Tape.write w T) } := by
  simp [runConfig, stepConfig, hr, h, transition]

theorem optionCellExpand_tapeAtCells_moveRight
    (leftRev : List (Option Bool)) (cell : Option Bool)
    (rest : List (Option Bool)) :
    Tape.moveRight { left := leftRev, head := cell, right := rest } =
      tapeAtCells (cell :: leftRev) rest := by
  cases rest <;> rfl

/--
Leftward scan of a self-looping state over a nonblank segment, stopping with
the head on the first blank strictly left of the segment.
-/
theorem optionCellExpand_run_scanLeft
    {D : MachineDescription} {s : Nat}
    (hf : D.lookupTransition s (some false) =
      some (transition s (some false) (some false) Direction.left s))
    (ht : D.lookupTransition s (some true) =
      some (transition s (some true) (some true) Direction.left s)) :
    forall (seg : Word Bool) (cur : Bool)
      (base right : List (Option Bool)),
      D.runConfig (seg.length + 1)
          { state := s
            tape :=
              tapeAtCells (List.append (seg.map some) (none :: base))
                (some cur :: right) } =
        { state := s
          tape :=
            tapeAtCells base
              (none ::
                List.append (seg.reverse.map some)
                  (some cur :: right)) } := by
  intro seg
  induction seg with
  | nil =>
      intro cur base right
      show D.runConfig 1
          { state := s
            tape := tapeAtCells (none :: base) (some cur :: right) } =
        { state := s
          tape := tapeAtCells base (none :: some cur :: right) }
      cases cur with
      | false =>
          rw [optionCellExpand_runConfig_one_of_lookup hf _ rfl]
          simp [Tape.write, Tape.move, Tape.moveLeft, tapeAtCells]
      | true =>
          rw [optionCellExpand_runConfig_one_of_lookup ht _ rfl]
          simp [Tape.write, Tape.move, Tape.moveLeft, tapeAtCells]
  | cons x xs ih =>
      intro cur base right
      rw [show (x :: xs).length + 1 = 1 + (xs.length + 1) by
        simp
        lia]
      rw [runConfig_add]
      have hstep :
          D.runConfig 1
              { state := s
                tape :=
                  tapeAtCells
                    (List.append ((x :: xs).map some) (none :: base))
                    (some cur :: right) } =
            { state := s
              tape :=
                tapeAtCells (List.append (xs.map some) (none :: base))
                  (some x :: some cur :: right) } := by
        cases cur with
        | false =>
            rw [optionCellExpand_runConfig_one_of_lookup hf _ rfl]
            simp [Tape.write, Tape.move, Tape.moveLeft, tapeAtCells]
        | true =>
            rw [optionCellExpand_runConfig_one_of_lookup ht _ rfl]
            simp [Tape.write, Tape.move, Tape.moveLeft, tapeAtCells]
      rw [hstep]
      rw [ih x base (some cur :: right)]
      simp [List.map_append, List.append_assoc]

theorem optionCellExpand_cond_false {α : Sort u} {a b : α} :
    cond false a b = b := rfl

theorem optionCellExpand_cond_true {α : Sort u} {a b : α} :
    cond true a b = a := rfl

/--
Rightward shift carry: the carried bit is written under the head, the read
bit becomes the new carry, and the final blank write turns around into a
leftward walk that stops on the blank vacated at the start of the shift.
The remaining word sits at the right record edge, so the blank past it is
implicit in the tape record.
-/
theorem optionCellExpand_run_carryShift
    {D : MachineDescription} {cF cT wl : Nat}
    (hff : D.lookupTransition cF (some false) =
      some (transition cF (some false) (some false) Direction.right cF))
    (hft : D.lookupTransition cF (some true) =
      some (transition cF (some true) (some false) Direction.right cT))
    (hfn : D.lookupTransition cF none =
      some (transition cF none (some false) Direction.left wl))
    (htf : D.lookupTransition cT (some false) =
      some (transition cT (some false) (some true) Direction.right cF))
    (htt : D.lookupTransition cT (some true) =
      some (transition cT (some true) (some true) Direction.right cT))
    (htn : D.lookupTransition cT none =
      some (transition cT none (some true) Direction.left wl))
    (hwf : D.lookupTransition wl (some false) =
      some (transition wl (some false) (some false) Direction.left wl))
    (hwt : D.lookupTransition wl (some true) =
      some (transition wl (some true) (some true) Direction.left wl)) :
    forall (rest : Word Bool) (c : Bool) (blockRev : Word Bool)
      (base : List (Option Bool)),
      D.runConfig (2 * rest.length + blockRev.length + 1)
          { state := cond c cT cF
            tape :=
              tapeAtCells
                (List.append (blockRev.map some) (none :: base))
                (rest.map some) } =
        { state := wl
          tape :=
            tapeAtCells base
              (none ::
                List.append (blockRev.reverse.map some)
                  (some c :: rest.map some)) } := by
  intro rest
  induction rest with
  | nil =>
      intro c blockRev base
      rw [show 2 * ([] : Word Bool).length + blockRev.length + 1 =
          1 + blockRev.length by
        simp
        lia]
      rw [runConfig_add]
      have hread :
          Tape.read
              (tapeAtCells
                (List.append (blockRev.map some) (none :: base))
                (([] : Word Bool).map some)) = none := by
        cases blockRev <;> rfl
      have hstep :
          D.runConfig 1
              { state := cond c cT cF
                tape :=
                  tapeAtCells
                    (List.append (blockRev.map some) (none :: base))
                    (([] : Word Bool).map some) } =
            { state := wl
              tape :=
                Tape.move Direction.left
                  (Tape.write (some c)
                    (tapeAtCells
                      (List.append (blockRev.map some) (none :: base))
                      [])) } := by
        cases c with
        | false =>
            simp only [optionCellExpand_cond_false]
            rw [optionCellExpand_runConfig_one_of_lookup hfn _ hread]
            rfl
        | true =>
            simp only [optionCellExpand_cond_true]
            rw [optionCellExpand_runConfig_one_of_lookup htn _ hread]
            rfl
      rw [hstep]
      cases blockRev with
      | nil =>
          simp [Tape.write, Tape.move, Tape.moveLeft, tapeAtCells,
            runConfig]
      | cons x xs =>
          have hmove :
              Tape.move Direction.left
                  (Tape.write (some c)
                    (tapeAtCells
                      (List.append ((x :: xs).map some) (none :: base))
                      [])) =
                tapeAtCells (List.append (xs.map some) (none :: base))
                  (some x :: [some c]) := by
            simp [Tape.write, Tape.move, Tape.moveLeft, tapeAtCells]
          -- walk back over the already-shifted block
          rw [hmove]
          rw [show (x :: xs).length = xs.length + 1 by rfl]
          rw [optionCellExpand_run_scanLeft hwf hwt xs x base [some c]]
          simp [List.map_append, List.append_assoc]
  | cons d rest2 ih =>
      intro c blockRev base
      rw [show 2 * (d :: rest2).length + blockRev.length + 1 =
          1 + (2 * rest2.length + (blockRev.length + 1) + 1) by
        simp
        lia]
      rw [runConfig_add]
      have hstep :
          D.runConfig 1
              { state := cond c cT cF
                tape :=
                  tapeAtCells
                    (List.append (blockRev.map some) (none :: base))
                    ((d :: rest2).map some) } =
            { state := cond d cT cF
              tape :=
                tapeAtCells
                  (List.append ((c :: blockRev).map some) (none :: base))
                  (rest2.map some) } := by
        cases c with
        | false =>
            cases d with
            | false =>
                simp only [optionCellExpand_cond_false]
                rw [optionCellExpand_runConfig_one_of_lookup hff _ rfl]
                simp [Tape.write, Tape.move,
                  optionCellExpand_tapeAtCells_moveRight, tapeAtCells]
            | true =>
                simp only [optionCellExpand_cond_false, optionCellExpand_cond_true]
                rw [optionCellExpand_runConfig_one_of_lookup hft _ rfl]
                simp [Tape.write, Tape.move,
                  optionCellExpand_tapeAtCells_moveRight, tapeAtCells]
        | true =>
            cases d with
            | false =>
                simp only [optionCellExpand_cond_false, optionCellExpand_cond_true]
                rw [optionCellExpand_runConfig_one_of_lookup htf _ rfl]
                simp [Tape.write, Tape.move,
                  optionCellExpand_tapeAtCells_moveRight, tapeAtCells]
            | true =>
                simp only [optionCellExpand_cond_true]
                rw [optionCellExpand_runConfig_one_of_lookup htt _ rfl]
                simp [Tape.write, Tape.move,
                  optionCellExpand_tapeAtCells_moveRight, tapeAtCells]
      rw [hstep]
      rw [show 2 * rest2.length + (blockRev.length + 1) + 1 =
          2 * rest2.length + ((c :: blockRev).length) + 1 by rfl]
      rw [ih d (c :: blockRev) base]
      simp [List.map_append, List.append_assoc]

/-- Shift carry entered on a freshly vacated boundary (no shifted block yet). -/
theorem optionCellExpand_run_carryShift_fresh
    {D : MachineDescription} {cF cT wl : Nat}
    (hff : D.lookupTransition cF (some false) =
      some (transition cF (some false) (some false) Direction.right cF))
    (hft : D.lookupTransition cF (some true) =
      some (transition cF (some true) (some false) Direction.right cT))
    (hfn : D.lookupTransition cF none =
      some (transition cF none (some false) Direction.left wl))
    (htf : D.lookupTransition cT (some false) =
      some (transition cT (some false) (some true) Direction.right cF))
    (htt : D.lookupTransition cT (some true) =
      some (transition cT (some true) (some true) Direction.right cT))
    (htn : D.lookupTransition cT none =
      some (transition cT none (some true) Direction.left wl))
    (hwf : D.lookupTransition wl (some false) =
      some (transition wl (some false) (some false) Direction.left wl))
    (hwt : D.lookupTransition wl (some true) =
      some (transition wl (some true) (some true) Direction.left wl)) :
    forall (rest : Word Bool) (c : Bool) (base : List (Option Bool)),
      D.runConfig (2 * rest.length + 1)
          { state := cond c cT cF
            tape := tapeAtCells (none :: base) (rest.map some) } =
        { state := wl
          tape := tapeAtCells base (none :: some c :: rest.map some) } := by
  intro rest c base
  have h :=
    optionCellExpand_run_carryShift hff hft hfn htf htt htn hwf hwt
      rest c [] base
  simpa using h

/--
One complete shift pass: vacate the word's left edge, carry the word one cell
to the right, walk back to the vacated blank, and step right onto the moved
word's new left edge in the next pass's start state.
-/
theorem optionCellExpand_run_shiftPass
    {D : MachineDescription} {sS cF cT wl sNext : Nat}
    (hsf : D.lookupTransition sS (some false) =
      some (transition sS (some false) none Direction.right cF))
    (hst : D.lookupTransition sS (some true) =
      some (transition sS (some true) none Direction.right cT))
    (hff : D.lookupTransition cF (some false) =
      some (transition cF (some false) (some false) Direction.right cF))
    (hft : D.lookupTransition cF (some true) =
      some (transition cF (some true) (some false) Direction.right cT))
    (hfn : D.lookupTransition cF none =
      some (transition cF none (some false) Direction.left wl))
    (htf : D.lookupTransition cT (some false) =
      some (transition cT (some false) (some true) Direction.right cF))
    (htt : D.lookupTransition cT (some true) =
      some (transition cT (some true) (some true) Direction.right cT))
    (htn : D.lookupTransition cT none =
      some (transition cT none (some true) Direction.left wl))
    (hwf : D.lookupTransition wl (some false) =
      some (transition wl (some false) (some false) Direction.left wl))
    (hwt : D.lookupTransition wl (some true) =
      some (transition wl (some true) (some true) Direction.left wl))
    (hexit : D.lookupTransition wl none =
      some (transition wl none none Direction.right sNext)) :
    forall (b : Bool) (rest : Word Bool) (base : List (Option Bool)),
      D.runConfig (2 * rest.length + 3)
          { state := sS
            tape := tapeAtCells base (List.map some (b :: rest)) } =
        { state := sNext
          tape := tapeAtCells (none :: base) (List.map some (b :: rest)) } := by
  intro b rest base
  rw [show 2 * rest.length + 3 = 1 + ((2 * rest.length + 1) + 1) by lia]
  rw [runConfig_add]
  have hvac :
      D.runConfig 1
          { state := sS
            tape := tapeAtCells base (List.map some (b :: rest)) } =
        { state := cond b cT cF
          tape := tapeAtCells (none :: base) (rest.map some) } := by
    cases b with
    | false =>
        simp only [optionCellExpand_cond_false]
        rw [optionCellExpand_runConfig_one_of_lookup hsf _ rfl]
        simp [Tape.write, Tape.move, optionCellExpand_tapeAtCells_moveRight,
          tapeAtCells]
    | true =>
        simp only [optionCellExpand_cond_true]
        rw [optionCellExpand_runConfig_one_of_lookup hst _ rfl]
        simp [Tape.write, Tape.move, optionCellExpand_tapeAtCells_moveRight,
          tapeAtCells]
  rw [hvac]
  rw [runConfig_add]
  rw [optionCellExpand_run_carryShift_fresh hff hft hfn htf htt htn hwf hwt
    rest b base]
  rw [optionCellExpand_runConfig_one_of_lookup hexit _ rfl]
  simp [Tape.write, Tape.move, optionCellExpand_tapeAtCells_moveRight,
          tapeAtCells]

/-! ## Concrete shift passes 1-6 -/

theorem optionCellExpand_run_pass1 :
    forall (b : Bool) (rest : Word Bool) (base : List (Option Bool)),
      optionCellExpandAppendDescription.runConfig (2 * rest.length + 3)
          { state := 1
            tape := tapeAtCells base (List.map some (b :: rest)) } =
        { state := 5
          tape := tapeAtCells (none :: base) (List.map some (b :: rest)) } :=
  optionCellExpand_run_shiftPass (D := optionCellExpandAppendDescription)
    (sS := 1) (cF := 2) (cT := 3) (wl := 4) (sNext := 5)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem optionCellExpand_run_pass2 :
    forall (b : Bool) (rest : Word Bool) (base : List (Option Bool)),
      optionCellExpandAppendDescription.runConfig (2 * rest.length + 3)
          { state := 5
            tape := tapeAtCells base (List.map some (b :: rest)) } =
        { state := 9
          tape := tapeAtCells (none :: base) (List.map some (b :: rest)) } :=
  optionCellExpand_run_shiftPass (D := optionCellExpandAppendDescription)
    (sS := 5) (cF := 6) (cT := 7) (wl := 8) (sNext := 9)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem optionCellExpand_run_pass3 :
    forall (b : Bool) (rest : Word Bool) (base : List (Option Bool)),
      optionCellExpandAppendDescription.runConfig (2 * rest.length + 3)
          { state := 9
            tape := tapeAtCells base (List.map some (b :: rest)) } =
        { state := 13
          tape := tapeAtCells (none :: base) (List.map some (b :: rest)) } :=
  optionCellExpand_run_shiftPass (D := optionCellExpandAppendDescription)
    (sS := 9) (cF := 10) (cT := 11) (wl := 12) (sNext := 13)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem optionCellExpand_run_pass4 :
    forall (b : Bool) (rest : Word Bool) (base : List (Option Bool)),
      optionCellExpandAppendDescription.runConfig (2 * rest.length + 3)
          { state := 13
            tape := tapeAtCells base (List.map some (b :: rest)) } =
        { state := 17
          tape := tapeAtCells (none :: base) (List.map some (b :: rest)) } :=
  optionCellExpand_run_shiftPass (D := optionCellExpandAppendDescription)
    (sS := 13) (cF := 14) (cT := 15) (wl := 16) (sNext := 17)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem optionCellExpand_run_pass5 :
    forall (b : Bool) (rest : Word Bool) (base : List (Option Bool)),
      optionCellExpandAppendDescription.runConfig (2 * rest.length + 3)
          { state := 17
            tape := tapeAtCells base (List.map some (b :: rest)) } =
        { state := 21
          tape := tapeAtCells (none :: base) (List.map some (b :: rest)) } :=
  optionCellExpand_run_shiftPass (D := optionCellExpandAppendDescription)
    (sS := 17) (cF := 18) (cT := 19) (wl := 20) (sNext := 21)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem optionCellExpand_run_pass6 :
    forall (b : Bool) (rest : Word Bool) (base : List (Option Bool)),
      optionCellExpandAppendDescription.runConfig (2 * rest.length + 3)
          { state := 21
            tape := tapeAtCells base (List.map some (b :: rest)) } =
        { state := 25
          tape := tapeAtCells (none :: base) (List.map some (b :: rest)) } :=
  optionCellExpand_run_shiftPass (D := optionCellExpandAppendDescription)
    (sS := 21) (cF := 22) (cT := 23) (wl := 24) (sNext := 25)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-!
## Expansion loop tape views
-/

/-- Physical two-cell code bits for a word, in input order. -/
def optionCellExpandCodeBits : Word Bool -> Word Bool
  | [] => []
  | b :: rest =>
      List.append (if b then [true, false] else [false, true])
        (optionCellExpandCodeBits rest)

theorem optionCellExpand_codeBits_map_some (w : Word Bool) :
    List.map some (optionCellExpandCodeBits w) =
      logicalCellListCode (w.map some) := by
  induction w with
  | nil => rfl
  | cons b rest ih =>
      cases b <;>
        simp [optionCellExpandCodeBits, logicalCellListBits,
          logicalCellBits, ih]

theorem optionCellExpandCodeBits_append (u v : Word Bool) :
    optionCellExpandCodeBits (List.append u v) =
      List.append (optionCellExpandCodeBits u)
        (optionCellExpandCodeBits v) := by
  induction u with
  | nil => rfl
  | cons b rest ih =>
      have ih' := ih
      simp only [List.append_eq] at ih'
      cases b <;> simp [optionCellExpandCodeBits, ih']

/--
Loop view between iterations: the head sits one step right of the boundary
blank, on the first remaining input bit (or on the blank right record edge
when the input is exhausted).  Emitted codes lie left of the boundary, above
the five vacated prefix scratch cells.
-/
def optionCellExpandLoopTape (emitted rest : Word Bool) : Tape Bool :=
  tapeAtCells
    (none ::
      List.append
        (List.map some (optionCellExpandCodeBits emitted).reverse)
        (List.replicate 5 (none : Option Bool)))
    (rest.map some)

/-- The six shift passes land exactly on the loop entry view. -/
theorem optionCellExpand_run_shiftPhase (b : Bool) (rest : Word Bool) :
    optionCellExpandAppendDescription.runConfig (12 * rest.length + 18)
        { state := 1
          tape := tapeAtCells [] (List.map some (b :: rest)) } =
      { state := 25
        tape := optionCellExpandLoopTape [] (b :: rest) } := by
  rw [show 12 * rest.length + 18 =
      (2 * rest.length + 3) + ((2 * rest.length + 3) +
        ((2 * rest.length + 3) + ((2 * rest.length + 3) +
          ((2 * rest.length + 3) + (2 * rest.length + 3))))) by lia]
  rw [runConfig_add]
  rw [optionCellExpand_run_pass1 b rest []]
  rw [runConfig_add]
  rw [optionCellExpand_run_pass2 b rest [none]]
  rw [runConfig_add]
  rw [optionCellExpand_run_pass3 b rest (none :: [none])]
  rw [runConfig_add]
  rw [optionCellExpand_run_pass4 b rest (none :: none :: [none])]
  rw [runConfig_add]
  rw [optionCellExpand_run_pass5 b rest (none :: none :: none :: [none])]
  rw [optionCellExpand_run_pass6 b rest
    (none :: none :: none :: none :: [none])]
  rfl

/-! ## Expansion loop -/

theorem optionCellExpand_run_carryLoopF :
    forall (rest : Word Bool) (c : Bool) (base : List (Option Bool)),
      optionCellExpandAppendDescription.runConfig (2 * rest.length + 1)
          { state := cond c 29 28
            tape := tapeAtCells (none :: base) (rest.map some) } =
        { state := 32
          tape := tapeAtCells base (none :: some c :: rest.map some) } :=
  optionCellExpand_run_carryShift_fresh
    (D := optionCellExpandAppendDescription)
    (cF := 28) (cT := 29) (wl := 32) rfl rfl rfl rfl rfl rfl rfl rfl

theorem optionCellExpand_run_carryLoopT :
    forall (rest : Word Bool) (c : Bool) (base : List (Option Bool)),
      optionCellExpandAppendDescription.runConfig (2 * rest.length + 1)
          { state := cond c 31 30
            tape := tapeAtCells (none :: base) (rest.map some) } =
        { state := 33
          tape := tapeAtCells base (none :: some c :: rest.map some) } :=
  optionCellExpand_run_carryShift_fresh
    (D := optionCellExpandAppendDescription)
    (cF := 30) (cT := 31) (wl := 33) rfl rfl rfl rfl rfl rfl rfl rfl

/--
One expansion-loop iteration over an opaque lower left context: consume the
bit under the head, shift the remaining tail one cell right, write the
consumed bit's two-cell code, and re-enter the loop head read one step right
of the new boundary blank.
-/
theorem optionCellExpand_run_loopIterCore (b : Bool) (rest : Word Bool)
    (low : List (Option Bool)) :
    optionCellExpandAppendDescription.runConfig (2 * rest.length + 6)
        { state := 25
          tape := tapeAtCells (none :: low) (List.map some (b :: rest)) } =
      { state := 25
        tape :=
          tapeAtCells
            (none ::
              (cond b (some false) (some true)) ::
                (some b : Option Bool) :: low)
            (rest.map some) } := by
  have hs1 :
      forall (low' : List (Option Bool)) (right : List (Option Bool)),
        optionCellExpandAppendDescription.runConfig 1
            { state := 25
              tape := tapeAtCells (none :: low') (some b :: right) } =
          { state := cond b 27 26
            tape := tapeAtCells (none :: none :: low') right } := by
    intro low' right
    cases b with
    | false =>
        simp only [optionCellExpand_cond_false]
        rw [optionCellExpand_runConfig_one_of_lookup
          (rfl :
            optionCellExpandAppendDescription.lookupTransition 25
                (some false) =
              some (transition 25 (some false) none Direction.right 26))
          _ rfl]
        simp [Tape.write, Tape.move, optionCellExpand_tapeAtCells_moveRight,
          tapeAtCells]
    | true =>
        simp only [optionCellExpand_cond_true]
        rw [optionCellExpand_runConfig_one_of_lookup
          (rfl :
            optionCellExpandAppendDescription.lookupTransition 25
                (some true) =
              some (transition 25 (some true) none Direction.right 27))
          _ rfl]
        simp [Tape.write, Tape.move, optionCellExpand_tapeAtCells_moveRight,
          tapeAtCells]
  have hs4 :
      forall (low' : List (Option Bool)) (right : List (Option Bool)),
        optionCellExpandAppendDescription.runConfig 1
            { state := cond b 33 32
              tape := tapeAtCells (none :: none :: low') (none :: right) } =
          { state := cond b 35 34
            tape := tapeAtCells (none :: low') (none :: none :: right) } := by
    intro low' right
    cases b with
    | false =>
        simp only [optionCellExpand_cond_false]
        rw [optionCellExpand_runConfig_one_of_lookup
          (rfl :
            optionCellExpandAppendDescription.lookupTransition 32 none =
              some (transition 32 none none Direction.left 34)) _ rfl]
        simp [Tape.write, Tape.move, Tape.moveLeft, tapeAtCells]
    | true =>
        simp only [optionCellExpand_cond_true]
        rw [optionCellExpand_runConfig_one_of_lookup
          (rfl :
            optionCellExpandAppendDescription.lookupTransition 33 none =
              some (transition 33 none none Direction.left 35)) _ rfl]
        simp [Tape.write, Tape.move, Tape.moveLeft, tapeAtCells]
  have hs5 :
      forall (low' : List (Option Bool)) (right : List (Option Bool)),
        optionCellExpandAppendDescription.runConfig 1
            { state := cond b 35 34
              tape := tapeAtCells (none :: low') (none :: right) } =
          { state := cond b 37 36
            tape :=
              tapeAtCells low'
                (none :: (cond b (some false) (some true)) :: right) } := by
    intro low' right
    cases b with
    | false =>
        simp only [optionCellExpand_cond_false]
        rw [optionCellExpand_runConfig_one_of_lookup
          (rfl :
            optionCellExpandAppendDescription.lookupTransition 34 none =
              some (transition 34 none (some true) Direction.left 36)) _ rfl]
        simp [Tape.write, Tape.move, Tape.moveLeft, tapeAtCells]
    | true =>
        simp only [optionCellExpand_cond_true]
        rw [optionCellExpand_runConfig_one_of_lookup
          (rfl :
            optionCellExpandAppendDescription.lookupTransition 35 none =
              some (transition 35 none (some false) Direction.left 37)) _ rfl]
        simp [Tape.write, Tape.move, Tape.moveLeft, tapeAtCells]
  have hs6 :
      forall (low' : List (Option Bool)) (right : List (Option Bool)),
        optionCellExpandAppendDescription.runConfig 1
            { state := cond b 37 36
              tape :=
                tapeAtCells low'
                  (none ::
                    (cond b (some false) (some true)) :: right) } =
          { state := 38
            tape :=
              tapeAtCells ((some b : Option Bool) :: low')
                ((cond b (some false) (some true)) :: right) } := by
    intro low' right
    cases b with
    | false =>
        simp only [optionCellExpand_cond_false]
        rw [optionCellExpand_runConfig_one_of_lookup
          (rfl :
            optionCellExpandAppendDescription.lookupTransition 36 none =
              some (transition 36 none (some false) Direction.right 38))
          _ rfl]
        simp [Tape.write, Tape.move, optionCellExpand_tapeAtCells_moveRight,
          tapeAtCells]
    | true =>
        simp only [optionCellExpand_cond_true]
        rw [optionCellExpand_runConfig_one_of_lookup
          (rfl :
            optionCellExpandAppendDescription.lookupTransition 37 none =
              some (transition 37 none (some true) Direction.right 38))
          _ rfl]
        simp [Tape.write, Tape.move, optionCellExpand_tapeAtCells_moveRight,
          tapeAtCells]
  have hs7 :
      forall (low' : List (Option Bool)) (right : List (Option Bool)),
        optionCellExpandAppendDescription.runConfig 1
            { state := 38
              tape :=
                tapeAtCells low'
                  ((cond b (some false) (some true)) :: right) } =
          { state := 38
            tape :=
              tapeAtCells
                ((cond b (some false) (some true)) :: low') right } := by
    intro low' right
    cases b with
    | false =>
        simp only [optionCellExpand_cond_false]
        rw [optionCellExpand_runConfig_one_of_lookup
          (rfl :
            optionCellExpandAppendDescription.lookupTransition 38
                (some true) =
              some (transition 38 (some true) (some true) Direction.right 38))
          _ rfl]
        simp [Tape.write, Tape.move, optionCellExpand_tapeAtCells_moveRight,
          tapeAtCells]
    | true =>
        simp only [optionCellExpand_cond_true]
        rw [optionCellExpand_runConfig_one_of_lookup
          (rfl :
            optionCellExpandAppendDescription.lookupTransition 38
                (some false) =
              some (transition 38 (some false) (some false)
                Direction.right 38))
          _ rfl]
        simp [Tape.write, Tape.move, optionCellExpand_tapeAtCells_moveRight,
          tapeAtCells]
  have hs8 :
      forall (low' : List (Option Bool)) (right : List (Option Bool)),
        optionCellExpandAppendDescription.runConfig 1
            { state := 38
              tape := tapeAtCells low' (none :: right) } =
          { state := 25
            tape := tapeAtCells (none :: low') right } := by
    intro low' right
    rw [optionCellExpand_runConfig_one_of_lookup
      (rfl :
        optionCellExpandAppendDescription.lookupTransition 38 none =
          some (transition 38 none none Direction.right 25)) _ rfl]
    simp [Tape.write, Tape.move, optionCellExpand_tapeAtCells_moveRight,
      tapeAtCells]
  cases rest with
  | nil =>
      rw [show 2 * ([] : Word Bool).length + 6 =
          1 + (1 + (1 + (1 + (1 + 1)))) by simp]
      rw [runConfig_add]
      rw [show List.map some (b :: ([] : Word Bool)) = [some b] by rfl]
      rw [hs1 low []]
      rw [runConfig_add]
      have hs2 :
          optionCellExpandAppendDescription.runConfig 1
              { state := cond b 27 26
                tape := tapeAtCells (none :: none :: low) [] } =
            { state := cond b 35 34
              tape := tapeAtCells (none :: low) (none :: [none]) } := by
        cases b with
        | false =>
            simp only [optionCellExpand_cond_false]
            rw [optionCellExpand_runConfig_one_of_lookup
              (rfl :
                optionCellExpandAppendDescription.lookupTransition 26 none =
                  some (transition 26 none none Direction.left 34)) _ rfl]
            simp [Tape.write, Tape.move, Tape.moveLeft, tapeAtCells]
        | true =>
            simp only [optionCellExpand_cond_true]
            rw [optionCellExpand_runConfig_one_of_lookup
              (rfl :
                optionCellExpandAppendDescription.lookupTransition 27 none =
                  some (transition 27 none none Direction.left 35)) _ rfl]
            simp [Tape.write, Tape.move, Tape.moveLeft, tapeAtCells]
      rw [hs2]
      rw [runConfig_add]
      rw [hs5 low [none]]
      rw [runConfig_add]
      rw [hs6 low [none]]
      rw [runConfig_add]
      rw [hs7 ((some b : Option Bool) :: low) [none]]
      rw [hs8 ((cond b (some false) (some true)) ::
        (some b : Option Bool) :: low) []]
      rfl
  | cons c rest2 =>
      rw [show 2 * (c :: rest2).length + 6 =
          1 + (1 + ((2 * rest2.length + 1) + (1 + (1 + (1 + (1 + 1)))))) by
        simp
        lia]
      rw [runConfig_add]
      rw [show List.map some (b :: c :: rest2) =
        some b :: some c :: rest2.map some by rfl]
      rw [hs1 low (some c :: rest2.map some)]
      rw [runConfig_add]
      have hs2 :
          optionCellExpandAppendDescription.runConfig 1
              { state := cond b 27 26
                tape :=
                  tapeAtCells (none :: none :: low)
                    (some c :: rest2.map some) } =
            { state :=
                cond b (cond c 31 30) (cond c 29 28)
              tape :=
                tapeAtCells (none :: none :: none :: low)
                  (rest2.map some) } := by
        cases b with
        | false =>
            simp only [optionCellExpand_cond_false]
            cases c with
            | false =>
                simp only [optionCellExpand_cond_false]
                rw [optionCellExpand_runConfig_one_of_lookup
                  (rfl :
                    optionCellExpandAppendDescription.lookupTransition 26
                        (some false) =
                      some (transition 26 (some false) none
                        Direction.right 28)) _ rfl]
                simp [Tape.write, Tape.move,
                  optionCellExpand_tapeAtCells_moveRight, tapeAtCells]
            | true =>
                simp only [optionCellExpand_cond_true]
                rw [optionCellExpand_runConfig_one_of_lookup
                  (rfl :
                    optionCellExpandAppendDescription.lookupTransition 26
                        (some true) =
                      some (transition 26 (some true) none
                        Direction.right 29)) _ rfl]
                simp [Tape.write, Tape.move,
                  optionCellExpand_tapeAtCells_moveRight, tapeAtCells]
        | true =>
            simp only [optionCellExpand_cond_true]
            cases c with
            | false =>
                simp only [optionCellExpand_cond_false]
                rw [optionCellExpand_runConfig_one_of_lookup
                  (rfl :
                    optionCellExpandAppendDescription.lookupTransition 27
                        (some false) =
                      some (transition 27 (some false) none
                        Direction.right 30)) _ rfl]
                simp [Tape.write, Tape.move,
                  optionCellExpand_tapeAtCells_moveRight, tapeAtCells]
            | true =>
                simp only [optionCellExpand_cond_true]
                rw [optionCellExpand_runConfig_one_of_lookup
                  (rfl :
                    optionCellExpandAppendDescription.lookupTransition 27
                        (some true) =
                      some (transition 27 (some true) none
                        Direction.right 31)) _ rfl]
                simp [Tape.write, Tape.move,
                  optionCellExpand_tapeAtCells_moveRight, tapeAtCells]
      rw [hs2]
      rw [runConfig_add]
      have hs3 :
          optionCellExpandAppendDescription.runConfig (2 * rest2.length + 1)
              { state :=
                  cond b (cond c 31 30) (cond c 29 28)
                tape :=
                  tapeAtCells (none :: none :: none :: low)
                    (rest2.map some) } =
            { state := cond b 33 32
              tape :=
                tapeAtCells (none :: none :: low)
                  (none :: some c :: rest2.map some) } := by
        cases b with
        | false =>
            simp only [optionCellExpand_cond_false]
            exact optionCellExpand_run_carryLoopF rest2 c (none :: none :: low)
        | true =>
            simp only [optionCellExpand_cond_true]
            exact optionCellExpand_run_carryLoopT rest2 c (none :: none :: low)
      rw [hs3]
      rw [runConfig_add]
      rw [hs4 low (some c :: rest2.map some)]
      rw [runConfig_add]
      rw [hs5 low (none :: some c :: rest2.map some)]
      rw [runConfig_add]
      rw [hs6 low (none :: some c :: rest2.map some)]
      rw [runConfig_add]
      rw [hs7 ((some b : Option Bool) :: low)
        (none :: some c :: rest2.map some)]
      rw [hs8 ((cond b (some false) (some true)) ::
        (some b : Option Bool) :: low) (some c :: rest2.map some)]
      rfl

/-- One expansion-loop iteration in the loop tape view. -/
theorem optionCellExpand_run_loopIter (emitted : Word Bool) (b : Bool)
    (rest : Word Bool) :
    optionCellExpandAppendDescription.runConfig (2 * rest.length + 6)
        { state := 25
          tape := optionCellExpandLoopTape emitted (b :: rest) } =
      { state := 25
        tape :=
          optionCellExpandLoopTape (List.append emitted [b]) rest } := by
  rw [show optionCellExpandLoopTape emitted (b :: rest) =
      tapeAtCells
        (none ::
          List.append
            (List.map some (optionCellExpandCodeBits emitted).reverse)
            (List.replicate 5 (none : Option Bool)))
        (List.map some (b :: rest)) from rfl]
  rw [optionCellExpand_run_loopIterCore b rest _]
  cases b with
  | false =>
      have hc : optionCellExpandCodeBits (List.append emitted [false]) =
          List.append (optionCellExpandCodeBits emitted) [false, true] := by
        rw [optionCellExpandCodeBits_append]
        rfl
      show _ =
        ({ state := 25
           tape :=
             tapeAtCells
               (none ::
                 List.append
                   (List.map some
                     (optionCellExpandCodeBits
                       (List.append emitted [false])).reverse)
                   (List.replicate 5 (none : Option Bool)))
               (rest.map some) } : MachineDescription.Configuration)
      rw [hc]
      simp [List.reverse_append]
  | true =>
      have hc : optionCellExpandCodeBits (List.append emitted [true]) =
          List.append (optionCellExpandCodeBits emitted) [true, false] := by
        rw [optionCellExpandCodeBits_append]
        rfl
      show _ =
        ({ state := 25
           tape :=
             tapeAtCells
               (none ::
                 List.append
                   (List.map some
                     (optionCellExpandCodeBits
                       (List.append emitted [true])).reverse)
                   (List.replicate 5 (none : Option Bool)))
               (rest.map some) } : MachineDescription.Configuration)
      rw [hc]
      simp [List.reverse_append]

/-- Exact fuel for the whole expansion loop. -/
def optionCellExpandLoopFuel : Word Bool -> Nat
  | [] => 0
  | _ :: rest => (2 * rest.length + 6) + optionCellExpandLoopFuel rest

/-- The expansion loop consumes the remaining word into emitted codes. -/
theorem optionCellExpand_run_loop (rem : Word Bool) :
    forall emitted : Word Bool,
      optionCellExpandAppendDescription.runConfig
          (optionCellExpandLoopFuel rem)
          { state := 25
            tape := optionCellExpandLoopTape emitted rem } =
        { state := 25
          tape := optionCellExpandLoopTape (List.append emitted rem) [] } := by
  induction rem with
  | nil =>
      intro emitted
      simp [optionCellExpandLoopFuel, runConfig]
  | cons b rest ih =>
      intro emitted
      rw [show optionCellExpandLoopFuel (b :: rest) =
          (2 * rest.length + 6) + optionCellExpandLoopFuel rest from rfl]
      rw [runConfig_add]
      rw [optionCellExpand_run_loopIter emitted b rest]
      rw [ih (List.append emitted [b])]
      simp [List.append_assoc]

/-! ## Fixed suffix, rewind, and backward prefix write -/

/-- Fixed writer step at the right record edge. -/
theorem optionCellExpand_run_edgeWrite
    {D : MachineDescription} {s s' : Nat} {w : Option Bool}
    (h : D.lookupTransition s none =
      some (transition s none w Direction.right s'))
    (L : List (Option Bool)) :
    D.runConfig 1 { state := s, tape := tapeAtCells L [] } =
      { state := s', tape := tapeAtCells (w :: L) [] } := by
  rw [optionCellExpand_runConfig_one_of_lookup h _ rfl]
  rfl

/--
Cells right of the input block in the final layout: separator, guarded blank
scratch tape, separator, guarded blank output tape, final separator.
-/
def optionCellExpandTailCells : List (Option Bool) :=
  [none, some false, some false, some true, some true, some false,
    some false, some false, some false, none, some false, some false,
    some true, some true, some false, some false, some false, some false,
    none]

/-- The eighteen fixed suffix writers (states 41-58). -/
theorem optionCellExpand_run_suffixWriters (L : List (Option Bool)) :
    optionCellExpandAppendDescription.runConfig 18
        { state := 41, tape := tapeAtCells L [] } =
      { state := 59
        tape :=
          tapeAtCells
            (some false :: some false :: some false :: some false ::
              some true :: some true :: some false :: some false :: none ::
                some false :: some false :: some false :: some false ::
                  some true :: some true :: some false :: some false ::
                    none :: L) [] } := by
  rw [show (18 : Nat) =
      1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 +
        (1 + (1 + (1 + (1 + 1)))))))))))))))) by decide]
  rw [runConfig_add]
  rw [optionCellExpand_run_edgeWrite
    (rfl : optionCellExpandAppendDescription.lookupTransition 41 none =
      some (transition 41 none none Direction.right 42)) L]
  rw [runConfig_add]
  rw [optionCellExpand_run_edgeWrite
    (rfl : optionCellExpandAppendDescription.lookupTransition 42 none =
      some (transition 42 none (some false) Direction.right 43)) _]
  rw [runConfig_add]
  rw [optionCellExpand_run_edgeWrite
    (rfl : optionCellExpandAppendDescription.lookupTransition 43 none =
      some (transition 43 none (some false) Direction.right 44)) _]
  rw [runConfig_add]
  rw [optionCellExpand_run_edgeWrite
    (rfl : optionCellExpandAppendDescription.lookupTransition 44 none =
      some (transition 44 none (some true) Direction.right 45)) _]
  rw [runConfig_add]
  rw [optionCellExpand_run_edgeWrite
    (rfl : optionCellExpandAppendDescription.lookupTransition 45 none =
      some (transition 45 none (some true) Direction.right 46)) _]
  rw [runConfig_add]
  rw [optionCellExpand_run_edgeWrite
    (rfl : optionCellExpandAppendDescription.lookupTransition 46 none =
      some (transition 46 none (some false) Direction.right 47)) _]
  rw [runConfig_add]
  rw [optionCellExpand_run_edgeWrite
    (rfl : optionCellExpandAppendDescription.lookupTransition 47 none =
      some (transition 47 none (some false) Direction.right 48)) _]
  rw [runConfig_add]
  rw [optionCellExpand_run_edgeWrite
    (rfl : optionCellExpandAppendDescription.lookupTransition 48 none =
      some (transition 48 none (some false) Direction.right 49)) _]
  rw [runConfig_add]
  rw [optionCellExpand_run_edgeWrite
    (rfl : optionCellExpandAppendDescription.lookupTransition 49 none =
      some (transition 49 none (some false) Direction.right 50)) _]
  rw [runConfig_add]
  rw [optionCellExpand_run_edgeWrite
    (rfl : optionCellExpandAppendDescription.lookupTransition 50 none =
      some (transition 50 none none Direction.right 51)) _]
  rw [runConfig_add]
  rw [optionCellExpand_run_edgeWrite
    (rfl : optionCellExpandAppendDescription.lookupTransition 51 none =
      some (transition 51 none (some false) Direction.right 52)) _]
  rw [runConfig_add]
  rw [optionCellExpand_run_edgeWrite
    (rfl : optionCellExpandAppendDescription.lookupTransition 52 none =
      some (transition 52 none (some false) Direction.right 53)) _]
  rw [runConfig_add]
  rw [optionCellExpand_run_edgeWrite
    (rfl : optionCellExpandAppendDescription.lookupTransition 53 none =
      some (transition 53 none (some true) Direction.right 54)) _]
  rw [runConfig_add]
  rw [optionCellExpand_run_edgeWrite
    (rfl : optionCellExpandAppendDescription.lookupTransition 54 none =
      some (transition 54 none (some true) Direction.right 55)) _]
  rw [runConfig_add]
  rw [optionCellExpand_run_edgeWrite
    (rfl : optionCellExpandAppendDescription.lookupTransition 55 none =
      some (transition 55 none (some false) Direction.right 56)) _]
  rw [runConfig_add]
  rw [optionCellExpand_run_edgeWrite
    (rfl : optionCellExpandAppendDescription.lookupTransition 56 none =
      some (transition 56 none (some false) Direction.right 57)) _]
  rw [runConfig_add]
  rw [optionCellExpand_run_edgeWrite
    (rfl : optionCellExpandAppendDescription.lookupTransition 57 none =
      some (transition 57 none (some false) Direction.right 58)) _]
  rw [optionCellExpand_run_edgeWrite
    (rfl : optionCellExpandAppendDescription.lookupTransition 58 none =
      some (transition 58 none (some false) Direction.right 59)) _]

/-- Rewind scan over the top guarded blank block (state 60). -/
theorem optionCellExpand_run_scanGB60 (base right : List (Option Bool)) :
    optionCellExpandAppendDescription.runConfig 8
        { state := 60
          tape :=
            tapeAtCells
              (some false :: some false :: some false :: some true ::
                some true :: some false :: some false :: none :: base)
              (some false :: right) } =
      { state := 60
        tape :=
          tapeAtCells base
            (none :: some false :: some false :: some true :: some true ::
              some false :: some false :: some false :: some false ::
                right) } := by
  have h :=
    optionCellExpand_run_scanLeft
      (D := optionCellExpandAppendDescription) (s := 60) rfl rfl
      [false, false, false, true, true, false, false] false base right
  simpa using h

/-- Rewind scan over the lower guarded blank block (state 61). -/
theorem optionCellExpand_run_scanGB61 (base right : List (Option Bool)) :
    optionCellExpandAppendDescription.runConfig 8
        { state := 61
          tape :=
            tapeAtCells
              (some false :: some false :: some false :: some true ::
                some true :: some false :: some false :: none :: base)
              (some false :: right) } =
      { state := 61
        tape :=
          tapeAtCells base
            (none :: some false :: some false :: some true :: some true ::
              some false :: some false :: some false :: some false ::
                right) } := by
  have h :=
    optionCellExpand_run_scanLeft
      (D := optionCellExpandAppendDescription) (s := 61) rfl rfl
      [false, false, false, true, true, false, false] false base right
  simpa using h

/--
From the first suffix writer to the rewind state on the second cell of the
right guard: fixed suffix writes, turnaround on the final separator, and the
two separator-counting scans.
-/
theorem optionCellExpand_run_suffixRewind (L : List (Option Bool)) :
    optionCellExpandAppendDescription.runConfig 37
        { state := 41, tape := tapeAtCells (some false :: L) [] } =
      { state := 62
        tape := tapeAtCells L (some false :: optionCellExpandTailCells) } := by
  rw [show (37 : Nat) = 18 + (1 + (8 + (1 + (8 + 1)))) by decide]
  rw [runConfig_add]
  rw [optionCellExpand_run_suffixWriters (some false :: L)]
  rw [runConfig_add]
  have hturn :
      optionCellExpandAppendDescription.runConfig 1
          { state := 59
            tape :=
              tapeAtCells
                (some false :: some false :: some false :: some false ::
                  some true :: some true :: some false :: some false ::
                    none :: some false :: some false :: some false ::
                      some false :: some true :: some true :: some false ::
                        some false :: none :: some false :: L) [] } =
        { state := 60
          tape :=
            tapeAtCells
              (some false :: some false :: some false :: some true ::
                some true :: some false :: some false :: none ::
                  some false :: some false :: some false :: some false ::
                    some true :: some true :: some false :: some false ::
                      none :: some false :: L)
              (some false :: [none]) } := by
    rw [optionCellExpand_runConfig_one_of_lookup
      (rfl : optionCellExpandAppendDescription.lookupTransition 59 none =
        some (transition 59 none none Direction.left 60)) _ rfl]
    rfl
  rw [hturn]
  rw [runConfig_add]
  rw [optionCellExpand_run_scanGB60
    (some false :: some false :: some false :: some false :: some true ::
      some true :: some false :: some false :: none :: some false :: L)
    [none]]
  rw [runConfig_add]
  have hexitA :
      optionCellExpandAppendDescription.runConfig 1
          { state := 60
            tape :=
              tapeAtCells
                (some false :: some false :: some false :: some false ::
                  some true :: some true :: some false :: some false ::
                    none :: some false :: L)
                (none :: some false :: some false :: some true ::
                  some true :: some false :: some false :: some false ::
                    some false :: [none]) } =
        { state := 61
          tape :=
            tapeAtCells
              (some false :: some false :: some false :: some true ::
                some true :: some false :: some false :: none ::
                  some false :: L)
              (some false :: none :: some false :: some false ::
                some true :: some true :: some false :: some false ::
                  some false :: some false :: [none]) } := by
    rw [optionCellExpand_runConfig_one_of_lookup
      (rfl : optionCellExpandAppendDescription.lookupTransition 60 none =
        some (transition 60 none none Direction.left 61)) _ rfl]
    rfl
  rw [hexitA]
  rw [runConfig_add]
  rw [optionCellExpand_run_scanGB61 (some false :: L)
    (none :: some false :: some false :: some true :: some true ::
      some false :: some false :: some false :: some false :: [none])]
  have hexitB :
      optionCellExpandAppendDescription.runConfig 1
          { state := 61
            tape :=
              tapeAtCells (some false :: L)
                (none :: some false :: some false :: some true ::
                  some true :: some false :: some false :: some false ::
                    some false :: none :: some false :: some false ::
                      some true :: some true :: some false :: some false ::
                        some false :: some false :: [none]) } =
        { state := 62
          tape :=
            tapeAtCells L (some false :: optionCellExpandTailCells) } := by
    rw [optionCellExpand_runConfig_one_of_lookup
      (rfl : optionCellExpandAppendDescription.lookupTransition 61 none =
        some (transition 61 none none Direction.left 62)) _ rfl]
    rfl
  rw [hexitB]

/--
Final rewind: cross the blank-free code block, then write the head marker and
the left guard backwards, arriving into the halt state on the left boundary
separator.
-/
theorem optionCellExpand_run_finalRewind (seg : Word Bool)
    (right : List (Option Bool)) :
    optionCellExpandAppendDescription.runConfig (seg.length + 5)
        { state := 62
          tape :=
            tapeAtCells
              (List.append (seg.map some)
                (none :: none :: none :: none :: [none]))
              (some false :: right) } =
      { state := 0
        tape :=
          tapeAtCells []
            (none :: some false :: some false :: some true :: some true ::
              List.append (List.map some seg.reverse)
                (some false :: right)) } := by
  rw [show seg.length + 5 = (seg.length + 1) + (1 + (1 + (1 + 1))) by lia]
  rw [runConfig_add]
  rw [optionCellExpand_run_scanLeft
    (D := optionCellExpandAppendDescription) (s := 62) rfl rfl
    seg false (none :: none :: none :: [none]) right]
  rw [runConfig_add]
  have ha :
      optionCellExpandAppendDescription.runConfig 1
          { state := 62
            tape :=
              tapeAtCells (none :: none :: none :: [none])
                (none ::
                  List.append (List.map some seg.reverse)
                    (some false :: right)) } =
        { state := 63
          tape :=
            tapeAtCells (none :: none :: [none])
              (none :: some true ::
                List.append (List.map some seg.reverse)
                  (some false :: right)) } := by
    rw [optionCellExpand_runConfig_one_of_lookup
      (rfl : optionCellExpandAppendDescription.lookupTransition 62 none =
        some (transition 62 none (some true) Direction.left 63)) _ rfl]
    rfl
  rw [ha]
  rw [runConfig_add]
  have hb :
      optionCellExpandAppendDescription.runConfig 1
          { state := 63
            tape :=
              tapeAtCells (none :: none :: [none])
                (none :: some true ::
                  List.append (List.map some seg.reverse)
                    (some false :: right)) } =
        { state := 64
          tape :=
            tapeAtCells (none :: [none])
              (none :: some true :: some true ::
                List.append (List.map some seg.reverse)
                  (some false :: right)) } := by
    rw [optionCellExpand_runConfig_one_of_lookup
      (rfl : optionCellExpandAppendDescription.lookupTransition 63 none =
        some (transition 63 none (some true) Direction.left 64)) _ rfl]
    rfl
  rw [hb]
  rw [runConfig_add]
  have hc :
      optionCellExpandAppendDescription.runConfig 1
          { state := 64
            tape :=
              tapeAtCells (none :: [none])
                (none :: some true :: some true ::
                  List.append (List.map some seg.reverse)
                    (some false :: right)) } =
        { state := 65
          tape :=
            tapeAtCells [none]
              (none :: some false :: some true :: some true ::
                List.append (List.map some seg.reverse)
                  (some false :: right)) } := by
    rw [optionCellExpand_runConfig_one_of_lookup
      (rfl : optionCellExpandAppendDescription.lookupTransition 64 none =
        some (transition 64 none (some false) Direction.left 65)) _ rfl]
    rfl
  rw [hc]
  rw [optionCellExpand_runConfig_one_of_lookup
    (rfl : optionCellExpandAppendDescription.lookupTransition 65 none =
      some (transition 65 none (some false) Direction.left 0)) _ rfl]
  rfl

/-- Loop exit into the right-guard writes and the first suffix writer. -/
theorem optionCellExpand_run_gEntry (low : List (Option Bool)) :
    optionCellExpandAppendDescription.runConfig 3
        { state := 25, tape := tapeAtCells (none :: low) [] } =
      { state := 41
        tape := tapeAtCells (some false :: some false :: low) [] } := by
  rw [show (3 : Nat) = 1 + (1 + 1) by decide]
  rw [runConfig_add]
  have h1 :
      optionCellExpandAppendDescription.runConfig 1
          { state := 25, tape := tapeAtCells (none :: low) [] } =
        { state := 39, tape := tapeAtCells low (none :: [some false]) } := by
    rw [optionCellExpand_runConfig_one_of_lookup
      (rfl : optionCellExpandAppendDescription.lookupTransition 25 none =
        some (transition 25 none (some false) Direction.left 39)) _ rfl]
    rfl
  rw [h1]
  rw [runConfig_add]
  have h2 :
      optionCellExpandAppendDescription.runConfig 1
          { state := 39, tape := tapeAtCells low (none :: [some false]) } =
        { state := 40
          tape := tapeAtCells (some false :: low) [some false] } := by
    rw [optionCellExpand_runConfig_one_of_lookup
      (rfl : optionCellExpandAppendDescription.lookupTransition 39 none =
        some (transition 39 none (some false) Direction.right 40)) _ rfl]
    rfl
  rw [h2]
  rw [optionCellExpand_runConfig_one_of_lookup
    (rfl :
      optionCellExpandAppendDescription.lookupTransition 40 (some false) =
        some (transition 40 (some false) (some false) Direction.right 41))
    _ rfl]
  rfl

/-! ## Top-level runs and the run contract -/

/-- Exact fuel for a nonempty input word. -/
def optionCellExpandConsFuel (b : Bool) (rest : Word Bool) : Nat :=
  (12 * rest.length + 18) +
    (optionCellExpandLoopFuel (b :: rest) +
      (3 + (37 +
        ((false :: (optionCellExpandCodeBits (b :: rest)).reverse).length +
          5))))

/-- Explicit final layout for a nonempty input word. -/
theorem optionCellExpandAppendTargetCells_cons_explicit
    (b : Bool) (rest : Word Bool) :
    optionCellExpandAppendTargetCells (b :: rest) =
      none :: some false :: some false :: some true :: some true ::
        List.append (logicalCellListCode (List.map some (b :: rest)))
          (some false :: some false :: optionCellExpandTailCells) := by
  cases b <;>
    simp [optionCellExpandAppendTargetCells,
      optionCellExpandAppendPrefixCells,
      optionCellExpandAppendScannedCells,
      optionCellExpandAppendBitCells,
      optionCellExpandAppendRightGuardCells,
      optionCellExpandAppendSuffixCells,
      guardedBlankLogicalTapeCode, guardedInputWordLogicalTapeCode,
      optionCellExpandTailCells, logicalCellCode, headMarkerCells,
      tapeSeparatorCells, logicalCellListBits,
      logicalCellBits]

/-- Full exact run for a nonempty input word. -/
theorem optionCellExpand_run_cons (b : Bool) (rest : Word Bool) :
    optionCellExpandAppendDescription.runConfig
        (optionCellExpandConsFuel b rest)
        { state := 1, tape := Tape.input (b :: rest) } =
      { state := 0
        tape :=
          tapeAtCells []
            (optionCellExpandAppendTargetCells (b :: rest)) } := by
  rw [show Tape.input (b :: rest) =
    tapeAtCells [] (List.map some (b :: rest)) from rfl]
  rw [show optionCellExpandConsFuel b rest =
    (12 * rest.length + 18) +
      (optionCellExpandLoopFuel (b :: rest) +
        (3 + (37 +
          ((false ::
            (optionCellExpandCodeBits (b :: rest)).reverse).length +
              5)))) from rfl]
  rw [runConfig_add]
  rw [optionCellExpand_run_shiftPhase b rest]
  rw [runConfig_add]
  rw [optionCellExpand_run_loop (b :: rest) []]
  rw [show optionCellExpandLoopTape
      (List.append ([] : Word Bool) (b :: rest)) [] =
    tapeAtCells
      (none ::
        List.append
          (List.map some (optionCellExpandCodeBits (b :: rest)).reverse)
          (List.replicate 5 (none : Option Bool)))
      [] from rfl]
  rw [runConfig_add]
  rw [optionCellExpand_run_gEntry _]
  rw [runConfig_add]
  rw [optionCellExpand_run_suffixRewind
    (some false ::
      List.append
        (List.map some (optionCellExpandCodeBits (b :: rest)).reverse)
        (List.replicate 5 (none : Option Bool)))]
  rw [show (some false ::
      List.append
        (List.map some (optionCellExpandCodeBits (b :: rest)).reverse)
        (List.replicate 5 (none : Option Bool))) =
    List.append
      (List.map some
        ((false :: (optionCellExpandCodeBits (b :: rest)).reverse) :
          Word Bool))
      (none :: none :: none :: none :: [none]) from rfl]
  rw [optionCellExpand_run_finalRewind
    (false :: (optionCellExpandCodeBits (b :: rest)).reverse)
    optionCellExpandTailCells]
  rw [optionCellExpandAppendTargetCells_cons_explicit b rest]
  rw [List.reverse_cons]
  rw [List.reverse_reverse]
  rw [List.map_append]
  rw [optionCellExpand_codeBits_map_some]
  simp [List.append_assoc]

/-- Exact halting run for a nonempty input word. -/
theorem optionCellExpandAppendDescription_haltsFrom_cons
    (b : Bool) (rest : Word Bool) :
    optionCellExpandAppendDescription.HaltsFromTape
      (Tape.input (b :: rest))
      (tapeAtCells [] (optionCellExpandAppendTargetCells (b :: rest))) := by
  refine ⟨optionCellExpandConsFuel b rest, ?_, ?_⟩
  · show
      (optionCellExpandAppendDescription.runConfig
        (optionCellExpandConsFuel b rest)
        { state := 1, tape := Tape.input (b :: rest) }).state = 0
    rw [optionCellExpand_run_cons]
  · show
      (optionCellExpandAppendDescription.runConfig
        (optionCellExpandConsFuel b rest)
        { state := 1, tape := Tape.input (b :: rest) }).tape =
      tapeAtCells [] (optionCellExpandAppendTargetCells (b :: rest))
    rw [optionCellExpand_run_cons]

/-- Exact halting run for the empty input word (kernel-evaluated). -/
theorem optionCellExpandAppendDescription_haltsFrom_nil :
    optionCellExpandAppendDescription.HaltsFromTape
      (Tape.input ([] : Word Bool))
      (tapeAtCells [] (optionCellExpandAppendTargetCells [])) := by
  refine ⟨54, ?_, ?_⟩ <;> decide

theorem optionCellExpandAppendDescription_runSpec :
    OptionCellExpandAppendRunSpec optionCellExpandAppendDescription := by
  refine ⟨optionCellExpandAppendDescription_subroutineReady, ?_⟩
  intro bits
  cases bits with
  | nil => exact optionCellExpandAppendDescription_haltsFrom_nil
  | cons b rest =>
      exact optionCellExpandAppendDescription_haltsFrom_cons b rest

end StructuredConstructionTargets

end Computability
end FoC

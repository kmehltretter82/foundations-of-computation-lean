import FoC.Computability.Compiler.Structured.Lowering.Dispatcher.BranchingHeadCell

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
Lift an arbitrary-state run through a copied branching reader whose three local
read exits have been redirected to a continuation-state family.
-/
theorem runsFromStateTapeEquiv_offsetReadExitRetargetDescription
    {offset : Nat} {localTarget target : Option Bool -> Nat}
    (hbelow : forall cell : Option Bool, target cell < offset)
    {D : MachineDescription}
    (hD :
      forall exitCell : Option Bool,
        D.TransitionFreeAt (localTarget exitCell))
    {sourceState : Nat} {observed : Option Bool}
    {Tin Tout : Tape Bool}
    (hrun :
      RunsFromStateTapeEquiv D sourceState (localTarget observed)
        Tin Tout) :
    RunsFromStateTapeEquiv
      (MachineDescription.offsetReadExitRetargetDescription
        offset localTarget target D)
      (MachineDescription.retargetReadExitState
        offset localTarget target sourceState)
      (MachineDescription.retargetReadExitState
        offset localTarget target (localTarget observed)) Tin Tout := by
  rcases hrun with ⟨n, Tactual, hrun, hout⟩
  refine ⟨n, Tactual, ?_, hout⟩
  have hretarget :=
    MachineDescription.offsetReadExitRetargetDescription_runConfig_eq
      (offset := offset) (localTarget := localTarget) (target := target)
      hbelow hD hrun
  simpa [MachineDescription.readExitRetargetConfiguration] using hretarget

/--
A two-step finite-control jump that preserves a tape whose current cell is
blank, up to {name}`Tape.Equiv`.

The ordinary backend has no stay move.  Static dispatcher handoffs therefore
use a right-left bounce from separator states when they need to change only the
finite-control state.
-/
def blankHeadBounceJumpDescription
    (stateCount source scratch target : Nat) : MachineDescription where
  stateCount := stateCount
  start := source
  halt := target
  transitions :=
    [ { source := source
        read := none
        write := none
        move := Direction.right
        target := scratch },
      { source := scratch
        read := none
        write := none
        move := Direction.left
        target := target },
      { source := scratch
        read := some false
        write := some false
        move := Direction.left
        target := target },
      { source := scratch
        read := some true
        write := some true
        move := Direction.left
        target := target } ]

private theorem moveLeft_moveRight_equiv_self
    (T : Tape Bool) :
    Tape.Equiv
      (Tape.move Direction.left (Tape.move Direction.right T)) T := by
  cases T with
  | mk left head right =>
      simp [Tape.Equiv, Tape.move, Tape.moveLeft, Tape.moveRight]
      cases right <;> simp [Tape.dropTrailingNone]

theorem blankHeadBounceJumpDescription_lookup_source
    (stateCount source scratch target : Nat) :
    MachineDescription.lookupTransition
        (blankHeadBounceJumpDescription stateCount source scratch target)
        source none =
      some
        ({ source := source
           read := none
           write := none
           move := Direction.right
           target := scratch } : TransitionDescription) := by
  simp [blankHeadBounceJumpDescription,
    MachineDescription.lookupTransition, MachineDescription.Matches]

theorem blankHeadBounceJumpDescription_lookup_scratch
    {stateCount source scratch target : Nat}
    (hsourceScratch : source ≠ scratch)
    (cell : Option Bool) :
    MachineDescription.lookupTransition
        (blankHeadBounceJumpDescription stateCount source scratch target)
        scratch cell =
      some
        ({ source := scratch
           read := cell
           write := cell
           move := Direction.left
           target := target } : TransitionDescription) := by
  have hsourceScratchBeq : (source == scratch) = false := by
    rw [beq_eq_false_iff_ne]
    exact hsourceScratch
  cases cell with
  | none =>
      simp [blankHeadBounceJumpDescription,
        MachineDescription.lookupTransition, MachineDescription.Matches,
        hsourceScratchBeq]
  | some bit =>
      cases bit <;>
        simp [blankHeadBounceJumpDescription,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          hsourceScratchBeq]

theorem blankHeadBounceJumpDescription_runsFromBlankHead
    {stateCount source scratch target : Nat}
    {T : Tape Bool}
    (hsourceScratch : source ≠ scratch)
    (hread : Tape.read T = none) :
    RunsFromStateTapeEquiv
      (blankHeadBounceJumpDescription stateCount source scratch target)
      source target T T := by
  refine
    ⟨2, Tape.move Direction.left (Tape.move Direction.right T), ?_,
      moveLeft_moveRight_equiv_self T⟩
  cases T with
  | mk left head right =>
      simp [Tape.read] at hread
      cases hread
      cases right with
      | nil =>
          simp [MachineDescription.runConfig,
            MachineDescription.stepConfig,
            blankHeadBounceJumpDescription_lookup_source,
            blankHeadBounceJumpDescription_lookup_scratch hsourceScratch,
            Tape.read, Tape.move, Tape.moveLeft, Tape.moveRight,
            Tape.write]
      | cons rightHead rightTail =>
          cases rightHead <;>
            simp [MachineDescription.runConfig,
              MachineDescription.stepConfig,
              blankHeadBounceJumpDescription_lookup_source,
              blankHeadBounceJumpDescription_lookup_scratch hsourceScratch,
              Tape.read, Tape.move, Tape.moveLeft, Tape.moveRight,
              Tape.write]

theorem blankHeadBounceJumpDescription_wellFormed
    {stateCount source scratch target : Nat}
    (hsource : source < stateCount)
    (hscratch : scratch < stateCount)
    (htarget : target < stateCount)
    (hsourceScratch : source ≠ scratch) :
    (blankHeadBounceJumpDescription
      stateCount source scratch target).WellFormed := by
  constructor
  · exact Nat.lt_of_le_of_lt (Nat.zero_le source) hsource
  constructor
  · exact hsource
  constructor
  · exact htarget
  constructor
  · intro t ht
    simp [blankHeadBounceJumpDescription] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact ⟨hsource, hscratch⟩
    · exact ⟨hscratch, htarget⟩
    · exact ⟨hscratch, htarget⟩
    · exact ⟨hscratch, htarget⟩
  · intro t u ht hu hkey
    simp [blankHeadBounceJumpDescription] at ht hu
    rcases ht with rfl | rfl | rfl | rfl <;>
      rcases hu with rfl | rfl | rfl | rfl <;>
      simp [TransitionDescription.SameKey,
        TransitionDescription.SameAction, hsourceScratch] at hkey ⊢
    exact False.elim (hsourceScratch hkey.symm)

theorem blankHeadBounceJumpDescription_haltTransitionFree
    {stateCount source scratch target : Nat}
    (htargetSource : target ≠ source)
    (htargetScratch : target ≠ scratch) :
    (blankHeadBounceJumpDescription
      stateCount source scratch target).HaltTransitionFree := by
  have hsourceTarget : source ≠ target := fun h => htargetSource h.symm
  have hscratchTarget : scratch ≠ target := fun h => htargetScratch h.symm
  intro t ht
  simp [blankHeadBounceJumpDescription] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact hsourceTarget
  · exact hscratchTarget
  · exact hscratchTarget
  · exact hscratchTarget

theorem blankHeadBounceJumpDescription_subroutineReady
    {stateCount source scratch target : Nat}
    (hsource : source < stateCount)
    (hscratch : scratch < stateCount)
    (htarget : target < stateCount)
    (hsourceScratch : source ≠ scratch)
    (htargetSource : target ≠ source)
    (htargetScratch : target ≠ scratch) :
    (blankHeadBounceJumpDescription
      stateCount source scratch target).SubroutineReady :=
  ⟨blankHeadBounceJumpDescription_wellFormed
      hsource hscratch htarget hsourceScratch,
    blankHeadBounceJumpDescription_haltTransitionFree
      htargetSource htargetScratch⟩

theorem atTapeSeparator_read
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    {physical : Tape Bool}
    (hseparator : AtTapeSeparator logical tapeIndex physical) :
    Tape.read physical = none := by
  rcases hseparator with ⟨_hle, hphysical⟩
  rw [hphysical]
  unfold tapeAtEncodedSplit encodedSuffixFromTape
  cases logical.drop tapeIndex <;>
    simp [encodedStructuredTapeCells, tapeSeparatorCells, tapeAtCells,
      Tape.read]

theorem blankHeadBounceJumpDescription_runsFromTapeSeparator
    {stateCount source scratch target : Nat}
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    {physical : Tape Bool}
    (hsourceScratch : source ≠ scratch)
    (hseparator : AtTapeSeparator logical tapeIndex physical) :
    RunsFromStateTapeEquiv
      (blankHeadBounceJumpDescription stateCount source scratch target)
      source target physical physical :=
  blankHeadBounceJumpDescription_runsFromBlankHead
    hsourceScratch (atTapeSeparator_read hseparator)

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

def retargetedBranchingTape0ReadHeadCellAllExitsDescription
    (offset : Nat) (target : Option Bool -> Nat) :
    MachineDescription :=
  MachineDescription.offsetReadExitRetargetDescription offset
    branchingTape0ReadHeadCellAndReturnToSeparatorTarget
    target
    branchingTape0ReadHeadCellAndReturnToSeparatorDescription

theorem
    retargetedBranchingTape0ReadHeadCellAllExitsDescription_subroutineReady
    {offset : Nat} {target : Option Bool -> Nat}
    (hbelow : forall cell : Option Bool, target cell < offset) :
    (retargetedBranchingTape0ReadHeadCellAllExitsDescription
      offset target).SubroutineReady :=
  MachineDescription.offsetReadExitRetargetDescription_subroutineReady
    hbelow
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
    retargetedBranchingTape0ReadHeadCellAllExitsDescription_runsFromGuardedBlockStart
    {offset : Nat} {target : Option Bool -> Nat}
    (hbelow : forall cell : Option Bool, target cell < offset)
    {logical : List (Tape Bool)}
    (hlength : logical.length = 3) :
    exists separatorPhysical : Tape Bool,
      AtExistingTapeSeparator (guardLogicalTapes logical) 0
        separatorPhysical ∧
        RunsFromStateTapeEquiv
          (retargetedBranchingTape0ReadHeadCellAllExitsDescription
            offset target)
          (retargetedBranchingTape0ReadHeadCellAllExitsDescription
            offset target).start
          (target (Tape.read (Description.tapeAt logical 0)))
          (encodedGuardedStructuredTapes logical)
          separatorPhysical := by
  rcases
      branchingTape0ReadHeadCellAndReturnToSeparatorDescription_runsFromGuardedBlockStart
        hlength with
    ⟨separatorPhysical, hseparator, hrun⟩
  have hcopy :=
    runsFromStateTapeEquiv_offsetReadExitRetargetDescription
      (offset := offset)
      (localTarget :=
        branchingTape0ReadHeadCellAndReturnToSeparatorTarget)
      (target := target)
      hbelow
      branchingTape0ReadHeadCellAndReturnToSeparatorDescription_transitionFreeAt
      (observed := Tape.read (Description.tapeAt logical 0))
      hrun
  exact
    ⟨separatorPhysical, hseparator, by
      cases hread : Tape.read (Description.tapeAt logical 0) with
      | none =>
          simpa
            [retargetedBranchingTape0ReadHeadCellAllExitsDescription,
              MachineDescription.offsetReadExitRetargetDescription,
              MachineDescription.retargetReadExitState,
              branchingTape0ReadHeadCellAndReturnToSeparatorTarget,
              branchingSeparatorReadHeadCellTarget,
              BranchingHeadCellReturn.targetForRead, hread] using hcopy
      | some bit =>
          cases bit with
          | false =>
              simpa
                [retargetedBranchingTape0ReadHeadCellAllExitsDescription,
                  MachineDescription.offsetReadExitRetargetDescription,
                  MachineDescription.retargetReadExitState,
                  branchingTape0ReadHeadCellAndReturnToSeparatorTarget,
                  branchingSeparatorReadHeadCellTarget,
                  BranchingHeadCellReturn.targetForRead, hread] using! hcopy
          | true =>
              simpa
                [retargetedBranchingTape0ReadHeadCellAllExitsDescription,
                  MachineDescription.offsetReadExitRetargetDescription,
                  MachineDescription.retargetReadExitState,
                  branchingTape0ReadHeadCellAndReturnToSeparatorTarget,
                  branchingSeparatorReadHeadCellTarget,
                  BranchingHeadCellReturn.targetForRead, hread] using! hcopy⟩

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

def retargetedBranchingTape1ReadHeadCellAllExitsDescription
    (offset : Nat) (target : Option Bool -> Nat) :
    MachineDescription :=
  MachineDescription.offsetReadExitRetargetDescription offset
    branchingTape1ReadHeadCellAndReturnToSeparatorTarget
    target
    branchingTape1ReadHeadCellAndReturnToSeparatorDescription

theorem
    retargetedBranchingTape1ReadHeadCellAllExitsDescription_subroutineReady
    {offset : Nat} {target : Option Bool -> Nat}
    (hbelow : forall cell : Option Bool, target cell < offset) :
    (retargetedBranchingTape1ReadHeadCellAllExitsDescription
      offset target).SubroutineReady :=
  MachineDescription.offsetReadExitRetargetDescription_subroutineReady
    hbelow
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
    retargetedBranchingTape1ReadHeadCellAllExitsDescription_runsFromGuardedBlockStart
    {offset : Nat} {target : Option Bool -> Nat}
    (hbelow : forall cell : Option Bool, target cell < offset)
    {logical : List (Tape Bool)}
    (hlength : logical.length = 3) :
    exists separatorPhysical : Tape Bool,
      AtExistingTapeSeparator (guardLogicalTapes logical) 1
        separatorPhysical ∧
        RunsFromStateTapeEquiv
          (retargetedBranchingTape1ReadHeadCellAllExitsDescription
            offset target)
          (retargetedBranchingTape1ReadHeadCellAllExitsDescription
            offset target).start
          (target (Tape.read (Description.tapeAt logical 1)))
          (encodedGuardedStructuredTapes logical)
          separatorPhysical := by
  rcases
      branchingTape1ReadHeadCellAndReturnToSeparatorDescription_runsFromGuardedBlockStart
        hlength with
    ⟨separatorPhysical, hseparator, hrun⟩
  have hcopy :=
    runsFromStateTapeEquiv_offsetReadExitRetargetDescription
      (offset := offset)
      (localTarget :=
        branchingTape1ReadHeadCellAndReturnToSeparatorTarget)
      (target := target)
      hbelow
      branchingTape1ReadHeadCellAndReturnToSeparatorDescription_transitionFreeAt
      (observed := Tape.read (Description.tapeAt logical 1))
      hrun
  exact
    ⟨separatorPhysical, hseparator, by
      cases hread : Tape.read (Description.tapeAt logical 1) with
      | none =>
          simpa
            [retargetedBranchingTape1ReadHeadCellAllExitsDescription,
              MachineDescription.offsetReadExitRetargetDescription,
              MachineDescription.retargetReadExitState,
              branchingTape1ReadHeadCellAndReturnToSeparatorTarget,
              branchingSeparatorReadHeadCellTarget,
              BranchingHeadCellReturn.targetForRead, hread] using hcopy
      | some bit =>
          cases bit with
          | false =>
              simpa
                [retargetedBranchingTape1ReadHeadCellAllExitsDescription,
                  MachineDescription.offsetReadExitRetargetDescription,
                  MachineDescription.retargetReadExitState,
                  branchingTape1ReadHeadCellAndReturnToSeparatorTarget,
                  branchingSeparatorReadHeadCellTarget,
                  BranchingHeadCellReturn.targetForRead, hread] using! hcopy
          | true =>
              simpa
                [retargetedBranchingTape1ReadHeadCellAllExitsDescription,
                  MachineDescription.offsetReadExitRetargetDescription,
                  MachineDescription.retargetReadExitState,
                  branchingTape1ReadHeadCellAndReturnToSeparatorTarget,
                  branchingSeparatorReadHeadCellTarget,
                  BranchingHeadCellReturn.targetForRead, hread] using! hcopy⟩

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

def retargetedBranchingTape2ReadHeadCellAllExitsDescription
    (offset : Nat) (target : Option Bool -> Nat) :
    MachineDescription :=
  MachineDescription.offsetReadExitRetargetDescription offset
    branchingTape2ReadHeadCellAndReturnToSeparatorTarget
    target
    branchingTape2ReadHeadCellAndReturnToSeparatorDescription

theorem
    retargetedBranchingTape2ReadHeadCellAllExitsDescription_subroutineReady
    {offset : Nat} {target : Option Bool -> Nat}
    (hbelow : forall cell : Option Bool, target cell < offset) :
    (retargetedBranchingTape2ReadHeadCellAllExitsDescription
      offset target).SubroutineReady :=
  MachineDescription.offsetReadExitRetargetDescription_subroutineReady
    hbelow
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
    retargetedBranchingTape2ReadHeadCellAllExitsDescription_runsFromGuardedBlockStart
    {offset : Nat} {target : Option Bool -> Nat}
    (hbelow : forall cell : Option Bool, target cell < offset)
    {logical : List (Tape Bool)}
    (hlength : logical.length = 3) :
    exists separatorPhysical : Tape Bool,
      AtExistingTapeSeparator (guardLogicalTapes logical) 2
        separatorPhysical ∧
        RunsFromStateTapeEquiv
          (retargetedBranchingTape2ReadHeadCellAllExitsDescription
            offset target)
          (retargetedBranchingTape2ReadHeadCellAllExitsDescription
            offset target).start
          (target (Tape.read (Description.tapeAt logical 2)))
          (encodedGuardedStructuredTapes logical)
          separatorPhysical := by
  rcases
      branchingTape2ReadHeadCellAndReturnToSeparatorDescription_runsFromGuardedBlockStart
        hlength with
    ⟨separatorPhysical, hseparator, hrun⟩
  have hcopy :=
    runsFromStateTapeEquiv_offsetReadExitRetargetDescription
      (offset := offset)
      (localTarget :=
        branchingTape2ReadHeadCellAndReturnToSeparatorTarget)
      (target := target)
      hbelow
      branchingTape2ReadHeadCellAndReturnToSeparatorDescription_transitionFreeAt
      (observed := Tape.read (Description.tapeAt logical 2))
      hrun
  exact
    ⟨separatorPhysical, hseparator, by
      cases hread : Tape.read (Description.tapeAt logical 2) with
      | none =>
          simpa
            [retargetedBranchingTape2ReadHeadCellAllExitsDescription,
              MachineDescription.offsetReadExitRetargetDescription,
              MachineDescription.retargetReadExitState,
              branchingTape2ReadHeadCellAndReturnToSeparatorTarget,
              branchingSeparatorReadHeadCellTarget,
              BranchingHeadCellReturn.targetForRead, hread] using hcopy
      | some bit =>
          cases bit with
          | false =>
              simpa
                [retargetedBranchingTape2ReadHeadCellAllExitsDescription,
                  MachineDescription.offsetReadExitRetargetDescription,
                  MachineDescription.retargetReadExitState,
                  branchingTape2ReadHeadCellAndReturnToSeparatorTarget,
                  branchingSeparatorReadHeadCellTarget,
                  BranchingHeadCellReturn.targetForRead, hread] using! hcopy
          | true =>
              simpa
                [retargetedBranchingTape2ReadHeadCellAllExitsDescription,
                  MachineDescription.offsetReadExitRetargetDescription,
                  MachineDescription.retargetReadExitState,
                  branchingTape2ReadHeadCellAndReturnToSeparatorTarget,
                  branchingSeparatorReadHeadCellTarget,
                  BranchingHeadCellReturn.targetForRead, hread] using! hcopy⟩

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

theorem SupportsReadWriteRows3.lookupFromReadTuple_lowersGuardedTransitionEquiv_withGuardSlackRefresh
    {D : Description} (hD : SupportsReadWriteRows3 D)
    {state : Nat} {reads : ReadTuple3} {t : Transition}
    (hlookup :
      lookupTransitionFromReadTuple3 D state reads = some t)
    {refresh : MachineDescription}
    (hrefresh : GuardSlackRefreshContract refresh) :
    LowersGuardedTransitionEquiv D t
      (readActionSlackRow3DescriptionOfRowWithGuardSlackRefresh
        t refresh) :=
  hD.row_lowersGuardedTransitionEquiv_withGuardSlackRefresh
    (lookupTransitionFromReadTuple3_mem hlookup) hrefresh

theorem SupportsReadWriteRows3.lookupFromReadTuple_lowersGuardedTransitionEquiv_withStructuredSingletonRefresh
    {D : Description} (hD : SupportsReadWriteRows3 D)
    {state : Nat} {reads : ReadTuple3} {t : Transition}
    (hlookup :
      lookupTransitionFromReadTuple3 D state reads = some t)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefreshContract refresh) :
    LowersGuardedTransitionEquiv D t
      (readActionSlackRow3DescriptionOfRowWithStructuredSingletonRefresh
        t refresh) :=
  hD.row_lowersGuardedTransitionEquiv_withStructuredSingletonRefresh
    (lookupTransitionFromReadTuple3_mem hlookup) hrefresh

theorem SupportsReadWriteRows3.lookupFromReadTuple_lowersGuardedTransitionEquiv_withStructuredSingleton3Refresh
    {D : Description} (hD : SupportsReadWriteRows3 D)
    {state : Nat} {reads : ReadTuple3} {t : Transition}
    (hlookup :
      lookupTransitionFromReadTuple3 D state reads = some t)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh) :
    LowersGuardedTransitionEquiv D t
      (readActionSlackRow3DescriptionOfRowWithStructuredSingletonRefresh
        t refresh) :=
  hD.row_lowersGuardedTransitionEquiv_withStructuredSingleton3Refresh
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

def tape0ReaderTargets (D : Description) (state : Nat) :
    Option Bool -> Nat :=
  fun read0 => tape0ReaderTarget D state read0

def tape1ReaderTargets (D : Description) (state : Nat)
    (read0 : Option Bool) : Option Bool -> Nat :=
  fun read1 => tape1ReaderTarget D state read0 read1

def tape2ReaderTargets (D : Description) (state : Nat)
    (read0 read1 : Option Bool) : Option Bool -> Nat :=
  fun read2 =>
    tape2ReaderTarget D state
      { read0 := read0, read1 := read1, read2 := read2 }

/--
Start of the copied tape-0 reader block in the eventual three-head reader
table.  All finite-control states below this offset are compact dispatcher
states ({name}`ready`, {name}`afterRead`, {name}`afterRead0`, and
{name}`afterRead1`).
-/
def tape0ReaderOffset (D : Description) : Nat :=
  readerStateLimit D

def tape0ReaderLimit (D : Description) : Nat :=
  tape0ReaderOffset D +
    branchingTape0ReadHeadCellAndReturnToSeparatorDescription.stateCount

def afterRead0JumpScratchBase (D : Description) : Nat :=
  tape0ReaderLimit D

def afterRead0JumpScratch (D : Description) (state : Nat)
    (read0 : Option Bool) : Nat :=
  afterRead0JumpScratchBase D + 3 * state + ReadTuple3.readCode read0

def afterRead0JumpLimit (D : Description) : Nat :=
  afterRead0JumpScratchBase D + 3 * D.stateCount

def tape1ReaderOffset (D : Description) : Nat :=
  afterRead0JumpLimit D

def tape1ReaderLimit (D : Description) : Nat :=
  tape1ReaderOffset D +
    branchingTape1ReadHeadCellAndReturnToSeparatorDescription.stateCount

def afterRead1JumpScratchBase (D : Description) : Nat :=
  tape1ReaderLimit D

def afterRead1JumpScratch (D : Description) (state : Nat)
    (read0 read1 : Option Bool) : Nat :=
  afterRead1JumpScratchBase D + 9 * state +
    ReadTuple3.code01 read0 read1

def afterRead1JumpLimit (D : Description) : Nat :=
  afterRead1JumpScratchBase D + 9 * D.stateCount

def tape2ReaderOffset (D : Description) : Nat :=
  afterRead1JumpLimit D

def tape2ReaderLimit (D : Description) : Nat :=
  tape2ReaderOffset D +
    branchingTape2ReadHeadCellAndReturnToSeparatorDescription.stateCount

def threeHeadReaderStateLimit (D : Description) : Nat :=
  tape2ReaderLimit D

def tape1ReaderStart (D : Description) (state : Nat)
    (read0 : Option Bool) : Nat :=
  (retargetedBranchingTape1ReadHeadCellAllExitsDescription
    (tape1ReaderOffset D) (tape1ReaderTargets D state read0)).start

def tape2ReaderStart (D : Description) (state : Nat)
    (read0 read1 : Option Bool) : Nat :=
  (retargetedBranchingTape2ReadHeadCellAllExitsDescription
    (tape2ReaderOffset D)
    (tape2ReaderTargets D state read0 read1)).start

def afterRead0JumpDescription (D : Description) (state : Nat)
    (read0 : Option Bool) : MachineDescription :=
  blankHeadBounceJumpDescription (threeHeadReaderStateLimit D)
    (afterRead0 D state read0)
    (afterRead0JumpScratch D state read0)
    (tape1ReaderStart D state read0)

def afterRead1JumpDescription (D : Description) (state : Nat)
    (read0 read1 : Option Bool) : MachineDescription :=
  blankHeadBounceJumpDescription (threeHeadReaderStateLimit D)
    (afterRead1 D state read0 read1)
    (afterRead1JumpScratch D state read0 read1)
    (tape2ReaderStart D state read0 read1)

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

theorem afterRead0Base_le_readerStateLimit
    (D : Description) :
    afterRead0Base D ≤ readerStateLimit D := by
  unfold readerStateLimit afterRead1Base
  lia

theorem afterRead1Base_le_readerStateLimit
    (D : Description) :
    afterRead1Base D ≤ readerStateLimit D := by
  unfold readerStateLimit
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

theorem tape0ReaderTargets_lt_readerStateLimit
    (D : Description) {state : Nat}
    (hstate : state < D.stateCount) :
    forall read0 : Option Bool,
      tape0ReaderTargets D state read0 < readerStateLimit D := by
  intro read0
  have htarget :=
    tape0ReaderTarget_lt_afterRead1Base D read0 hstate
  have hlimit := afterRead1Base_le_readerStateLimit D
  simpa [tape0ReaderTargets] using Nat.lt_of_lt_of_le htarget hlimit

theorem tape1ReaderTargets_lt_readerStateLimit
    (D : Description) {state : Nat} (read0 : Option Bool)
    (hstate : state < D.stateCount) :
    forall read1 : Option Bool,
      tape1ReaderTargets D state read0 read1 < readerStateLimit D := by
  intro read1
  simpa [tape1ReaderTargets] using
    tape1ReaderTarget_lt_readerStateLimit D read0 read1 hstate

theorem tape2ReaderTargets_lt_readerStateLimit
    (D : Description) {state : Nat}
    (read0 read1 : Option Bool)
    (hstate : state < D.stateCount) :
    forall read2 : Option Bool,
      tape2ReaderTargets D state read0 read1 read2 < readerStateLimit D := by
  intro read2
  have htarget :=
    tape2ReaderTarget_lt_afterRead0Base D
      ({ read0 := read0, read1 := read1, read2 := read2 } : ReadTuple3)
      hstate
  have hlimit := afterRead0Base_le_readerStateLimit D
  simpa [tape2ReaderTargets] using Nat.lt_of_lt_of_le htarget hlimit

theorem readerStateLimit_le_tape0ReaderOffset
    (D : Description) :
    readerStateLimit D ≤ tape0ReaderOffset D := by
  exact Nat.le_refl _

theorem readerStateLimit_le_tape1ReaderOffset
    (D : Description) :
    readerStateLimit D ≤ tape1ReaderOffset D := by
  unfold tape1ReaderOffset afterRead0JumpLimit
    afterRead0JumpScratchBase tape0ReaderLimit tape0ReaderOffset
  lia

theorem readerStateLimit_le_tape2ReaderOffset
    (D : Description) :
    readerStateLimit D ≤ tape2ReaderOffset D := by
  unfold tape2ReaderOffset afterRead1JumpLimit
    afterRead1JumpScratchBase tape1ReaderLimit tape1ReaderOffset
    afterRead0JumpLimit afterRead0JumpScratchBase tape0ReaderLimit
    tape0ReaderOffset
  lia

theorem tape0ReaderTargets_lt_tape0ReaderOffset
    (D : Description) {state : Nat}
    (hstate : state < D.stateCount) :
    forall read0 : Option Bool,
      tape0ReaderTargets D state read0 < tape0ReaderOffset D := by
  intro read0
  simpa [tape0ReaderOffset] using
    tape0ReaderTargets_lt_readerStateLimit D hstate read0

theorem tape1ReaderTargets_lt_tape1ReaderOffset
    (D : Description) {state : Nat} (read0 : Option Bool)
    (hstate : state < D.stateCount) :
    forall read1 : Option Bool,
      tape1ReaderTargets D state read0 read1 < tape1ReaderOffset D := by
  intro read1
  exact
    Nat.lt_of_lt_of_le
      (tape1ReaderTargets_lt_readerStateLimit D read0 hstate read1)
      (readerStateLimit_le_tape1ReaderOffset D)

theorem tape2ReaderTargets_lt_tape2ReaderOffset
    (D : Description) {state : Nat} (read0 read1 : Option Bool)
    (hstate : state < D.stateCount) :
    forall read2 : Option Bool,
      tape2ReaderTargets D state read0 read1 read2 < tape2ReaderOffset D := by
  intro read2
  exact
    Nat.lt_of_lt_of_le
      (tape2ReaderTargets_lt_readerStateLimit D read0 read1 hstate read2)
      (readerStateLimit_le_tape2ReaderOffset D)

theorem afterRead0JumpScratch_lt_afterRead0JumpLimit
    (D : Description) {state : Nat} (read0 : Option Bool)
    (hstate : state < D.stateCount) :
    afterRead0JumpScratch D state read0 <
      afterRead0JumpLimit D := by
  have hcode := ReadTuple3.readCode_lt_three read0
  unfold afterRead0JumpScratch afterRead0JumpLimit
  lia

theorem afterRead1JumpScratch_lt_afterRead1JumpLimit
    (D : Description) {state : Nat}
    (read0 read1 : Option Bool)
    (hstate : state < D.stateCount) :
    afterRead1JumpScratch D state read0 read1 <
      afterRead1JumpLimit D := by
  have hcode := ReadTuple3.code01_lt_nine read0 read1
  unfold afterRead1JumpScratch afterRead1JumpLimit
  lia

theorem afterRead0_lt_afterRead0JumpScratch
    (D : Description) {state : Nat} (read0 : Option Bool)
    (hstate : state < D.stateCount) :
    afterRead0 D state read0 <
      afterRead0JumpScratch D state read0 := by
  have hlow :=
    Nat.lt_of_lt_of_le
      (afterRead0_lt_afterRead1Base D read0 hstate)
      (afterRead1Base_le_readerStateLimit D)
  have hle :
      readerStateLimit D ≤
        afterRead0JumpScratch D state read0 := by
    unfold afterRead0JumpScratch afterRead0JumpScratchBase
      tape0ReaderLimit tape0ReaderOffset
    lia
  exact Nat.lt_of_lt_of_le hlow hle

theorem afterRead1_lt_afterRead1JumpScratch
    (D : Description) {state : Nat}
    (read0 read1 : Option Bool)
    (hstate : state < D.stateCount) :
    afterRead1 D state read0 read1 <
      afterRead1JumpScratch D state read0 read1 := by
  have hlow :=
    afterRead1_lt_readerStateLimit D read0 read1 hstate
  have hle :
      readerStateLimit D ≤
        afterRead1JumpScratch D state read0 read1 := by
    unfold afterRead1JumpScratch afterRead1JumpScratchBase
      tape1ReaderLimit tape1ReaderOffset afterRead0JumpLimit
      afterRead0JumpScratchBase tape0ReaderLimit tape0ReaderOffset
    lia
  exact Nat.lt_of_lt_of_le hlow hle

theorem afterRead0_ne_afterRead0JumpScratch
    (D : Description) {state : Nat} (read0 : Option Bool)
    (hstate : state < D.stateCount) :
    afterRead0 D state read0 ≠
      afterRead0JumpScratch D state read0 :=
  Nat.ne_of_lt (afterRead0_lt_afterRead0JumpScratch D read0 hstate)

theorem afterRead1_ne_afterRead1JumpScratch
    (D : Description) {state : Nat}
    (read0 read1 : Option Bool)
    (hstate : state < D.stateCount) :
    afterRead1 D state read0 read1 ≠
      afterRead1JumpScratch D state read0 read1 :=
  Nat.ne_of_lt
    (afterRead1_lt_afterRead1JumpScratch D read0 read1 hstate)

theorem afterRead0JumpDescription_runsFromBlankHead
    (D : Description) {state : Nat} (read0 : Option Bool)
    (hstate : state < D.stateCount)
    {physical : Tape Bool}
    (hread : Tape.read physical = none) :
    RunsFromStateTapeEquiv
      (afterRead0JumpDescription D state read0)
      (afterRead0 D state read0)
      (tape1ReaderStart D state read0)
      physical physical := by
  simpa [afterRead0JumpDescription] using
    blankHeadBounceJumpDescription_runsFromBlankHead
      (afterRead0_ne_afterRead0JumpScratch D read0 hstate)
      hread

theorem afterRead1JumpDescription_runsFromBlankHead
    (D : Description) {state : Nat}
    (read0 read1 : Option Bool)
    (hstate : state < D.stateCount)
    {physical : Tape Bool}
    (hread : Tape.read physical = none) :
    RunsFromStateTapeEquiv
      (afterRead1JumpDescription D state read0 read1)
      (afterRead1 D state read0 read1)
      (tape2ReaderStart D state read0 read1)
      physical physical := by
  simpa [afterRead1JumpDescription] using
    blankHeadBounceJumpDescription_runsFromBlankHead
      (afterRead1_ne_afterRead1JumpScratch D read0 read1 hstate)
      hread

theorem afterRead0JumpDescription_runsFromTapeSeparator
    (D : Description) {state : Nat} (read0 : Option Bool)
    (hstate : state < D.stateCount)
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    {physical : Tape Bool}
    (hseparator : AtTapeSeparator logical tapeIndex physical) :
    RunsFromStateTapeEquiv
      (afterRead0JumpDescription D state read0)
      (afterRead0 D state read0)
      (tape1ReaderStart D state read0)
      physical physical :=
  afterRead0JumpDescription_runsFromBlankHead
    D read0 hstate (atTapeSeparator_read hseparator)

theorem afterRead1JumpDescription_runsFromTapeSeparator
    (D : Description) {state : Nat}
    (read0 read1 : Option Bool)
    (hstate : state < D.stateCount)
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    {physical : Tape Bool}
    (hseparator : AtTapeSeparator logical tapeIndex physical) :
    RunsFromStateTapeEquiv
      (afterRead1JumpDescription D state read0 read1)
      (afterRead1 D state read0 read1)
      (tape2ReaderStart D state read0 read1)
      physical physical :=
  afterRead1JumpDescription_runsFromBlankHead
    D read0 read1 hstate (atTapeSeparator_read hseparator)

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

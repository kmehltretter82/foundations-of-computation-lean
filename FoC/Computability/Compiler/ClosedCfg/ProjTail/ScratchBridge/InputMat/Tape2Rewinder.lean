import FoC.Computability.Compiler.Structured.Lowering.ThreeTapeHelpers
import FoC.Computability.Compiler.Structured.Lowering.ThreeTapeTactic
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTableChecks
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.RightEdgeRewind
import FoC.Computability.Compiler.Structured.Lowering.ConcreteRefresh

set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

/-!
# Tape-2 preserving right-edge rewinder

Rewinds a completed visible word on logical tape 2 from its right boundary to
the first word cell, preserving arbitrary logical tapes 0 and 1 exactly.
-/

namespace FoC
namespace Computability

open Languages
open CommonGround.FiniteTransducers

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering
namespace ThreeTape
namespace CountWindowInputMat
namespace Tape2Rewinder

def enter : Nat := 0
def rewind : Nat := 1
def halt : Nat := 2

def rowsForTape2Read
    (source : Nat) (read2 : Option Bool)
    (action2 : TapeAction) (target : Nat) : List Transition :=
  allReads2 fun read0 read1 =>
    row source read0 read1 read2 keepS keepS action2 target

def rows : List Transition :=
  [ rowsForTape2Read enter none keepL rewind
  , rowsForTape2Read enter (some false) keepL rewind
  , rowsForTape2Read enter (some true) keepL rewind
  , rowsForTape2Read rewind (some false) keepL rewind
  , rowsForTape2Read rewind (some true) keepL rewind
  , rowsForTape2Read rewind none keepR halt ].flatten

def description : Description :=
  ThreeTape.description 3 enter halt rows

syntax "tape2_rewind_step " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| tape2_rewind_step [$lemmas,*]) =>
      `(tactic|
        three_tape_step [description, rows, rowsForTape2Read,
          allReads2, allReadCells, List.find?, enter, rewind, halt, $lemmas,*])

theorem description_subroutineReady : description.SubroutineReady :=
  structuredDescription_subroutineReady_of_bool description (by decide)

theorem description_supports : SupportsReadWriteRows3 description :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)

def sourceTape (bits : Word Bool) : Tape Bool :=
  rightEdgeRewindSourceTape bits []

def targetTape (bits : Word Bool) : Tape Bool :=
  rightEdgeScanSourceTapeFromLeft [none] bits []

def rewindTape
    (remainingRev : Word Bool) (current : Bool)
    (processed : Word Bool) : Tape Bool :=
  tapeAtCells (remainingRev.map some)
    (some current :: List.append (processed.map some) [none])

def doneTape (bits : Word Bool) : Tape Bool :=
  tapeAtCells []
    (none :: List.append (bits.map some) [none])

theorem enter_nil_step (T0 T1 : Tape Bool) :
    description.runConfig 1
        (config enter T0 T1 (sourceTape [])) =
      config rewind T0 T1 (doneTape []) := by
  cases h0 : T0.head with
  | none =>
      cases h1 : T1.head with
      | none =>
          tape2_rewind_step [sourceTape, doneTape,
            rightEdgeRewindSourceTape, tapeAtCells, h0, h1]
      | some b1 =>
          cases b1 <;>
            tape2_rewind_step [sourceTape, doneTape,
              rightEdgeRewindSourceTape, tapeAtCells, h0, h1]
  | some b0 =>
      cases b0 <;>
        cases h1 : T1.head with
        | none =>
            tape2_rewind_step [sourceTape, doneTape,
              rightEdgeRewindSourceTape, tapeAtCells, h0, h1]
        | some b1 =>
            cases b1 <;>
              tape2_rewind_step [sourceTape, doneTape,
                rightEdgeRewindSourceTape, tapeAtCells, h0, h1]
  done

theorem enter_cons_step
    (remainingRev : Word Bool) (current : Bool)
    (T0 T1 : Tape Bool) :
    description.runConfig 1
        (config enter T0 T1
          (sourceTape ((current :: remainingRev).reverse))) =
      config rewind T0 T1 (rewindTape remainingRev current []) := by
  cases h0 : T0.head with
  | none =>
      cases h1 : T1.head with
      | none =>
          cases current <;>
            tape2_rewind_step [sourceTape, rewindTape,
              rightEdgeRewindSourceTape, tapeAtCells, h0, h1]
      | some b1 =>
          cases b1 <;> cases current <;>
            tape2_rewind_step [sourceTape, rewindTape,
              rightEdgeRewindSourceTape, tapeAtCells, h0, h1]
  | some b0 =>
      cases b0 <;>
        cases h1 : T1.head with
        | none =>
            cases current <;>
              tape2_rewind_step [sourceTape, rewindTape,
                rightEdgeRewindSourceTape, tapeAtCells, h0, h1]
        | some b1 =>
            cases b1 <;> cases current <;>
              tape2_rewind_step [sourceTape, rewindTape,
                rightEdgeRewindSourceTape, tapeAtCells, h0, h1]
  done

theorem rewind_step
    (remainingRev processed : Word Bool) (current : Bool)
    (T0 T1 : Tape Bool) :
    description.runConfig 1
        (config rewind T0 T1
          (rewindTape remainingRev current processed)) =
      match remainingRev with
      | [] =>
          config rewind T0 T1 (doneTape (current :: processed))
      | next :: tail =>
          config rewind T0 T1
            (rewindTape tail next (current :: processed)) := by
  cases remainingRev with
  | nil =>
      cases h0 : T0.head with
      | none =>
          cases h1 : T1.head with
          | none =>
              cases current <;>
                tape2_rewind_step [rewindTape, doneTape,
                  tapeAtCells, h0, h1]
          | some b1 =>
              cases b1 <;> cases current <;>
                tape2_rewind_step [rewindTape, doneTape,
                  tapeAtCells, h0, h1]
      | some b0 =>
          cases b0 <;>
            cases h1 : T1.head with
            | none =>
                cases current <;>
                  tape2_rewind_step [rewindTape, doneTape,
                    tapeAtCells, h0, h1]
            | some b1 =>
                cases b1 <;> cases current <;>
                  tape2_rewind_step [rewindTape, doneTape,
                    tapeAtCells, h0, h1]
  | cons next tail =>
      cases h0 : T0.head with
      | none =>
          cases h1 : T1.head with
          | none =>
              cases current <;>
                tape2_rewind_step [rewindTape, doneTape,
                  tapeAtCells, h0, h1]
          | some b1 =>
              cases b1 <;> cases current <;>
                tape2_rewind_step [rewindTape, doneTape,
                  tapeAtCells, h0, h1]
      | some b0 =>
          cases b0 <;>
            cases h1 : T1.head with
            | none =>
                cases current <;>
                  tape2_rewind_step [rewindTape, doneTape,
                    tapeAtCells, h0, h1]
            | some b1 =>
                cases b1 <;> cases current <;>
                  tape2_rewind_step [rewindTape, doneTape,
                    tapeAtCells, h0, h1]
  done

theorem rewind_run
    (remainingRev processed : Word Bool) (current : Bool)
    (T0 T1 : Tape Bool) :
    description.runConfig (remainingRev.length + 1)
        (config rewind T0 T1
          (rewindTape remainingRev current processed)) =
      config rewind T0 T1
        (doneTape
          (List.append remainingRev.reverse (current :: processed))) := by
  induction remainingRev generalizing current processed with
  | nil =>
      simpa using rewind_step [] processed current T0 T1
  | cons next tail ih =>
      rw [show (next :: tail).length + 1 = 1 + (tail.length + 1) by
        simp [Nat.add_comm]]
      rw [Description.runConfig_add]
      rw [rewind_step]
      simp only
      rw [ih (current :: processed) next]
      simp [List.reverse_cons, List.append_assoc]
      done

theorem rewind_finish (bits : Word Bool) (T0 T1 : Tape Bool) :
    description.runConfig 1
        (config rewind T0 T1 (doneTape bits)) =
      config halt T0 T1 (targetTape bits) := by
  cases h0 : T0.head with
  | none =>
      cases h1 : T1.head with
      | none =>
          cases bits with
          | nil =>
              tape2_rewind_step [doneTape, targetTape,
                rightEdgeScanSourceTapeFromLeft, tapeAtCells, h0, h1]
          | cons bit rest =>
              cases bit <;>
                tape2_rewind_step [doneTape, targetTape,
                  rightEdgeScanSourceTapeFromLeft, tapeAtCells, h0, h1]
      | some b1 =>
          cases b1 <;>
            cases bits with
            | nil =>
                tape2_rewind_step [doneTape, targetTape,
                  rightEdgeScanSourceTapeFromLeft, tapeAtCells, h0, h1]
            | cons bit rest =>
                cases bit <;>
                  tape2_rewind_step [doneTape, targetTape,
                    rightEdgeScanSourceTapeFromLeft, tapeAtCells, h0, h1]
  | some b0 =>
      cases b0 <;>
        cases h1 : T1.head with
        | none =>
            cases bits with
            | nil =>
                tape2_rewind_step [doneTape, targetTape,
                  rightEdgeScanSourceTapeFromLeft, tapeAtCells, h0, h1]
            | cons bit rest =>
                cases bit <;>
                  tape2_rewind_step [doneTape, targetTape,
                    rightEdgeScanSourceTapeFromLeft, tapeAtCells, h0, h1]
        | some b1 =>
            cases b1 <;>
              cases bits with
              | nil =>
                  tape2_rewind_step [doneTape, targetTape,
                    rightEdgeScanSourceTapeFromLeft, tapeAtCells, h0, h1]
              | cons bit rest =>
                  cases bit <;>
                    tape2_rewind_step [doneTape, targetTape,
                      rightEdgeScanSourceTapeFromLeft, tapeAtCells, h0, h1]
  done

def fullFuel (bits : Word Bool) : Nat :=
  bits.length + 2

theorem full_run (bits : Word Bool) (T0 T1 : Tape Bool) :
    description.runConfig (fullFuel bits)
        (config enter T0 T1 (sourceTape bits)) =
      config halt T0 T1 (targetTape bits) := by
  rw [fullFuel]
  cases hrev : bits.reverse with
  | nil =>
      have hbits : bits = [] := by
        apply List.eq_nil_of_length_eq_zero
        have hlength := congrArg List.length hrev
        simpa using hlength
      subst bits
      rw [show [].length + 2 = 1 + 1 by rfl]
      rw [Description.runConfig_add]
      rw [enter_nil_step]
      exact rewind_finish [] T0 T1
      done
  | cons current remainingRev =>
      have hbits : (current :: remainingRev).reverse = bits := by
        rw [← hrev]
        simp
      have hlen : bits.length = remainingRev.length + 1 := by
        have hlength := congrArg List.length hrev
        simpa using hlength
      rw [show bits.length + 2 =
          1 + ((remainingRev.length + 1) + 1) by lia]
      rw [Description.runConfig_add]
      rw [← hbits]
      rw [enter_cons_step]
      rw [Description.runConfig_add]
      rw [rewind_run]
      rw [show List.append remainingRev.reverse [current] =
          (current :: remainingRev).reverse by simp]
      exact rewind_finish (current :: remainingRev).reverse T0 T1
      done

def loweredDescription : MachineDescription :=
  lowerStructured3Description description

theorem loweredDescription_subroutineReady :
    loweredDescription.SubroutineReady := by
  simpa [loweredDescription] using
    lowerStructured3Description_subroutineReady
      description_subroutineReady.left description_supports

theorem loweredDescription_realizes
    (bits : Word Bool) (T0 T1 : Tape Bool) :
    loweredDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes T0 T1 (sourceTape bits))
      (encodedGuardedStructured3Tapes T0 T1 (targetTape bits)) := by
  simpa [loweredDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      description_subroutineReady.left description_subroutineReady.right
      description_supports
      (c := config enter T0 T1 (sourceTape bits))
      (tapes := [T0, T1, targetTape bits])
      rfl rfl ⟨fullFuel bits, full_run bits T0 T1⟩

end Tape2Rewinder
end CountWindowInputMat
end ThreeTape
end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC

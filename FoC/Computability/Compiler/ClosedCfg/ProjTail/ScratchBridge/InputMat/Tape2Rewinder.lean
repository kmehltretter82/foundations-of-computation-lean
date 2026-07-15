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


def sourceTapeWithContext
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    (rightPadding : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append (bits.reverse.map some) (none :: baseLeft))
    (none :: rightPadding)

def targetTapeWithContext
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    (rightPadding : List (Option Bool)) : Tape Bool :=
  tapeAtCells (none :: baseLeft)
    (List.append (bits.map some) (none :: rightPadding))

def rewindTapeWithContext
    (baseLeft : List (Option Bool))
    (remainingRev : Word Bool) (current : Bool)
    (processed : Word Bool)
    (rightPadding : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append (remainingRev.map some) (none :: baseLeft))
    (some current ::
      List.append (processed.map some) (none :: rightPadding))


theorem enter_withContext_step
    (baseLeft : List (Option Bool))
    (remainingRev : Word Bool) (current : Bool)
    (rightPadding : List (Option Bool))
    (T0 T1 : Tape Bool) :
    description.runConfig 1
        (config enter T0 T1
          (tapeAtCells
            (some current ::
              (remainingRev.map some ++ none :: baseLeft))
            (none :: rightPadding))) =
      config rewind T0 T1
        (rewindTapeWithContext baseLeft remainingRev current []
          rightPadding) := by
  cases h0 : T0.head with
  | none =>
      cases h1 : T1.head with
      | none =>
          cases current <;>
            tape2_rewind_step [rewindTapeWithContext,
              tapeAtCells, h0, h1]
      | some bit =>
          cases bit <;> cases current <;>
            tape2_rewind_step [rewindTapeWithContext,
              tapeAtCells, h0, h1]
  | some bit0 =>
      cases bit0 <;>
        cases h1 : T1.head with
        | none =>
            cases current <;>
              tape2_rewind_step [rewindTapeWithContext,
                tapeAtCells, h0, h1]
        | some bit1 =>
            cases bit1 <;> cases current <;>
              tape2_rewind_step [rewindTapeWithContext,
                tapeAtCells, h0, h1]
  done


theorem rewind_withContext_step
    (baseLeft : List (Option Bool))
    (remainingRev processed : Word Bool) (current : Bool)
    (rightPadding : List (Option Bool))
    (T0 T1 : Tape Bool) :
    description.runConfig 1
        (config rewind T0 T1
          (rewindTapeWithContext baseLeft remainingRev current processed
            rightPadding)) =
      match remainingRev with
      | [] =>
          config rewind T0 T1
            (tapeAtCells baseLeft
              (none :: some current ::
                List.append (processed.map some)
                  (none :: rightPadding)))
      | next :: rest =>
          config rewind T0 T1
            (rewindTapeWithContext baseLeft rest next
              (current :: processed) rightPadding) := by
  cases remainingRev with
  | nil =>
      cases h0 : T0.head with
      | none =>
          cases h1 : T1.head with
          | none =>
              cases current <;>
                tape2_rewind_step [rewindTapeWithContext,
                  tapeAtCells, h0, h1]
          | some bit =>
              cases bit <;> cases current <;>
                tape2_rewind_step [rewindTapeWithContext,
                  tapeAtCells, h0, h1]
      | some bit0 =>
          cases bit0 <;>
            cases h1 : T1.head with
            | none =>
                cases current <;>
                  tape2_rewind_step [rewindTapeWithContext,
                    tapeAtCells, h0, h1]
            | some bit1 =>
                cases bit1 <;> cases current <;>
                  tape2_rewind_step [rewindTapeWithContext,
                    tapeAtCells, h0, h1]
  | cons next rest =>
      cases h0 : T0.head with
      | none =>
          cases h1 : T1.head with
          | none =>
              cases current <;> cases next <;>
                tape2_rewind_step [rewindTapeWithContext,
                  tapeAtCells, h0, h1]
          | some bit =>
              cases bit <;> cases current <;> cases next <;>
                tape2_rewind_step [rewindTapeWithContext,
                  tapeAtCells, h0, h1]
      | some bit0 =>
          cases bit0 <;>
            cases h1 : T1.head with
            | none =>
                cases current <;> cases next <;>
                  tape2_rewind_step [rewindTapeWithContext,
                    tapeAtCells, h0, h1]
            | some bit1 =>
                cases bit1 <;> cases current <;> cases next <;>
                  tape2_rewind_step [rewindTapeWithContext,
                    tapeAtCells, h0, h1]
  done


theorem rewind_withContext_run
    (baseLeft : List (Option Bool))
    (remainingRev processed : Word Bool) (current : Bool)
    (rightPadding : List (Option Bool))
    (T0 T1 : Tape Bool) :
    description.runConfig (remainingRev.length + 1)
        (config rewind T0 T1
          (rewindTapeWithContext baseLeft remainingRev current processed
            rightPadding)) =
      config rewind T0 T1
        (tapeAtCells baseLeft
          (none :: List.append
            ((List.append remainingRev.reverse
              (current :: processed)).map some)
            (none :: rightPadding))) := by
  induction remainingRev generalizing current processed with
  | nil =>
      simpa [List.append_assoc] using
        rewind_withContext_step baseLeft [] processed current
          rightPadding T0 T1
  | cons next rest ih =>
      rw [show (next :: rest).length + 1 = 1 + (rest.length + 1) by
        simp
        lia]
      rw [Description.runConfig_add]
      rw [rewind_withContext_step]
      rw [ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]
      done


theorem rewind_withContext_finish
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    (rightPadding : List (Option Bool))
    (T0 T1 : Tape Bool) :
    description.runConfig 1
        (config rewind T0 T1
          (tapeAtCells baseLeft
            (none :: List.append (bits.map some)
              (none :: rightPadding)))) =
      config halt T0 T1
        (targetTapeWithContext baseLeft bits rightPadding) := by
  cases h0 : T0.head with
  | none =>
      cases h1 : T1.head with
      | none =>
          cases bits <;>
            tape2_rewind_step [targetTapeWithContext,
              tapeAtCells, h0, h1]
      | some bit =>
          cases bit <;> cases bits <;>
            tape2_rewind_step [targetTapeWithContext,
              tapeAtCells, h0, h1]
  | some bit0 =>
      cases bit0 <;>
        cases h1 : T1.head with
        | none =>
            cases bits <;>
              tape2_rewind_step [targetTapeWithContext,
                tapeAtCells, h0, h1]
        | some bit1 =>
            cases bit1 <;> cases bits <;>
              tape2_rewind_step [targetTapeWithContext,
                tapeAtCells, h0, h1]
  done

def fullFuel (bits : Word Bool) : Nat :=
  bits.length + 2


theorem description_run_withContext
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    (rightPadding : List (Option Bool))
    (T0 T1 : Tape Bool) :
    description.runConfig (fullFuel bits)
        (config enter T0 T1
          (sourceTapeWithContext baseLeft bits rightPadding)) =
      config halt T0 T1
        (targetTapeWithContext baseLeft bits rightPadding) := by
  cases hrev : bits.reverse with
  | nil =>
      have hbits : bits = [] := by
        apply List.eq_nil_of_length_eq_zero
        have hlength := congrArg List.length hrev
        simpa using hlength
      subst bits
      rw [show fullFuel [] = 1 + 1 by rfl]
      rw [Description.runConfig_add]
      change description.runConfig 1
        (description.runConfig 1
          (config enter T0 T1
            (tapeAtCells (none :: baseLeft)
              (none :: rightPadding)))) = _
      have henter :
          description.runConfig 1
              (config enter T0 T1
                (tapeAtCells (none :: baseLeft)
                  (none :: rightPadding))) =
            config rewind T0 T1
              (tapeAtCells baseLeft
                (none :: none :: rightPadding)) := by
        cases h0 : T0.head with
        | none =>
            cases h1 : T1.head with
            | none =>
                tape2_rewind_step [tapeAtCells, h0, h1]
            | some bit =>
                cases bit <;>
                  tape2_rewind_step [tapeAtCells, h0, h1]
        | some bit0 =>
            cases bit0 <;>
              cases h1 : T1.head with
              | none =>
                  tape2_rewind_step [tapeAtCells, h0, h1]
              | some bit1 =>
                  cases bit1 <;>
                    tape2_rewind_step [tapeAtCells, h0, h1]
      rw [henter]
      simpa using
        rewind_withContext_finish baseLeft [] rightPadding T0 T1
      done
  | cons current remainingRev =>
      have hbits : (current :: remainingRev).reverse = bits := by
        rw [← hrev]
        simp
      have hlen : bits.length = remainingRev.length + 1 := by
        have hlength := congrArg List.length hrev
        simpa using hlength
      rw [fullFuel]
      rw [show bits.length + 2 =
          1 + ((remainingRev.length + 1) + 1) by lia]
      rw [Description.runConfig_add]
      simp only [sourceTapeWithContext, hrev, List.map_cons,
        List.append_eq, List.cons_append]
      rw [enter_withContext_step]
      rw [Description.runConfig_add]
      rw [rewind_withContext_run]
      rw [show List.append remainingRev.reverse [current] = bits by
        simpa using hbits]
      exact rewind_withContext_finish baseLeft bits rightPadding T0 T1
      done

def loweredDescription : MachineDescription :=
  lowerStructured3Description description

theorem loweredDescription_subroutineReady :
    loweredDescription.SubroutineReady := by
  simpa [loweredDescription] using
    lowerStructured3Description_subroutineReady
      description_subroutineReady.left description_supports


theorem loweredDescription_realizes_withContext
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    (rightPadding : List (Option Bool))
    (T0 T1 : Tape Bool) :
    loweredDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes T0 T1
        (sourceTapeWithContext baseLeft bits rightPadding))
      (encodedGuardedStructured3Tapes T0 T1
        (targetTapeWithContext baseLeft bits rightPadding)) := by
  simpa [loweredDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      description_subroutineReady.left description_subroutineReady.right
      description_supports
      (c := config enter T0 T1
        (sourceTapeWithContext baseLeft bits rightPadding))
      (tapes :=
        [T0, T1, targetTapeWithContext baseLeft bits rightPadding])
      rfl rfl
      ⟨fullFuel bits,
        description_run_withContext baseLeft bits rightPadding T0 T1⟩
  done

end Tape2Rewinder
end CountWindowInputMat
end ThreeTape
end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC

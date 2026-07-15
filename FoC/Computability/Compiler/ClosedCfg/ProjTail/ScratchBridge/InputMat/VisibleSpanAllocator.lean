import FoC.Computability.Compiler.Structured.Lowering.ThreeTapeHelpers
import FoC.Computability.Compiler.Structured.Lowering.ThreeTapeTactic
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTableChecks
import FoC.Computability.Compiler.Structured.Lowering.ConcreteRefresh

set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

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
namespace VisibleSpanAllocator

def scan : Nat := 0
def rewind : Nat := 1
def halt : Nat := 2

def rowsForCounterRead
    (source : Nat) (counterRead : Option Bool)
    (action0 action1 action2 : TapeAction)
    (target : Nat) : List Transition :=
  allReads2
    (fun read0 read1 =>
      row source read0 read1 counterRead action0 action1 action2 target)

def rows : List Transition :=
  [ rowsForCounterRead scan (some false) keepR keepS keepR scan
  , rowsForCounterRead scan (some true) keepR keepS keepR scan
  , rowsForCounterRead scan none keepS keepS keepL rewind
  , rowsForCounterRead rewind (some false) keepL keepS keepL rewind
  , rowsForCounterRead rewind (some true) keepL keepS keepL rewind
  , rowsForCounterRead rewind none keepS keepS keepR halt ].flatten

def description : Description :=
  ThreeTape.description 3 scan halt rows

syntax "repeater_step " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| repeater_step [$lemmas,*]) =>
      `(tactic|
        three_tape_step [description, rows, rowsForCounterRead,
          allReads2, allReadCells, List.find?, scan, rewind, halt, $lemmas,*])

theorem description_subroutineReady : description.SubroutineReady :=
  structuredDescription_subroutineReady_of_bool description (by decide)

theorem description_supports : SupportsReadWriteRows3 description :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)

def sourceTape (baseLeft : List (Option Bool)) : Tape Bool :=
  tapeAtCells baseLeft [none]

def targetTape
    (baseLeft : List (Option Bool)) (count : Nat) : Tape Bool :=
  tapeAtCells baseLeft
    (none :: List.replicate count (none : Option Bool))

def counterTape (bits : Word Bool) : Tape Bool :=
  tapeAtCells [none]
    (List.append (bits.map some) [none])

def scanDataTape
    (baseLeft : List (Option Bool)) (processed : Word Bool) : Tape Bool :=
  tapeAtCells
    (List.append
      (List.replicate processed.length (none : Option Bool)) baseLeft)
    [none]

def scanCounterTape
    (processed remaining : Word Bool) : Tape Bool :=
  tapeAtCells
    (List.append (processed.reverse.map some) [none])
    (List.append (remaining.map some) [none])

theorem scan_step
    (baseLeft : List (Option Bool)) (processed rest : Word Bool)
    (bit : Bool) (middle : Tape Bool) :
    description.runConfig 1
        (config scan (scanDataTape baseLeft processed) middle
          (scanCounterTape processed (bit :: rest))) =
      config scan (scanDataTape baseLeft (List.append processed [bit])) middle
        (scanCounterTape (List.append processed [bit]) rest) := by
  cases hm : middle.head with
  | none =>
      cases bit <;> cases processed <;> cases rest <;>
        repeater_step [scanDataTape, scanCounterTape, List.replicate_succ,
          List.reverse_append, List.map_append, List.append_assoc,
          tapeAtCells, hm]
  | some mid =>
      cases mid <;> cases bit <;> cases processed <;> cases rest <;>
        repeater_step [scanDataTape, scanCounterTape, List.replicate_succ,
          List.reverse_append, List.map_append, List.append_assoc,
          tapeAtCells, hm]

theorem scan_run
    (baseLeft : List (Option Bool)) (processed remaining : Word Bool)
    (middle : Tape Bool) :
    description.runConfig remaining.length
        (config scan (scanDataTape baseLeft processed) middle
          (scanCounterTape processed remaining)) =
      config scan
        (scanDataTape baseLeft (List.append processed remaining)) middle
        (scanCounterTape (List.append processed remaining) []) := by
  induction remaining generalizing processed with
  | nil =>
      simp [Description.runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        lia]
      rw [Description.runConfig_add]
      rw [scan_step]
      rw [ih (List.append processed [bit])]
      simp [List.append_assoc]

theorem scan_finish
    (baseLeft : List (Option Bool)) (processed : Word Bool)
    (middle : Tape Bool) :
    description.runConfig 1
        (config scan (scanDataTape baseLeft processed) middle
          (scanCounterTape processed [])) =
      config rewind (scanDataTape baseLeft processed) middle
        (Tape.move Direction.left (scanCounterTape processed [])) := by
  cases hm : middle.head with
  | none =>
      repeater_step [scanDataTape, scanCounterTape, tapeAtCells, hm]
  | some mid =>
      cases mid <;>
        repeater_step [scanDataTape, scanCounterTape, tapeAtCells, hm]

def rewindDataTape
    (baseLeft : List (Option Bool)) (remaining restored : Nat) : Tape Bool :=
  tapeAtCells
    (List.append
      (List.replicate remaining (none : Option Bool)) baseLeft)
    (none :: List.replicate restored (none : Option Bool))

def rewindCounterTape
    (remainingRev : Word Bool) (current : Bool)
    (processed : Word Bool) : Tape Bool :=
  tapeAtCells
    (List.append (remainingRev.map some) [none])
    (some current ::
      List.append (processed.map some) [none])

def doneCounterTape (processed : Word Bool) : Tape Bool :=
  tapeAtCells []
    (none :: List.append (processed.map some) [none])

theorem scan_to_rewind_shape
    (baseLeft : List (Option Bool)) (bits : Word Bool) :
    scanDataTape baseLeft bits =
      rewindDataTape baseLeft bits.length 0 := by
  simp [scanDataTape, rewindDataTape]

theorem counter_scan_to_rewind_shape
    (current : Bool) (remainingRev : Word Bool) :
    Tape.move Direction.left
        (scanCounterTape (current :: remainingRev).reverse []) =
      rewindCounterTape remainingRev current [] := by
  simp [scanCounterTape, rewindCounterTape, tapeAtCells,
    Tape.move, Tape.moveLeft, List.map_append, List.append_assoc]

theorem counter_scan_to_done_shape :
    Tape.move Direction.left (scanCounterTape [] []) =
      doneCounterTape [] := by
  simp [scanCounterTape, doneCounterTape, tapeAtCells,
    Tape.move, Tape.moveLeft]

theorem rewind_step
    (baseLeft : List (Option Bool)) (remainingRev processed : Word Bool)
    (current : Bool) (middle : Tape Bool) :
    description.runConfig 1
        (config rewind
          (rewindDataTape baseLeft (remainingRev.length + 1)
            processed.length)
          middle (rewindCounterTape remainingRev current processed)) =
      match remainingRev with
      | [] =>
          config rewind
            (rewindDataTape baseLeft 0 (processed.length + 1)) middle
            (doneCounterTape (current :: processed))
      | next :: tail =>
          config rewind
            (rewindDataTape baseLeft (tail.length + 1)
              (processed.length + 1))
            middle (rewindCounterTape tail next (current :: processed)) := by
  cases remainingRev with
  | nil =>
      cases hm : middle.head with
      | none =>
          cases current <;> cases processed <;>
            repeater_step [rewindDataTape, rewindCounterTape, doneCounterTape,
              List.replicate_succ, List.append_assoc, tapeAtCells, hm]
      | some mid =>
          cases mid <;> cases current <;> cases processed <;>
            repeater_step [rewindDataTape, rewindCounterTape, doneCounterTape,
              List.replicate_succ, List.append_assoc, tapeAtCells, hm]
  | cons next tail =>
      cases hm : middle.head with
      | none =>
          cases current <;> cases next <;> cases tail <;> cases processed <;>
            repeater_step [rewindDataTape, rewindCounterTape, doneCounterTape,
              List.replicate_succ, List.append_assoc, tapeAtCells, hm]
      | some mid =>
          cases mid <;> cases current <;> cases next <;> cases tail <;>
            cases processed <;>
              repeater_step [rewindDataTape, rewindCounterTape, doneCounterTape,
                List.replicate_succ, List.append_assoc, tapeAtCells, hm]

theorem rewind_run
    (baseLeft : List (Option Bool)) (remainingRev processed : Word Bool)
    (current : Bool) (middle : Tape Bool) :
    description.runConfig (remainingRev.length + 1)
        (config rewind
          (rewindDataTape baseLeft (remainingRev.length + 1)
            processed.length)
          middle (rewindCounterTape remainingRev current processed)) =
      config rewind
        (rewindDataTape baseLeft 0
          (processed.length + remainingRev.length + 1))
        middle
        (doneCounterTape
          (List.append remainingRev.reverse (current :: processed))) := by
  induction remainingRev generalizing current processed with
  | nil =>
      simpa [rewindDataTape] using
        rewind_step baseLeft [] processed current middle
  | cons next tail ih =>
      rw [show (next :: tail).length + 1 = 1 + (tail.length + 1) by
        simp
        lia]
      rw [Description.runConfig_add]
      have hcount : 1 + (tail.length + 1) = (next :: tail).length + 1 := by
        simp
        lia
      rw [hcount]
      rw [rewind_step]
      simp only [List.length_cons]
      have hprocessed : processed.length + 1 = (current :: processed).length := by
        simp
      rw [hprocessed]
      rw [ih (current :: processed) next]
      simp [List.reverse_cons, List.append_assoc]
      rw [show processed.length + 1 + tail.length + 1 =
          processed.length + (tail.length + 1) + 1 by lia]

theorem rewind_finish
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    (middle : Tape Bool) :
    description.runConfig 1
        (config rewind (rewindDataTape baseLeft 0 bits.length) middle
          (doneCounterTape bits)) =
      config halt (targetTape baseLeft bits.length) middle
        (counterTape bits) := by
  cases hm : middle.head with
  | none =>
      cases bits <;>
        repeater_step [rewindDataTape, doneCounterTape, targetTape,
          counterTape, List.append_assoc, tapeAtCells, hm]
  | some mid =>
      cases mid <;> cases bits <;>
        repeater_step [rewindDataTape, doneCounterTape, targetTape,
          counterTape, List.append_assoc, tapeAtCells, hm]

def fullFuel (bits : Word Bool) : Nat :=
  bits.length + 1 + bits.length + 1

theorem full_run
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    (middle : Tape Bool) :
    description.runConfig (fullFuel bits)
        (config scan (sourceTape baseLeft) middle (counterTape bits)) =
      config halt (targetTape baseLeft bits.length) middle
        (counterTape bits) := by
  rw [fullFuel]
  rw [show bits.length + 1 + bits.length + 1 =
      bits.length + (1 + (bits.length + 1)) by lia]
  rw [Description.runConfig_add]
  change
    description.runConfig (1 + (bits.length + 1))
      (description.runConfig bits.length
        (config scan (scanDataTape baseLeft []) middle
          (scanCounterTape [] bits))) = _
  rw [scan_run]
  rw [Description.runConfig_add]
  rw [scan_finish]
  cases hrev : bits.reverse with
  | nil =>
      have hbits : bits = [] := by
        apply List.eq_nil_of_length_eq_zero
        have := congrArg List.length hrev
        simpa using this
      subst bits
      rw [scan_to_rewind_shape]
      change
        description.runConfig 1
          (config rewind (rewindDataTape baseLeft 0 0) middle
            (Tape.move Direction.left (scanCounterTape [] []))) = _
      rw [counter_scan_to_done_shape]
      exact rewind_finish baseLeft [] middle
  | cons current remainingRev =>
      have hbits : (current :: remainingRev).reverse = bits := by
        rw [← hrev]
        simp
      have hlen : bits.length = remainingRev.length + 1 := by
        have := congrArg List.length hrev
        simpa using this
      rw [scan_to_rewind_shape]
      change
        description.runConfig (bits.length + 1)
          (config rewind (rewindDataTape baseLeft bits.length 0) middle
            (Tape.move Direction.left (scanCounterTape bits []))) = _
      have hcounter :
          Tape.move Direction.left (scanCounterTape bits []) =
            rewindCounterTape remainingRev current [] := by
        rw [← hbits]
        exact counter_scan_to_rewind_shape current remainingRev
      rw [hcounter, hlen]
      rw [Description.runConfig_add]
      have hrewind :=
        rewind_run baseLeft remainingRev ([] : Word Bool) current middle
      simp only [List.length_nil, Nat.zero_add] at hrewind
      rw [hrewind]
      have hdone : List.append remainingRev.reverse [current] = bits := by
        simpa using hbits
      rw [hdone, ← hlen]
      exact rewind_finish baseLeft bits middle

def loweredDescription : MachineDescription :=
  lowerStructured3Description description

theorem loweredDescription_subroutineReady :
    loweredDescription.SubroutineReady := by
  simpa [loweredDescription] using
    lowerStructured3Description_subroutineReady
      description_subroutineReady.left description_supports

theorem loweredDescription_realizes
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    (middle : Tape Bool) :
    loweredDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (sourceTape baseLeft) middle (counterTape bits))
      (encodedGuardedStructured3Tapes
        (targetTape baseLeft bits.length) middle (counterTape bits)) := by
  simpa [loweredDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      description_subroutineReady.left description_subroutineReady.right
      description_supports
      (c := config scan (sourceTape baseLeft) middle (counterTape bits))
      (tapes :=
        [ targetTape baseLeft bits.length, middle, counterTape bits ])
      rfl rfl ⟨fullFuel bits, full_run baseLeft bits middle⟩

end VisibleSpanAllocator
end CountWindowInputMat
end ThreeTape
end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC

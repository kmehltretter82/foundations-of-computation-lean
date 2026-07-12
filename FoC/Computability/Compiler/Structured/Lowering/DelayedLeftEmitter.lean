import FoC.Computability.Compiler.Structured.Lowering.ThreeTapeHelpers

set_option doc.verso true

/-!
# Delayed leftward emission

Shared tape algebra for structured machines that emit a word backwards with a
one-bit hold. Each event writes the previous hold while moving left; the final
flush writes the last hold in place. This avoids a trailing blank to the left
of the exact output word.
-/

namespace FoC
namespace Computability

open Languages

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering
namespace ThreeTape

/-- Tape contents after streaming a prefix, excluding its held final bit. -/
def delayedLeftEmissionTape (bits : List Bool) : Tape Bool where
  left := []
  head := none
  right := (bits.dropLast.reverse).map some

/-- Write the previous hold and move left, or stay for the first bit. -/
def delayedLeftEmitAction : Option Bool -> TapeAction
  | none => keepS
  | some bit => writeBitL bit

/-- Write the final held bit without moving. -/
def delayedLeftFlushAction : Option Bool -> TapeAction
  | none => keepS
  | some bit => writeS (some bit)

@[simp] theorem delayedLeftEmissionTape_nil :
    delayedLeftEmissionTape [] = Tape.blank := rfl

theorem delayedLeftEmissionTape_read (bits : List Bool) :
    Tape.read (delayedLeftEmissionTape bits) = none := rfl

/-- One delayed emission event extends the abstract streamed prefix. -/
theorem delayedLeftEmitAction_apply
    {bits : List Bool} {hold : Option Bool}
    (hhold : hold = bits.getLast?) (bit : Bool) :
    (delayedLeftEmitAction hold).apply (delayedLeftEmissionTape bits) =
      delayedLeftEmissionTape (List.append bits [bit]) := by
  cases hlast : bits.getLast? with
  | none =>
      have hbits : bits = [] := List.getLast?_eq_none_iff.mp hlast
      subst bits
      simp at hhold
      subst hold
      rfl
  | some last =>
      rcases List.getLast?_eq_some_iff.mp hlast with ⟨front, rfl⟩
      have hhold' : hold = some last := by simpa using hhold
      rw [hhold']
      show
        Tape.moveLeft
            (Tape.write (some last)
              (delayedLeftEmissionTape (front ++ [last]))) =
          delayedLeftEmissionTape ((front ++ [last]) ++ [bit])
      simp [delayedLeftEmissionTape, Tape.write, Tape.moveLeft]

/-- Flushing turns the delayed representation into the exact reversed word. -/
theorem delayedLeftFlushAction_apply
    {bits : List Bool} {hold : Option Bool}
    (hhold : hold = bits.getLast?) :
    (delayedLeftFlushAction hold).apply (delayedLeftEmissionTape bits) =
      Tape.input bits.reverse := by
  cases hlast : bits.getLast? with
  | none =>
      have hbits : bits = [] := List.getLast?_eq_none_iff.mp hlast
      subst bits
      simp at hhold
      subst hold
      rfl
  | some last =>
      rcases List.getLast?_eq_some_iff.mp hlast with ⟨front, rfl⟩
      have hhold' : hold = some last := by simpa using hhold
      rw [hhold']
      show
        Tape.write (some last)
            (delayedLeftEmissionTape (front ++ [last])) =
          Tape.input (front ++ [last]).reverse
      cases hrev : front.reverse with
      | nil =>
          have hfront : front = [] := by
            simpa using congrArg List.reverse hrev
          subst front
          rfl
      | cons bit rest =>
          simp [delayedLeftEmissionTape, Tape.write, Tape.input, hrev]

end ThreeTape
end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC

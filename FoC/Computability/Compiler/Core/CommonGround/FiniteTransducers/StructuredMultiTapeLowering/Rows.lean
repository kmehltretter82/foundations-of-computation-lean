import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.CursorBasic

set_option doc.verso true

/-!
# Structured row lowerings
-/

namespace FoC
namespace Computability

open Languages

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

/-!
## Concrete row machines
-/

/--
Concrete row machine for a three-tape row whose actions are all
{name}`TapeAction.stay`.

The row read tuple is handled by the {name}`LowersTransition` precondition:
this machine is only used after structured lookup has already established that
the row is the active row.  Therefore the physical implementation is the
zero-step no-op machine.
-/
def stayRow3Description (_t : Transition) : MachineDescription :=
  cursorNoopDescription

private theorem list_eq_three_of_length_eq_three
    {α : Type u} {xs : List α}
    (h : xs.length = 3) :
    exists a : α, exists b : α, exists c : α,
      xs = [a, b, c] := by
  cases xs with
  | nil =>
      simp at h
  | cons a rest =>
      cases rest with
      | nil =>
          simp at h
      | cons b rest =>
          cases rest with
          | nil =>
              simp at h
          | cons c rest =>
              cases rest with
              | nil =>
                  exact ⟨a, b, c, rfl⟩
              | cons _d _rest =>
                  simp at h

theorem applyActions_three_stay
    (D : Description) (hD : D.tapeCount = 3)
    (T U V : Tape Bool) :
    D.applyActions
        [TapeAction.stay, TapeAction.stay, TapeAction.stay]
        [T, U, V] =
      [T, U, V] := by
  rw [Description.applyActions_three D hD]
  simp [TapeAction.stay, TapeAction.apply, HeadMove.apply]

theorem stayRow3Description_lowersTransition
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (hactions :
      t.actions =
        [TapeAction.stay, TapeAction.stay, TapeAction.stay]) :
    LowersTransition D t (stayRow3Description t) where
  subroutineReady := cursorNoopDescription_subroutineReady
  realizes := by
    intro c hc _hsource _hreads
    have hlen : c.tapes.length = 3 := by
      simpa [hD] using hc
    rcases list_eq_three_of_length_eq_three hlen with
      ⟨T, U, V, htapes⟩
    cases c with
    | mk state tapes =>
        simp at htapes
        cases htapes
        change
          cursorNoopDescription.HaltsFromTape
            (encodedStructuredTapes [T, U, V])
            (encodedStructuredTapes
              (D.applyActions t.actions [T, U, V]))
        rw [hactions, applyActions_three_stay D hD T U V]
        exact cursorNoopDescription_haltsFromTape
          (encodedStructuredTapes [T, U, V])
end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC

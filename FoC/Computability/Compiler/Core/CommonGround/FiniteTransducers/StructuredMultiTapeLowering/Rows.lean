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

/--
Stay-capable version of the all-stay three-tape row machine.

This is intentionally a no-transition stay machine: it validates the
Milestone-8 stay-contract path without changing the existing exact
{lit}`cursorNoopDescription` row.
-/
def stayRow3DescriptionWithStay (_t : Transition) :
    MachineDescriptionWithStay where
  stateCount := 1
  start := 0
  halt := 0
  transitions := []

theorem stayRow3DescriptionWithStay_wellFormed
    (t : Transition) :
    (stayRow3DescriptionWithStay t).WellFormed := by
  simp [stayRow3DescriptionWithStay, MachineDescriptionWithStay.WellFormed,
    MachineDescriptionWithStay.Deterministic]

theorem stayRow3DescriptionWithStay_haltTransitionFree
    (t : Transition) :
    (stayRow3DescriptionWithStay t).HaltTransitionFree := by
  intro row hrow
  simp [stayRow3DescriptionWithStay] at hrow

theorem stayRow3DescriptionWithStay_subroutineReady
    (t : Transition) :
    (stayRow3DescriptionWithStay t).SubroutineReady :=
  ⟨stayRow3DescriptionWithStay_wellFormed t,
    stayRow3DescriptionWithStay_haltTransitionFree t⟩

theorem stayRow3DescriptionWithStay_haltsFromTape
    (t : Transition) (T : Tape Bool) :
    (stayRow3DescriptionWithStay t).HaltsFromTape T T := by
  refine ⟨0, ?_⟩
  simp [MachineDescriptionWithStay.HaltsFromTapeIn,
    MachineDescriptionWithStay.runConfig, stayRow3DescriptionWithStay]

theorem stayRow3DescriptionWithStay_compile_subroutineReady
    (t : Transition) :
    (stayRow3DescriptionWithStay t).compile.SubroutineReady := by
  constructor
  · simp [stayRow3DescriptionWithStay, MachineDescriptionWithStay.compile,
      MachineDescriptionWithStay.compileTransitions,
      MachineDescription.WellFormed, MachineDescription.Deterministic]
  · intro row hrow
    simp [stayRow3DescriptionWithStay, MachineDescriptionWithStay.compile,
      MachineDescriptionWithStay.compileTransitions] at hrow

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

theorem stayRow3DescriptionWithStay_lowersTransition
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (hactions :
      t.actions =
        [TapeAction.stay, TapeAction.stay, TapeAction.stay]) :
    LowersTransitionWithStay D t (stayRow3DescriptionWithStay t) where
  subroutineReady := stayRow3DescriptionWithStay_subroutineReady t
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
          (stayRow3DescriptionWithStay t).HaltsFromTape
            (encodedStructuredTapes [T, U, V])
            (encodedStructuredTapes
              (D.applyActions t.actions [T, U, V]))
        rw [hactions, applyActions_three_stay D hD T U V]
        exact stayRow3DescriptionWithStay_haltsFromTape t
          (encodedStructuredTapes [T, U, V])

theorem stayRow3DescriptionWithStay_lowersTransitionEquiv
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (hactions :
      t.actions =
        [TapeAction.stay, TapeAction.stay, TapeAction.stay]) :
    LowersTransitionEquiv D t
      ((stayRow3DescriptionWithStay t).compile) :=
  LowersTransitionWithStay.toCompiledEquiv
    (stayRow3DescriptionWithStay_lowersTransition D t hD hactions)
    (stayRow3DescriptionWithStay_compile_subroutineReady t)
end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC

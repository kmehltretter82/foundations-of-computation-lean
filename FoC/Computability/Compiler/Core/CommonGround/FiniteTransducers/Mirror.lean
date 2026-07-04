import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.Basic

set_option doc.verso true

/-!
# Mirrored finite-machine helpers

This module contains direction/tape mirroring helpers for finite transducer
components.  It is intentionally below specialized transducer modules in the
import graph so leaves can use mirrored machines without importing their parent
packaging files.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers

def mirroredDirection : Direction -> Direction
  | Direction.left => Direction.right
  | Direction.right => Direction.left

def mirroredTape (T : Tape Bool) : Tape Bool :=
  { left := T.right
    head := T.head
    right := T.left }

def mirroredTransition (row : TransitionDescription) :
    TransitionDescription :=
  { row with move := mirroredDirection row.move }

def mirroredDescription (D : MachineDescription) :
    MachineDescription :=
  { D with transitions := D.transitions.map mirroredTransition }

private theorem mirroredDirection_involutive (dir : Direction) :
    mirroredDirection (mirroredDirection dir) = dir := by
  cases dir <;> rfl

theorem mirroredTape_involutive (T : Tape Bool) :
    mirroredTape (mirroredTape T) = T := by
  cases T <;> rfl

private theorem mirroredTransition_involutive (row : TransitionDescription) :
    mirroredTransition (mirroredTransition row) = row := by
  cases row
  simp [mirroredTransition, mirroredDirection_involutive]

theorem mirroredTape_write (cell : Option Bool) (T : Tape Bool) :
    mirroredTape (Tape.write cell T) =
      Tape.write cell (mirroredTape T) := by
  cases T <;> rfl

theorem mirroredTape_read (T : Tape Bool) :
    Tape.read (mirroredTape T) = Tape.read T := by
  cases T <;> rfl

theorem mirroredTape_move (dir : Direction) (T : Tape Bool) :
    mirroredTape (Tape.move dir T) =
      Tape.move (mirroredDirection dir) (mirroredTape T) := by
  cases dir <;> cases T with
  | mk left head right =>
      cases left <;> cases right <;>
        simp [mirroredTape, mirroredDirection, Tape.move,
          Tape.moveLeft, Tape.moveRight]

private theorem mirroredTransition_matches
    (source : Nat) (read : Option Bool)
    (row : TransitionDescription) :
    Matches source read (mirroredTransition row) =
      Matches source read row := by
  cases row
  simp [mirroredTransition, Matches]

theorem mirroredDescription_lookupTransition
    (D : MachineDescription) (source : Nat) (read : Option Bool) :
    (mirroredDescription D).lookupTransition source read =
      (D.lookupTransition source read).map mirroredTransition := by
  unfold mirroredDescription lookupTransition
  induction D.transitions with
  | nil =>
      rfl
  | cons row rows ih =>
      cases hmatch : Matches source read row <;>
        simp [hmatch, mirroredTransition_matches, ih]

theorem mirroredDescription_stepConfig
    (D : MachineDescription) (c : Configuration) :
    (mirroredDescription D).stepConfig
        { state := c.state, tape := mirroredTape c.tape } =
      match D.stepConfig c with
      | none => none
      | some next =>
          some { state := next.state, tape := mirroredTape next.tape } := by
  unfold stepConfig
  rw [mirroredTape_read]
  rw [mirroredDescription_lookupTransition]
  cases hlookup : D.lookupTransition c.state (Tape.read c.tape) with
  | none =>
      simp
  | some row =>
      simp [mirroredTransition]
      rw [← mirroredTape_write]
      exact
        (mirroredTape_move row.move
          (Tape.write row.write c.tape)).symm

theorem mirroredDescription_runConfig
    (D : MachineDescription) (n : Nat) (c : Configuration) :
    (mirroredDescription D).runConfig n
        { state := c.state, tape := mirroredTape c.tape } =
      { state := (D.runConfig n c).state
        tape := mirroredTape (D.runConfig n c).tape } := by
  induction n generalizing c with
  | zero =>
      rfl
  | succ n ih =>
      rw [runConfig]
      rw [mirroredDescription_stepConfig]
      cases hstep : D.stepConfig c with
      | none =>
          simp [runConfig, hstep]
      | some next =>
          simp [runConfig, hstep]
          exact ih next

theorem mirroredDescription_wellFormed
    (D : MachineDescription) (hD : D.WellFormed) :
    (mirroredDescription D).WellFormed := by
  rcases hD with ⟨hcount, hstart, hhalt, hrows, hdet⟩
  refine ⟨hcount, hstart, hhalt, ?_, ?_⟩
  · intro row hrow
    rw [mirroredDescription] at hrow
    rcases List.mem_map.mp hrow with ⟨base, hbase, rfl⟩
    simpa [mirroredTransition, TransitionDescription.WellFormed] using
      hrows base hbase
  · intro t u ht hu hkey
    rw [mirroredDescription] at ht hu
    rcases List.mem_map.mp ht with ⟨baseT, hbaseT, rfl⟩
    rcases List.mem_map.mp hu with ⟨baseU, hbaseU, rfl⟩
    have hbaseKey :
        TransitionDescription.SameKey baseT baseU := by
      simpa [mirroredTransition, TransitionDescription.SameKey] using hkey
    have hbaseAction := hdet baseT baseU hbaseT hbaseU hbaseKey
    rcases hbaseAction with ⟨hwrite, hmove, htarget⟩
    exact
      ⟨hwrite,
        by simpa [mirroredTransition] using
          congrArg mirroredDirection hmove,
        htarget⟩

theorem mirroredDescription_haltTransitionFree
    (D : MachineDescription) (hD : D.HaltTransitionFree) :
    (mirroredDescription D).HaltTransitionFree := by
  intro row hrow hsource
  rw [mirroredDescription] at hrow
  rcases List.mem_map.mp hrow with ⟨base, hbase, rfl⟩
  exact hD base hbase hsource

theorem mirroredDescription_subroutineReady
    (D : MachineDescription) (hD : D.SubroutineReady) :
    (mirroredDescription D).SubroutineReady :=
  ⟨mirroredDescription_wellFormed D hD.left,
    mirroredDescription_haltTransitionFree D hD.right⟩

theorem mirroredTape_equiv {T U : Tape Bool}
    (h : Tape.Equiv T U) :
    Tape.Equiv (mirroredTape T) (mirroredTape U) := by
  rcases h with ⟨hleft, hhead, hright⟩
  exact ⟨hright, hhead, hleft⟩

theorem mirroredDescription_haltsFromTape
    {D : MachineDescription} {Tin Tout : Tape Bool}
    (h : D.HaltsFromTape Tin Tout) :
    (mirroredDescription D).HaltsFromTape
      (mirroredTape Tin) (mirroredTape Tout) := by
  rcases h with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  rcases hn with ⟨hstate, htape⟩
  change
    ((mirroredDescription D).runConfig n
        { state := D.start, tape := mirroredTape Tin }).state =
      (mirroredDescription D).halt ∧
    ((mirroredDescription D).runConfig n
        { state := D.start, tape := mirroredTape Tin }).tape =
      mirroredTape Tout
  have hrun :=
    mirroredDescription_runConfig D n
      { state := D.start, tape := Tin }
  constructor
  · rw [hrun]
    simpa [mirroredDescription] using hstate
  · rw [hrun]
    simp [htape]

theorem mirroredDescription_haltsFromTapeEquiv
    {D : MachineDescription} {Tin Tout : Tape Bool}
    (h : D.HaltsFromTapeEquiv Tin Tout) :
    (mirroredDescription D).HaltsFromTapeEquiv
      (mirroredTape Tin) (mirroredTape Tout) := by
  rcases h with ⟨Tactual, hhalt, hequiv⟩
  exact
    ⟨mirroredTape Tactual,
      mirroredDescription_haltsFromTape hhalt,
      mirroredTape_equiv hequiv⟩

end FiniteTransducers
end CommonGround

end Computability
end FoC

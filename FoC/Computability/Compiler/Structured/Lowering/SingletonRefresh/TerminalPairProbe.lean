import FoC.Computability.Compiler.Structured.Lowering.SingletonRefresh.OpeningProbe

set_option doc.verso true

/-!
# Singleton terminal-pair probe

Terminal-pair probe and terminal-bit facts for singleton-shape refresh.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

/-!
## False-branch terminal-pair probe
-/

def singletonTerminalPairProbeTargetCeiling
    (canonicalTarget rightBoundaryTarget : Nat) : Nat :=
  Nat.max canonicalTarget rightBoundaryTarget

def singletonTerminalPairProbeStateCount
    (canonicalTarget rightBoundaryTarget : Nat) : Nat :=
  singletonTerminalPairProbeTargetCeiling
      canonicalTarget rightBoundaryTarget + 12

def singletonTerminalPairProbeHalt
    (canonicalTarget rightBoundaryTarget : Nat) : Nat :=
  singletonTerminalPairProbeTargetCeiling
      canonicalTarget rightBoundaryTarget + 11

private theorem singletonTerminalPairProbe_local_lt
    (canonicalTarget rightBoundaryTarget localState : Nat)
    (hlocal : localState ≤ 10) :
    localState <
      singletonTerminalPairProbeStateCount
        canonicalTarget rightBoundaryTarget := by
  unfold singletonTerminalPairProbeStateCount
  lia

private theorem singletonTerminalPairProbe_halt_lt
    (canonicalTarget rightBoundaryTarget : Nat) :
    singletonTerminalPairProbeHalt
        canonicalTarget rightBoundaryTarget <
      singletonTerminalPairProbeStateCount
        canonicalTarget rightBoundaryTarget := by
  unfold singletonTerminalPairProbeHalt
    singletonTerminalPairProbeStateCount
  lia

private theorem singletonTerminalPairProbe_canonicalTarget_lt
    (canonicalTarget rightBoundaryTarget : Nat) :
    canonicalTarget <
      singletonTerminalPairProbeStateCount
        canonicalTarget rightBoundaryTarget := by
  have hle :
      canonicalTarget ≤
        singletonTerminalPairProbeTargetCeiling
          canonicalTarget rightBoundaryTarget := by
    unfold singletonTerminalPairProbeTargetCeiling
    exact Nat.le_max_left _ _
  unfold singletonTerminalPairProbeStateCount
  lia

private theorem singletonTerminalPairProbe_rightBoundaryTarget_lt
    (canonicalTarget rightBoundaryTarget : Nat) :
    rightBoundaryTarget <
      singletonTerminalPairProbeStateCount
        canonicalTarget rightBoundaryTarget := by
  have hle :
      rightBoundaryTarget ≤
        singletonTerminalPairProbeTargetCeiling
          canonicalTarget rightBoundaryTarget := by
    unfold singletonTerminalPairProbeTargetCeiling
    exact Nat.le_max_right _ _
  unfold singletonTerminalPairProbeStateCount
  lia

private theorem singletonTerminalPairProbe_source_ne_halt
    {canonicalTarget rightBoundaryTarget source : Nat}
    (hsource : source ≤ 10) :
    source ≠
      singletonTerminalPairProbeHalt
        canonicalTarget rightBoundaryTarget := by
  intro h
  have hlt :
      source <
        singletonTerminalPairProbeHalt
          canonicalTarget rightBoundaryTarget := by
    unfold singletonTerminalPairProbeHalt
    lia
  rw [← h] at hlt
  exact Nat.lt_irrefl source hlt

/--
False-branch discriminator for singleton endpoint refresh.

Starting at the opening separator, this machine scans to the closing separator,
backs up to the first bit of the terminal token pair, and distinguishes
right-boundary slack ({lit}`11` head marker before the final head-cell token)
from canonical guarded input (a logical-cell token before the final blank guard
cell).  It then rewinds to the opening separator before jumping to the selected
caller-supplied branch target.
-/
def singletonTerminalPairProbeDescription
    (canonicalTarget rightBoundaryTarget : Nat) :
    MachineDescription where
  stateCount :=
    singletonTerminalPairProbeStateCount
      canonicalTarget rightBoundaryTarget
  start := 0
  halt :=
    singletonTerminalPairProbeHalt
      canonicalTarget rightBoundaryTarget
  transitions :=
    [ transition 0 none none Direction.right 1
    , transition 1 (some false) (some false) Direction.right 1
    , transition 1 (some true) (some true) Direction.right 1
    , transition 1 none none Direction.left 2
    , transition 2 (some false) (some false) Direction.left 3
    , transition 2 (some true) (some true) Direction.left 3
    , transition 3 (some false) (some false) Direction.left 4
    , transition 3 (some true) (some true) Direction.left 4
    , transition 4 (some false) (some false) Direction.left 5
    , transition 4 (some true) (some true) Direction.left 5
    , transition 5 (some false) (some false) Direction.left 7
    , transition 5 (some true) (some true) Direction.right 6
    , transition 6 (some false) (some false) Direction.left 7
    , transition 6 (some true) (some true) Direction.left 9
    , transition 7 (some false) (some false) Direction.left 7
    , transition 7 (some true) (some true) Direction.left 7
    , transition 7 none none Direction.right 8
    , transition 8 (some false) (some false) Direction.left
        canonicalTarget
    , transition 8 (some true) (some true) Direction.left
        canonicalTarget
    , transition 9 (some false) (some false) Direction.left 9
    , transition 9 (some true) (some true) Direction.left 9
    , transition 9 none none Direction.right 10
    , transition 10 (some false) (some false) Direction.left
        rightBoundaryTarget
    , transition 10 (some true) (some true) Direction.left
        rightBoundaryTarget ]

theorem singletonTerminalPairProbeDescription_wellFormed
    (canonicalTarget rightBoundaryTarget : Nat) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).WellFormed := by
  refine ⟨
    singletonTerminalPairProbe_local_lt
      canonicalTarget rightBoundaryTarget 0 (by decide),
    singletonTerminalPairProbe_local_lt
      canonicalTarget rightBoundaryTarget 0 (by decide),
    singletonTerminalPairProbe_halt_lt
      canonicalTarget rightBoundaryTarget,
    ?_,
    ?_⟩
  · intro t ht
    simp [singletonTerminalPairProbeDescription] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 0 (by decide),
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 1 (by decide)⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 1 (by decide),
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 1 (by decide)⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 1 (by decide),
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 1 (by decide)⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 1 (by decide),
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 2 (by decide)⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 2 (by decide),
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 3 (by decide)⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 2 (by decide),
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 3 (by decide)⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 3 (by decide),
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 4 (by decide)⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 3 (by decide),
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 4 (by decide)⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 4 (by decide),
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 5 (by decide)⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 4 (by decide),
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 5 (by decide)⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 5 (by decide),
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 7 (by decide)⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 5 (by decide),
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 6 (by decide)⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 6 (by decide),
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 7 (by decide)⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 6 (by decide),
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 9 (by decide)⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 7 (by decide),
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 7 (by decide)⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 7 (by decide),
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 7 (by decide)⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 7 (by decide),
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 8 (by decide)⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 8 (by decide),
        singletonTerminalPairProbe_canonicalTarget_lt
          canonicalTarget rightBoundaryTarget⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 8 (by decide),
        singletonTerminalPairProbe_canonicalTarget_lt
          canonicalTarget rightBoundaryTarget⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 9 (by decide),
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 9 (by decide)⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 9 (by decide),
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 9 (by decide)⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 9 (by decide),
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 10 (by decide)⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 10 (by decide),
        singletonTerminalPairProbe_rightBoundaryTarget_lt
          canonicalTarget rightBoundaryTarget⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 10 (by decide),
        singletonTerminalPairProbe_rightBoundaryTarget_lt
          canonicalTarget rightBoundaryTarget⟩
  · intro t u ht hu hkey
    simp [singletonTerminalPairProbeDescription] at ht hu
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [TransitionDescription.SameKey,
        TransitionDescription.SameAction, transition] at hkey ⊢

theorem singletonTerminalPairProbeDescription_haltTransitionFree
    (canonicalTarget rightBoundaryTarget : Nat) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).HaltTransitionFree := by
  intro t ht
  simp [singletonTerminalPairProbeDescription] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    first
    | exact singletonTerminalPairProbe_source_ne_halt
        (canonicalTarget := canonicalTarget)
        (rightBoundaryTarget := rightBoundaryTarget)
        (source := 0) (by decide)
    | exact singletonTerminalPairProbe_source_ne_halt
        (canonicalTarget := canonicalTarget)
        (rightBoundaryTarget := rightBoundaryTarget)
        (source := 1) (by decide)
    | exact singletonTerminalPairProbe_source_ne_halt
        (canonicalTarget := canonicalTarget)
        (rightBoundaryTarget := rightBoundaryTarget)
        (source := 2) (by decide)
    | exact singletonTerminalPairProbe_source_ne_halt
        (canonicalTarget := canonicalTarget)
        (rightBoundaryTarget := rightBoundaryTarget)
        (source := 3) (by decide)
    | exact singletonTerminalPairProbe_source_ne_halt
        (canonicalTarget := canonicalTarget)
        (rightBoundaryTarget := rightBoundaryTarget)
        (source := 4) (by decide)
    | exact singletonTerminalPairProbe_source_ne_halt
        (canonicalTarget := canonicalTarget)
        (rightBoundaryTarget := rightBoundaryTarget)
        (source := 5) (by decide)
    | exact singletonTerminalPairProbe_source_ne_halt
        (canonicalTarget := canonicalTarget)
        (rightBoundaryTarget := rightBoundaryTarget)
        (source := 6) (by decide)
    | exact singletonTerminalPairProbe_source_ne_halt
        (canonicalTarget := canonicalTarget)
        (rightBoundaryTarget := rightBoundaryTarget)
        (source := 7) (by decide)
    | exact singletonTerminalPairProbe_source_ne_halt
        (canonicalTarget := canonicalTarget)
        (rightBoundaryTarget := rightBoundaryTarget)
        (source := 8) (by decide)
    | exact singletonTerminalPairProbe_source_ne_halt
        (canonicalTarget := canonicalTarget)
        (rightBoundaryTarget := rightBoundaryTarget)
        (source := 9) (by decide)
    | exact singletonTerminalPairProbe_source_ne_halt
        (canonicalTarget := canonicalTarget)
        (rightBoundaryTarget := rightBoundaryTarget)
        (source := 10) (by decide)

theorem singletonTerminalPairProbeDescription_subroutineReady
    (canonicalTarget rightBoundaryTarget : Nat) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).SubroutineReady :=
  ⟨singletonTerminalPairProbeDescription_wellFormed
      canonicalTarget rightBoundaryTarget,
    singletonTerminalPairProbeDescription_haltTransitionFree
      canonicalTarget rightBoundaryTarget⟩

private theorem singletonTerminalPairProbeDescription_step_scan_bit
    (canonicalTarget rightBoundaryTarget : Nat)
    (left right : List (Option Bool)) (bit : Bool) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).runConfig 1
        { state := 1
          tape := tapeAtCells left (some bit :: right) } =
      { state := 1
        tape := tapeAtCells (some bit :: left) right } := by
  cases bit <;> cases right <;>
    simp [singletonTerminalPairProbeDescription,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      transition, tapeAtCells, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

private theorem singletonTerminalPairProbeDescription_step_scan_finish
    (canonicalTarget rightBoundaryTarget : Nat)
    (left padding : List (Option Bool)) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).runConfig 1
        { state := 1
          tape := tapeAtCells left (none :: padding) } =
      { state := 2
        tape :=
          Tape.move Direction.left
            (tapeAtCells left (none :: padding)) } := by
  cases left <;> cases padding <;>
    simp [singletonTerminalPairProbeDescription,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      transition, tapeAtCells, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft]

theorem singletonTerminalPairProbeDescription_run_scan
    (canonicalTarget rightBoundaryTarget : Nat)
    (bits : Word Bool) (left padding : List (Option Bool)) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).runConfig bits.length
        { state := 1
          tape :=
            tapeAtCells left
              (List.append (bits.map some) (none :: padding)) } =
      { state := 1
        tape :=
          tapeAtCells
            (List.append (bits.reverse.map some) left)
            (none :: padding) } := by
  induction bits generalizing left with
  | nil =>
      simp [MachineDescription.runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        lia]
      rw [MachineDescription.runConfig_add]
      change
        (singletonTerminalPairProbeDescription
          canonicalTarget rightBoundaryTarget).runConfig rest.length
            ((singletonTerminalPairProbeDescription
              canonicalTarget rightBoundaryTarget).runConfig 1
              { state := 1
                tape :=
                  tapeAtCells left
                    (some bit ::
                      List.append (rest.map some)
                        (none :: padding)) }) =
          { state := 1
            tape :=
              tapeAtCells
                (List.append ((bit :: rest).reverse.map some) left)
                (none :: padding) }
      rw [singletonTerminalPairProbeDescription_step_scan_bit
        canonicalTarget rightBoundaryTarget left
        (List.append (rest.map some) (none :: padding)) bit]
      simpa [List.reverse_cons, List.map_append,
        List.append_assoc] using ih (some bit :: left)

theorem singletonTerminalPairProbeDescription_run_scan_to_terminal
    (canonicalTarget rightBoundaryTarget : Nat)
    (bits : Word Bool) (padding : List (Option Bool)) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).runConfig (bits.length + 1)
        { state := 1
          tape :=
            tapeAtCells []
              (List.append (bits.map some) (none :: padding)) } =
      { state := 2
        tape :=
          Tape.move Direction.left
            (tapeAtCells (bits.reverse.map some)
              (none :: padding)) } := by
  rw [MachineDescription.runConfig_add]
  rw [singletonTerminalPairProbeDescription_run_scan]
  rw [singletonTerminalPairProbeDescription_step_scan_finish]
  simp

theorem singletonTerminalPairProbeDescription_run_scan_to_terminal_from_left
    (canonicalTarget rightBoundaryTarget : Nat)
    (bits : Word Bool) (left padding : List (Option Bool)) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).runConfig (bits.length + 1)
        { state := 1
          tape :=
            tapeAtCells left
              (List.append (bits.map some) (none :: padding)) } =
      { state := 2
        tape :=
          Tape.move Direction.left
            (tapeAtCells
              (List.append (bits.reverse.map some) left)
              (none :: padding)) } := by
  rw [MachineDescription.runConfig_add]
  rw [singletonTerminalPairProbeDescription_run_scan]
  rw [singletonTerminalPairProbeDescription_step_scan_finish]

private theorem singletonTerminalPairProbeDescription_step_start
    (canonicalTarget rightBoundaryTarget : Nat)
    (bits : Word Bool) (padding : List (Option Bool)) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).runConfig 1
        { state :=
            (singletonTerminalPairProbeDescription
              canonicalTarget rightBoundaryTarget).start
          tape :=
            tapeAtCells []
              (none ::
                List.append (bits.map some) (none :: padding)) } =
      { state := 1
        tape :=
          tapeAtCells [none]
            (List.append (bits.map some) (none :: padding)) } := by
  cases bits with
  | nil =>
      cases padding <;>
        simp [singletonTerminalPairProbeDescription,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          transition, tapeAtCells, Tape.read, Tape.write, Tape.move,
          Tape.moveRight]
  | cons bit rest =>
      cases bit <;> cases rest <;> cases padding <;>
        simp [singletonTerminalPairProbeDescription,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          transition, tapeAtCells, Tape.read, Tape.write, Tape.move,
          Tape.moveRight]

private theorem singletonTerminalPairProbeDescription_step_rewind_canonical_finish
    (canonicalTarget rightBoundaryTarget : Nat)
    (current : Bool) (rightTail : List (Option Bool)) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).runConfig 2
        { state := 7
          tape :=
            tapeAtCells [] (none :: some current :: rightTail) } =
      { state := canonicalTarget
        tape :=
          tapeAtCells [] (none :: some current :: rightTail) } := by
  cases current <;> cases rightTail <;>
    simp [singletonTerminalPairProbeDescription,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      transition, tapeAtCells, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft, Tape.moveRight]

private theorem singletonTerminalPairProbeDescription_step_rewind_right_finish
    (canonicalTarget rightBoundaryTarget : Nat)
    (current : Bool) (rightTail : List (Option Bool)) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).runConfig 2
        { state := 9
          tape :=
            tapeAtCells [] (none :: some current :: rightTail) } =
      { state := rightBoundaryTarget
        tape :=
          tapeAtCells [] (none :: some current :: rightTail) } := by
  cases current <;> cases rightTail <;>
    simp [singletonTerminalPairProbeDescription,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      transition, tapeAtCells, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft, Tape.moveRight]

private theorem singletonTerminalPairProbeDescription_run_rewind_canonical
    (canonicalTarget rightBoundaryTarget : Nat)
    (leftStack : Word Bool) (current : Bool)
    (rightTail : List (Option Bool)) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).runConfig
        (leftStack.length + 3)
        { state := 7
          tape :=
            tapeAtCells
              (List.append (leftStack.map some) [none])
              (some current :: rightTail) } =
      { state := canonicalTarget
        tape :=
          tapeAtCells []
            (none ::
              List.append
                ((List.append leftStack.reverse [current]).map some)
                rightTail) } := by
  induction leftStack generalizing current rightTail with
  | nil =>
      rw [show ([] : Word Bool).length + 3 = 1 + 2 by rfl]
      rw [MachineDescription.runConfig_add]
      have hstep :
          (singletonTerminalPairProbeDescription
            canonicalTarget rightBoundaryTarget).runConfig 1
            { state := 7
              tape :=
                tapeAtCells
                  (List.append (([] : Word Bool).map some) [none])
                  (some current :: rightTail) } =
          { state := 7
            tape :=
              tapeAtCells [] (none :: some current :: rightTail) } := by
        cases current <;> cases rightTail <;>
          simp [singletonTerminalPairProbeDescription,
            MachineDescription.runConfig, MachineDescription.stepConfig,
            MachineDescription.lookupTransition,
            MachineDescription.Matches, transition, tapeAtCells,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      rw [hstep]
      simpa using
        singletonTerminalPairProbeDescription_step_rewind_canonical_finish
          canonicalTarget rightBoundaryTarget current rightTail
  | cons next rest ih =>
      rw [show (next :: rest).length + 3 =
        1 + (rest.length + 3) by
        simp
        lia]
      rw [MachineDescription.runConfig_add]
      have hstep :
          (singletonTerminalPairProbeDescription
            canonicalTarget rightBoundaryTarget).runConfig 1
            { state := 7
              tape :=
                tapeAtCells
                  (List.append ((next :: rest).map some) [none])
                  (some current :: rightTail) } =
          { state := 7
            tape :=
              tapeAtCells
                (List.append (rest.map some) [none])
                (some next :: some current :: rightTail) } := by
        cases next <;> cases current <;> cases rightTail <;>
          simp [singletonTerminalPairProbeDescription,
            MachineDescription.runConfig, MachineDescription.stepConfig,
            MachineDescription.lookupTransition,
            MachineDescription.Matches, transition, tapeAtCells,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc]
        using ih next (some current :: rightTail)

private theorem singletonTerminalPairProbeDescription_run_rewind_right
    (canonicalTarget rightBoundaryTarget : Nat)
    (leftStack : Word Bool) (current : Bool)
    (rightTail : List (Option Bool)) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).runConfig
        (leftStack.length + 3)
        { state := 9
          tape :=
            tapeAtCells
              (List.append (leftStack.map some) [none])
              (some current :: rightTail) } =
      { state := rightBoundaryTarget
        tape :=
          tapeAtCells []
            (none ::
              List.append
                ((List.append leftStack.reverse [current]).map some)
                rightTail) } := by
  induction leftStack generalizing current rightTail with
  | nil =>
      rw [show ([] : Word Bool).length + 3 = 1 + 2 by rfl]
      rw [MachineDescription.runConfig_add]
      have hstep :
          (singletonTerminalPairProbeDescription
            canonicalTarget rightBoundaryTarget).runConfig 1
            { state := 9
              tape :=
                tapeAtCells
                  (List.append (([] : Word Bool).map some) [none])
                  (some current :: rightTail) } =
          { state := 9
            tape :=
              tapeAtCells [] (none :: some current :: rightTail) } := by
        cases current <;> cases rightTail <;>
          simp [singletonTerminalPairProbeDescription,
            MachineDescription.runConfig, MachineDescription.stepConfig,
            MachineDescription.lookupTransition,
            MachineDescription.Matches, transition, tapeAtCells,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      rw [hstep]
      simpa using
        singletonTerminalPairProbeDescription_step_rewind_right_finish
          canonicalTarget rightBoundaryTarget current rightTail
  | cons next rest ih =>
      rw [show (next :: rest).length + 3 =
        1 + (rest.length + 3) by
        simp
        lia]
      rw [MachineDescription.runConfig_add]
      have hstep :
          (singletonTerminalPairProbeDescription
            canonicalTarget rightBoundaryTarget).runConfig 1
            { state := 9
              tape :=
                tapeAtCells
                  (List.append ((next :: rest).map some) [none])
                  (some current :: rightTail) } =
          { state := 9
            tape :=
              tapeAtCells
                (List.append (rest.map some) [none])
                (some next :: some current :: rightTail) } := by
        cases next <;> cases current <;> cases rightTail <;>
          simp [singletonTerminalPairProbeDescription,
            MachineDescription.runConfig, MachineDescription.stepConfig,
            MachineDescription.lookupTransition,
            MachineDescription.Matches, transition, tapeAtCells,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc]
        using ih next (some current :: rightTail)

private theorem singletonTerminalPairProbeDescription_run_rewind_canonical_after_left
    (canonicalTarget rightBoundaryTarget : Nat)
    (leftStack : Word Bool) (current : Bool)
    (rightTail : List (Option Bool)) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).runConfig
        (leftStack.length + 2)
        { state := 7
          tape :=
            Tape.move Direction.left
              (tapeAtCells
                (List.append (leftStack.map some) [none])
                (some current :: rightTail)) } =
      { state := canonicalTarget
        tape :=
          tapeAtCells []
            (none ::
              List.append (leftStack.reverse.map some)
                (some current :: rightTail)) } := by
  cases leftStack with
  | nil =>
      simpa [Tape.move, Tape.moveLeft, tapeAtCells] using
        singletonTerminalPairProbeDescription_step_rewind_canonical_finish
          canonicalTarget rightBoundaryTarget current rightTail
  | cons next rest =>
      rw [show (next :: rest).length + 2 = rest.length + 3 by
        simp]
      simpa [Tape.move, Tape.moveLeft, tapeAtCells, List.reverse_cons,
        List.map_append, List.append_assoc] using
        singletonTerminalPairProbeDescription_run_rewind_canonical
          canonicalTarget rightBoundaryTarget rest next
          (some current :: rightTail)

private theorem singletonTerminalPairProbeDescription_run_terminal_right_from_state2
    (canonicalTarget rightBoundaryTarget : Nat)
    (pfxRev : Word Bool) (b0 b1 : Bool)
    (padding : List (Option Bool)) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).runConfig
        (pfxRev.length + 8)
        { state := 2
          tape :=
            tapeAtCells
              (some b0 :: some true :: some true ::
                List.append (pfxRev.map some) [none])
              (some b1 :: none :: padding) } =
      { state := rightBoundaryTarget
        tape :=
          tapeAtCells []
            (none ::
              List.append
                ((List.append pfxRev.reverse [true]).map some)
                (some true :: some b0 :: some b1 :: none :: padding)) } := by
  rw [show pfxRev.length + 8 = 5 + (pfxRev.length + 3) by
    lia]
  rw [MachineDescription.runConfig_add]
  have hterminal :
      (singletonTerminalPairProbeDescription
        canonicalTarget rightBoundaryTarget).runConfig 5
        { state := 2
          tape :=
            tapeAtCells
              (some b0 :: some true :: some true ::
                List.append (pfxRev.map some) [none])
              (some b1 :: none :: padding) } =
      { state := 9
        tape :=
          tapeAtCells
            (List.append (pfxRev.map some) [none])
            (some true :: some true :: some b0 :: some b1 ::
              none :: padding) } := by
    cases b0 <;> cases b1 <;> cases padding <;>
      simp [singletonTerminalPairProbeDescription,
        MachineDescription.runConfig, MachineDescription.stepConfig,
        MachineDescription.lookupTransition,
        MachineDescription.Matches, transition, tapeAtCells,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft,
        Tape.moveRight]
  rw [hterminal]
  simpa [List.append_assoc] using
    singletonTerminalPairProbeDescription_run_rewind_right
      canonicalTarget rightBoundaryTarget pfxRev true
      (some true :: some b0 :: some b1 :: none :: padding)

private theorem singletonTerminalPairProbeDescription_run_terminal_canonical_false_from_state2
    (canonicalTarget rightBoundaryTarget : Nat)
    (pfxRev : Word Bool) (c1 : Bool)
    (padding : List (Option Bool)) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).runConfig
        (pfxRev.length + 6)
        { state := 2
          tape :=
            tapeAtCells
              (some false :: some c1 :: some false ::
                List.append (pfxRev.map some) [none])
              (some false :: none :: padding) } =
      { state := canonicalTarget
        tape :=
          tapeAtCells []
            (none ::
              List.append (pfxRev.reverse.map some)
                (some false :: some c1 :: some false :: some false ::
                  none :: padding)) } := by
  rw [show pfxRev.length + 6 = 4 + (pfxRev.length + 2) by
    lia]
  rw [MachineDescription.runConfig_add]
  have hterminal :
      (singletonTerminalPairProbeDescription
        canonicalTarget rightBoundaryTarget).runConfig 4
        { state := 2
          tape :=
            tapeAtCells
              (some false :: some c1 :: some false ::
                List.append (pfxRev.map some) [none])
              (some false :: none :: padding) } =
      { state := 7
        tape :=
          Tape.move Direction.left
            (tapeAtCells
              (List.append (pfxRev.map some) [none])
              (some false :: some c1 :: some false :: some false ::
                none :: padding)) } := by
    cases c1 <;> cases padding <;>
      simp [singletonTerminalPairProbeDescription,
        MachineDescription.runConfig, MachineDescription.stepConfig,
        MachineDescription.lookupTransition,
        MachineDescription.Matches, transition, tapeAtCells,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft]
  rw [hterminal]
  simpa [List.append_assoc] using
    singletonTerminalPairProbeDescription_run_rewind_canonical_after_left
      canonicalTarget rightBoundaryTarget pfxRev false
      (some c1 :: some false :: some false :: none :: padding)

private theorem singletonTerminalPairProbeDescription_run_terminal_canonical_true_from_state2
    (canonicalTarget rightBoundaryTarget : Nat)
    (pfxRev : Word Bool) (padding : List (Option Bool)) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).runConfig
        (pfxRev.length + 8)
        { state := 2
          tape :=
            tapeAtCells
              (some false :: some false :: some true ::
                List.append (pfxRev.map some) [none])
              (some false :: none :: padding) } =
      { state := canonicalTarget
        tape :=
          tapeAtCells []
            (none ::
              List.append
                ((List.append pfxRev.reverse [true]).map some)
                (some false :: some false :: some false ::
                  none :: padding)) } := by
  rw [show pfxRev.length + 8 = 5 + (pfxRev.length + 3) by
    lia]
  rw [MachineDescription.runConfig_add]
  have hterminal :
      (singletonTerminalPairProbeDescription
        canonicalTarget rightBoundaryTarget).runConfig 5
        { state := 2
          tape :=
            tapeAtCells
              (some false :: some false :: some true ::
                List.append (pfxRev.map some) [none])
              (some false :: none :: padding) } =
      { state := 7
        tape :=
          tapeAtCells
            (List.append (pfxRev.map some) [none])
            (some true :: some false :: some false :: some false ::
              none :: padding) } := by
    cases padding <;>
      simp [singletonTerminalPairProbeDescription,
        MachineDescription.runConfig, MachineDescription.stepConfig,
        MachineDescription.lookupTransition,
        MachineDescription.Matches, transition, tapeAtCells,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft,
        Tape.moveRight]
  rw [hterminal]
  simpa [List.append_assoc] using
    singletonTerminalPairProbeDescription_run_rewind_canonical
      canonicalTarget rightBoundaryTarget pfxRev true
      (some false :: some false :: some false :: none :: padding)

theorem singletonTerminalPairProbeDescription_reaches_rightBoundary_bits
    (canonicalTarget rightBoundaryTarget : Nat)
    (pfxBits : Word Bool) (head : Option Bool)
    (padding : List (Option Bool)) :
    exists steps : Nat,
      (singletonTerminalPairProbeDescription
        canonicalTarget rightBoundaryTarget).runConfig steps
        { state :=
            (singletonTerminalPairProbeDescription
              canonicalTarget rightBoundaryTarget).start
          tape :=
            tapeAtCells []
              (none ::
                List.append
                  ((List.append pfxBits
                    (List.append [true, true]
                      (logicalCellBits head))).map some)
                  (none :: padding)) } =
      { state := rightBoundaryTarget
        tape :=
          tapeAtCells []
            (none ::
              List.append
                ((List.append pfxBits
                  (List.append [true, true]
                    (logicalCellBits head))).map some)
                (none :: padding)) } := by
  cases head with
  | none =>
      let bits : Word Bool :=
        List.append pfxBits
          (List.append [true, true]
            (logicalCellBits (none : Option Bool)))
      refine ⟨(1 + (bits.length + 1)) + (pfxBits.length + 8), ?_⟩
      change
        (singletonTerminalPairProbeDescription
          canonicalTarget rightBoundaryTarget).runConfig
            ((1 + (bits.length + 1)) + (pfxBits.length + 8))
            { state :=
                (singletonTerminalPairProbeDescription
                  canonicalTarget rightBoundaryTarget).start
              tape :=
                tapeAtCells []
                  (none ::
                    List.append (bits.map some) (none :: padding)) } =
          { state := rightBoundaryTarget
            tape :=
              tapeAtCells []
                (none ::
                  List.append (bits.map some) (none :: padding)) }
      rw [MachineDescription.runConfig_add]
      have hentry :
          (singletonTerminalPairProbeDescription
            canonicalTarget rightBoundaryTarget).runConfig
              (1 + (bits.length + 1))
              { state :=
                  (singletonTerminalPairProbeDescription
                    canonicalTarget rightBoundaryTarget).start
                tape :=
                  tapeAtCells []
                    (none ::
                      List.append (bits.map some) (none :: padding)) } =
            { state := 2
              tape :=
                tapeAtCells
                  (some false :: some true :: some true ::
                    List.append (pfxBits.reverse.map some) [none])
                  (some false :: none :: padding) } := by
        rw [MachineDescription.runConfig_add]
        rw [singletonTerminalPairProbeDescription_step_start]
        rw [singletonTerminalPairProbeDescription_run_scan_to_terminal_from_left]
        simp [bits, logicalCellBits, List.reverse_append,
          tapeAtCells, Tape.move, Tape.moveLeft]
      rw [hentry]
      simpa [bits, logicalCellBits, List.map_append, List.append_assoc]
        using
          singletonTerminalPairProbeDescription_run_terminal_right_from_state2
            canonicalTarget rightBoundaryTarget pfxBits.reverse false false
            padding
  | some bit =>
      cases bit
      · let bits : Word Bool :=
          List.append pfxBits
            (List.append [true, true]
              (logicalCellBits (some false)))
        refine ⟨(1 + (bits.length + 1)) + (pfxBits.length + 8), ?_⟩
        change
          (singletonTerminalPairProbeDescription
            canonicalTarget rightBoundaryTarget).runConfig
              ((1 + (bits.length + 1)) + (pfxBits.length + 8))
              { state :=
                  (singletonTerminalPairProbeDescription
                    canonicalTarget rightBoundaryTarget).start
                tape :=
                  tapeAtCells []
                    (none ::
                      List.append (bits.map some) (none :: padding)) } =
            { state := rightBoundaryTarget
              tape :=
                tapeAtCells []
                  (none ::
                    List.append (bits.map some) (none :: padding)) }
        rw [MachineDescription.runConfig_add]
        have hentry :
            (singletonTerminalPairProbeDescription
              canonicalTarget rightBoundaryTarget).runConfig
                (1 + (bits.length + 1))
                { state :=
                    (singletonTerminalPairProbeDescription
                      canonicalTarget rightBoundaryTarget).start
                  tape :=
                    tapeAtCells []
                      (none ::
                        List.append (bits.map some) (none :: padding)) } =
              { state := 2
                tape :=
                  tapeAtCells
                    (some false :: some true :: some true ::
                      List.append (pfxBits.reverse.map some) [none])
                    (some true :: none :: padding) } := by
          rw [MachineDescription.runConfig_add]
          rw [singletonTerminalPairProbeDescription_step_start]
          rw [singletonTerminalPairProbeDescription_run_scan_to_terminal_from_left]
          simp [bits, logicalCellBits, List.reverse_append,
            tapeAtCells, Tape.move, Tape.moveLeft]
        rw [hentry]
        simpa [bits, logicalCellBits, List.map_append, List.append_assoc]
          using
            singletonTerminalPairProbeDescription_run_terminal_right_from_state2
              canonicalTarget rightBoundaryTarget pfxBits.reverse false true
              padding
      · let bits : Word Bool :=
          List.append pfxBits
            (List.append [true, true]
              (logicalCellBits (some true)))
        refine ⟨(1 + (bits.length + 1)) + (pfxBits.length + 8), ?_⟩
        change
          (singletonTerminalPairProbeDescription
            canonicalTarget rightBoundaryTarget).runConfig
              ((1 + (bits.length + 1)) + (pfxBits.length + 8))
              { state :=
                  (singletonTerminalPairProbeDescription
                    canonicalTarget rightBoundaryTarget).start
                tape :=
                  tapeAtCells []
                    (none ::
                      List.append (bits.map some) (none :: padding)) } =
            { state := rightBoundaryTarget
              tape :=
                tapeAtCells []
                  (none ::
                    List.append (bits.map some) (none :: padding)) }
        rw [MachineDescription.runConfig_add]
        have hentry :
            (singletonTerminalPairProbeDescription
              canonicalTarget rightBoundaryTarget).runConfig
                (1 + (bits.length + 1))
                { state :=
                    (singletonTerminalPairProbeDescription
                      canonicalTarget rightBoundaryTarget).start
                  tape :=
                    tapeAtCells []
                      (none ::
                        List.append (bits.map some) (none :: padding)) } =
              { state := 2
                tape :=
                  tapeAtCells
                    (some true :: some true :: some true ::
                      List.append (pfxBits.reverse.map some) [none])
                    (some false :: none :: padding) } := by
          rw [MachineDescription.runConfig_add]
          rw [singletonTerminalPairProbeDescription_step_start]
          rw [singletonTerminalPairProbeDescription_run_scan_to_terminal_from_left]
          simp [bits, logicalCellBits, List.reverse_append,
            tapeAtCells, Tape.move, Tape.moveLeft]
        rw [hentry]
        simpa [bits, logicalCellBits, List.map_append, List.append_assoc]
          using
          singletonTerminalPairProbeDescription_run_terminal_right_from_state2
            canonicalTarget rightBoundaryTarget pfxBits.reverse true false
            padding

theorem singletonTerminalPairProbeDescription_reaches_canonical_bits
    (canonicalTarget rightBoundaryTarget : Nat)
    (pfxBits : Word Bool) (cell : Option Bool)
    (padding : List (Option Bool)) :
    exists steps : Nat,
      (singletonTerminalPairProbeDescription
        canonicalTarget rightBoundaryTarget).runConfig steps
        { state :=
            (singletonTerminalPairProbeDescription
              canonicalTarget rightBoundaryTarget).start
          tape :=
            tapeAtCells []
              (none ::
                List.append
                  ((List.append pfxBits
                    (List.append (logicalCellBits cell)
                      (logicalCellBits none))).map some)
                  (none :: padding)) } =
      { state := canonicalTarget
        tape :=
          tapeAtCells []
            (none ::
              List.append
                ((List.append pfxBits
                  (List.append (logicalCellBits cell)
                    (logicalCellBits none))).map some)
                (none :: padding)) } := by
  cases cell with
  | none =>
      let bits : Word Bool :=
        List.append pfxBits
          (List.append (logicalCellBits (none : Option Bool))
            (logicalCellBits none))
      refine ⟨(1 + (bits.length + 1)) + (pfxBits.length + 6), ?_⟩
      change
        (singletonTerminalPairProbeDescription
          canonicalTarget rightBoundaryTarget).runConfig
            ((1 + (bits.length + 1)) + (pfxBits.length + 6))
            { state :=
                (singletonTerminalPairProbeDescription
                  canonicalTarget rightBoundaryTarget).start
              tape :=
                tapeAtCells []
                  (none ::
                    List.append (bits.map some) (none :: padding)) } =
          { state := canonicalTarget
            tape :=
              tapeAtCells []
                (none ::
                  List.append (bits.map some) (none :: padding)) }
      rw [MachineDescription.runConfig_add]
      have hentry :
          (singletonTerminalPairProbeDescription
            canonicalTarget rightBoundaryTarget).runConfig
              (1 + (bits.length + 1))
              { state :=
                  (singletonTerminalPairProbeDescription
                    canonicalTarget rightBoundaryTarget).start
                tape :=
                  tapeAtCells []
                    (none ::
                      List.append (bits.map some) (none :: padding)) } =
            { state := 2
              tape :=
                tapeAtCells
                  (some false :: some false :: some false ::
                    List.append (pfxBits.reverse.map some) [none])
                  (some false :: none :: padding) } := by
        rw [MachineDescription.runConfig_add]
        rw [singletonTerminalPairProbeDescription_step_start]
        rw [singletonTerminalPairProbeDescription_run_scan_to_terminal_from_left]
        simp [bits, logicalCellBits, List.reverse_append,
          tapeAtCells, Tape.move, Tape.moveLeft]
      rw [hentry]
      simpa [bits, logicalCellBits, List.map_append, List.append_assoc]
        using
          singletonTerminalPairProbeDescription_run_terminal_canonical_false_from_state2
            canonicalTarget rightBoundaryTarget pfxBits.reverse false
            padding
  | some bit =>
      cases bit
      · let bits : Word Bool :=
          List.append pfxBits
            (List.append (logicalCellBits (some false))
              (logicalCellBits none))
        refine ⟨(1 + (bits.length + 1)) + (pfxBits.length + 6), ?_⟩
        change
          (singletonTerminalPairProbeDescription
            canonicalTarget rightBoundaryTarget).runConfig
              ((1 + (bits.length + 1)) + (pfxBits.length + 6))
              { state :=
                  (singletonTerminalPairProbeDescription
                    canonicalTarget rightBoundaryTarget).start
                tape :=
                  tapeAtCells []
                    (none ::
                      List.append (bits.map some) (none :: padding)) } =
            { state := canonicalTarget
              tape :=
                tapeAtCells []
                  (none ::
                    List.append (bits.map some) (none :: padding)) }
        rw [MachineDescription.runConfig_add]
        have hentry :
            (singletonTerminalPairProbeDescription
              canonicalTarget rightBoundaryTarget).runConfig
                (1 + (bits.length + 1))
                { state :=
                    (singletonTerminalPairProbeDescription
                      canonicalTarget rightBoundaryTarget).start
                  tape :=
                    tapeAtCells []
                      (none ::
                        List.append (bits.map some) (none :: padding)) } =
              { state := 2
                tape :=
                  tapeAtCells
                    (some false :: some true :: some false ::
                      List.append (pfxBits.reverse.map some) [none])
                    (some false :: none :: padding) } := by
          rw [MachineDescription.runConfig_add]
          rw [singletonTerminalPairProbeDescription_step_start]
          rw [singletonTerminalPairProbeDescription_run_scan_to_terminal_from_left]
          simp [bits, logicalCellBits, List.reverse_append,
            tapeAtCells, Tape.move, Tape.moveLeft]
        rw [hentry]
        simpa [bits, logicalCellBits, List.map_append, List.append_assoc]
          using
            singletonTerminalPairProbeDescription_run_terminal_canonical_false_from_state2
              canonicalTarget rightBoundaryTarget pfxBits.reverse true
              padding
      · let bits : Word Bool :=
          List.append pfxBits
            (List.append (logicalCellBits (some true))
              (logicalCellBits none))
        refine ⟨(1 + (bits.length + 1)) + (pfxBits.length + 8), ?_⟩
        change
          (singletonTerminalPairProbeDescription
            canonicalTarget rightBoundaryTarget).runConfig
              ((1 + (bits.length + 1)) + (pfxBits.length + 8))
              { state :=
                  (singletonTerminalPairProbeDescription
                    canonicalTarget rightBoundaryTarget).start
                tape :=
                  tapeAtCells []
                    (none ::
                      List.append (bits.map some) (none :: padding)) } =
            { state := canonicalTarget
              tape :=
                tapeAtCells []
                  (none ::
                    List.append (bits.map some) (none :: padding)) }
        rw [MachineDescription.runConfig_add]
        have hentry :
            (singletonTerminalPairProbeDescription
              canonicalTarget rightBoundaryTarget).runConfig
                (1 + (bits.length + 1))
                { state :=
                    (singletonTerminalPairProbeDescription
                      canonicalTarget rightBoundaryTarget).start
                  tape :=
                    tapeAtCells []
                      (none ::
                        List.append (bits.map some) (none :: padding)) } =
              { state := 2
                tape :=
                  tapeAtCells
                    (some false :: some false :: some true ::
                      List.append (pfxBits.reverse.map some) [none])
                    (some false :: none :: padding) } := by
          rw [MachineDescription.runConfig_add]
          rw [singletonTerminalPairProbeDescription_step_start]
          rw [singletonTerminalPairProbeDescription_run_scan_to_terminal_from_left]
          simp [bits, logicalCellBits, List.reverse_append,
            tapeAtCells, Tape.move, Tape.moveLeft]
        rw [hentry]
        simpa [bits, logicalCellBits, List.map_append, List.append_assoc]
          using
            singletonTerminalPairProbeDescription_run_terminal_canonical_true_from_state2
              canonicalTarget rightBoundaryTarget pfxBits.reverse
              padding

/-!
## Terminal-bit facts for the false branch
-/

theorem logicalCellListBits_cons_append_none_terminal
    (cell : Option Bool) (rest : List (Option Bool)) :
    exists (pfx : Word Bool) (last : Option Bool),
      logicalCellListBits (cell :: rest ++ [none]) =
        List.append pfx
          (List.append (logicalCellBits last)
            (logicalCellBits none)) := by
  induction rest generalizing cell with
  | nil =>
      exact ⟨[], cell, by simp [logicalCellListBits]⟩
  | cons next tail ih =>
      rcases ih next with ⟨pfx, last, htail⟩
      refine ⟨List.append (logicalCellBits cell) pfx, last, ?_⟩
      change
        List.append (logicalCellBits cell)
            (logicalCellListBits (next :: tail ++ [none])) =
          List.append (List.append (logicalCellBits cell) pfx)
            (List.append (logicalCellBits last)
              (logicalCellBits none))
      rw [htail]
      simp [List.append_assoc]

theorem SingletonGuardSlackEndpointShape.canonical_singleton_bits_terminal_cell_guard
    (target : Tape Bool) :
    exists (pfxBits : Word Bool) (cell : Option Bool),
      logicalTapeBits (guardLogicalTape target) =
        List.append pfxBits
          (List.append (logicalCellBits cell)
            (logicalCellBits none)) := by
  cases target with
  | mk left head right =>
      rcases
          logicalCellListBits_cons_append_none_terminal
            head right with
        ⟨pfx, cell, htail⟩
      have hcellTail :
          List.append (logicalCellBits head)
              (logicalCellListBits (right ++ [none])) =
            List.append pfx
              (List.append (logicalCellBits cell)
                (logicalCellBits none)) := by
        simpa [logicalCellListBits] using! htail
      refine
        ⟨List.append
          (List.append
            (logicalCellListBits
              (List.reverse (left ++ [none])))
            [true, true])
          pfx, cell, ?_⟩
      have htail' :
          List.append (logicalCellBits head)
              (List.append (logicalCellListBits right)
                (logicalCellListBits [none])) =
            List.append pfx
              (List.append (logicalCellBits cell)
                (logicalCellBits none)) := by
        simpa [logicalCellListBits_append, List.append_assoc]
          using hcellTail
      simp [logicalTapeBits, guardLogicalTape, List.append_assoc]
      exact
        congrArg
          (fun tail =>
            List.append (logicalCellListBits (none :: left.reverse))
              (true :: true :: tail))
          htail'

theorem SingletonGuardSlackEndpointShape.rightBoundary_bits_terminal_head
    (left : List (Option Bool)) (head : Option Bool) :
    logicalTapeBits
        ({ left := left ++ [none], head := head, right := [] } :
          Tape Bool) =
      List.append (logicalCellListBits (none :: left.reverse))
        (List.append [true, true] (logicalCellBits head)) := by
  simp [logicalTapeBits, logicalCellListBits, List.reverse_append,
    List.append_assoc]

theorem SingletonGuardSlackEndpointShape.canonical_singleton_physical_terminal_bits
    (target : Tape Bool) :
    exists (pfxBits : Word Bool) (cell : Option Bool),
      encodedGuardedStructuredTapes [target] =
        tapeAtCells []
          (List.append tapeSeparatorCells
            (List.append
              (List.map some
                (List.append pfxBits
                  (List.append (logicalCellBits cell)
                    (logicalCellBits none))))
              tapeSeparatorCells)) := by
  rcases
      SingletonGuardSlackEndpointShape.canonical_singleton_bits_terminal_cell_guard
        target with
    ⟨pfxBits, cell, hbits⟩
  refine ⟨pfxBits, cell, ?_⟩
  simp [encodedGuardedStructuredTapes, guardLogicalTapes,
    encodedStructuredTapes, encodedStructuredTapeCells,
    logicalTapeCode_eq_map_some, hbits]

theorem SingletonGuardSlackEndpointShape.rightBoundary_physical_terminal_bits
    (left : List (Option Bool)) (head : Option Bool) :
    encodedStructuredTapes
        [({ left := left ++ [none], head := head, right := [] } :
          Tape Bool)] =
      tapeAtCells []
        (List.append tapeSeparatorCells
          (List.append
            (List.map some
              (List.append (logicalCellListBits (none :: left.reverse))
                (List.append [true, true] (logicalCellBits head))))
            tapeSeparatorCells)) := by
  simp [encodedStructuredTapes, encodedStructuredTapeCells,
    logicalTapeCode_eq_map_some,
    SingletonGuardSlackEndpointShape.rightBoundary_bits_terminal_head]

theorem singletonTerminalPairProbeDescription_reaches_canonical
    (canonicalTarget rightBoundaryTarget : Nat)
    (target : Tape Bool) :
    exists steps : Nat,
      (singletonTerminalPairProbeDescription
        canonicalTarget rightBoundaryTarget).runConfig steps
        { state :=
            (singletonTerminalPairProbeDescription
              canonicalTarget rightBoundaryTarget).start
          tape := encodedGuardedStructuredTapes [target] } =
      { state := canonicalTarget
        tape := encodedGuardedStructuredTapes [target] } := by
  rcases
      SingletonGuardSlackEndpointShape.canonical_singleton_physical_terminal_bits
        target with
    ⟨pfxBits, cell, hphysical⟩
  rw [hphysical]
  simpa [tapeSeparatorCells, List.map_append, List.append_assoc] using
    singletonTerminalPairProbeDescription_reaches_canonical_bits
      canonicalTarget rightBoundaryTarget pfxBits cell []

theorem singletonTerminalPairProbeDescription_reaches_canonical_cons
    (canonicalTarget rightBoundaryTarget : Nat)
    (target : Tape Bool) (rest : List (Tape Bool)) :
    exists steps : Nat,
      (singletonTerminalPairProbeDescription
        canonicalTarget rightBoundaryTarget).runConfig steps
        { state :=
            (singletonTerminalPairProbeDescription
              canonicalTarget rightBoundaryTarget).start
          tape := encodedStructuredTapes (guardLogicalTape target :: rest) } =
      { state := canonicalTarget
        tape := encodedStructuredTapes (guardLogicalTape target :: rest) } := by
  rcases
      SingletonGuardSlackEndpointShape.canonical_singleton_bits_terminal_cell_guard
        target with
    ⟨pfxBits, cell, hbits⟩
  rcases encodedStructuredTapeCells_startsWith_separator rest with
    ⟨padding, hpadding⟩
  simpa [encodedStructuredTapes, encodedStructuredTapeCells,
    logicalTapeCode_eq_map_some, hbits, hpadding, tapeSeparatorCells,
    List.map_append, List.append_assoc] using
    singletonTerminalPairProbeDescription_reaches_canonical_bits
      canonicalTarget rightBoundaryTarget pfxBits cell padding

theorem singletonTerminalPairProbeDescription_reaches_rightBoundary
    (canonicalTarget rightBoundaryTarget : Nat)
    (left : List (Option Bool)) (head : Option Bool) :
    exists steps : Nat,
      (singletonTerminalPairProbeDescription
        canonicalTarget rightBoundaryTarget).runConfig steps
        { state :=
            (singletonTerminalPairProbeDescription
              canonicalTarget rightBoundaryTarget).start
          tape :=
            encodedStructuredTapes
              [({ left := left ++ [none], head := head, right := [] } :
                Tape Bool)] } =
      { state := rightBoundaryTarget
        tape :=
          encodedStructuredTapes
            [({ left := left ++ [none], head := head, right := [] } :
              Tape Bool)] } := by
  rw [
    SingletonGuardSlackEndpointShape.rightBoundary_physical_terminal_bits
      left head]
  simpa [tapeSeparatorCells, List.map_append, List.append_assoc] using
    singletonTerminalPairProbeDescription_reaches_rightBoundary_bits
      canonicalTarget rightBoundaryTarget
      (logicalCellListBits (none :: left.reverse)) head []

theorem singletonTerminalPairProbeDescription_reaches_rightBoundary_cons
    (canonicalTarget rightBoundaryTarget : Nat)
    (left : List (Option Bool)) (head : Option Bool)
    (rest : List (Tape Bool)) :
    exists steps : Nat,
      (singletonTerminalPairProbeDescription
        canonicalTarget rightBoundaryTarget).runConfig steps
        { state :=
            (singletonTerminalPairProbeDescription
              canonicalTarget rightBoundaryTarget).start
          tape :=
            encodedStructuredTapes
              (({ left := left ++ [none], head := head, right := [] } :
                Tape Bool) :: rest) } =
      { state := rightBoundaryTarget
        tape :=
          encodedStructuredTapes
            (({ left := left ++ [none], head := head, right := [] } :
              Tape Bool) :: rest) } := by
  rcases encodedStructuredTapeCells_startsWith_separator rest with
    ⟨padding, hpadding⟩
  simpa [encodedStructuredTapes, encodedStructuredTapeCells,
    logicalTapeCode_eq_map_some,
    SingletonGuardSlackEndpointShape.rightBoundary_bits_terminal_head,
    hpadding, tapeSeparatorCells, List.map_append, List.append_assoc] using
    singletonTerminalPairProbeDescription_reaches_rightBoundary_bits
      canonicalTarget rightBoundaryTarget
      (logicalCellListBits (none :: left.reverse)) head padding

theorem singletonTerminalPairProbeDescription_reaches_of_afterOpening_read_false
    (canonicalTarget rightBoundaryTarget : Nat)
    {target : List (Tape Bool)} {physical : Tape Bool}
    (hshape : SingletonGuardSlackEndpointShape target physical)
    (hread : Tape.read (Tape.moveRight physical) = some false) :
    (exists (targetTape : Tape Bool) (steps : Nat),
      target = [targetTape] ∧
        physical = encodedGuardedStructuredTapes [targetTape] ∧
        (singletonTerminalPairProbeDescription
          canonicalTarget rightBoundaryTarget).runConfig steps
          { state :=
              (singletonTerminalPairProbeDescription
                canonicalTarget rightBoundaryTarget).start
            tape := physical } =
        { state := canonicalTarget
          tape := physical }) ∨
      exists (left : List (Option Bool)) (head : Option Bool)
          (steps : Nat),
        target =
          [({ left := left, head := head, right := [] } : Tape Bool)] ∧
          physical =
            encodedStructuredTapes
              [({ left := left ++ [none], head := head, right := [] } :
                Tape Bool)] ∧
          (singletonTerminalPairProbeDescription
            canonicalTarget rightBoundaryTarget).runConfig steps
            { state :=
                (singletonTerminalPairProbeDescription
                  canonicalTarget rightBoundaryTarget).start
              tape := physical } =
          { state := rightBoundaryTarget
            tape := physical } := by
  cases
      SingletonGuardSlackEndpointShape.afterOpening_read_false_cases
        hshape hread with
  | inl hcanonical =>
      rcases hcanonical with ⟨targetTape, htarget, hphysical⟩
      rcases
          singletonTerminalPairProbeDescription_reaches_canonical
            canonicalTarget rightBoundaryTarget targetTape with
        ⟨steps, hrun⟩
      left
      refine ⟨targetTape, steps, htarget, hphysical, ?_⟩
      rw [hphysical]
      exact hrun
  | inr hright =>
      rcases hright with ⟨left, head, htarget, hphysical⟩
      rcases
          singletonTerminalPairProbeDescription_reaches_rightBoundary
            canonicalTarget rightBoundaryTarget left head with
        ⟨steps, hrun⟩
      right
      refine ⟨left, head, steps, htarget, hphysical, ?_⟩
      rw [hphysical]
      exact hrun


end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC

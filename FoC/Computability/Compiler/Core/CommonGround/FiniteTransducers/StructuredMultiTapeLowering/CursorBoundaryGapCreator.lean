import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.CursorBoundaryGap

set_option doc.verso true

/-!
# Boundary suffix-gap creator core

This module starts the concrete machine side of the suffix-preserving singleton
head refresh path.  The first leaf is an online two-cell right-shift core.  It
scans from the opening separator to the separator after the first segment
payload, writes two blanks there, and carries overwritten cells two positions
to the right until it observes the trailing all-blank region.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

def headSuffixGapShiftPairState
    (first second : Option Bool) : Nat :=
  match first, second with
  | none, none => 3
  | none, some false => 4
  | none, some true => 5
  | some false, none => 6
  | some false, some false => 7
  | some false, some true => 8
  | some true, none => 9
  | some true, some false => 10
  | some true, some true => 11

def headSuffixGapShiftHalt : Nat :=
  12

def headSuffixGapShiftDescription : MachineDescription where
  stateCount := 13
  start := 0
  halt := headSuffixGapShiftHalt
  transitions :=
    [ transition 0 none none Direction.right 1
    , transition 1 (some false) (some false) Direction.right 1
    , transition 1 (some true) (some true) Direction.right 1
    , transition 1 none none Direction.right 2
    , transition 2 none none Direction.right
        (headSuffixGapShiftPairState none none)
    , transition 2 (some false) none Direction.right
        (headSuffixGapShiftPairState none (some false))
    , transition 2 (some true) none Direction.right
        (headSuffixGapShiftPairState none (some true))
    , transition (headSuffixGapShiftPairState none none)
        none none Direction.left headSuffixGapShiftHalt
    , transition (headSuffixGapShiftPairState none none)
        (some false) none Direction.right
        (headSuffixGapShiftPairState none (some false))
    , transition (headSuffixGapShiftPairState none none)
        (some true) none Direction.right
        (headSuffixGapShiftPairState none (some true))
    , transition (headSuffixGapShiftPairState none (some false))
        none none Direction.right
        (headSuffixGapShiftPairState (some false) none)
    , transition (headSuffixGapShiftPairState none (some false))
        (some false) none Direction.right
        (headSuffixGapShiftPairState (some false) (some false))
    , transition (headSuffixGapShiftPairState none (some false))
        (some true) none Direction.right
        (headSuffixGapShiftPairState (some false) (some true))
    , transition (headSuffixGapShiftPairState none (some true))
        none none Direction.right
        (headSuffixGapShiftPairState (some true) none)
    , transition (headSuffixGapShiftPairState none (some true))
        (some false) none Direction.right
        (headSuffixGapShiftPairState (some true) (some false))
    , transition (headSuffixGapShiftPairState none (some true))
        (some true) none Direction.right
        (headSuffixGapShiftPairState (some true) (some true))
    , transition (headSuffixGapShiftPairState (some false) none)
        none (some false) Direction.right
        (headSuffixGapShiftPairState none none)
    , transition (headSuffixGapShiftPairState (some false) none)
        (some false) (some false) Direction.right
        (headSuffixGapShiftPairState none (some false))
    , transition (headSuffixGapShiftPairState (some false) none)
        (some true) (some false) Direction.right
        (headSuffixGapShiftPairState none (some true))
    , transition (headSuffixGapShiftPairState (some false) (some false))
        none (some false) Direction.right
        (headSuffixGapShiftPairState (some false) none)
    , transition (headSuffixGapShiftPairState (some false) (some false))
        (some false) (some false) Direction.right
        (headSuffixGapShiftPairState (some false) (some false))
    , transition (headSuffixGapShiftPairState (some false) (some false))
        (some true) (some false) Direction.right
        (headSuffixGapShiftPairState (some false) (some true))
    , transition (headSuffixGapShiftPairState (some false) (some true))
        none (some false) Direction.right
        (headSuffixGapShiftPairState (some true) none)
    , transition (headSuffixGapShiftPairState (some false) (some true))
        (some false) (some false) Direction.right
        (headSuffixGapShiftPairState (some true) (some false))
    , transition (headSuffixGapShiftPairState (some false) (some true))
        (some true) (some false) Direction.right
        (headSuffixGapShiftPairState (some true) (some true))
    , transition (headSuffixGapShiftPairState (some true) none)
        none (some true) Direction.right
        (headSuffixGapShiftPairState none none)
    , transition (headSuffixGapShiftPairState (some true) none)
        (some false) (some true) Direction.right
        (headSuffixGapShiftPairState none (some false))
    , transition (headSuffixGapShiftPairState (some true) none)
        (some true) (some true) Direction.right
        (headSuffixGapShiftPairState none (some true))
    , transition (headSuffixGapShiftPairState (some true) (some false))
        none (some true) Direction.right
        (headSuffixGapShiftPairState (some false) none)
    , transition (headSuffixGapShiftPairState (some true) (some false))
        (some false) (some true) Direction.right
        (headSuffixGapShiftPairState (some false) (some false))
    , transition (headSuffixGapShiftPairState (some true) (some false))
        (some true) (some true) Direction.right
        (headSuffixGapShiftPairState (some false) (some true))
    , transition (headSuffixGapShiftPairState (some true) (some true))
        none (some true) Direction.right
        (headSuffixGapShiftPairState (some true) none)
    , transition (headSuffixGapShiftPairState (some true) (some true))
        (some false) (some true) Direction.right
        (headSuffixGapShiftPairState (some true) (some false))
    , transition (headSuffixGapShiftPairState (some true) (some true))
        (some true) (some true) Direction.right
        (headSuffixGapShiftPairState (some true) (some true)) ]

theorem headSuffixGapShiftDescription_wellFormed :
    headSuffixGapShiftDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := headSuffixGapShiftDescription.transitions)
      (stateCount := headSuffixGapShiftDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := headSuffixGapShiftDescription.transitions)
      (by decide)

theorem headSuffixGapShiftDescription_haltTransitionFree :
    headSuffixGapShiftDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := headSuffixGapShiftDescription.transitions)
    (state := headSuffixGapShiftDescription.halt)
    (by decide)

theorem headSuffixGapShiftDescription_subroutineReady :
    headSuffixGapShiftDescription.SubroutineReady :=
  ⟨headSuffixGapShiftDescription_wellFormed,
    headSuffixGapShiftDescription_haltTransitionFree⟩

theorem headSuffixGapShiftDescription_run_opening
    (bits : Word Bool) (suffixTail : List (Option Bool)) :
    headSuffixGapShiftDescription.runConfig 1
        { state := headSuffixGapShiftDescription.start
          tape :=
            tapeAtCells []
              (none :: List.append (bits.map some)
                (none :: suffixTail)) } =
      { state := 1
        tape :=
          tapeAtCells [none]
            (List.append (bits.map some) (none :: suffixTail)) } := by
  cases bits <;> cases suffixTail <;>
    simp [headSuffixGapShiftDescription, MachineDescription.runConfig,
      MachineDescription.stepConfig, MachineDescription.lookupTransition,
      MachineDescription.Matches, transition, tapeAtCells, Tape.read, Tape.write,
      Tape.move, Tape.moveRight]

theorem headSuffixGapShiftDescription_run_payloadScan
    (bits processed : Word Bool) (leftBase suffixTail : List (Option Bool)) :
    headSuffixGapShiftDescription.runConfig bits.length
        { state := 1
          tape :=
            tapeAtCells
              (List.append (processed.reverse.map some) leftBase)
              (List.append (bits.map some) (none :: suffixTail)) } =
      { state := 1
        tape :=
          tapeAtCells
            (List.append ((List.append processed bits).reverse.map some)
              leftBase)
            (none :: suffixTail) } := by
  induction bits generalizing processed with
  | nil =>
      simp [MachineDescription.runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp [Nat.add_comm]]
      rw [MachineDescription.runConfig_add]
      have hstep :
          headSuffixGapShiftDescription.runConfig 1
              { state := 1
                tape :=
                  tapeAtCells
                    (List.append (processed.reverse.map some) leftBase)
                    (List.append ((bit :: rest).map some)
                      (none :: suffixTail)) } =
            { state := 1
              tape :=
                tapeAtCells
                  (some bit ::
                    List.append (processed.reverse.map some) leftBase)
                  (List.append (rest.map some) (none :: suffixTail)) } := by
        cases bit <;> cases rest <;> cases suffixTail <;>
          simp [headSuffixGapShiftDescription,
            MachineDescription.runConfig, MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            transition, tapeAtCells, Tape.read, Tape.write, Tape.move,
            Tape.moveRight]
      rw [hstep]
      simpa [List.reverse_append, List.map_append, List.append_assoc]
        using ih (List.append processed [bit])

theorem headSuffixGapShiftDescription_run_to_boundary
    (bits : Word Bool) (suffixTail : List (Option Bool)) :
    headSuffixGapShiftDescription.runConfig (bits.length + 2)
        { state := headSuffixGapShiftDescription.start
          tape :=
            tapeAtCells []
              (none :: List.append (bits.map some)
                (none :: suffixTail)) } =
      { state := 2
        tape :=
          tapeAtCells
            (none :: List.append (bits.reverse.map some) [none])
            suffixTail } := by
  rw [show bits.length + 2 = 1 + (bits.length + 1) by lia]
  rw [MachineDescription.runConfig_add]
  rw [headSuffixGapShiftDescription_run_opening]
  rw [show bits.length + 1 = bits.length + 1 by rfl]
  rw [MachineDescription.runConfig_add]
  have hscan :
      headSuffixGapShiftDescription.runConfig bits.length
          { state := 1
            tape :=
              tapeAtCells [none]
                (List.append (bits.map some) (none :: suffixTail)) } =
        { state := 1
          tape :=
            tapeAtCells
              (List.append (bits.reverse.map some) [none])
              (none :: suffixTail) } := by
    simpa using
      headSuffixGapShiftDescription_run_payloadScan bits [] [none]
        suffixTail
  rw [hscan]
  cases suffixTail <;>
    simp [headSuffixGapShiftDescription, MachineDescription.runConfig,
      MachineDescription.stepConfig, MachineDescription.lookupTransition,
      MachineDescription.Matches, transition, tapeAtCells, Tape.read, Tape.write,
      Tape.move, Tape.moveRight]

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC

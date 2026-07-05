import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.StructuredRefresh
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.FiniteMachineTactics

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

private theorem singletonTerminalPairProbeDescription_step_start_withPrefix
    (canonicalTarget rightBoundaryTarget : Nat)
    (base : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).runConfig 1
        { state :=
            (singletonTerminalPairProbeDescription
              canonicalTarget rightBoundaryTarget).start
          tape :=
            tapeAtCells base
              (none ::
                List.append (bits.map some) (none :: padding)) } =
      { state := 1
        tape :=
          tapeAtCells (none :: base)
            (List.append (bits.map some) (none :: padding)) } := by
  cases bits with
  | nil =>
      cases base <;> cases padding <;>
        machine_step [singletonTerminalPairProbeDescription]
  | cons bit rest =>
      cases bit <;> cases rest <;> cases base <;> cases padding <;>
        machine_step [singletonTerminalPairProbeDescription]

private theorem singletonTerminalPairProbeDescription_step_rewind_canonical_finish_withPrefix
    (canonicalTarget rightBoundaryTarget : Nat)
    (base : List (Option Bool)) (current : Bool)
    (rightTail : List (Option Bool)) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).runConfig 2
        { state := 7
          tape :=
            tapeAtCells base (none :: some current :: rightTail) } =
      { state := canonicalTarget
        tape :=
          tapeAtCells base (none :: some current :: rightTail) } := by
  cases base <;> cases current <;> cases rightTail <;>
    machine_step [singletonTerminalPairProbeDescription]

private theorem singletonTerminalPairProbeDescription_step_rewind_right_finish_withPrefix
    (canonicalTarget rightBoundaryTarget : Nat)
    (base : List (Option Bool)) (current : Bool)
    (rightTail : List (Option Bool)) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).runConfig 2
        { state := 9
          tape :=
            tapeAtCells base (none :: some current :: rightTail) } =
      { state := rightBoundaryTarget
        tape :=
          tapeAtCells base (none :: some current :: rightTail) } := by
  cases base <;> cases current <;> cases rightTail <;>
    machine_step [singletonTerminalPairProbeDescription]

private theorem singletonTerminalPairProbeDescription_run_rewind_canonical_withPrefix
    (canonicalTarget rightBoundaryTarget : Nat)
    (base : List (Option Bool)) (leftStack : Word Bool)
    (current : Bool) (rightTail : List (Option Bool)) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).runConfig
        (leftStack.length + 3)
        { state := 7
          tape :=
            tapeAtCells
              (List.append (leftStack.map some) (none :: base))
              (some current :: rightTail) } =
      { state := canonicalTarget
        tape :=
          tapeAtCells base
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
                  (List.append (([] : Word Bool).map some) (none :: base))
                  (some current :: rightTail) } =
          { state := 7
            tape :=
              tapeAtCells base (none :: some current :: rightTail) } := by
        cases current <;> cases base <;> cases rightTail <;>
          machine_step [singletonTerminalPairProbeDescription]
      rw [hstep]
      simpa using
        singletonTerminalPairProbeDescription_step_rewind_canonical_finish_withPrefix
          canonicalTarget rightBoundaryTarget base current rightTail
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
                  (List.append ((next :: rest).map some) (none :: base))
                  (some current :: rightTail) } =
          { state := 7
            tape :=
              tapeAtCells
                (List.append (rest.map some) (none :: base))
                (some next :: some current :: rightTail) } := by
        cases next <;> cases current <;> cases base <;>
          cases rightTail <;>
          machine_step [singletonTerminalPairProbeDescription]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc]
        using ih next (some current :: rightTail)

private theorem singletonTerminalPairProbeDescription_run_rewind_right_withPrefix
    (canonicalTarget rightBoundaryTarget : Nat)
    (base : List (Option Bool)) (leftStack : Word Bool)
    (current : Bool) (rightTail : List (Option Bool)) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).runConfig
        (leftStack.length + 3)
        { state := 9
          tape :=
            tapeAtCells
              (List.append (leftStack.map some) (none :: base))
              (some current :: rightTail) } =
      { state := rightBoundaryTarget
        tape :=
          tapeAtCells base
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
                  (List.append (([] : Word Bool).map some) (none :: base))
                  (some current :: rightTail) } =
          { state := 9
            tape :=
              tapeAtCells base (none :: some current :: rightTail) } := by
        cases current <;> cases base <;> cases rightTail <;>
          machine_step [singletonTerminalPairProbeDescription]
      rw [hstep]
      simpa using
        singletonTerminalPairProbeDescription_step_rewind_right_finish_withPrefix
          canonicalTarget rightBoundaryTarget base current rightTail
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
                  (List.append ((next :: rest).map some) (none :: base))
                  (some current :: rightTail) } =
          { state := 9
            tape :=
              tapeAtCells
                (List.append (rest.map some) (none :: base))
                (some next :: some current :: rightTail) } := by
        cases next <;> cases current <;> cases base <;>
          cases rightTail <;>
          machine_step [singletonTerminalPairProbeDescription]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc]
        using ih next (some current :: rightTail)

private theorem singletonTerminalPairProbeDescription_run_rewind_canonical_after_left_withPrefix
    (canonicalTarget rightBoundaryTarget : Nat)
    (base : List (Option Bool)) (leftStack : Word Bool)
    (current : Bool) (rightTail : List (Option Bool)) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).runConfig
        (leftStack.length + 2)
        { state := 7
          tape :=
            Tape.move Direction.left
              (tapeAtCells
                (List.append (leftStack.map some) (none :: base))
                (some current :: rightTail)) } =
      { state := canonicalTarget
        tape :=
          tapeAtCells base
            (none ::
              List.append (leftStack.reverse.map some)
                (some current :: rightTail)) } := by
  cases leftStack with
  | nil =>
      simpa [Tape.move, Tape.moveLeft, tapeAtCells] using
        singletonTerminalPairProbeDescription_step_rewind_canonical_finish_withPrefix
          canonicalTarget rightBoundaryTarget base current rightTail
  | cons next rest =>
      rw [show (next :: rest).length + 2 = rest.length + 3 by
        simp]
      simpa [Tape.move, Tape.moveLeft, tapeAtCells, List.reverse_cons,
        List.map_append, List.append_assoc] using
        singletonTerminalPairProbeDescription_run_rewind_canonical_withPrefix
          canonicalTarget rightBoundaryTarget base rest next
          (some current :: rightTail)

private theorem singletonTerminalPairProbeDescription_run_terminal_right_from_state2_withPrefix
    (canonicalTarget rightBoundaryTarget : Nat)
    (base : List (Option Bool)) (pfxRev : Word Bool)
    (b0 b1 : Bool) (padding : List (Option Bool)) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).runConfig
        (pfxRev.length + 8)
        { state := 2
          tape :=
            tapeAtCells
              (some b0 :: some true :: some true ::
                List.append (pfxRev.map some) (none :: base))
              (some b1 :: none :: padding) } =
      { state := rightBoundaryTarget
        tape :=
          tapeAtCells base
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
                List.append (pfxRev.map some) (none :: base))
              (some b1 :: none :: padding) } =
      { state := 9
        tape :=
          tapeAtCells
            (List.append (pfxRev.map some) (none :: base))
            (some true :: some true :: some b0 :: some b1 ::
              none :: padding) } := by
    cases b0 <;> cases b1 <;> cases base <;> cases padding <;>
      machine_step [singletonTerminalPairProbeDescription]
  rw [hterminal]
  simpa [List.append_assoc] using
    singletonTerminalPairProbeDescription_run_rewind_right_withPrefix
      canonicalTarget rightBoundaryTarget base pfxRev true
      (some true :: some b0 :: some b1 :: none :: padding)

private theorem singletonTerminalPairProbeDescription_run_terminal_canonical_false_from_state2_withPrefix
    (canonicalTarget rightBoundaryTarget : Nat)
    (base : List (Option Bool)) (pfxRev : Word Bool)
    (c1 : Bool) (padding : List (Option Bool)) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).runConfig
        (pfxRev.length + 6)
        { state := 2
          tape :=
            tapeAtCells
              (some false :: some c1 :: some false ::
                List.append (pfxRev.map some) (none :: base))
              (some false :: none :: padding) } =
      { state := canonicalTarget
        tape :=
          tapeAtCells base
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
                List.append (pfxRev.map some) (none :: base))
              (some false :: none :: padding) } =
      { state := 7
        tape :=
          Tape.move Direction.left
            (tapeAtCells
              (List.append (pfxRev.map some) (none :: base))
              (some false :: some c1 :: some false :: some false ::
                none :: padding)) } := by
    cases c1 <;> cases base <;> cases padding <;>
      machine_step [singletonTerminalPairProbeDescription]
  rw [hterminal]
  simpa [List.append_assoc] using
    singletonTerminalPairProbeDescription_run_rewind_canonical_after_left_withPrefix
      canonicalTarget rightBoundaryTarget base pfxRev false
      (some c1 :: some false :: some false :: none :: padding)

private theorem singletonTerminalPairProbeDescription_run_terminal_canonical_true_from_state2_withPrefix
    (canonicalTarget rightBoundaryTarget : Nat)
    (base : List (Option Bool)) (pfxRev : Word Bool)
    (padding : List (Option Bool)) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).runConfig
        (pfxRev.length + 8)
        { state := 2
          tape :=
            tapeAtCells
              (some false :: some false :: some true ::
                List.append (pfxRev.map some) (none :: base))
              (some false :: none :: padding) } =
      { state := canonicalTarget
        tape :=
          tapeAtCells base
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
                List.append (pfxRev.map some) (none :: base))
              (some false :: none :: padding) } =
      { state := 7
        tape :=
          tapeAtCells
            (List.append (pfxRev.map some) (none :: base))
            (some true :: some false :: some false :: some false ::
              none :: padding) } := by
    cases base <;> cases padding <;>
      machine_step [singletonTerminalPairProbeDescription]
  rw [hterminal]
  simpa [List.append_assoc] using
    singletonTerminalPairProbeDescription_run_rewind_canonical_withPrefix
      canonicalTarget rightBoundaryTarget base pfxRev true
      (some false :: some false :: some false :: none :: padding)

theorem singletonTerminalPairProbeDescription_reaches_rightBoundary_bits_withPrefix
    (canonicalTarget rightBoundaryTarget : Nat)
    (base : List (Option Bool)) (pfxBits : Word Bool)
    (head : Option Bool) (padding : List (Option Bool)) :
    exists steps : Nat,
      (singletonTerminalPairProbeDescription
        canonicalTarget rightBoundaryTarget).runConfig steps
        { state :=
            (singletonTerminalPairProbeDescription
              canonicalTarget rightBoundaryTarget).start
          tape :=
            tapeAtCells base
              (none ::
                List.append
                  ((List.append pfxBits
                    (List.append [true, true]
                      (logicalCellBits head))).map some)
                  (none :: padding)) } =
      { state := rightBoundaryTarget
        tape :=
          tapeAtCells base
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
                tapeAtCells base
                  (none ::
                    List.append (bits.map some) (none :: padding)) } =
          { state := rightBoundaryTarget
            tape :=
              tapeAtCells base
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
                  tapeAtCells base
                    (none ::
                      List.append (bits.map some) (none :: padding)) } =
            { state := 2
              tape :=
                tapeAtCells
                  (some false :: some true :: some true ::
                    List.append (pfxBits.reverse.map some) (none :: base))
                  (some false :: none :: padding) } := by
        rw [MachineDescription.runConfig_add]
        rw [singletonTerminalPairProbeDescription_step_start_withPrefix]
        rw [singletonTerminalPairProbeDescription_run_scan_to_terminal_from_left]
        simp [bits, logicalCellBits, List.reverse_append,
          tapeAtCells, Tape.move, Tape.moveLeft]
      rw [hentry]
      simpa [bits, logicalCellBits, List.map_append, List.append_assoc]
        using
          singletonTerminalPairProbeDescription_run_terminal_right_from_state2_withPrefix
            canonicalTarget rightBoundaryTarget base pfxBits.reverse
            false false padding
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
                  tapeAtCells base
                    (none ::
                      List.append (bits.map some) (none :: padding)) } =
            { state := rightBoundaryTarget
              tape :=
                tapeAtCells base
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
                    tapeAtCells base
                      (none ::
                        List.append (bits.map some) (none :: padding)) } =
              { state := 2
                tape :=
                  tapeAtCells
                    (some false :: some true :: some true ::
                      List.append (pfxBits.reverse.map some) (none :: base))
                    (some true :: none :: padding) } := by
          rw [MachineDescription.runConfig_add]
          rw [singletonTerminalPairProbeDescription_step_start_withPrefix]
          rw [singletonTerminalPairProbeDescription_run_scan_to_terminal_from_left]
          simp [bits, logicalCellBits, List.reverse_append,
            tapeAtCells, Tape.move, Tape.moveLeft]
        rw [hentry]
        simpa [bits, logicalCellBits, List.map_append, List.append_assoc]
          using
            singletonTerminalPairProbeDescription_run_terminal_right_from_state2_withPrefix
              canonicalTarget rightBoundaryTarget base pfxBits.reverse
              false true padding
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
                  tapeAtCells base
                    (none ::
                      List.append (bits.map some) (none :: padding)) } =
            { state := rightBoundaryTarget
              tape :=
                tapeAtCells base
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
                    tapeAtCells base
                      (none ::
                        List.append (bits.map some) (none :: padding)) } =
              { state := 2
                tape :=
                  tapeAtCells
                    (some true :: some true :: some true ::
                      List.append (pfxBits.reverse.map some) (none :: base))
                    (some false :: none :: padding) } := by
          rw [MachineDescription.runConfig_add]
          rw [singletonTerminalPairProbeDescription_step_start_withPrefix]
          rw [singletonTerminalPairProbeDescription_run_scan_to_terminal_from_left]
          simp [bits, logicalCellBits, List.reverse_append,
            tapeAtCells, Tape.move, Tape.moveLeft]
        rw [hentry]
        simpa [bits, logicalCellBits, List.map_append, List.append_assoc]
          using
          singletonTerminalPairProbeDescription_run_terminal_right_from_state2_withPrefix
            canonicalTarget rightBoundaryTarget base pfxBits.reverse
            true false padding

theorem singletonTerminalPairProbeDescription_reaches_canonical_bits_withPrefix
    (canonicalTarget rightBoundaryTarget : Nat)
    (base : List (Option Bool)) (pfxBits : Word Bool)
    (cell : Option Bool) (padding : List (Option Bool)) :
    exists steps : Nat,
      (singletonTerminalPairProbeDescription
        canonicalTarget rightBoundaryTarget).runConfig steps
        { state :=
            (singletonTerminalPairProbeDescription
              canonicalTarget rightBoundaryTarget).start
          tape :=
            tapeAtCells base
              (none ::
                List.append
                  ((List.append pfxBits
                    (List.append (logicalCellBits cell)
                      (logicalCellBits none))).map some)
                  (none :: padding)) } =
      { state := canonicalTarget
        tape :=
          tapeAtCells base
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
                tapeAtCells base
                  (none ::
                    List.append (bits.map some) (none :: padding)) } =
          { state := canonicalTarget
            tape :=
              tapeAtCells base
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
                  tapeAtCells base
                    (none ::
                      List.append (bits.map some) (none :: padding)) } =
            { state := 2
              tape :=
                tapeAtCells
                  (some false :: some false :: some false ::
                    List.append (pfxBits.reverse.map some) (none :: base))
                  (some false :: none :: padding) } := by
        rw [MachineDescription.runConfig_add]
        rw [singletonTerminalPairProbeDescription_step_start_withPrefix]
        rw [singletonTerminalPairProbeDescription_run_scan_to_terminal_from_left]
        simp [bits, logicalCellBits, List.reverse_append,
          tapeAtCells, Tape.move, Tape.moveLeft]
      rw [hentry]
      simpa [bits, logicalCellBits, List.map_append, List.append_assoc]
        using
          singletonTerminalPairProbeDescription_run_terminal_canonical_false_from_state2_withPrefix
            canonicalTarget rightBoundaryTarget base pfxBits.reverse false
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
                  tapeAtCells base
                    (none ::
                      List.append (bits.map some) (none :: padding)) } =
            { state := canonicalTarget
              tape :=
                tapeAtCells base
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
                    tapeAtCells base
                      (none ::
                        List.append (bits.map some) (none :: padding)) } =
              { state := 2
                tape :=
                  tapeAtCells
                    (some false :: some true :: some false ::
                      List.append (pfxBits.reverse.map some) (none :: base))
                    (some false :: none :: padding) } := by
          rw [MachineDescription.runConfig_add]
          rw [singletonTerminalPairProbeDescription_step_start_withPrefix]
          rw [singletonTerminalPairProbeDescription_run_scan_to_terminal_from_left]
          simp [bits, logicalCellBits, List.reverse_append,
            tapeAtCells, Tape.move, Tape.moveLeft]
        rw [hentry]
        simpa [bits, logicalCellBits, List.map_append, List.append_assoc]
          using
            singletonTerminalPairProbeDescription_run_terminal_canonical_false_from_state2_withPrefix
              canonicalTarget rightBoundaryTarget base pfxBits.reverse true
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
                  tapeAtCells base
                    (none ::
                      List.append (bits.map some) (none :: padding)) } =
            { state := canonicalTarget
              tape :=
                tapeAtCells base
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
                    tapeAtCells base
                      (none ::
                        List.append (bits.map some) (none :: padding)) } =
              { state := 2
                tape :=
                  tapeAtCells
                    (some false :: some false :: some true ::
                      List.append (pfxBits.reverse.map some) (none :: base))
                    (some false :: none :: padding) } := by
          rw [MachineDescription.runConfig_add]
          rw [singletonTerminalPairProbeDescription_step_start_withPrefix]
          rw [singletonTerminalPairProbeDescription_run_scan_to_terminal_from_left]
          simp [bits, logicalCellBits, List.reverse_append,
            tapeAtCells, Tape.move, Tape.moveLeft]
        rw [hentry]
        simpa [bits, logicalCellBits, List.map_append, List.append_assoc]
          using
            singletonTerminalPairProbeDescription_run_terminal_canonical_true_from_state2_withPrefix
              canonicalTarget rightBoundaryTarget base pfxBits.reverse
              padding

theorem singletonTerminalPairProbeDescription_reaches_selectedCanonical
    (canonicalTarget rightBoundaryTarget : Nat)
    (encodedPrefix : List (Option Bool))
    (target : Tape Bool) (rest : List (Tape Bool)) :
    exists steps : Nat,
      (singletonTerminalPairProbeDescription
        canonicalTarget rightBoundaryTarget).runConfig steps
        { state :=
            (singletonTerminalPairProbeDescription
              canonicalTarget rightBoundaryTarget).start
          tape :=
            tapeAtEncodedSplit encodedPrefix
              (encodedStructuredTapeCells
                (guardLogicalTape target :: rest)) } =
      { state := canonicalTarget
        tape :=
          tapeAtEncodedSplit encodedPrefix
            (encodedStructuredTapeCells
              (guardLogicalTape target :: rest)) } := by
  rcases
      SingletonGuardSlackEndpointShape.canonical_singleton_bits_terminal_cell_guard
        target with
    ⟨pfxBits, cell, hbits⟩
  rcases encodedStructuredTapeCells_startsWith_separator rest with
    ⟨padding, hpadding⟩
  simpa [tapeAtEncodedSplit, encodedStructuredTapeCells,
    logicalTapeCode_eq_map_some, hbits, hpadding, tapeSeparatorCells,
    List.map_append, List.append_assoc] using
    singletonTerminalPairProbeDescription_reaches_canonical_bits_withPrefix
      canonicalTarget rightBoundaryTarget encodedPrefix.reverse pfxBits
      cell padding

theorem singletonTerminalPairProbeDescription_reaches_selectedRightBoundary
    (canonicalTarget rightBoundaryTarget : Nat)
    (encodedPrefix : List (Option Bool))
    (left : List (Option Bool)) (head : Option Bool)
    (rest : List (Tape Bool)) :
    exists steps : Nat,
      (singletonTerminalPairProbeDescription
        canonicalTarget rightBoundaryTarget).runConfig steps
        { state :=
            (singletonTerminalPairProbeDescription
              canonicalTarget rightBoundaryTarget).start
          tape :=
            tapeAtEncodedSplit encodedPrefix
              (encodedStructuredTapeCells
                (({ left := left ++ [none], head := head,
                    right := [] } : Tape Bool) :: rest)) } =
      { state := rightBoundaryTarget
        tape :=
          tapeAtEncodedSplit encodedPrefix
            (encodedStructuredTapeCells
              (({ left := left ++ [none], head := head,
                  right := [] } : Tape Bool) :: rest)) } := by
  rcases encodedStructuredTapeCells_startsWith_separator rest with
    ⟨padding, hpadding⟩
  simpa [tapeAtEncodedSplit, encodedStructuredTapeCells,
    logicalTapeCode_eq_map_some,
    SingletonGuardSlackEndpointShape.rightBoundary_bits_terminal_head,
    hpadding, tapeSeparatorCells, List.map_append, List.append_assoc] using
    singletonTerminalPairProbeDescription_reaches_rightBoundary_bits_withPrefix
      canonicalTarget rightBoundaryTarget encodedPrefix.reverse
      (logicalCellListBits (none :: left.reverse)) head padding

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC

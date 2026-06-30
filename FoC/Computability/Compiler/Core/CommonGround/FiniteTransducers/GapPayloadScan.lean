import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.Basic

set_option doc.verso true

/-!
# Gap-to-payload right-edge scanner

This module provides a fixed pass used after a variable-width field has been
erased to blanks.  The machine starts at the left edge of the blank gap, moves
right across the gap, then scans a nonempty Boolean payload and halts on the
last payload bit.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers

def rightBlankGapPayloadScanDescription : MachineDescription where
  stateCount := 3
  start := 0
  halt := 2
  transitions :=
    [ transition 0 none none Direction.right 0
    , transition 0 (some false) (some false) Direction.right 1
    , transition 0 (some true) (some true) Direction.right 1
    , transition 1 (some false) (some false) Direction.right 1
    , transition 1 (some true) (some true) Direction.right 1
    , transition 1 none none Direction.left 2 ]

def rightBlankGapPayloadScanSourceTape
    (baseLeft : List (Option Bool)) (gap : Nat)
    (current : Bool) (payloadRest : Word Bool)
    (padding : List (Option Bool)) : Tape Bool :=
  tapeAtCells baseLeft
    (List.append
      (List.replicate gap (none : Option Bool))
      (some current :: List.append (payloadRest.map some)
        (none :: padding)))

def rightBlankGapPayloadScanTargetTape
    (baseLeft : List (Option Bool)) (gap : Nat)
    (current : Bool) (payloadRest : Word Bool)
    (padding : List (Option Bool)) : Tape Bool :=
  Tape.move Direction.left
    (tapeAtCells
      (List.append ((current :: payloadRest).reverse.map some)
        (List.append (List.replicate gap (none : Option Bool))
          baseLeft))
      (none :: padding))

def rightBlankGapPayloadScanSourceTapeImplicit
    (baseLeft : List (Option Bool)) (gap : Nat)
    (current : Bool) (payloadRest : Word Bool) : Tape Bool :=
  tapeAtCells baseLeft
    (List.append
      (List.replicate gap (none : Option Bool))
      (some current :: payloadRest.map some))

def rightBlankGapPayloadScanTargetTapeImplicit
    (baseLeft : List (Option Bool)) (gap : Nat)
    (current : Bool) (payloadRest : Word Bool) : Tape Bool :=
  Tape.move Direction.left
    (tapeAtCells
      (List.append ((current :: payloadRest).reverse.map some)
        (List.append (List.replicate gap (none : Option Bool))
          baseLeft))
      [])

theorem gapPayloadScan_replicate_none_append_none_cons
    (n : Nat) (tail : List (Option Bool)) :
    List.append (List.replicate n (none : Option Bool))
        (none :: tail) =
      List.append (List.replicate (n + 1) (none : Option Bool))
        tail := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        List.append (List.replicate (n + 1) (none : Option Bool))
            (none :: tail) =
          none :: List.append (List.replicate n (none : Option Bool))
            (none :: tail) := by
              simp [List.replicate_succ]
        _ =
          none :: List.append
            (List.replicate (n + 1) (none : Option Bool)) tail := by
              rw [ih]
        _ =
          List.append
            (List.replicate (n + 1 + 1) (none : Option Bool)) tail := by
              simp [List.replicate_succ]

theorem rightBlankGapPayloadScanDescription_wellFormed :
    rightBlankGapPayloadScanDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := rightBlankGapPayloadScanDescription.transitions)
      (stateCount := rightBlankGapPayloadScanDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := rightBlankGapPayloadScanDescription.transitions)
      (by decide)

theorem rightBlankGapPayloadScanDescription_haltTransitionFree :
    rightBlankGapPayloadScanDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := rightBlankGapPayloadScanDescription.transitions)
    (state := rightBlankGapPayloadScanDescription.halt)
    (by decide)

theorem rightBlankGapPayloadScanDescription_subroutineReady :
    rightBlankGapPayloadScanDescription.SubroutineReady :=
  ⟨rightBlankGapPayloadScanDescription_wellFormed,
    rightBlankGapPayloadScanDescription_haltTransitionFree⟩

theorem rightBlankGapPayloadScanSourceTapeImplicit_move_left_move_right
    (baseLeft : List (Option Bool)) (gap : Nat)
    (current : Bool) (payloadRest : Word Bool)
    (hgap : 0 < gap) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (rightBlankGapPayloadScanSourceTapeImplicit
            baseLeft gap current payloadRest)) =
      rightBlankGapPayloadScanSourceTapeImplicit
        baseLeft gap current payloadRest := by
  cases gap with
  | zero =>
      omega
  | succ gap =>
      cases gap with
      | zero =>
          simp [rightBlankGapPayloadScanSourceTapeImplicit, tapeAtCells,
            Tape.move, Tape.moveLeft, Tape.moveRight, List.replicate_succ]
      | succ gap =>
          simp [rightBlankGapPayloadScanSourceTapeImplicit, tapeAtCells,
            Tape.move, Tape.moveLeft, Tape.moveRight, List.replicate_succ]

theorem rightBlankGapPayloadScanDescription_step_gap_blank
    (left right : List (Option Bool)) :
    rightBlankGapPayloadScanDescription.runConfig 1
        { state := rightBlankGapPayloadScanDescription.start
          tape := tapeAtCells left (none :: right) } =
      { state := rightBlankGapPayloadScanDescription.start
        tape := tapeAtCells (none :: left) right } := by
  cases right <;>
    simp [rightBlankGapPayloadScanDescription, runConfig, stepConfig,
      lookupTransition, Matches, transition, Tape.read, Tape.write,
      Tape.move, Tape.moveRight, tapeAtCells]

theorem rightBlankGapPayloadScanDescription_run_gap
    (baseLeft : List (Option Bool)) (gap : Nat)
    (current : Bool) (payloadRest : Word Bool)
    (padding : List (Option Bool)) :
    rightBlankGapPayloadScanDescription.runConfig gap
        { state := rightBlankGapPayloadScanDescription.start
          tape :=
            rightBlankGapPayloadScanSourceTape
              baseLeft gap current payloadRest padding } =
      { state := rightBlankGapPayloadScanDescription.start
        tape :=
          tapeAtCells
            (List.append
              (List.replicate gap (none : Option Bool))
              baseLeft)
            (some current :: List.append (payloadRest.map some)
              (none :: padding)) } := by
  induction gap generalizing baseLeft with
  | zero =>
      rfl
  | succ gap ih =>
      rw [show gap + 1 = 1 + gap by omega]
      rw [runConfig_add]
      have hstep :
          rightBlankGapPayloadScanDescription.runConfig 1
              { state := rightBlankGapPayloadScanDescription.start
                tape :=
                  rightBlankGapPayloadScanSourceTape
                    baseLeft (1 + gap) current payloadRest padding } =
            { state := rightBlankGapPayloadScanDescription.start
              tape :=
                rightBlankGapPayloadScanSourceTape
                  (none :: baseLeft) gap current payloadRest padding } := by
        rw [rightBlankGapPayloadScanSourceTape]
        rw [show
          List.replicate (1 + gap) (none : Option Bool) =
            none :: List.replicate gap (none : Option Bool) by
          simp [Nat.add_comm, List.replicate_succ]]
        change
          rightBlankGapPayloadScanDescription.runConfig 1
              { state := rightBlankGapPayloadScanDescription.start
                tape :=
                  tapeAtCells baseLeft
                    (none ::
                      List.append
                        (List.replicate gap (none : Option Bool))
                        (some current ::
                          List.append (payloadRest.map some)
                            (none :: padding))) } =
            { state := rightBlankGapPayloadScanDescription.start
              tape :=
                rightBlankGapPayloadScanSourceTape
                  (none :: baseLeft) gap current payloadRest padding }
        rw [rightBlankGapPayloadScanDescription_step_gap_blank]
        rfl
      rw [hstep]
      rw [show 1 + gap = gap + 1 by omega]
      rw [← gapPayloadScan_replicate_none_append_none_cons gap
        baseLeft]
      simpa [rightBlankGapPayloadScanSourceTape,
        List.append_assoc] using ih (none :: baseLeft)

theorem rightBlankGapPayloadScanDescription_run_gap_implicit
    (baseLeft : List (Option Bool)) (gap : Nat)
    (current : Bool) (payloadRest : Word Bool) :
    rightBlankGapPayloadScanDescription.runConfig gap
        { state := rightBlankGapPayloadScanDescription.start
          tape :=
            rightBlankGapPayloadScanSourceTapeImplicit
              baseLeft gap current payloadRest } =
      { state := rightBlankGapPayloadScanDescription.start
        tape :=
          tapeAtCells
            (List.append
              (List.replicate gap (none : Option Bool))
              baseLeft)
            (some current :: payloadRest.map some) } := by
  induction gap generalizing baseLeft with
  | zero =>
      rfl
  | succ gap ih =>
      rw [show gap + 1 = 1 + gap by omega]
      rw [runConfig_add]
      have hstep :
          rightBlankGapPayloadScanDescription.runConfig 1
              { state := rightBlankGapPayloadScanDescription.start
                tape :=
                  rightBlankGapPayloadScanSourceTapeImplicit
                    baseLeft (1 + gap) current payloadRest } =
            { state := rightBlankGapPayloadScanDescription.start
              tape :=
                rightBlankGapPayloadScanSourceTapeImplicit
                  (none :: baseLeft) gap current payloadRest } := by
        rw [rightBlankGapPayloadScanSourceTapeImplicit]
        rw [show
          List.replicate (1 + gap) (none : Option Bool) =
            none :: List.replicate gap (none : Option Bool) by
          simp [Nat.add_comm, List.replicate_succ]]
        change
          rightBlankGapPayloadScanDescription.runConfig 1
              { state := rightBlankGapPayloadScanDescription.start
                tape :=
                  tapeAtCells baseLeft
                    (none ::
                      List.append
                        (List.replicate gap (none : Option Bool))
                        (some current :: payloadRest.map some)) } =
            { state := rightBlankGapPayloadScanDescription.start
              tape :=
                rightBlankGapPayloadScanSourceTapeImplicit
                  (none :: baseLeft) gap current payloadRest }
        rw [rightBlankGapPayloadScanDescription_step_gap_blank]
        rfl
      rw [hstep]
      rw [show 1 + gap = gap + 1 by omega]
      rw [← gapPayloadScan_replicate_none_append_none_cons gap
        baseLeft]
      simpa [rightBlankGapPayloadScanSourceTapeImplicit,
        List.append_assoc] using ih (none :: baseLeft)

theorem rightBlankGapPayloadScanDescription_step_enter_payload
    (left : List (Option Bool)) (current : Bool)
    (payloadRest : Word Bool) (padding : List (Option Bool)) :
    rightBlankGapPayloadScanDescription.runConfig 1
        { state := rightBlankGapPayloadScanDescription.start
          tape :=
            tapeAtCells left
              (some current :: List.append (payloadRest.map some)
                (none :: padding)) } =
      { state := 1
        tape :=
          tapeAtCells (some current :: left)
            (List.append (payloadRest.map some) (none :: padding)) } := by
  cases current <;> cases payloadRest <;> cases padding <;>
    simp [rightBlankGapPayloadScanDescription, runConfig, stepConfig,
      lookupTransition, Matches, transition, Tape.read, Tape.write,
      Tape.move, Tape.moveRight, tapeAtCells]

theorem rightBlankGapPayloadScanDescription_step_enter_payload_implicit
    (left : List (Option Bool)) (current : Bool)
    (payloadRest : Word Bool) :
    rightBlankGapPayloadScanDescription.runConfig 1
        { state := rightBlankGapPayloadScanDescription.start
          tape :=
            tapeAtCells left (some current :: payloadRest.map some) } =
      { state := 1
        tape := tapeAtCells (some current :: left)
          (payloadRest.map some) } := by
  cases current <;> cases payloadRest <;>
    simp [rightBlankGapPayloadScanDescription, runConfig, stepConfig,
      lookupTransition, Matches, transition, Tape.read, Tape.write,
      Tape.move, Tape.moveRight, tapeAtCells]

theorem rightBlankGapPayloadScanDescription_step_payload_bit
    (left right : List (Option Bool)) (bit : Bool) :
    rightBlankGapPayloadScanDescription.runConfig 1
        { state := 1
          tape := tapeAtCells left (some bit :: right) } =
      { state := 1
        tape := tapeAtCells (some bit :: left) right } := by
  cases bit <;> cases right <;>
    simp [rightBlankGapPayloadScanDescription, runConfig, stepConfig,
      lookupTransition, Matches, transition, Tape.read, Tape.write,
      Tape.move, Tape.moveRight, tapeAtCells]

theorem rightBlankGapPayloadScanDescription_run_payload
    (baseLeft : List (Option Bool))
    (remaining processed : Word Bool)
    (padding : List (Option Bool)) :
    rightBlankGapPayloadScanDescription.runConfig remaining.length
        { state := 1
          tape :=
            tapeAtCells
              (List.append (processed.map some) baseLeft)
              (List.append (remaining.map some) (none :: padding)) } =
      { state := 1
        tape :=
          tapeAtCells
            (List.append
              ((List.append remaining.reverse processed).map some)
              baseLeft)
            (none :: padding) } := by
  induction remaining generalizing processed with
  | nil =>
      rfl
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        omega]
      rw [runConfig_add]
      change
        rightBlankGapPayloadScanDescription.runConfig rest.length
            (rightBlankGapPayloadScanDescription.runConfig 1
              { state := 1
                tape :=
                  tapeAtCells
                    (List.append (processed.map some) baseLeft)
                    (some bit ::
                      List.append (rest.map some) (none :: padding)) }) =
          { state := 1
            tape :=
              tapeAtCells
                (List.append
                  ((List.append (bit :: rest).reverse processed).map some)
                  baseLeft)
                (none :: padding) }
      rw [rightBlankGapPayloadScanDescription_step_payload_bit]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (bit :: processed)

theorem rightBlankGapPayloadScanDescription_run_payload_implicit
    (baseLeft : List (Option Bool))
    (remaining processed : Word Bool) :
    rightBlankGapPayloadScanDescription.runConfig remaining.length
        { state := 1
          tape :=
            tapeAtCells
              (List.append (processed.map some) baseLeft)
              (remaining.map some) } =
      { state := 1
        tape :=
          tapeAtCells
            (List.append
              ((List.append remaining.reverse processed).map some)
              baseLeft)
            [] } := by
  induction remaining generalizing processed with
  | nil =>
      rfl
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        omega]
      rw [runConfig_add]
      change
        rightBlankGapPayloadScanDescription.runConfig rest.length
            (rightBlankGapPayloadScanDescription.runConfig 1
              { state := 1
                tape :=
                  tapeAtCells
                    (List.append (processed.map some) baseLeft)
                    (some bit :: rest.map some) }) =
          { state := 1
            tape :=
              tapeAtCells
                (List.append
                  ((List.append (bit :: rest).reverse processed).map some)
                  baseLeft)
                [] }
      rw [rightBlankGapPayloadScanDescription_step_payload_bit]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (bit :: processed)

theorem rightBlankGapPayloadScanDescription_step_finish
    (left padding : List (Option Bool)) :
    rightBlankGapPayloadScanDescription.runConfig 1
        { state := 1
          tape := tapeAtCells left (none :: padding) } =
      { state := rightBlankGapPayloadScanDescription.halt
        tape :=
          Tape.move Direction.left
            (tapeAtCells left (none :: padding)) } := by
  cases left <;> cases padding <;>
    simp [rightBlankGapPayloadScanDescription, runConfig, stepConfig,
      lookupTransition, Matches, transition, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft, tapeAtCells]

theorem rightBlankGapPayloadScanDescription_step_finish_implicit
    (left : List (Option Bool)) :
    rightBlankGapPayloadScanDescription.runConfig 1
        { state := 1
          tape := tapeAtCells left [] } =
      { state := rightBlankGapPayloadScanDescription.halt
        tape := Tape.move Direction.left (tapeAtCells left []) } := by
  simpa using
    rightBlankGapPayloadScanDescription_step_finish left []

theorem rightBlankGapPayloadScanDescription_run_to_target
    (baseLeft : List (Option Bool)) (gap : Nat)
    (current : Bool) (payloadRest : Word Bool)
    (padding : List (Option Bool)) :
    rightBlankGapPayloadScanDescription.runConfig
        (gap + payloadRest.length + 2)
        { state := rightBlankGapPayloadScanDescription.start
          tape :=
            rightBlankGapPayloadScanSourceTape
              baseLeft gap current payloadRest padding } =
      { state := rightBlankGapPayloadScanDescription.halt
        tape :=
          rightBlankGapPayloadScanTargetTape
            baseLeft gap current payloadRest padding } := by
  rw [show gap + payloadRest.length + 2 =
      gap + (1 + (payloadRest.length + 1)) by omega]
  rw [runConfig_add]
  rw [rightBlankGapPayloadScanDescription_run_gap]
  rw [runConfig_add]
  rw [rightBlankGapPayloadScanDescription_step_enter_payload]
  rw [runConfig_add]
  change
    rightBlankGapPayloadScanDescription.runConfig 1
      (rightBlankGapPayloadScanDescription.runConfig payloadRest.length
        { state := 1
          tape :=
            tapeAtCells
              (List.append ([current].map some)
                (List.append
                  (List.replicate gap (none : Option Bool))
                  baseLeft))
              (List.append (payloadRest.map some) (none :: padding)) }) =
      { state := rightBlankGapPayloadScanDescription.halt
        tape :=
          rightBlankGapPayloadScanTargetTape
            baseLeft gap current payloadRest padding }
  rw [rightBlankGapPayloadScanDescription_run_payload]
  rw [rightBlankGapPayloadScanDescription_step_finish]
  simp [rightBlankGapPayloadScanTargetTape, List.reverse_cons,
    List.map_append, List.append_assoc]

theorem rightBlankGapPayloadScanDescription_run_to_target_implicit
    (baseLeft : List (Option Bool)) (gap : Nat)
    (current : Bool) (payloadRest : Word Bool) :
    rightBlankGapPayloadScanDescription.runConfig
        (gap + payloadRest.length + 2)
        { state := rightBlankGapPayloadScanDescription.start
          tape :=
            rightBlankGapPayloadScanSourceTapeImplicit
              baseLeft gap current payloadRest } =
      { state := rightBlankGapPayloadScanDescription.halt
        tape :=
          rightBlankGapPayloadScanTargetTapeImplicit
            baseLeft gap current payloadRest } := by
  rw [show gap + payloadRest.length + 2 =
      gap + (1 + (payloadRest.length + 1)) by omega]
  rw [runConfig_add]
  rw [rightBlankGapPayloadScanDescription_run_gap_implicit]
  rw [runConfig_add]
  rw [rightBlankGapPayloadScanDescription_step_enter_payload_implicit]
  rw [runConfig_add]
  change
    rightBlankGapPayloadScanDescription.runConfig 1
      (rightBlankGapPayloadScanDescription.runConfig payloadRest.length
        { state := 1
          tape :=
            tapeAtCells
              (List.append ([current].map some)
                (List.append
                  (List.replicate gap (none : Option Bool))
                  baseLeft))
              (payloadRest.map some) }) =
      { state := rightBlankGapPayloadScanDescription.halt
        tape :=
          rightBlankGapPayloadScanTargetTapeImplicit
            baseLeft gap current payloadRest }
  rw [rightBlankGapPayloadScanDescription_run_payload_implicit]
  rw [rightBlankGapPayloadScanDescription_step_finish_implicit]
  simp [rightBlankGapPayloadScanTargetTapeImplicit, List.reverse_cons,
    List.map_append, List.append_assoc]

theorem rightBlankGapPayloadScanDescription_haltsFromTape
    (baseLeft : List (Option Bool)) (gap : Nat)
    (current : Bool) (payloadRest : Word Bool)
    (padding : List (Option Bool)) :
    rightBlankGapPayloadScanDescription.HaltsFromTape
      (rightBlankGapPayloadScanSourceTape
        baseLeft gap current payloadRest padding)
      (rightBlankGapPayloadScanTargetTape
        baseLeft gap current payloadRest padding) := by
  refine ⟨gap + payloadRest.length + 2, ?_⟩
  constructor <;>
    rw [rightBlankGapPayloadScanDescription_run_to_target]

theorem rightBlankGapPayloadScanDescription_haltsFromTapeImplicit
    (baseLeft : List (Option Bool)) (gap : Nat)
    (current : Bool) (payloadRest : Word Bool) :
    rightBlankGapPayloadScanDescription.HaltsFromTape
      (rightBlankGapPayloadScanSourceTapeImplicit
        baseLeft gap current payloadRest)
      (rightBlankGapPayloadScanTargetTapeImplicit
        baseLeft gap current payloadRest) := by
  refine ⟨gap + payloadRest.length + 2, ?_⟩
  constructor <;>
    rw [rightBlankGapPayloadScanDescription_run_to_target_implicit]

end FiniteTransducers
end CommonGround

end Computability
end FoC

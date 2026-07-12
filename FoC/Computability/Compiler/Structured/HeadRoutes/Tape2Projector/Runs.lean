import FoC.Computability.Compiler.Structured.HeadRoutes.Tape2Projector.Machine

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering
namespace Tape2Projector

def prefixSourceTape
    (tape0Bits tape1Bits tape2Bits : Word Bool) : Tape Bool :=
  tapeAtCells []
    (none ::
      List.append (tape0Bits.map some)
        (none ::
          List.append (tape1Bits.map some)
            (none :: List.append (tape2Bits.map some) [none])))

def prefixTargetTape
    (tape0Bits tape1Bits tape2Bits : Word Bool) : Tape Bool :=
  tapeAtCells
    (List.append
      (List.replicate (tape0Bits.length + tape1Bits.length + 2)
        (none : Option Bool))
      [some false])
    (List.append (tape2Bits.map some) [none])

private theorem prefixEraserDescription_run_state1_bits
    (bits : Word Bool) (left right : List (Option Bool)) :
    prefixEraserDescription.runConfig bits.length
        { state := 1
          tape := tapeAtCells left
            (List.append (bits.map some) right) } =
      { state := 1
        tape := tapeAtCells
          (List.append
            (List.replicate bits.length (none : Option Bool)) left)
          right } := by
  induction bits generalizing left with
  | nil =>
      rfl
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp [Nat.add_comm]]
      rw [runConfig_add]
      change
        prefixEraserDescription.runConfig rest.length
            (prefixEraserDescription.runConfig 1
              { state := 1
                tape := tapeAtCells left
                  (some bit :: List.append (rest.map some) right) }) =
          { state := 1
            tape := tapeAtCells
              (List.append
                (List.replicate (1 + rest.length) none) left)
              right }
      rw [show
        prefixEraserDescription.runConfig 1
            { state := 1
              tape := tapeAtCells left
                (some bit :: List.append (rest.map some) right) } =
          { state := 1
            tape := tapeAtCells (none :: left)
              (List.append (rest.map some) right) } by
        cases bit <;>
          simp [prefixEraserDescription, runConfig, stepConfig,
            lookupTransition, Matches, transition, tapeAtCells,
            Tape.read, Tape.write, Tape.move, Tape.moveRight] <;>
          split <;> simp_all]
      rw [ih (none :: left)]
      rw [replicate_none_append_none_cons]
      rw [show 1 + rest.length = rest.length + 1 by lia]
      rw [List.replicate_succ]
      rfl

private theorem prefixEraserDescription_run_state2_bits
    (bits : Word Bool) (left right : List (Option Bool)) :
    prefixEraserDescription.runConfig bits.length
        { state := 2
          tape := tapeAtCells left
            (List.append (bits.map some) right) } =
      { state := 2
        tape := tapeAtCells
          (List.append
            (List.replicate bits.length (none : Option Bool)) left)
          right } := by
  induction bits generalizing left with
  | nil =>
      rfl
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp [Nat.add_comm]]
      rw [runConfig_add]
      change
        prefixEraserDescription.runConfig rest.length
            (prefixEraserDescription.runConfig 1
              { state := 2
                tape := tapeAtCells left
                  (some bit :: List.append (rest.map some) right) }) =
          { state := 2
            tape := tapeAtCells
              (List.append
                (List.replicate (1 + rest.length) none) left)
              right }
      rw [show
        prefixEraserDescription.runConfig 1
            { state := 2
              tape := tapeAtCells left
                (some bit :: List.append (rest.map some) right) } =
          { state := 2
            tape := tapeAtCells (none :: left)
              (List.append (rest.map some) right) } by
        cases bit <;>
          simp [prefixEraserDescription, runConfig, stepConfig,
            lookupTransition, Matches, transition, tapeAtCells,
            Tape.read, Tape.write, Tape.move, Tape.moveRight] <;>
          split <;> simp_all]
      rw [ih (none :: left)]
      rw [replicate_none_append_none_cons]
      rw [show 1 + rest.length = rest.length + 1 by lia]
      rw [List.replicate_succ]
      rfl

private theorem replicate_none_append_replicate_none_local
    (leftLength rightLength : Nat) :
    List.append
        (List.replicate leftLength (none : Option Bool))
        (List.replicate rightLength (none : Option Bool)) =
      List.replicate (leftLength + rightLength) (none : Option Bool) := by
  induction leftLength with
  | zero =>
      simp
  | succ leftLength ih =>
      rw [List.replicate_succ]
      change none ::
          List.append
            (List.replicate leftLength (none : Option Bool))
            (List.replicate rightLength (none : Option Bool)) =
        List.replicate (Nat.succ leftLength + rightLength)
          (none : Option Bool)
      rw [ih]
      rw [show Nat.succ leftLength + rightLength =
        (leftLength + rightLength) + 1 by lia]
      rw [List.replicate_succ]

private theorem replicate_none_append_replicate_none_tail
    (leftLength rightLength : Nat) (tail : List (Option Bool)) :
    List.append
        (List.replicate leftLength (none : Option Bool))
        (List.append
          (List.replicate rightLength (none : Option Bool)) tail) =
      List.append
        (List.replicate (leftLength + rightLength) (none : Option Bool))
        tail := by
  calc
    _ = List.append
        (List.append
          (List.replicate leftLength (none : Option Bool))
          (List.replicate rightLength (none : Option Bool)))
        tail :=
      (List.append_assoc _ _ _).symm
    _ = _ := congrArg (fun cells => List.append cells tail)
      (replicate_none_append_replicate_none_local
        leftLength rightLength)

private theorem prefixEraserPadding_eq
    (tape0Length tape1Length : Nat) :
    none ::
        List.append
          (List.replicate tape1Length (none : Option Bool))
          (none ::
            List.append
              (List.replicate tape0Length (none : Option Bool))
              [some false]) =
      List.append
        (List.replicate (tape0Length + tape1Length + 2)
          (none : Option Bool))
        [some false] := by
  calc
    _ = none :: none ::
        List.append
          (List.replicate (tape1Length + tape0Length)
            (none : Option Bool))
          [some false] := by
      rw [replicate_none_append_none_cons]
      exact congrArg (fun cells => none :: none :: cells)
        (replicate_none_append_replicate_none_tail
          tape1Length tape0Length [some false])
    _ = List.append
        (List.replicate (tape0Length + tape1Length + 2)
          (none : Option Bool))
        [some false] := by
      rw [show tape0Length + tape1Length + 2 =
        (tape1Length + tape0Length + 1) + 1 by lia]
      rw [List.replicate_succ, List.replicate_succ]
      rfl

theorem prefixEraserDescription_run
    (tape0Bits tape1Bits tape2Bits : Word Bool) :
    prefixEraserDescription.runConfig
        (tape0Bits.length + tape1Bits.length + 3)
        { state := prefixEraserDescription.start
          tape := prefixSourceTape tape0Bits tape1Bits tape2Bits } =
      { state := prefixEraserDescription.halt
        tape := prefixTargetTape tape0Bits tape1Bits tape2Bits } := by
  rw [show tape0Bits.length + tape1Bits.length + 3 =
      1 + (tape0Bits.length +
        (1 + (tape1Bits.length + 1))) by lia]
  rw [runConfig_add]
  have hstart :
      prefixEraserDescription.runConfig 1
          { state := prefixEraserDescription.start
            tape := prefixSourceTape tape0Bits tape1Bits tape2Bits } =
        { state := 1
          tape := tapeAtCells [some false]
            (List.append (tape0Bits.map some)
              (none ::
                List.append (tape1Bits.map some)
                  (none :: List.append (tape2Bits.map some) [none]))) } := by
    cases tape0Bits <;>
      simp [prefixEraserDescription, prefixSourceTape, runConfig,
        stepConfig, lookupTransition, Matches, transition, tapeAtCells,
        Tape.read, Tape.write, Tape.move, Tape.moveRight]
  rw [hstart]
  rw [runConfig_add]
  rw [prefixEraserDescription_run_state1_bits]
  have hseparator0 :
      prefixEraserDescription.runConfig 1
          { state := 1
            tape := tapeAtCells
              (List.append
                (List.replicate tape0Bits.length (none : Option Bool))
                [some false])
              (none ::
                List.append (tape1Bits.map some)
                  (none :: List.append (tape2Bits.map some) [none])) } =
        { state := 2
          tape := tapeAtCells
            (none ::
              List.append
                (List.replicate tape0Bits.length (none : Option Bool))
                [some false])
            (List.append (tape1Bits.map some)
              (none :: List.append (tape2Bits.map some) [none])) } := by
    cases tape1Bits <;>
      simp [prefixEraserDescription, runConfig, stepConfig,
        lookupTransition, Matches, transition, tapeAtCells,
        Tape.read, Tape.write, Tape.move, Tape.moveRight]
  rw [runConfig_add]
  rw [hseparator0]
  rw [runConfig_add]
  rw [prefixEraserDescription_run_state2_bits]
  have hseparator1 :
      prefixEraserDescription.runConfig 1
          { state := 2
            tape := tapeAtCells
              (List.append
                (List.replicate tape1Bits.length (none : Option Bool))
                (none ::
                  List.append
                    (List.replicate tape0Bits.length (none : Option Bool))
                    [some false]))
              (none :: List.append (tape2Bits.map some) [none]) } =
        { state := prefixEraserDescription.halt
          tape := prefixTargetTape tape0Bits tape1Bits tape2Bits } := by
    cases tape2Bits <;>
      simp [prefixEraserDescription, prefixTargetTape, runConfig,
        stepConfig, lookupTransition, Matches, transition, tapeAtCells,
        Tape.read, Tape.write, Tape.move, Tape.moveRight] <;>
      exact prefixEraserPadding_eq tape0Bits.length tape1Bits.length
  exact hseparator1

theorem prefixEraserDescription_haltsFromTape
    (tape0Bits tape1Bits tape2Bits : Word Bool) :
    prefixEraserDescription.HaltsFromTape
      (prefixSourceTape tape0Bits tape1Bits tape2Bits)
      (prefixTargetTape tape0Bits tape1Bits tape2Bits) := by
  refine ⟨tape0Bits.length + tape1Bits.length + 3, ?_⟩
  constructor <;> rw [prefixEraserDescription_run]

theorem encodedGuardedStructured3Tapes_eq_prefixSourceTape
    (T0 T1 T2 : Tape Bool) :
    encodedGuardedStructured3Tapes T0 T1 T2 =
      prefixSourceTape
        (logicalTapeBits (guardLogicalTape T0))
        (logicalTapeBits (guardLogicalTape T1))
        (logicalTapeBits (guardLogicalTape T2)) := by
  simp [encodedGuardedStructured3Tapes, encodedGuardedStructuredTapes,
    encodedStructuredTapes, guardLogicalTapes,
    encodedStructuredTapeCells, prefixSourceTape,
    logicalTapeCode_eq_map_some, tapeSeparatorCells]

theorem prefixEraserDescription_haltsFrom_encodedGuardedStructured3Tapes
    (T0 T1 T2 : Tape Bool) :
    prefixEraserDescription.HaltsFromTape
      (encodedGuardedStructured3Tapes T0 T1 T2)
      (prefixTargetTape
        (logicalTapeBits (guardLogicalTape T0))
        (logicalTapeBits (guardLogicalTape T1))
        (logicalTapeBits (guardLogicalTape T2))) := by
  rw [encodedGuardedStructured3Tapes_eq_prefixSourceTape]
  exact prefixEraserDescription_haltsFromTape _ _ _

def remainingEndpointCells : Word Bool -> List (Option Bool)
  | [] => [none, none]
  | first :: rest => (first :: rest).map some ++ [none]

def remainingEndpointBits (bits : Word Bool) : Word Bool :=
  logicalCellListBits (remainingEndpointCells bits)

@[simp] theorem remainingEndpointCells_filterMap
    (bits : Word Bool) :
    (remainingEndpointCells bits).filterMap (fun cell => cell) = bits := by
  cases bits <;>
    simp [remainingEndpointCells, Function.comp_def]

theorem logicalTapeBits_guard_input
    (bits : Word Bool) :
    logicalTapeBits (guardLogicalTape (Tape.input bits)) =
      List.append [false, false, true, true]
        (remainingEndpointBits bits) := by
  cases bits with
  | nil =>
      rfl
  | cons first rest =>
      cases first <;>
        simp [logicalTapeBits, guardLogicalTape, Tape.input,
          remainingEndpointBits, remainingEndpointCells,
          logicalCellListBits, logicalCellBits]

theorem logicalTapeBits_guard_moveRight_input
    (first : Bool) (rest : Word Bool) :
    logicalTapeBits
        (guardLogicalTape
          (Tape.move Direction.right (Tape.input (first :: rest)))) =
      List.append [false, false]
        (List.append (logicalCellBits (some first))
          (List.append [true, true] (remainingEndpointBits rest))) := by
  cases first with
  | false =>
      cases rest with
      | nil =>
          rfl
      | cons second tail =>
          cases second <;>
            simp [logicalTapeBits, guardLogicalTape, Tape.input,
              Tape.move, Tape.moveRight, remainingEndpointBits,
              remainingEndpointCells, logicalCellListBits, logicalCellBits]
  | true =>
      cases rest with
      | nil =>
          rfl
      | cons second tail =>
          cases second <;>
            simp [logicalTapeBits, guardLogicalTape, Tape.input,
              Tape.move, Tape.moveRight, remainingEndpointBits,
              remainingEndpointCells, logicalCellListBits, logicalCellBits]

def parserExactSourceTape
    (padding : Nat) (remaining : Word Bool) : Tape Bool :=
  tapeAtCells
    (List.append
      (List.replicate padding (none : Option Bool)) [some false])
    (List.append
      ((List.append [false, false, true, true] remaining).map some)
      [none])

def parserRightSourceTape
    (padding : Nat) (first : Bool) (remaining : Word Bool) : Tape Bool :=
  tapeAtCells
    (List.append
      (List.replicate padding (none : Option Bool)) [some false])
    (List.append
      ((List.append [false, false]
        (List.append (logicalCellBits (some first))
          (List.append [true, true] remaining))).map some)
      [none])

def parserTargetTape
    (metadata : Word Bool) (gap : Nat)
    (remaining : Word Bool) : Tape Bool :=
  tapeAtCells
    (List.append
      (List.replicate gap (none : Option Bool))
      (metadata.reverse.map some))
    (List.append (remaining.map some) [some false])

private theorem parserDescription_run_return_exact
    (padding : Nat) (right : List (Option Bool)) :
    parserDescription.runConfig (padding + 2)
        { state := 10
          tape := tapeAtCells
            (List.append
              (List.replicate padding (none : Option Bool))
              [some false])
            (none :: right) } =
      { state := 13
        tape := tapeAtCells [some false]
          (List.append
            (List.replicate (padding + 1) (none : Option Bool))
            right) } := by
  induction padding generalizing right with
  | zero =>
      cases right <;>
        simp [parserDescription, runConfig, stepConfig,
          lookupTransition, Matches, transition, tapeAtCells,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          Tape.moveRight, List.replicate_succ]
  | succ padding ih =>
      rw [show Nat.succ padding + 2 = 1 + (padding + 2) by lia]
      rw [runConfig_add]
      have hstep :
          parserDescription.runConfig 1
              { state := 10
                tape := tapeAtCells
                  (List.append
                    (List.replicate (Nat.succ padding)
                      (none : Option Bool))
                    [some false])
                  (none :: right) } =
            { state := 10
              tape := tapeAtCells
                (List.append
                  (List.replicate padding (none : Option Bool))
                  [some false])
                (none :: none :: right) } := by
        rw [show Nat.succ padding = padding + 1 by rfl]
        rw [List.replicate_succ]
        cases right <;>
          simp [parserDescription, runConfig, stepConfig,
            lookupTransition, Matches, transition, tapeAtCells,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      rw [hstep]
      rw [ih (none :: right)]
      rw [replicate_none_append_none_cons]
      rw [show Nat.succ padding + 1 = padding + 1 + 1 by lia]
      rw [List.replicate_succ]
      rfl

private theorem parserDescription_run_return_right_false
    (padding : Nat) (right : List (Option Bool)) :
    parserDescription.runConfig (padding + 2)
        { state := 11
          tape := tapeAtCells
            (List.append
              (List.replicate padding (none : Option Bool))
              [some false])
            (none :: right) } =
      { state := 14
        tape := tapeAtCells [some false]
          (List.append
            (List.replicate (padding + 1) (none : Option Bool))
            right) } := by
  induction padding generalizing right with
  | zero =>
      cases right <;>
        simp [parserDescription, runConfig, stepConfig,
          lookupTransition, Matches, transition, tapeAtCells,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          Tape.moveRight, List.replicate_succ]
  | succ padding ih =>
      rw [show Nat.succ padding + 2 = 1 + (padding + 2) by lia]
      rw [runConfig_add]
      have hstep :
          parserDescription.runConfig 1
              { state := 11
                tape := tapeAtCells
                  (List.append
                    (List.replicate (Nat.succ padding)
                      (none : Option Bool))
                    [some false])
                  (none :: right) } =
            { state := 11
              tape := tapeAtCells
                (List.append
                  (List.replicate padding (none : Option Bool))
                  [some false])
                (none :: none :: right) } := by
        rw [show Nat.succ padding = padding + 1 by rfl]
        rw [List.replicate_succ]
        cases right <;>
          simp [parserDescription, runConfig, stepConfig,
            lookupTransition, Matches, transition, tapeAtCells,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      rw [hstep]
      rw [ih (none :: right)]
      rw [replicate_none_append_none_cons]
      rw [show Nat.succ padding + 1 = padding + 1 + 1 by lia]
      rw [List.replicate_succ]
      rfl

private theorem parserDescription_run_return_right_true
    (padding : Nat) (right : List (Option Bool)) :
    parserDescription.runConfig (padding + 2)
        { state := 12
          tape := tapeAtCells
            (List.append
              (List.replicate padding (none : Option Bool))
              [some false])
            (none :: right) } =
      { state := 15
        tape := tapeAtCells [some false]
          (List.append
            (List.replicate (padding + 1) (none : Option Bool))
            right) } := by
  induction padding generalizing right with
  | zero =>
      cases right <;>
        simp [parserDescription, runConfig, stepConfig,
          lookupTransition, Matches, transition, tapeAtCells,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          Tape.moveRight, List.replicate_succ]
  | succ padding ih =>
      rw [show Nat.succ padding + 2 = 1 + (padding + 2) by lia]
      rw [runConfig_add]
      have hstep :
          parserDescription.runConfig 1
              { state := 12
                tape := tapeAtCells
                  (List.append
                    (List.replicate (Nat.succ padding)
                      (none : Option Bool))
                    [some false])
                  (none :: right) } =
            { state := 12
              tape := tapeAtCells
                (List.append
                  (List.replicate padding (none : Option Bool))
                  [some false])
                (none :: none :: right) } := by
        rw [show Nat.succ padding = padding + 1 by rfl]
        rw [List.replicate_succ]
        cases right <;>
          simp [parserDescription, runConfig, stepConfig,
            lookupTransition, Matches, transition, tapeAtCells,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      rw [hstep]
      rw [ih (none :: right)]
      rw [replicate_none_append_none_cons]
      rw [show Nat.succ padding + 1 = padding + 1 + 1 by lia]
      rw [List.replicate_succ]
      rfl

private theorem parserDescription_run_scan_bits
    (bits : Word Bool) (left right : List (Option Bool)) :
    parserDescription.runConfig bits.length
        { state := 21
          tape := tapeAtCells left
            (List.append (bits.map some) right) } =
      { state := 21
        tape := tapeAtCells
          (List.append (bits.reverse.map some) left) right } := by
  induction bits generalizing left with
  | nil =>
      rfl
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp [Nat.add_comm]]
      rw [runConfig_add]
      change
        parserDescription.runConfig rest.length
            (parserDescription.runConfig 1
              { state := 21
                tape := tapeAtCells left
                  (some bit :: List.append (rest.map some) right) }) =
          { state := 21
            tape := tapeAtCells
              (List.append ((bit :: rest).reverse.map some) left) right }
      rw [show
        parserDescription.runConfig 1
            { state := 21
              tape := tapeAtCells left
                (some bit :: List.append (rest.map some) right) } =
          { state := 21
            tape := tapeAtCells (some bit :: left)
              (List.append (rest.map some) right) } by
        cases bit <;>
          simp [parserDescription, runConfig, stepConfig,
            lookupTransition, Matches, transition, tapeAtCells,
            Tape.read, Tape.write, Tape.move, Tape.moveRight] <;>
          split <;> simp_all]
      rw [ih (some bit :: left)]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

private theorem parserDescription_run_rewind_bits
    (current : Bool) (leftward : Word Bool)
    (left right : List (Option Bool)) :
    parserDescription.runConfig (leftward.length + 2)
        { state := 22
          tape := tapeAtCells
            (List.append (leftward.map some) (none :: left))
            (some current :: right) } =
      { state := parserDescription.halt
        tape := tapeAtCells (none :: left)
          (List.append
            ((List.append leftward.reverse [current]).map some) right) } := by
  induction leftward generalizing current right with
  | nil =>
      cases current <;> cases right <;>
        simp [parserDescription, runConfig, stepConfig,
          lookupTransition, Matches, transition, tapeAtCells,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          Tape.moveRight]
  | cons next rest ih =>
      rw [show (next :: rest).length + 2 = 1 + (rest.length + 2) by
        simp only [List.length_cons]
        lia]
      rw [runConfig_add]
      have hstep :
          parserDescription.runConfig 1
              { state := 22
                tape := tapeAtCells
                  (List.append ((next :: rest).map some) (none :: left))
                  (some current :: right) } =
            { state := 22
              tape := tapeAtCells
                (List.append (rest.map some) (none :: left))
                (some next :: some current :: right) } := by
        cases current <;> cases next <;> cases right <;>
          simp [parserDescription, runConfig, stepConfig,
            lookupTransition, Matches, transition, tapeAtCells,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      rw [hstep]
      rw [ih next (some current :: right)]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

private theorem parserDescription_run_finish_rewind
    (current : Bool) (leftward : Word Bool)
    (left right : List (Option Bool)) :
    parserDescription.runConfig ((current :: leftward).length + 2)
        { state := 21
          tape := tapeAtCells
            (List.append ((current :: leftward).map some) (none :: left))
            (none :: right) } =
      { state := parserDescription.halt
        tape := tapeAtCells (none :: left)
          (List.append
            ((current :: leftward).reverse.map some)
            (some false :: right)) } := by
  rw [show (current :: leftward).length + 2 =
    1 + (leftward.length + 2) by
      simp only [List.length_cons]
      lia]
  rw [runConfig_add]
  have hboundary :
      parserDescription.runConfig 1
          { state := 21
            tape := tapeAtCells
              (List.append ((current :: leftward).map some) (none :: left))
              (none :: right) } =
        { state := 22
          tape := tapeAtCells
            (List.append (leftward.map some) (none :: left))
            (some current :: some false :: right) } := by
    cases current <;> cases leftward <;> cases right <;>
      simp [parserDescription, runConfig, stepConfig,
        lookupTransition, Matches, transition, tapeAtCells,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft]
  rw [hboundary]
  rw [parserDescription_run_rewind_bits]
  simp [List.reverse_cons, List.map_append, List.append_assoc]

private theorem parserDescription_run_finish_rewind_nonempty
    (first : Bool) (rest : Word Bool)
    (left right : List (Option Bool)) :
    parserDescription.runConfig ((first :: rest).length + 2)
        { state := 21
          tape := tapeAtCells
            (List.append ((first :: rest).reverse.map some) (none :: left))
            (none :: right) } =
      { state := parserDescription.halt
        tape := tapeAtCells (none :: left)
          (List.append ((first :: rest).map some) (some false :: right)) } := by
  cases hbackward : (first :: rest).reverse with
  | nil =>
      simp at hbackward
  | cons current leftward =>
      have hforward : (current :: leftward).reverse = first :: rest := by
        rw [← hbackward]
        simp
      have hlength : (current :: leftward).length = (first :: rest).length := by
        have := congrArg List.length hbackward
        simpa using this.symm
      simpa [hbackward, hforward, hlength] using
        parserDescription_run_finish_rewind current leftward left right

private theorem parserDescription_run_seek_blanks
    (padding : Nat) (left right : List (Option Bool)) :
    parserDescription.runConfig padding
        { state := 20
          tape := tapeAtCells left
            (List.append
              (List.replicate padding (none : Option Bool)) right) } =
      { state := 20
        tape := tapeAtCells
          (List.append
            (List.replicate padding (none : Option Bool)) left) right } := by
  induction padding generalizing left with
  | zero =>
      rfl
  | succ padding ih =>
      rw [show padding + 1 = 1 + padding by lia]
      rw [runConfig_add]
      have hstep :
          parserDescription.runConfig 1
              { state := 20
                tape := tapeAtCells left
                  (List.append
                    (List.replicate (1 + padding)
                      (none : Option Bool)) right) } =
            { state := 20
              tape := tapeAtCells (none :: left)
                (List.append
                  (List.replicate padding (none : Option Bool)) right) } := by
        rw [show 1 + padding = padding + 1 by lia]
        rw [List.replicate_succ]
        have hgeneric (rest : List (Option Bool)) :
            parserDescription.runConfig 1
                { state := 20
                  tape := tapeAtCells left (none :: rest) } =
              { state := 20
                tape := tapeAtCells (none :: left) rest } := by
          cases rest <;>
            simp [parserDescription, runConfig, stepConfig,
              lookupTransition, Matches, transition, tapeAtCells,
              Tape.read, Tape.write, Tape.move, Tape.moveRight]
        exact hgeneric _
      rw [hstep]
      rw [ih (none :: left)]
      rw [replicate_none_append_none_cons]
      rw [show 1 + padding = padding + 1 by lia]
      rw [List.replicate_succ]
      have hleft :
          none ::
              List.append
                (List.replicate padding (none : Option Bool)) left =
            List.append
              (none :: List.replicate padding (none : Option Bool)) left :=
        rfl
      rw [hleft]

private theorem parserDescription_run_scan_rewind
    (first : Bool) (rest : Word Bool)
    (left : List (Option Bool)) :
    parserDescription.runConfig (2 * (first :: rest).length + 2)
        { state := 20
          tape := tapeAtCells (none :: left)
            (List.append ((first :: rest).map some) [none]) } =
      { state := parserDescription.halt
        tape := tapeAtCells (none :: left)
          (List.append ((first :: rest).map some) [some false]) } := by
  rw [show 2 * (first :: rest).length + 2 =
    1 + (rest.length + ((first :: rest).length + 2)) by
      simp only [List.length_cons]
      lia]
  rw [runConfig_add]
  have hfirst :
      parserDescription.runConfig 1
          { state := 20
            tape := tapeAtCells (none :: left)
              (List.append ((first :: rest).map some) [none]) } =
        { state := 21
          tape := tapeAtCells (some first :: none :: left)
            (List.append (rest.map some) [none]) } := by
    cases first <;> cases rest <;>
      simp [parserDescription, runConfig, stepConfig,
        lookupTransition, Matches, transition, tapeAtCells,
        Tape.read, Tape.write, Tape.move, Tape.moveRight]
  rw [hfirst]
  rw [runConfig_add]
  rw [parserDescription_run_scan_bits]
  have hleft :
      List.append (rest.reverse.map some) (some first :: none :: left) =
        List.append ((first :: rest).reverse.map some) (none :: left) := by
    simp [List.reverse_cons, List.map_append, List.append_assoc]
  rw [hleft]
  exact parserDescription_run_finish_rewind_nonempty first rest left []

private theorem parserDescription_run_start_exact
    (padding : Nat) (remaining : Word Bool) :
    parserDescription.runConfig 4
        { state := parserDescription.start
          tape := parserExactSourceTape padding remaining } =
      { state := 10
        tape := tapeAtCells
          (List.append
            (List.replicate (padding + 2) (none : Option Bool))
            [some false])
          (none :: none :: List.append (remaining.map some) [none]) } := by
  rw [show 4 = 1 + (1 + (1 + 1)) by decide]
  rw [runConfig_add]
  have h0 :
      parserDescription.runConfig 1
          { state := parserDescription.start
            tape := parserExactSourceTape padding remaining } =
        { state := 1
          tape := tapeAtCells
            (none :: List.append
              (List.replicate padding (none : Option Bool)) [some false])
            (some false :: some true :: some true ::
              List.append (remaining.map some) [none]) } := by
    simp [parserDescription, parserExactSourceTape, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]
  rw [h0]
  rw [runConfig_add]
  have h1 :
      parserDescription.runConfig 1
          { state := 1
            tape := tapeAtCells
              (none :: List.append
                (List.replicate padding (none : Option Bool)) [some false])
              (some false :: some true :: some true ::
                List.append (remaining.map some) [none]) } =
        { state := 2
          tape := tapeAtCells
            (none :: none :: List.append
              (List.replicate padding (none : Option Bool)) [some false])
            (some true :: some true ::
              List.append (remaining.map some) [none]) } := by
    simp [parserDescription, runConfig, stepConfig,
      lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]
  rw [h1]
  rw [runConfig_add]
  have h2 :
      parserDescription.runConfig 1
          { state := 2
            tape := tapeAtCells
              (none :: none :: List.append
                (List.replicate padding (none : Option Bool)) [some false])
              (some true :: some true ::
                List.append (remaining.map some) [none]) } =
        { state := 4
          tape := tapeAtCells
            (none :: none :: none :: List.append
              (List.replicate padding (none : Option Bool)) [some false])
            (some true :: List.append (remaining.map some) [none]) } := by
    simp [parserDescription, runConfig, stepConfig,
      lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]
  rw [h2]
  have h3 :
      parserDescription.runConfig 1
          { state := 4
            tape := tapeAtCells
              (none :: none :: none :: List.append
                (List.replicate padding (none : Option Bool)) [some false])
              (some true :: List.append (remaining.map some) [none]) } =
        { state := 10
          tape := tapeAtCells
            (none :: none :: List.append
              (List.replicate padding (none : Option Bool)) [some false])
            (none :: none :: List.append (remaining.map some) [none]) } := by
    have hgeneric (left right : List (Option Bool)) :
        parserDescription.runConfig 1
            { state := 4
              tape := tapeAtCells (none :: left) (some true :: right) } =
          { state := 10
            tape := tapeAtCells left (none :: none :: right) } := by
      cases left <;> cases right <;>
        simp [parserDescription, runConfig, stepConfig,
          lookupTransition, Matches, transition, tapeAtCells,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft]
    exact hgeneric _ _
  rw [h3]
  rw [show padding + 2 = (padding + 1) + 1 by lia]
  rw [List.replicate_succ, List.replicate_succ]
  have hleft :
      none :: none ::
          List.append
            (List.replicate padding (none : Option Bool)) [some false] =
        List.append
          (none :: none :: List.replicate padding (none : Option Bool))
          [some false] :=
    rfl
  rw [hleft]

private theorem parserDescription_run_setup_exact
    (gap : Nat) (right : List (Option Bool)) :
    parserDescription.runConfig 2
        { state := 13
          tape := tapeAtCells [some false]
            (List.append
              (List.replicate (gap + 1) (none : Option Bool))
              (none :: right)) } =
      { state := 20
        tape := tapeAtCells [none, some false, some false]
          (List.append
            (List.replicate gap (none : Option Bool)) right) } := by
  have hsource :
      List.append
          (List.replicate (gap + 1) (none : Option Bool))
          (none :: right) =
        none :: none ::
          List.append (List.replicate gap (none : Option Bool)) right := by
    rw [List.replicate_succ]
    change none ::
        List.append (List.replicate gap (none : Option Bool))
          (none :: right) =
      none :: none ::
        List.append (List.replicate gap (none : Option Bool)) right
    rw [replicate_none_append_none_cons]
  rw [hsource]
  have hgeneric (rest : List (Option Bool)) :
      parserDescription.runConfig 2
          { state := 13
            tape := tapeAtCells [some false] (none :: none :: rest) } =
        { state := 20
          tape := tapeAtCells [none, some false, some false] rest } := by
    cases rest <;>
      simp [parserDescription, runConfig, stepConfig,
        lookupTransition, Matches, transition, tapeAtCells,
        Tape.read, Tape.write, Tape.move, Tape.moveRight]
  exact hgeneric _

private theorem parserDescription_run_setup_right_false
    (gap : Nat) (right : List (Option Bool)) :
    parserDescription.runConfig 2
        { state := 14
          tape := tapeAtCells [some false]
            (List.append
              (List.replicate (gap + 1) (none : Option Bool))
              (none :: right)) } =
      { state := 20
        tape := tapeAtCells [some false, some true, some false]
          (List.append
            (List.replicate gap (none : Option Bool)) right) } := by
  have hsource :
      List.append
          (List.replicate (gap + 1) (none : Option Bool))
          (none :: right) =
        none :: none ::
          List.append (List.replicate gap (none : Option Bool)) right := by
    rw [List.replicate_succ]
    change none ::
        List.append (List.replicate gap (none : Option Bool))
          (none :: right) =
      none :: none ::
        List.append (List.replicate gap (none : Option Bool)) right
    rw [replicate_none_append_none_cons]
  rw [hsource]
  have hgeneric (rest : List (Option Bool)) :
      parserDescription.runConfig 2
          { state := 14
            tape := tapeAtCells [some false] (none :: none :: rest) } =
        { state := 20
          tape := tapeAtCells [some false, some true, some false] rest } := by
    cases rest <;>
      simp [parserDescription, runConfig, stepConfig,
        lookupTransition, Matches, transition, tapeAtCells,
        Tape.read, Tape.write, Tape.move, Tape.moveRight]
  exact hgeneric _

private theorem parserDescription_run_setup_right_true
    (gap : Nat) (right : List (Option Bool)) :
    parserDescription.runConfig 2
        { state := 15
          tape := tapeAtCells [some false]
            (List.append
              (List.replicate (gap + 1) (none : Option Bool))
              (none :: right)) } =
      { state := 20
        tape := tapeAtCells [some true, some true, some false]
          (List.append
            (List.replicate gap (none : Option Bool)) right) } := by
  have hsource :
      List.append
          (List.replicate (gap + 1) (none : Option Bool))
          (none :: right) =
        none :: none ::
          List.append (List.replicate gap (none : Option Bool)) right := by
    rw [List.replicate_succ]
    change none ::
        List.append (List.replicate gap (none : Option Bool))
          (none :: right) =
      none :: none ::
        List.append (List.replicate gap (none : Option Bool)) right
    rw [replicate_none_append_none_cons]
  rw [hsource]
  have hgeneric (rest : List (Option Bool)) :
      parserDescription.runConfig 2
          { state := 15
            tape := tapeAtCells [some false] (none :: none :: rest) } =
        { state := 20
          tape := tapeAtCells [some true, some true, some false] rest } := by
    cases rest <;>
      simp [parserDescription, runConfig, stepConfig,
        lookupTransition, Matches, transition, tapeAtCells,
        Tape.read, Tape.write, Tape.move, Tape.moveRight]
  exact hgeneric _

theorem parserDescription_run_exact
    (padding : Nat) (first : Bool) (rest : Word Bool) :
    parserDescription.runConfig
        (2 * padding + 2 * (first :: rest).length + 14)
        { state := parserDescription.start
          tape := parserExactSourceTape padding (first :: rest) } =
      { state := parserDescription.halt
        tape := parserTargetTape [false, false] (padding + 3)
          (first :: rest) } := by
  rw [show 2 * padding + 2 * (first :: rest).length + 14 =
    4 + (((padding + 2) + 2) +
      (2 + ((padding + 2) +
        (2 * (first :: rest).length + 2)))) by lia]
  rw [runConfig_add]
  rw [parserDescription_run_start_exact]
  rw [runConfig_add]
  rw [parserDescription_run_return_exact]
  rw [runConfig_add]
  rw [parserDescription_run_setup_exact]
  rw [runConfig_add]
  rw [parserDescription_run_seek_blanks]
  have hleft :
      List.append
          (List.replicate (padding + 2) (none : Option Bool))
          [none, some false, some false] =
        none :: List.append
          (List.replicate (padding + 2) (none : Option Bool))
          [some false, some false] := by
    exact replicate_none_append_none_cons
      (padding + 2) [some false, some false]
  rw [hleft]
  rw [parserDescription_run_scan_rewind]
  unfold parserTargetTape
  rw [show padding + 3 = (padding + 2) + 1 by lia]
  rw [List.replicate_succ]
  rfl

private theorem parserDescription_run_start_right_false
    (padding : Nat) (remaining : Word Bool) :
    parserDescription.runConfig 6
        { state := parserDescription.start
          tape := parserRightSourceTape padding false remaining } =
      { state := 11
        tape := tapeAtCells
          (List.append
            (List.replicate (padding + 4) (none : Option Bool))
            [some false])
          (none :: none :: List.append (remaining.map some) [none]) } := by
  cases remaining <;>
    simp [parserDescription, parserRightSourceTape, logicalCellBits,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
      Tape.moveRight, List.replicate_succ]

private theorem parserDescription_run_start_right_true
    (padding : Nat) (remaining : Word Bool) :
    parserDescription.runConfig 6
        { state := parserDescription.start
          tape := parserRightSourceTape padding true remaining } =
      { state := 12
        tape := tapeAtCells
          (List.append
            (List.replicate (padding + 4) (none : Option Bool))
            [some false])
          (none :: none :: List.append (remaining.map some) [none]) } := by
  cases remaining <;>
    simp [parserDescription, parserRightSourceTape, logicalCellBits,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
      Tape.moveRight, List.replicate_succ]

theorem parserDescription_run_right
    (padding : Nat) (outputFirst remainingFirst : Bool)
    (remainingRest : Word Bool) :
    parserDescription.runConfig
        (2 * padding +
          2 * (remainingFirst :: remainingRest).length + 20)
        { state := parserDescription.start
          tape := parserRightSourceTape padding outputFirst
            (remainingFirst :: remainingRest) } =
      { state := parserDescription.halt
        tape := parserTargetTape [false, true, outputFirst] (padding + 4)
          (remainingFirst :: remainingRest) } := by
  cases outputFirst with
  | false =>
      rw [show 2 * padding +
          2 * (remainingFirst :: remainingRest).length + 20 =
        6 + (((padding + 4) + 2) +
          (2 + ((padding + 4) +
            (2 * (remainingFirst :: remainingRest).length + 2)))) by lia]
      rw [runConfig_add]
      rw [parserDescription_run_start_right_false]
      rw [runConfig_add]
      rw [parserDescription_run_return_right_false]
      rw [runConfig_add]
      rw [parserDescription_run_setup_right_false]
      rw [runConfig_add]
      rw [parserDescription_run_seek_blanks]
      have hleft :
          List.append
              (List.replicate (padding + 4) (none : Option Bool))
              [some false, some true, some false] =
            none :: List.append
              (List.replicate (padding + 3) (none : Option Bool))
              [some false, some true, some false] := by
        rw [show padding + 4 = (padding + 3) + 1 by lia]
        rw [List.replicate_succ]
        rfl
      rw [hleft]
      rw [parserDescription_run_scan_rewind]
      unfold parserTargetTape
      rw [show padding + 4 = (padding + 3) + 1 by lia]
      rw [List.replicate_succ]
      rfl
  | true =>
      rw [show 2 * padding +
          2 * (remainingFirst :: remainingRest).length + 20 =
        6 + (((padding + 4) + 2) +
          (2 + ((padding + 4) +
            (2 * (remainingFirst :: remainingRest).length + 2)))) by lia]
      rw [runConfig_add]
      rw [parserDescription_run_start_right_true]
      rw [runConfig_add]
      rw [parserDescription_run_return_right_true]
      rw [runConfig_add]
      rw [parserDescription_run_setup_right_true]
      rw [runConfig_add]
      rw [parserDescription_run_seek_blanks]
      have hleft :
          List.append
              (List.replicate (padding + 4) (none : Option Bool))
              [some true, some true, some false] =
            none :: List.append
              (List.replicate (padding + 3) (none : Option Bool))
              [some true, some true, some false] := by
        rw [show padding + 4 = (padding + 3) + 1 by lia]
        rw [List.replicate_succ]
        rfl
      rw [hleft]
      rw [parserDescription_run_scan_rewind]
      unfold parserTargetTape
      rw [show padding + 4 = (padding + 3) + 1 by lia]
      rw [List.replicate_succ]
      rfl

end Tape2Projector
end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC

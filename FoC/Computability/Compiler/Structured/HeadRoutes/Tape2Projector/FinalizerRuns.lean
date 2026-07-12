import FoC.Computability.Compiler.Structured.HeadRoutes.Tape2Projector.DecoderRuns

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

def finalizerPaddedSourceTape
    (output : List Bool) (gap : Nat) : Tape Bool :=
  tapeAtCells
    (List.append
      (List.append
        (List.replicate (gap + 1) (none : Option Bool))
        (output.reverse.map some))
      [none])
    []

def finalizerWordStartTape
    (output : List Bool) (rightPadding : Nat) : Tape Bool :=
  tapeAtCells [none]
    (List.append (output.map some)
      (List.replicate rightPadding (none : Option Bool)))

theorem decoderHaltTape_equiv_finalizerPaddedSourceTape
    (output : List Bool) (gap : Nat) :
    Tape.Equiv (decoderHaltTape output gap)
      (finalizerPaddedSourceTape output gap) := by
  constructor
  · unfold decoderHaltTape finalizerPaddedSourceTape
    simp only [tapeAtCells]
    rw [show gap + 1 = gap + 1 by rfl]
    rw [List.replicate_succ]
    change
      Tape.dropTrailingNone
          (none ::
            List.append
              (List.replicate gap (none : Option Bool))
              (output.reverse.map some)) =
        Tape.dropTrailingNone
          (List.append
            (none ::
              List.append
                (List.replicate gap (none : Option Bool))
                (output.reverse.map some))
            [none])
    exact
      (FoC.Computability.dropTrailingNone_append_none
        (none ::
          List.append
            (List.replicate gap (none : Option Bool))
            (output.reverse.map some))).symm
  · constructor <;> rfl

private theorem finalizerDescription_run_scan_left_blanks
    (padding : Nat) (anchor : Bool)
    (left right : List (Option Bool)) :
    finalizerDescription.runConfig (padding + 1)
        { state := 0
          tape := tapeAtCells
            (List.append
              (List.replicate padding (none : Option Bool))
              (some anchor :: left))
            (none :: right) } =
      { state := 0
        tape := tapeAtCells left
          (some anchor ::
            List.append
              (List.replicate (padding + 1) (none : Option Bool)) right) } := by
  induction padding generalizing right with
  | zero =>
      cases anchor <;> cases left <;> cases right <;>
        simp [finalizerDescription, runConfig, stepConfig,
          lookupTransition, Matches, transition, tapeAtCells,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          List.replicate_succ]
  | succ padding ih =>
      rw [show Nat.succ padding + 1 = 1 + (padding + 1) by lia]
      rw [runConfig_add]
      have hstep :
          finalizerDescription.runConfig 1
              { state := 0
                tape := tapeAtCells
                  (List.append
                    (List.replicate (Nat.succ padding)
                      (none : Option Bool))
                    (some anchor :: left))
                  (none :: right) } =
            { state := 0
              tape := tapeAtCells
                (List.append
                  (List.replicate padding (none : Option Bool))
                  (some anchor :: left))
                (none :: none :: right) } := by
        cases anchor <;> cases left <;> cases right <;>
          simp [finalizerDescription, runConfig, stepConfig,
            lookupTransition, Matches, transition, tapeAtCells,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft,
            List.replicate_succ]
      rw [hstep]
      rw [ih (none :: right)]
      have hright :
          List.append
              (List.replicate (padding + 1) (none : Option Bool))
              (none :: right) =
            List.append
              (List.replicate (Nat.succ padding + 1)
                (none : Option Bool)) right := by
        rw [replicate_none_append_none_cons]
        rw [show Nat.succ padding + 1 = (padding + 1) + 1 by lia]
        rw [List.replicate_succ]
        rfl
      rw [hright]
      rw [show Nat.succ padding + 1 = 1 + (padding + 1) by lia]

private theorem finalizerDescription_run_rewind_output
    (anchor : Bool) (leftward : Word Bool)
    (right : List (Option Bool)) :
    finalizerDescription.runConfig (leftward.length + 1)
        { state := 1
          tape := Tape.move Direction.left
            (tapeAtCells
              (List.append (leftward.map some) [none])
              (some anchor :: right)) } =
      { state := 2
        tape := tapeAtCells [none]
          (List.append ((anchor :: leftward).reverse.map some) right) } := by
  induction leftward generalizing anchor right with
  | nil =>
      cases anchor <;> cases right <;>
        simp [finalizerDescription, runConfig, stepConfig,
          lookupTransition, Matches, transition, tapeAtCells,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          Tape.moveRight]
  | cons next rest ih =>
      rw [show (next :: rest).length + 1 = 1 + (rest.length + 1) by
        simp only [List.length_cons]
        lia]
      rw [runConfig_add]
      have hstep :
          finalizerDescription.runConfig 1
              { state := 1
                tape := Tape.move Direction.left
                  (tapeAtCells
                    (List.append ((next :: rest).map some) [none])
                    (some anchor :: right)) } =
            { state := 1
              tape := Tape.move Direction.left
                (tapeAtCells
                  (List.append (rest.map some) [none])
                  (some next :: some anchor :: right)) } := by
        cases anchor <;> cases next <;> cases rest <;> cases right <;>
          simp [finalizerDescription, runConfig, stepConfig,
            lookupTransition, Matches, transition, tapeAtCells,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      rw [hstep]
      rw [ih next (some anchor :: right)]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem finalizerDescription_run_rewind
    (outputFirst : Bool) (outputRest : List Bool) (gap : Nat) :
    finalizerDescription.runConfig
        (gap + (outputFirst :: outputRest).length + 3)
        { state := finalizerDescription.start
          tape := finalizerPaddedSourceTape
            (outputFirst :: outputRest) gap } =
      { state := 2
        tape := finalizerWordStartTape
          (outputFirst :: outputRest) (gap + 2) } := by
  cases hbackward : (outputFirst :: outputRest).reverse with
  | nil =>
      simp at hbackward
  | cons anchor leftward =>
      have hforward : (anchor :: leftward).reverse =
          outputFirst :: outputRest := by
        rw [← hbackward]
        simp
      have hlength : leftward.length + 1 =
          (outputFirst :: outputRest).length := by
        have := congrArg List.length hbackward
        simpa using this.symm
      rw [show gap + (outputFirst :: outputRest).length + 3 =
        ((gap + 1) + 1) + (1 + (leftward.length + 1)) by lia]
      rw [runConfig_add]
      unfold finalizerPaddedSourceTape
      rw [hbackward]
      rw [List.map_cons]
      have hsource :
          List.append
              (List.append
                (List.replicate (gap + 1) (none : Option Bool))
                (some anchor :: leftward.map some))
              [none] =
            List.append
              (List.replicate (gap + 1) (none : Option Bool))
              (some anchor :: List.append (leftward.map some) [none]) := by
        simp [List.append_assoc]
      rw [hsource]
      rw [show finalizerDescription.start = 0 by rfl]
      have htape :
          tapeAtCells
              (List.append
                (List.replicate (gap + 1) (none : Option Bool))
                (some anchor :: List.append (leftward.map some) [none]))
              [] =
            tapeAtCells
              (List.append
                (List.replicate (gap + 1) (none : Option Bool))
                (some anchor :: List.append (leftward.map some) [none]))
              [none] :=
        rfl
      rw [htape]
      rw [finalizerDescription_run_scan_left_blanks]
      rw [show gap + 1 + 1 = gap + 2 by lia]
      have hpadding :
          List.append
              (List.replicate (gap + 2) (none : Option Bool)) [] =
            List.replicate (gap + 2) (none : Option Bool) :=
        List.append_nil _
      rw [hpadding]
      rw [runConfig_add]
      have hanchor :
          finalizerDescription.runConfig 1
              { state := 0
                tape := tapeAtCells
                  (List.append (leftward.map some) [none])
                  (some anchor ::
                    List.replicate (gap + 2) (none : Option Bool)) } =
            { state := 1
              tape := Tape.move Direction.left
                (tapeAtCells
                  (List.append (leftward.map some) [none])
                  (some anchor ::
                    List.replicate (gap + 2) (none : Option Bool))) } := by
        cases anchor <;> cases leftward <;>
          simp [finalizerDescription, runConfig, stepConfig,
            lookupTransition, Matches, transition, tapeAtCells,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      rw [hanchor]
      rw [finalizerDescription_run_rewind_output]
      unfold finalizerWordStartTape
      rw [hforward]

private theorem finalizerDescription_run_exact_first_bit
    (bit : Bool) (right : List (Option Bool)) :
    finalizerDescription.runConfig 5
        { state := 4
          tape := tapeAtCells [none, none, none] (some bit :: right) } =
      { state := 5
        tape := tapeAtCells [none, none, some bit, none] right } := by
  cases bit <;> cases right <;>
    simp [finalizerDescription, runConfig, stepConfig,
      lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

private theorem finalizerDescription_run_exact_next_bit
    (bit : Bool) (outputRev : List Bool)
    (right : List (Option Bool)) :
    finalizerDescription.runConfig 5
        { state := 5
          tape := tapeAtCells
            (none :: none ::
              List.append (outputRev.map some) [none])
            (some bit :: right) } =
      { state := 5
        tape := tapeAtCells
          (none :: none :: some bit ::
            List.append (outputRev.map some) [none]) right } := by
  cases bit <;> cases outputRev <;> cases right <;>
    simp [finalizerDescription, runConfig, stepConfig,
      lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

private theorem finalizerDescription_run_exact_rest
    (bits outputRev : List Bool)
    (right : List (Option Bool)) :
    finalizerDescription.runConfig (5 * bits.length)
        { state := 5
          tape := tapeAtCells
            (none :: none ::
              List.append (outputRev.map some) [none])
            (List.append (bits.map some) right) } =
      { state := 5
        tape := tapeAtCells
          (none :: none ::
            List.append
              ((List.append bits.reverse outputRev).map some) [none])
          right } := by
  induction bits generalizing outputRev with
  | nil =>
      rfl
  | cons bit rest ih =>
      rw [show 5 * (bit :: rest).length = 5 + 5 * rest.length by
        simp only [List.length_cons]
        lia]
      rw [runConfig_add]
      rw [List.map_cons]
      have hright :
          List.append (some bit :: rest.map some) right =
            some bit :: List.append (rest.map some) right :=
        rfl
      rw [hright]
      rw [finalizerDescription_run_exact_next_bit]
      have hleft :
          none :: none :: some bit ::
              List.append (outputRev.map some) [none] =
            none :: none ::
              List.append ((bit :: outputRev).map some) [none] :=
        rfl
      rw [hleft]
      rw [ih (bit :: outputRev)]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

private theorem finalizerDescription_run_exact_shift
    (first : Bool) (rest : List Bool)
    (right : List (Option Bool)) :
    finalizerDescription.runConfig (5 * (first :: rest).length)
        { state := 4
          tape := tapeAtCells [none, none, none]
            (List.append ((first :: rest).map some) right) } =
      { state := 5
        tape := tapeAtCells
          (none :: none ::
            List.append ((first :: rest).reverse.map some) [none])
          right } := by
  rw [show 5 * (first :: rest).length = 5 + 5 * rest.length by
    simp only [List.length_cons]
    lia]
  rw [runConfig_add]
  rw [List.map_cons]
  have hright :
      List.append (some first :: rest.map some) right =
        some first :: List.append (rest.map some) right :=
    rfl
  rw [hright]
  rw [finalizerDescription_run_exact_first_bit]
  have hleft :
      [none, none, some first, none] =
        none :: none ::
          List.append (([first] : List Bool).map some) [none] :=
    rfl
  rw [hleft]
  rw [finalizerDescription_run_exact_rest]
  simp [List.reverse_cons, List.map_append, List.append_assoc]

private theorem finalizerDescription_run_exact_rewind_shifted
    (current : Bool) (leftward : List Bool)
    (right : List (Option Bool)) :
    finalizerDescription.runConfig (leftward.length + 2)
        { state := 20
          tape := tapeAtCells
            (List.append (leftward.map some) [none])
            (some current :: right) } =
      { state := finalizerDescription.halt
        tape := tapeAtCells [none]
          (List.append ((current :: leftward).reverse.map some) right) } := by
  rw [show leftward.length + 2 = 1 + (leftward.length + 1) by lia]
  rw [runConfig_add]
  have hcurrent :
      finalizerDescription.runConfig 1
          { state := 20
            tape := tapeAtCells
              (List.append (leftward.map some) [none])
              (some current :: right) } =
        { state := 22
          tape := Tape.move Direction.left
            (tapeAtCells
              (List.append (leftward.map some) [none])
              (some current :: right)) } := by
    cases current <;> cases leftward <;> cases right <;>
      simp [finalizerDescription, runConfig, stepConfig,
        lookupTransition, Matches, transition, tapeAtCells,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft]
  rw [hcurrent]
  induction leftward generalizing current right with
  | nil =>
      cases current <;> cases right <;>
        simp [finalizerDescription, runConfig, stepConfig,
          lookupTransition, Matches, transition, tapeAtCells,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          Tape.moveRight]
  | cons next rest ih =>
      rw [show (next :: rest).length + 1 = 1 + (rest.length + 1) by
        simp only [List.length_cons]
        lia]
      rw [runConfig_add]
      have hstep :
          finalizerDescription.runConfig 1
              { state := 22
                tape := Tape.move Direction.left
                  (tapeAtCells
                    (List.append ((next :: rest).map some) [none])
                    (some current :: right)) } =
            { state := 22
              tape := Tape.move Direction.left
                (tapeAtCells
                  (List.append (rest.map some) [none])
                  (some next :: some current :: right)) } := by
        cases current <;> cases next <;> cases rest <;> cases right <;>
          simp [finalizerDescription, runConfig, stepConfig,
            lookupTransition, Matches, transition, tapeAtCells,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      rw [hstep]
      have hnext :
          finalizerDescription.runConfig 1
              { state := 20
                tape := tapeAtCells
                  (List.append (rest.map some) [none])
                  (some next :: some current :: right) } =
            { state := 22
              tape := Tape.move Direction.left
                (tapeAtCells
                  (List.append (rest.map some) [none])
                  (some next :: some current :: right)) } := by
        cases next <;> cases rest <;> cases right <;>
          simp [finalizerDescription, runConfig, stepConfig,
            lookupTransition, Matches, transition, tapeAtCells,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      rw [ih next (some current :: right) hnext]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

private theorem finalizerDescription_run_exact_finish
    (first : Bool) (rest : List Bool)
    (right : List (Option Bool)) :
    finalizerDescription.runConfig ((first :: rest).length + 4)
        { state := 5
          tape := tapeAtCells
            (none :: none ::
              List.append ((first :: rest).reverse.map some) [none])
            (none :: right) } =
      { state := finalizerDescription.halt
        tape := tapeAtCells [none]
          (List.append ((first :: rest).map some)
            (none :: none :: none :: right)) } := by
  cases hbackward : (first :: rest).reverse with
  | nil =>
      simp at hbackward
  | cons current leftward =>
      have hforward : (current :: leftward).reverse = first :: rest := by
        rw [← hbackward]
        simp
      have hlength : leftward.length + 1 = (first :: rest).length := by
        have := congrArg List.length hbackward
        simpa using this.symm
      rw [show (first :: rest).length + 4 =
        3 + (leftward.length + 2) by lia]
      rw [runConfig_add]
      have hblanks :
          finalizerDescription.runConfig 3
              { state := 5
                tape := tapeAtCells
                  (none :: none ::
                    List.append ((current :: leftward).map some) [none])
                  (none :: right) } =
            { state := 20
              tape := Tape.move Direction.left
                (tapeAtCells
                  (List.append ((current :: leftward).map some) [none])
                  (none :: none :: none :: right)) } := by
        cases current <;> cases leftward <;> cases right <;>
          simp [finalizerDescription, runConfig, stepConfig,
            lookupTransition, Matches, transition, tapeAtCells,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      rw [hblanks]
      have hmove :
          Tape.move Direction.left
              (tapeAtCells
                (List.append ((current :: leftward).map some) [none])
                (none :: none :: none :: right)) =
            tapeAtCells (List.append (leftward.map some) [none])
              (some current :: none :: none :: none :: right) := by
        cases current <;> cases leftward <;> cases right <;>
          simp [tapeAtCells, Tape.move, Tape.moveLeft]
      rw [hmove]
      rw [finalizerDescription_run_exact_rewind_shifted]
      rw [hforward]

def finalizerExactHaltTape
    (bits : List Bool) (rightPadding : Nat) : Tape Bool :=
  tapeAtCells [none]
    (List.append (bits.map some)
      (none :: none :: none ::
        List.replicate rightPadding (none : Option Bool)))

theorem finalizerExactHaltTape_equiv_input
    (bits : List Bool) (rightPadding : Nat) :
    Tape.Equiv (finalizerExactHaltTape bits rightPadding)
      (Tape.input bits) := by
  have hsuffix :
      none :: none :: none ::
          List.replicate rightPadding (none : Option Bool) =
        List.replicate (rightPadding + 3) (none : Option Bool) := by
    rw [show rightPadding + 3 =
      ((rightPadding + 1) + 1) + 1 by lia]
    rw [List.replicate_succ, List.replicate_succ, List.replicate_succ]
  cases bits with
  | nil =>
      simp [finalizerExactHaltTape, Tape.Equiv, Tape.input, Tape.blank,
        tapeAtCells, Tape.dropTrailingNone,
        FoC.Computability.dropTrailingNone_replicate_none]
  | cons first rest =>
      unfold finalizerExactHaltTape
      rw [hsuffix]
      simp [Tape.Equiv, Tape.input, tapeAtCells, Tape.dropTrailingNone,
        FoC.Computability.dropTrailingNone_append_replicate_none]

private theorem finalizerDescription_run_exact_metadata
    (bits : List Bool) (rightPadding : Nat) :
    finalizerDescription.runConfig 2
        { state := 2
          tape := finalizerWordStartTape
            (List.append [false, false] bits) rightPadding } =
      { state := 4
        tape := tapeAtCells [none, none, none]
          (List.append (bits.map some)
            (List.replicate rightPadding (none : Option Bool))) } := by
  cases bits <;> cases rightPadding <;>
    simp [finalizerDescription, finalizerWordStartTape, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveRight,
      List.replicate_succ]

private theorem finalizerDescription_run_exact_nonempty_core
    (first : Bool) (rest : List Bool) (rightTail : Nat) :
    finalizerDescription.runConfig (6 * (first :: rest).length + 6)
        { state := 2
          tape := finalizerWordStartTape
            (List.append [false, false] (first :: rest))
            (rightTail + 1) } =
      { state := finalizerDescription.halt
        tape := finalizerExactHaltTape (first :: rest) rightTail } := by
  rw [show 6 * (first :: rest).length + 6 =
    2 + (5 * (first :: rest).length +
      ((first :: rest).length + 4)) by lia]
  rw [runConfig_add]
  rw [finalizerDescription_run_exact_metadata]
  rw [runConfig_add]
  rw [finalizerDescription_run_exact_shift]
  rw [show rightTail + 1 = Nat.succ rightTail by rfl]
  rw [List.replicate_succ]
  rw [finalizerDescription_run_exact_finish]
  unfold finalizerExactHaltTape
  cases rest <;> cases rightTail <;>
    simp [tapeAtCells, List.replicate_succ]

private theorem finalizerDescription_run_exact_empty_core
    (rightTail : Nat) :
    finalizerDescription.runConfig 3
        { state := 2
          tape := finalizerWordStartTape [false, false]
            (rightTail + 1) } =
      { state := finalizerDescription.halt
        tape := tapeAtCells [none, none]
          (none :: none ::
            List.replicate rightTail (none : Option Bool)) } := by
  rw [show 3 = 2 + 1 by decide]
  rw [runConfig_add]
  change
    finalizerDescription.runConfig 1
        (finalizerDescription.runConfig 2
          { state := 2
            tape := finalizerWordStartTape
              (List.append [false, false] ([] : List Bool))
              (rightTail + 1) }) =
      { state := finalizerDescription.halt
        tape := tapeAtCells [none, none]
          (none :: none ::
            List.replicate rightTail (none : Option Bool)) }
  rw [finalizerDescription_run_exact_metadata]
  rw [show rightTail + 1 = Nat.succ rightTail by rfl]
  rw [List.replicate_succ]
  cases rightTail <;>
    simp [finalizerDescription, runConfig, stepConfig,
      lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft,
      List.replicate_succ]

private theorem finalizerDescription_run_exact_nonempty_padded
    (first : Bool) (rest : List Bool) (gap : Nat) :
    finalizerDescription.runConfig
        ((gap + (List.append [false, false] (first :: rest)).length + 3) +
          (6 * (first :: rest).length + 6))
        { state := finalizerDescription.start
          tape := finalizerPaddedSourceTape
            (List.append [false, false] (first :: rest)) gap } =
      { state := finalizerDescription.halt
        tape := finalizerExactHaltTape (first :: rest) (gap + 1) } := by
  rw [runConfig_add]
  rw [show List.append [false, false] (first :: rest) =
    false :: false :: first :: rest by rfl]
  rw [finalizerDescription_run_rewind]
  rw [show gap + 2 = (gap + 1) + 1 by lia]
  exact finalizerDescription_run_exact_nonempty_core first rest (gap + 1)

private theorem finalizerDescription_run_exact_empty_padded
    (gap : Nat) :
    finalizerDescription.runConfig
        ((gap + ([false, false] : List Bool).length + 3) + 3)
        { state := finalizerDescription.start
          tape := finalizerPaddedSourceTape [false, false] gap } =
      { state := finalizerDescription.halt
        tape := tapeAtCells [none, none]
          (none :: none ::
            List.replicate (gap + 1) (none : Option Bool)) } := by
  rw [runConfig_add]
  rw [finalizerDescription_run_rewind]
  rw [show gap + 2 = (gap + 1) + 1 by lia]
  exact finalizerDescription_run_exact_empty_core (gap + 1)

theorem finalizerDescription_haltsFromTapeEquiv_exact
    (bits : List Bool) (gap : Nat) :
    finalizerDescription.HaltsFromTapeEquiv
      (decoderHaltTape (List.append [false, false] bits) gap)
      (Tape.input bits) := by
  have hinput := decoderHaltTape_equiv_finalizerPaddedSourceTape
    (List.append [false, false] bits) gap
  cases bits with
  | nil =>
      let actual := tapeAtCells [none, none]
        (none :: none ::
          List.replicate (gap + 1) (none : Option Bool))
      have hpadded :
          finalizerDescription.HaltsFromTape
            (finalizerPaddedSourceTape [false, false] gap) actual := by
        refine ⟨(gap + ([false, false] : List Bool).length + 3) + 3, ?_⟩
        constructor <;>
          rw [finalizerDescription_run_exact_empty_padded]
      rcases MachineDescription.HaltsFromTapeEquiv_of_input_equiv
          (D := finalizerDescription)
          (Tin := finalizerPaddedSourceTape [false, false] gap)
          (Tin' := decoderHaltTape [false, false] gap)
          (Tout := actual)
          (Tape.Equiv.symm hinput) hpadded with
        ⟨actual', hactual', hequiv⟩
      refine ⟨actual', hactual', Tape.Equiv.trans hequiv ?_⟩
      simp [actual, Tape.Equiv, Tape.input, Tape.blank, tapeAtCells,
        Tape.dropTrailingNone,
        FoC.Computability.dropTrailingNone_replicate_none]
  | cons first rest =>
      have hpadded :
          finalizerDescription.HaltsFromTape
            (finalizerPaddedSourceTape
              (List.append [false, false] (first :: rest)) gap)
            (finalizerExactHaltTape (first :: rest) (gap + 1)) := by
        refine
          ⟨(gap +
              (List.append [false, false] (first :: rest)).length + 3) +
            (6 * (first :: rest).length + 6), ?_⟩
        constructor <;>
          rw [finalizerDescription_run_exact_nonempty_padded]
      rcases MachineDescription.HaltsFromTapeEquiv_of_input_equiv
          (D := finalizerDescription)
          (Tin := finalizerPaddedSourceTape
            (List.append [false, false] (first :: rest)) gap)
          (Tin' := decoderHaltTape
            (List.append [false, false] (first :: rest)) gap)
          (Tout := finalizerExactHaltTape (first :: rest) (gap + 1))
          (Tape.Equiv.symm hinput) hpadded with
        ⟨actual, hactual, hequiv⟩
      exact
        ⟨actual, hactual,
          Tape.Equiv.trans hequiv
            (finalizerExactHaltTape_equiv_input
              (first :: rest) (gap + 1))⟩

private theorem finalizerDescription_run_right_first_bit
    (bit : Bool) (right : List (Option Bool)) :
    finalizerDescription.runConfig 5
        { state := 6
          tape := tapeAtCells [none, none, none] (some bit :: right) } =
      { state := 7
        tape := tapeAtCells [none, none, some bit, none] right } := by
  cases bit <;> cases right <;>
    simp [finalizerDescription, runConfig, stepConfig,
      lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

private theorem finalizerDescription_run_right_next_bit
    (bit : Bool) (outputRev : List Bool)
    (right : List (Option Bool)) :
    finalizerDescription.runConfig 5
        { state := 7
          tape := tapeAtCells
            (none :: none ::
              List.append (outputRev.map some) [none])
            (some bit :: right) } =
      { state := 7
        tape := tapeAtCells
          (none :: none :: some bit ::
            List.append (outputRev.map some) [none]) right } := by
  cases bit <;> cases outputRev <;> cases right <;>
    simp [finalizerDescription, runConfig, stepConfig,
      lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

private theorem finalizerDescription_run_right_rest
    (bits outputRev : List Bool)
    (right : List (Option Bool)) :
    finalizerDescription.runConfig (5 * bits.length)
        { state := 7
          tape := tapeAtCells
            (none :: none ::
              List.append (outputRev.map some) [none])
            (List.append (bits.map some) right) } =
      { state := 7
        tape := tapeAtCells
          (none :: none ::
            List.append
              ((List.append bits.reverse outputRev).map some) [none])
          right } := by
  induction bits generalizing outputRev with
  | nil =>
      rfl
  | cons bit rest ih =>
      rw [show 5 * (bit :: rest).length = 5 + 5 * rest.length by
        simp only [List.length_cons]
        lia]
      rw [runConfig_add]
      rw [List.map_cons]
      have hright :
          List.append (some bit :: rest.map some) right =
            some bit :: List.append (rest.map some) right :=
        rfl
      rw [hright]
      rw [finalizerDescription_run_right_next_bit]
      have hleft :
          none :: none :: some bit ::
              List.append (outputRev.map some) [none] =
            none :: none ::
              List.append ((bit :: outputRev).map some) [none] :=
        rfl
      rw [hleft]
      rw [ih (bit :: outputRev)]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

private theorem finalizerDescription_run_right_shift
    (first : Bool) (rest : List Bool)
    (right : List (Option Bool)) :
    finalizerDescription.runConfig (5 * (first :: rest).length)
        { state := 6
          tape := tapeAtCells [none, none, none]
            (List.append ((first :: rest).map some) right) } =
      { state := 7
        tape := tapeAtCells
          (none :: none ::
            List.append ((first :: rest).reverse.map some) [none])
          right } := by
  rw [show 5 * (first :: rest).length = 5 + 5 * rest.length by
    simp only [List.length_cons]
    lia]
  rw [runConfig_add]
  rw [List.map_cons]
  have hright :
      List.append (some first :: rest.map some) right =
        some first :: List.append (rest.map some) right :=
    rfl
  rw [hright]
  rw [finalizerDescription_run_right_first_bit]
  have hleft :
      [none, none, some first, none] =
        none :: none ::
          List.append (([first] : List Bool).map some) [none] :=
    rfl
  rw [hleft]
  rw [finalizerDescription_run_right_rest]
  simp [List.reverse_cons, List.map_append, List.append_assoc]

private theorem finalizerDescription_run_right_metadata
    (bits : List Bool) (rightPadding : Nat) :
    finalizerDescription.runConfig 2
        { state := 2
          tape := finalizerWordStartTape
            (List.append [false, true] bits) rightPadding } =
      { state := 6
        tape := tapeAtCells [none, none, none]
          (List.append (bits.map some)
            (List.replicate rightPadding (none : Option Bool))) } := by
  cases bits <;> cases rightPadding <;>
    simp [finalizerDescription, finalizerWordStartTape, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveRight,
      List.replicate_succ]

private theorem finalizerDescription_run_state23_rewind
    (anchor : Bool) (leftward : List Bool)
    (right : List (Option Bool)) :
    finalizerDescription.runConfig (leftward.length + 1)
        { state := 23
          tape := Tape.move Direction.left
            (tapeAtCells
              (List.append (leftward.map some) [none])
              (some anchor :: right)) } =
      { state := 24
        tape := tapeAtCells [none]
          (List.append ((anchor :: leftward).reverse.map some) right) } := by
  induction leftward generalizing anchor right with
  | nil =>
      cases anchor <;> cases right <;>
        simp [finalizerDescription, runConfig, stepConfig,
          lookupTransition, Matches, transition, tapeAtCells,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          Tape.moveRight]
  | cons next rest ih =>
      rw [show (next :: rest).length + 1 = 1 + (rest.length + 1) by
        simp only [List.length_cons]
        lia]
      rw [runConfig_add]
      have hstep :
          finalizerDescription.runConfig 1
              { state := 23
                tape := Tape.move Direction.left
                  (tapeAtCells
                    (List.append ((next :: rest).map some) [none])
                    (some anchor :: right)) } =
            { state := 23
              tape := Tape.move Direction.left
                (tapeAtCells
                  (List.append (rest.map some) [none])
                  (some next :: some anchor :: right)) } := by
        cases anchor <;> cases next <;> cases rest <;> cases right <;>
          simp [finalizerDescription, runConfig, stepConfig,
            lookupTransition, Matches, transition, tapeAtCells,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      rw [hstep]
      rw [ih next (some anchor :: right)]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

private theorem finalizerDescription_run_right_rewind_shifted
    (current : Bool) (leftward : List Bool)
    (right : List (Option Bool)) :
    finalizerDescription.runConfig (leftward.length + 2)
        { state := 21
          tape := tapeAtCells
            (List.append (leftward.map some) [none])
            (some current :: right) } =
      { state := 24
        tape := tapeAtCells [none]
          (List.append ((current :: leftward).reverse.map some) right) } := by
  rw [show leftward.length + 2 = 1 + (leftward.length + 1) by lia]
  rw [runConfig_add]
  have hcurrent :
      finalizerDescription.runConfig 1
          { state := 21
            tape := tapeAtCells
              (List.append (leftward.map some) [none])
              (some current :: right) } =
        { state := 23
          tape := Tape.move Direction.left
            (tapeAtCells
              (List.append (leftward.map some) [none])
              (some current :: right)) } := by
    cases current <;> cases leftward <;> cases right <;>
      simp [finalizerDescription, runConfig, stepConfig,
        lookupTransition, Matches, transition, tapeAtCells,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft]
  rw [hcurrent]
  exact finalizerDescription_run_state23_rewind current leftward right

private theorem finalizerDescription_run_right_focus
    (first : Bool) (rest : List Bool)
    (right : List (Option Bool)) :
    finalizerDescription.runConfig 1
        { state := 24
          tape := tapeAtCells [none]
            (List.append ((first :: rest).map some) right) } =
      { state := finalizerDescription.halt
        tape := Tape.move Direction.right
          (tapeAtCells [none]
            (List.append ((first :: rest).map some) right)) } := by
  cases first <;> cases rest <;> cases right <;>
    simp [finalizerDescription, runConfig, stepConfig,
      lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

private theorem finalizerDescription_run_right_finish
    (first : Bool) (rest : List Bool)
    (right : List (Option Bool)) :
    finalizerDescription.runConfig ((first :: rest).length + 5)
        { state := 7
          tape := tapeAtCells
            (none :: none ::
              List.append ((first :: rest).reverse.map some) [none])
            (none :: right) } =
      { state := finalizerDescription.halt
        tape := Tape.move Direction.right
          (tapeAtCells [none]
            (List.append ((first :: rest).map some)
              (none :: none :: none :: right))) } := by
  cases hbackward : (first :: rest).reverse with
  | nil =>
      simp at hbackward
  | cons current leftward =>
      have hforward : (current :: leftward).reverse = first :: rest := by
        rw [← hbackward]
        simp
      have hlength : leftward.length + 1 = (first :: rest).length := by
        have := congrArg List.length hbackward
        simpa using this.symm
      rw [show (first :: rest).length + 5 =
        3 + ((leftward.length + 2) + 1) by lia]
      rw [runConfig_add]
      have hblanks :
          finalizerDescription.runConfig 3
              { state := 7
                tape := tapeAtCells
                  (none :: none ::
                    List.append ((current :: leftward).map some) [none])
                  (none :: right) } =
            { state := 21
              tape := Tape.move Direction.left
                (tapeAtCells
                  (List.append ((current :: leftward).map some) [none])
                  (none :: none :: none :: right)) } := by
        cases current <;> cases leftward <;> cases right <;>
          simp [finalizerDescription, runConfig, stepConfig,
            lookupTransition, Matches, transition, tapeAtCells,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      rw [hblanks]
      have hmove :
          Tape.move Direction.left
              (tapeAtCells
                (List.append ((current :: leftward).map some) [none])
                (none :: none :: none :: right)) =
            tapeAtCells (List.append (leftward.map some) [none])
              (some current :: none :: none :: none :: right) := by
        cases current <;> cases leftward <;> cases right <;>
          simp [tapeAtCells, Tape.move, Tape.moveLeft]
      rw [hmove]
      rw [runConfig_add]
      rw [finalizerDescription_run_right_rewind_shifted]
      rw [hforward]
      rw [finalizerDescription_run_right_focus]

private theorem finalizerDescription_run_right_core
    (first : Bool) (rest : List Bool) (rightTail : Nat) :
    finalizerDescription.runConfig (6 * (first :: rest).length + 7)
        { state := 2
          tape := finalizerWordStartTape
            (List.append [false, true] (first :: rest))
            (rightTail + 1) } =
      { state := finalizerDescription.halt
        tape := Tape.move Direction.right
          (finalizerExactHaltTape (first :: rest) rightTail) } := by
  rw [show 6 * (first :: rest).length + 7 =
    2 + (5 * (first :: rest).length +
      ((first :: rest).length + 5)) by lia]
  rw [runConfig_add]
  rw [finalizerDescription_run_right_metadata]
  rw [runConfig_add]
  rw [finalizerDescription_run_right_shift]
  rw [show rightTail + 1 = Nat.succ rightTail by rfl]
  rw [List.replicate_succ]
  rw [finalizerDescription_run_right_finish]
  unfold finalizerExactHaltTape
  cases rest <;> cases rightTail <;>
    simp [tapeAtCells, Tape.move, Tape.moveRight, List.replicate_succ]

private theorem finalizerDescription_run_right_padded
    (first : Bool) (rest : List Bool) (gap : Nat) :
    finalizerDescription.runConfig
        ((gap + (List.append [false, true] (first :: rest)).length + 3) +
          (6 * (first :: rest).length + 7))
        { state := finalizerDescription.start
          tape := finalizerPaddedSourceTape
            (List.append [false, true] (first :: rest)) gap } =
      { state := finalizerDescription.halt
        tape := Tape.move Direction.right
          (finalizerExactHaltTape (first :: rest) (gap + 1)) } := by
  rw [runConfig_add]
  rw [show List.append [false, true] (first :: rest) =
    false :: true :: first :: rest by rfl]
  rw [finalizerDescription_run_rewind]
  rw [show gap + 2 = (gap + 1) + 1 by lia]
  exact finalizerDescription_run_right_core first rest (gap + 1)

theorem finalizerDescription_haltsFromTapeEquiv_right
    (first : Bool) (rest : List Bool) (gap : Nat) :
    finalizerDescription.HaltsFromTapeEquiv
      (decoderHaltTape
        (List.append [false, true] (first :: rest)) gap)
      (Tape.move Direction.right (Tape.input (first :: rest))) := by
  have hinput := decoderHaltTape_equiv_finalizerPaddedSourceTape
    (List.append [false, true] (first :: rest)) gap
  have hpadded :
      finalizerDescription.HaltsFromTape
        (finalizerPaddedSourceTape
          (List.append [false, true] (first :: rest)) gap)
        (Tape.move Direction.right
          (finalizerExactHaltTape (first :: rest) (gap + 1))) := by
    refine
      ⟨(gap + (List.append [false, true] (first :: rest)).length + 3) +
        (6 * (first :: rest).length + 7), ?_⟩
    constructor <;>
      rw [finalizerDescription_run_right_padded]
  rcases MachineDescription.HaltsFromTapeEquiv_of_input_equiv
      (D := finalizerDescription)
      (Tin := finalizerPaddedSourceTape
        (List.append [false, true] (first :: rest)) gap)
      (Tin' := decoderHaltTape
        (List.append [false, true] (first :: rest)) gap)
      (Tout := Tape.move Direction.right
        (finalizerExactHaltTape (first :: rest) (gap + 1)))
      (Tape.Equiv.symm hinput) hpadded with
    ⟨actual, hactual, hequiv⟩
  exact
    ⟨actual, hactual,
      Tape.Equiv.trans hequiv
        (Tape.Equiv.move
          (finalizerExactHaltTape_equiv_input
            (first :: rest) (gap + 1)) Direction.right)⟩

end Tape2Projector
end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC

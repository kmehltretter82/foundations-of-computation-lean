import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.GuardedEgress.MetadataCycles

namespace FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
namespace GuardedEgress.MetadataTokenCopy

open Languages MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace Execution

private theorem run_enter_final
    (left right : List (Option Bool)) :
    description.runConfig 2
        { state := 2
          tape := tapeAtCells (none :: left) (some false :: right) } =
      { state := 94
        tape := tapeAtCells (none :: left) (none :: right) } := by
  cases left <;> cases right <;>
    simp [runConfig, stepConfig,
      show lookupTransition description 2 (some false) =
        some (transition 2 (some false) none Direction.left 3) by decide,
      show lookupTransition description 3 none =
        some (transition 3 none none Direction.right 94) by decide,
      transition, tapeAtCells, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft, Tape.moveRight]

private theorem step_final_94_blank
    (left right : List (Option Bool)) :
    description.runConfig 1
        { state := 94
          tape := tapeAtCells left (none :: right) } =
      { state := 94
        tape := tapeAtCells (none :: left) right } := by
  cases right <;>
    simp [runConfig, stepConfig,
      show lookupTransition description 94 none =
        some (transition 94 none none Direction.right 94) by decide,
      transition, tapeAtCells, Tape.read, Tape.write,
      Tape.move, Tape.moveRight]

private theorem run_final_94_blanks
    (n : Nat) (left right : List (Option Bool)) :
    description.runConfig n
        { state := 94
          tape := tapeAtCells left
            (List.append (List.replicate n (none : Option Bool)) right) } =
      { state := 94
        tape := tapeAtCells
          (List.append (List.replicate n (none : Option Bool)) left)
          right } := by
  induction n generalizing left with
  | zero => simp [runConfig]
  | succ n ih =>
      rw [show n + 1 = 1 + n by lia]
      rw [runConfig_add]
      rw [show List.replicate (1 + n) (none : Option Bool) =
        none :: List.replicate n none by
          rw [show 1 + n = Nat.succ n by lia]
          rfl]
      rw [show
        List.append (none :: List.replicate n (none : Option Bool)) right =
          none :: List.append (List.replicate n none) right by rfl]
      rw [step_final_94_blank]
      rw [ih (none :: left)]
      rw [replicate_none_append_none_cons]
      rfl

private theorem step_final_94_marker
    (left right : List (Option Bool)) :
    description.runConfig 1
        { state := 94
          tape := tapeAtCells left (some true :: right) } =
      { state := 95
        tape := Tape.move Direction.left
          (tapeAtCells left (none :: right)) } := by
  cases left <;> cases right <;>
    simp [runConfig, stepConfig,
      show lookupTransition description 94 (some true) =
        some (transition 94 (some true) none Direction.left 95) by decide,
      transition, tapeAtCells, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft]

private theorem step_final_95_blank
    (left right : List (Option Bool)) :
    description.runConfig 1
        { state := 95
          tape := Tape.move Direction.left
            (tapeAtCells (none :: left) (none :: right)) } =
      { state := 95
        tape := Tape.move Direction.left
          (tapeAtCells left (none :: none :: right)) } := by
  cases left <;> cases right <;>
    simp [runConfig, stepConfig,
      show lookupTransition description 95 none =
        some (transition 95 none none Direction.left 95) by decide,
      transition, tapeAtCells, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft]

private theorem run_final_95_blanks
    (n : Nat) (left right : List (Option Bool)) :
    description.runConfig n
        { state := 95
          tape := Tape.move Direction.left
            (tapeAtCells
              (List.append (List.replicate n (none : Option Bool)) left)
              (none :: right)) } =
      { state := 95
        tape := Tape.move Direction.left
          (tapeAtCells left
            (List.append (List.replicate n (none : Option Bool))
              (none :: right))) } := by
  induction n generalizing right with
  | zero => simp [runConfig]
  | succ n ih =>
      rw [show n + 1 = 1 + n by lia]
      rw [runConfig_add]
      rw [show List.replicate (1 + n) (none : Option Bool) =
        none :: List.replicate n none by
          rw [show 1 + n = Nat.succ n by lia]
          rfl]
      rw [show
        List.append (none :: List.replicate n (none : Option Bool)) left =
          none :: List.append (List.replicate n none) left by rfl]
      rw [step_final_95_blank]
      rw [ih (none :: right)]
      rw [replicate_none_append_none_cons]
      rfl

private theorem step_final_95_present
    (bit next : Bool) (left right : List (Option Bool)) :
    description.runConfig 1
        { state := 95
          tape := tapeAtCells (some next :: left) (some bit :: right) } =
      { state := 96
        tape := tapeAtCells left (some next :: some bit :: right) } := by
  cases right <;>
    simp [runConfig, stepConfig,
      show lookupTransition description 95 (some bit) =
        some (transition 95 (some bit) (some bit) Direction.left 96) by
          cases bit <;> decide,
      transition, tapeAtCells, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft]

private theorem step_final_96_present
    (bit next : Bool) (left right : List (Option Bool)) :
    description.runConfig 1
        { state := 96
          tape := tapeAtCells (some next :: left) (some bit :: right) } =
      { state := 97
        tape := tapeAtCells left (some next :: some bit :: right) } := by
  cases right <;>
    simp [runConfig, stepConfig,
      show lookupTransition description 96 (some bit) =
        some (transition 96 (some bit) (some bit) Direction.left 97) by
          cases bit <;> decide,
      transition, tapeAtCells, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft]

private theorem step_final_97_present
    (bit next : Bool) (left right : List (Option Bool)) :
    description.runConfig 1
        { state := 97
          tape := tapeAtCells (some next :: left) (some bit :: right) } =
      { state := 0
        tape := tapeAtCells left (some next :: some bit :: right) } := by
  cases right <;>
    simp [runConfig, stepConfig,
      show lookupTransition description 97 (some bit) =
        some (transition 97 (some bit) (some bit) Direction.left 0) by
          cases bit <;> decide,
      transition, tapeAtCells, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft]

private theorem run_final_tail_bits
    (h0 h1 h2 h3 : Bool)
    (left right : List (Option Bool)) (current : Option Bool) :
    description.runConfig 3
        { state := 95
          tape := Tape.move Direction.left
            (tapeAtCells
              (some h3 :: some h2 :: some h1 :: some h0 :: left)
              (current :: right)) } =
      { state := 0
        tape := tapeAtCells left
          (some h0 :: some h1 :: some h2 :: some h3 ::
            current :: right) } := by
  change
    description.runConfig 3
        { state := 95
          tape := tapeAtCells
            (some h2 :: some h1 :: some h0 :: left)
            (some h3 :: current :: right) } = _
  rw [show 3 = 1 + (1 + 1) by rfl]
  rw [runConfig_add]
  rw [step_final_95_present h3 h2]
  rw [runConfig_add]
  rw [step_final_96_present h2 h1]
  rw [step_final_97_present h1 h0]

theorem run_finish
    (baseLeft : List (Option Bool)) (emitted : Word Bool)
    (h0 h1 h2 h3 : Bool) (gap : Nat)
    (tokens : List TokenKind) (right : List (Option Bool)) :
    exists steps : Nat,
      description.runConfig steps
          { state := description.start
            tape := loopTape baseLeft emitted [h0, h1, h2, h3]
              (gap + 1) [] tokens right } =
        { state := description.halt
          tape := targetTape baseLeft emitted [h0, h1, h2, h3]
            (gap + 1) tokens right } := by
  let n : Nat := 8 * tokens.length + 1
  let m : Nat := (n + 1) + (gap + 1)
  let word : Word Bool := List.append (tokenBits tokens) emitted
  let tailLeft : List (Option Bool) :=
    some h3 :: some h2 :: some h1 :: some h0 ::
      List.append (word.reverse.map some) baseLeft
  let afterGuard : List (Option Bool) :=
    List.append (List.replicate (gap + 1) (none : Option Bool)) tailLeft
  have hseek0 := run_seek_erased_suffix n false afterGuard right
  have hseek :
      description.runConfig (n + 1)
          { state := description.start
            tape := loopTape baseLeft emitted [h0, h1, h2, h3]
              (gap + 1) [] tokens right } =
        { state := 2
          tape := tapeAtCells afterGuard
            (some false ::
              List.append (List.replicate n (none : Option Bool))
                (some true :: right)) } := by
    simpa [loopTape, n, word, tailLeft, afterGuard,
      List.map_reverse, List.map_append, List.append_assoc] using hseek0
  have hafterGuard :
      afterGuard =
        none :: List.append (List.replicate gap (none : Option Bool))
          tailLeft := by
    unfold afterGuard
    rw [show gap + 1 = Nat.succ gap by lia]
    rfl
  have henter0 := run_enter_final
    (List.append (List.replicate gap (none : Option Bool)) tailLeft)
    (List.append (List.replicate n (none : Option Bool))
      (some true :: right))
  have henter :
      description.runConfig 2
          { state := 2
            tape := tapeAtCells afterGuard
              (some false ::
                List.append (List.replicate n (none : Option Bool))
                  (some true :: right)) } =
        { state := 94
          tape := tapeAtCells afterGuard
            (none ::
              List.append (List.replicate n (none : Option Bool))
                (some true :: right)) } := by
    simpa [hafterGuard] using henter0
  have hright94 :
      none :: List.append (List.replicate n (none : Option Bool))
          (some true :: right) =
        List.append (List.replicate (n + 1) none)
          (some true :: right) := by
    rw [show n + 1 = Nat.succ n by lia]
    rfl
  have hscan94 := run_final_94_blanks (n + 1) afterGuard
    (some true :: right)
  have hmarker := step_final_94_marker
    (List.append (List.replicate (n + 1) (none : Option Bool)) afterGuard)
    right
  have hfullLeft :
      List.append (List.replicate (n + 1) (none : Option Bool)) afterGuard =
        List.append (List.replicate m none) tailLeft := by
    unfold afterGuard m
    calc
      _ = List.append
          (List.append (List.replicate (n + 1) (none : Option Bool))
            (List.replicate (gap + 1) none)) tailLeft :=
        (List.append_assoc _ _ _).symm
      _ = _ := congrArg (fun xs : List (Option Bool) =>
        List.append xs tailLeft)
        (List.replicate_append_replicate
          (n := n + 1) (m := gap + 1) (a := (none : Option Bool)))
  have hscan95 := run_final_95_blanks m tailLeft right
  have hright95 :
      List.append (List.replicate m (none : Option Bool))
          (none :: right) =
        none :: List.append (List.replicate m none) right :=
    replicate_none_append_none_cons m right
  have hbits := run_final_tail_bits h0 h1 h2 h3
    (List.append (word.reverse.map some) baseLeft)
    (List.append (List.replicate m (none : Option Bool)) right) none
  have hfinalBlanks :
      none :: List.append (List.replicate m (none : Option Bool)) right =
        List.append
          (List.replicate ((gap + 1) + 8 * tokens.length + 3) none)
          right := by
    rw [show (gap + 1) + 8 * tokens.length + 3 = m + 1 by
      unfold m n
      lia]
    rw [List.replicate_succ]
    rfl
  let totalSteps : Nat :=
    (n + 1) + (2 + ((n + 1) + (1 + (m + 3))))
  refine ⟨totalSteps, ?_⟩
  unfold totalSteps
  rw [runConfig_add]
  rw [hseek]
  rw [runConfig_add]
  rw [henter]
  rw [hright94]
  rw [runConfig_add]
  rw [hscan94]
  rw [runConfig_add]
  rw [hmarker]
  rw [hfullLeft]
  rw [runConfig_add]
  rw [hscan95]
  rw [hright95]
  rw [hbits]
  rw [hfinalBlanks]
  simp [targetTape, word, description,
    List.append_assoc]

end Execution

open Execution

/--
The metadata copier is exact on its live contract: four tail bits and a
strictly positive blank gap.  The natural `gap` argument records the blanks
beyond the required first one.
-/
theorem description_haltsFromTape
    (baseLeft : List (Option Bool)) (emitted : Word Bool)
    (h0 h1 h2 h3 : Bool) (gap : Nat)
    (tokens : List TokenKind) (right : List (Option Bool)) :
    description.HaltsFromTape
      (sourceTape baseLeft emitted [h0, h1, h2, h3]
        (gap + 1) tokens right)
      (targetTape baseLeft emitted [h0, h1, h2, h3]
        (gap + 1) tokens right) := by
  rcases run_cycles baseLeft emitted h0 h1 h2 h3 gap
      tokens [] right with
    ⟨cycleSteps, hcycles⟩
  have hcycles' :
      description.runConfig cycleSteps
          { state := description.start
            tape := sourceTape baseLeft emitted [h0, h1, h2, h3]
              (gap + 1) tokens right } =
        { state := description.start
          tape := loopTape baseLeft emitted [h0, h1, h2, h3]
            (gap + 1) [] tokens right } := by
    simpa [sourceTape] using hcycles
  rcases run_finish baseLeft emitted h0 h1 h2 h3 gap
      tokens right with
    ⟨finishSteps, hfinish⟩
  let totalSteps : Nat := cycleSteps + finishSteps
  have hrun :
      description.runConfig totalSteps
          { state := description.start
            tape := sourceTape baseLeft emitted [h0, h1, h2, h3]
              (gap + 1) tokens right } =
        { state := description.halt
          tape := targetTape baseLeft emitted [h0, h1, h2, h3]
            (gap + 1) tokens right } := by
    unfold totalSteps
    rw [runConfig_add]
    rw [hcycles']
    rw [hfinish]
  refine ⟨totalSteps, ?_, ?_⟩
  · exact congrArg Configuration.state hrun
  · exact congrArg Configuration.tape hrun

/-- Tape-equivalence form of `description_haltsFromTape`. -/
theorem description_haltsFromTapeEquiv
    (baseLeft : List (Option Bool)) (emitted : Word Bool)
    (h0 h1 h2 h3 : Bool) (gap : Nat)
    (tokens : List TokenKind) (right : List (Option Bool)) :
    description.HaltsFromTapeEquiv
      (sourceTape baseLeft emitted [h0, h1, h2, h3]
        (gap + 1) tokens right)
      (targetTape baseLeft emitted [h0, h1, h2, h3]
        (gap + 1) tokens right) :=
  (description_haltsFromTape baseLeft emitted h0 h1 h2 h3 gap
    tokens right).toEquiv

end GuardedEgress.MetadataTokenCopy
end FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore

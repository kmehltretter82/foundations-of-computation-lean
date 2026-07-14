import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.GuardedEgress.MetadataDefs

namespace FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
namespace GuardedEgress.MetadataTokenCopy

open Languages MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace Execution

private theorem run_state2_blank_prefix
    (n : Nat) (boundary : Bool)
    (left right : List (Option Bool)) :
    description.runConfig (n + 1)
        { state := 2
          tape := tapeAtCells
            (List.append (List.replicate n (none : Option Bool))
              (some boundary :: left))
            (none :: right) } =
      { state := 2
        tape := tapeAtCells left
          (some boundary ::
            List.append
              (List.replicate (n + 1) (none : Option Bool)) right) } := by
  induction n generalizing right with
  | zero =>
      cases boundary <;> cases left <;> cases right <;>
        simp [description, commonTransitions, kinds,
          tokenRouteTransitions, runConfig, stepConfig,
          lookupTransition, Matches, transition, tapeAtCells,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          List.replicate_succ]
  | succ n ih =>
      rw [show Nat.succ n + 1 = 1 + (n + 1) by lia]
      rw [runConfig_add]
      rw [show List.replicate (n + 1) (none : Option Bool) =
        none :: List.replicate n none by
          rw [show n + 1 = Nat.succ n by lia]
          rfl]
      rw [show
        description.runConfig 1
            { state := 2
              tape := tapeAtCells
                (List.append
                  (none :: List.replicate n (none : Option Bool))
                  (some boundary :: left))
                (none :: right) } =
          { state := 2
            tape := tapeAtCells
              (List.append (List.replicate n (none : Option Bool))
                (some boundary :: left))
              (none :: none :: right) } by
        simp [description, commonTransitions, kinds,
          tokenRouteTransitions, runConfig, stepConfig,
          lookupTransition, Matches, transition, tapeAtCells,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft]]
      rw [ih (none :: right)]
      rw [replicate_none_append_none_cons]
      rw [show 1 + (n + 1) = (n + 1) + 1 by lia]
      rw [List.replicate_succ]
      rw [List.replicate_succ]
      rw [List.replicate_succ]
      rfl

theorem run_seek_erased_suffix
    (n : Nat) (boundary : Bool)
    (left right : List (Option Bool)) :
    description.runConfig (n + 1)
        { state := description.start
          tape := tapeAtCells
            (List.append (List.replicate n (none : Option Bool))
              (some boundary :: left))
            (some true :: right) } =
      { state := 2
        tape := tapeAtCells left
          (some boundary ::
            List.append (List.replicate n (none : Option Bool))
              (some true :: right)) } := by
  cases n with
  | zero =>
      cases boundary <;> cases left <;> cases right <;>
        simp [description, commonTransitions, kinds,
          tokenRouteTransitions, runConfig, stepConfig,
          lookupTransition, Matches, transition, tapeAtCells,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft]
  | succ n =>
      rw [show Nat.succ n + 1 = 1 + (n + 1) by lia]
      rw [runConfig_add]
      rw [show List.replicate (n + 1) (none : Option Bool) =
        none :: List.replicate n none by
          rw [show n + 1 = Nat.succ n by lia]
          rfl]
      rw [show
        description.runConfig 1
            { state := description.start
              tape := tapeAtCells
                (List.append
                  (none :: List.replicate n (none : Option Bool))
                  (some boundary :: left))
                (some true :: right) } =
          { state := 2
            tape := tapeAtCells
              (List.append (List.replicate n (none : Option Bool))
                (some boundary :: left))
              (none :: some true :: right) } by
        simp [description, commonTransitions, kinds,
          tokenRouteTransitions, runConfig, stepConfig,
          lookupTransition, Matches, transition, tapeAtCells,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft]]
      rw [run_state2_blank_prefix n boundary left (some true :: right)]
      rw [List.replicate_succ]

set_option maxRecDepth 100000 in
theorem run_decode_token
    (kind : TokenKind) (boundary : Bool)
    (left right : List (Option Bool)) :
    description.runConfig 8
        { state := 2
          tape := decodeSourceTape kind (some boundary :: left) right } =
      { state := toGuardState kind
        tape := tapeAtCells left
          (some boundary ::
            List.append (List.replicate 8 (none : Option Bool)) right) } := by
  cases kind <;> cases boundary <;> cases left <;> cases right <;>
    simp [decodeSourceTape, encodedTokenCells, TokenKind.bits,
      logicalCellListBits, logicalCellBits,
      description, commonTransitions, kinds, tokenRouteTransitions,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
      List.replicate_succ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem run_to_guard_present
    (kind : TokenKind) (current : Bool)
    (pendingLeft : List Bool)
    (left right : List (Option Bool)) :
    description.runConfig (pendingLeft.length + 2)
        { state := toGuardState kind
          tape := tapeAtCells
            (List.append (pendingLeft.map some) (none :: left))
            (some current :: right) } =
      { state := scanGapState kind
        tape := Tape.move Direction.left
          (tapeAtCells left
            (none ::
              List.append (pendingLeft.reverse.map some)
                (some current :: right))) } := by
  induction pendingLeft generalizing current right with
  | nil =>
      cases kind <;> cases current <;> cases left <;> cases right <;>
        simp [description, commonTransitions, kinds,
          tokenRouteTransitions, toGuardState, scanGapState,
          backTwoState, backOneState, prependStartState,
          prependScanState, prependWriteTwoState,
          prependWriteOneState, prependWriteZeroState,
          prependReturnState, TokenKind.b0, TokenKind.b1,
          TokenKind.b2, TokenKind.b3,
          runConfig, stepConfig, lookupTransition, Matches,
          transition, tapeAtCells, Tape.read, Tape.write,
          Tape.move, Tape.moveLeft]
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 2 =
        1 + (rest.length + 2) by
          simp
          lia]
      rw [runConfig_add]
      rw [show
        description.runConfig 1
            { state := toGuardState kind
              tape := tapeAtCells
                (List.append ((bit :: rest).map some) (none :: left))
                (some current :: right) } =
          { state := toGuardState kind
            tape := tapeAtCells
              (List.append (rest.map some) (none :: left))
              (some bit :: some current :: right) } by
        cases kind <;> cases current <;> cases bit <;> cases right <;>
          simp [description, commonTransitions, kinds,
            tokenRouteTransitions, toGuardState, scanGapState,
            backTwoState, backOneState, prependStartState,
            prependScanState, prependWriteTwoState,
            prependWriteOneState, prependWriteZeroState,
            prependReturnState, TokenKind.b0, TokenKind.b1,
            TokenKind.b2, TokenKind.b3,
            runConfig, stepConfig,
            lookupTransition, Matches, transition, tapeAtCells,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft]]
      rw [ih bit (some current :: right)]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem step_scanGap_blank
    (kind : TokenKind) (left right : List (Option Bool)) :
    description.runConfig 1
        { state := scanGapState kind
          tape := tapeAtCells left (none :: right) } =
      { state := scanGapState kind
        tape := Tape.move Direction.left
          (tapeAtCells left (none :: right)) } := by
  cases kind <;> cases left <;> cases right <;>
    simp [description, commonTransitions, kinds,
      tokenRouteTransitions, toGuardState, scanGapState,
      backTwoState, backOneState, prependStartState,
      prependScanState, prependWriteTwoState,
      prependWriteOneState, prependWriteZeroState,
      prependReturnState, TokenKind.b0, TokenKind.b1,
      TokenKind.b2, TokenKind.b3,
      runConfig, stepConfig, lookupTransition, Matches,
      transition, tapeAtCells, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem step_scanGap_present
    (kind : TokenKind) (bit : Bool)
    (left right : List (Option Bool)) :
    description.runConfig 1
        { state := scanGapState kind
          tape := tapeAtCells left (some bit :: right) } =
      { state := backTwoState kind
        tape := Tape.move Direction.left
          (tapeAtCells left (some bit :: right)) } := by
  cases kind <;> cases bit <;> cases left <;> cases right <;>
    simp [description, commonTransitions, kinds,
      tokenRouteTransitions, toGuardState, scanGapState,
      backTwoState, backOneState, prependStartState,
      prependScanState, prependWriteTwoState,
      prependWriteOneState, prependWriteZeroState,
      prependReturnState, TokenKind.b0, TokenKind.b1,
      TokenKind.b2, TokenKind.b3,
      runConfig, stepConfig, lookupTransition, Matches,
      transition, tapeAtCells, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem step_backTwo_present
    (kind : TokenKind) (bit : Bool)
    (left right : List (Option Bool)) :
    description.runConfig 1
        { state := backTwoState kind
          tape := tapeAtCells left (some bit :: right) } =
      { state := backOneState kind
        tape := Tape.move Direction.left
          (tapeAtCells left (some bit :: right)) } := by
  cases kind <;> cases bit <;> cases left <;> cases right <;>
    simp [description, commonTransitions, kinds,
      tokenRouteTransitions, toGuardState, scanGapState,
      backTwoState, backOneState, prependStartState,
      prependScanState, prependWriteTwoState,
      prependWriteOneState, prependWriteZeroState,
      prependReturnState, TokenKind.b0, TokenKind.b1,
      TokenKind.b2, TokenKind.b3,
      runConfig, stepConfig, lookupTransition, Matches,
      transition, tapeAtCells, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem step_backOne_present
    (kind : TokenKind) (bit : Bool)
    (left right : List (Option Bool)) :
    description.runConfig 1
        { state := backOneState kind
          tape := tapeAtCells left (some bit :: right) } =
      { state := prependStartState kind
        tape := Tape.move Direction.left
          (tapeAtCells left (some bit :: right)) } := by
  cases kind <;> cases bit <;> cases left <;> cases right <;>
    simp [description, commonTransitions, kinds,
      tokenRouteTransitions, toGuardState, scanGapState,
      backTwoState, backOneState, prependStartState,
      prependScanState, prependWriteTwoState,
      prependWriteOneState, prependWriteZeroState,
      prependReturnState, TokenKind.b0, TokenKind.b1,
      TokenKind.b2, TokenKind.b3,
      runConfig, stepConfig, lookupTransition, Matches,
      transition, tapeAtCells, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem run_gap_to_prepend_start
    (kind : TokenKind) (gap : Nat)
    (h0 h1 h2 h3 : Bool)
    (left right : List (Option Bool)) :
    description.runConfig (gap + 3)
        { state := scanGapState kind
          tape := Tape.move Direction.left
            (tapeAtCells
              (List.append (List.replicate gap (none : Option Bool))
                (some h3 :: some h2 :: some h1 :: some h0 :: left))
              (none :: right)) } =
      { state := prependStartState kind
        tape := tapeAtCells left
          (some h0 :: some h1 :: some h2 :: some h3 ::
            List.append (List.replicate gap (none : Option Bool))
              (none :: right)) } := by
  induction gap generalizing right with
  | zero =>
      change
        description.runConfig 3
            { state := scanGapState kind
              tape := tapeAtCells
                (some h2 :: some h1 :: some h0 :: left)
                (some h3 :: none :: right) } =
          { state := prependStartState kind
            tape := tapeAtCells left
              (some h0 :: some h1 :: some h2 :: some h3 ::
                none :: right) }
      rw [show 3 = 1 + (1 + 1) by rfl]
      rw [runConfig_add]
      rw [step_scanGap_present kind h3 _ (none :: right)]
      rw [show
        Tape.move Direction.left
            (tapeAtCells (some h2 :: some h1 :: some h0 :: left)
              (some h3 :: none :: right)) =
          tapeAtCells (some h1 :: some h0 :: left)
            (some h2 :: some h3 :: none :: right) by rfl]
      rw [runConfig_add]
      rw [step_backTwo_present kind h2 _
        (some h3 :: none :: right)]
      rw [show
        Tape.move Direction.left
            (tapeAtCells (some h1 :: some h0 :: left)
              (some h2 :: some h3 :: none :: right)) =
          tapeAtCells (some h0 :: left)
            (some h1 :: some h2 :: some h3 :: none :: right) by rfl]
      rw [step_backOne_present kind h1 _
        (some h2 :: some h3 :: none :: right)]
      rw [show
        Tape.move Direction.left
            (tapeAtCells (some h0 :: left)
              (some h1 :: some h2 :: some h3 :: none :: right)) =
          tapeAtCells left
            (some h0 :: some h1 :: some h2 :: some h3 :: none :: right) by rfl]
  | succ gap ih =>
      rw [show Nat.succ gap + 3 = 1 + (gap + 3) by lia]
      rw [runConfig_add]
      rw [show List.replicate (gap + 1) (none : Option Bool) =
        none :: List.replicate gap none by
          rw [show gap + 1 = Nat.succ gap by lia]
          rfl]
      rw [show
        Tape.move Direction.left
            (tapeAtCells
              (List.append
                (none :: List.replicate gap (none : Option Bool))
                (some h3 :: some h2 :: some h1 :: some h0 :: left))
              (none :: right)) =
          tapeAtCells
            (List.append (List.replicate gap (none : Option Bool))
              (some h3 :: some h2 :: some h1 :: some h0 :: left))
            (none :: none :: right) by rfl]
      rw [step_scanGap_blank kind _ (none :: right)]
      rw [ih (none :: right)]
      rw [replicate_none_append_none_cons]
      rfl

end Execution

end GuardedEgress.MetadataTokenCopy
end FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore

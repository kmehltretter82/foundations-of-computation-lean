import scratch_u18_egress_integration

namespace FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
namespace GuardedEgress.MetadataTokenCopyScratch

open Languages MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

/-!
The guarded egress metadata contains only four token kinds.  Copying these
tokens from right to left and prepending each one to the assembled tape field
preserves their original order without a second block-reversal phase.
-/

inductive TokenKind where
  | tick
  | done
  | zero
  | one
deriving DecidableEq, Repr

def TokenKind.bits : TokenKind -> Word Bool
  | .tick => [false, false, true, false]
  | .done => [false, false, true, true]
  | .zero => [false, true, false, true]
  | .one => [false, true, true, false]

def TokenKind.b0 : TokenKind -> Bool
  | .tick | .done | .zero | .one => false

def TokenKind.b1 : TokenKind -> Bool
  | .tick | .done => false
  | .zero | .one => true

def TokenKind.b2 : TokenKind -> Bool
  | .tick | .done | .one => true
  | .zero => false

def TokenKind.b3 : TokenKind -> Bool
  | .tick | .one => false
  | .done | .zero => true

@[simp] theorem TokenKind.bits_eq_components (kind : TokenKind) :
    kind.bits = [kind.b0, kind.b1, kind.b2, kind.b3] := by
  cases kind <;> rfl

def kinds : List TokenKind :=
  [.tick, .done, .zero, .one]

def toGuardState : TokenKind -> Nat
  | .tick => 25
  | .done => 26
  | .zero => 27
  | .one => 28

def scanGapState : TokenKind -> Nat
  | .tick => 29
  | .done => 30
  | .zero => 31
  | .one => 32

def backTwoState : TokenKind -> Nat
  | .tick => 33
  | .done => 34
  | .zero => 35
  | .one => 36

def backOneState : TokenKind -> Nat
  | .tick => 37
  | .done => 38
  | .zero => 39
  | .one => 40

def prependStartState : TokenKind -> Nat
  | .tick => 41
  | .done => 42
  | .zero => 43
  | .one => 44

def prependScanState : TokenKind -> Bool -> Nat
  | .tick, false => 45
  | .tick, true => 46
  | .done, false => 47
  | .done, true => 48
  | .zero, false => 49
  | .zero, true => 50
  | .one, false => 51
  | .one, true => 52

def prependWriteTwoState : TokenKind -> Bool -> Nat
  | .tick, false => 53
  | .tick, true => 54
  | .done, false => 55
  | .done, true => 56
  | .zero, false => 57
  | .zero, true => 58
  | .one, false => 59
  | .one, true => 60

def prependWriteOneState : TokenKind -> Bool -> Nat
  | .tick, false => 61
  | .tick, true => 62
  | .done, false => 63
  | .done, true => 64
  | .zero, false => 65
  | .zero, true => 66
  | .one, false => 67
  | .one, true => 68

def prependWriteZeroState : TokenKind -> Bool -> Nat
  | .tick, false => 69
  | .tick, true => 70
  | .done, false => 71
  | .done, true => 72
  | .zero, false => 73
  | .zero, true => 74
  | .one, false => 75
  | .one, true => 76

def prependReturnState : TokenKind -> Bool -> Nat
  | .tick, false => 77
  | .tick, true => 78
  | .done, false => 79
  | .done, true => 80
  | .zero, false => 81
  | .zero, true => 82
  | .one, false => 83
  | .one, true => 84

def tokenRouteTransitions (kind : TokenKind) :
    List TransitionDescription :=
  [ transition (toGuardState kind) (some false) (some false)
      Direction.left (toGuardState kind)
  , transition (toGuardState kind) (some true) (some true)
      Direction.left (toGuardState kind)
  , transition (toGuardState kind) none none
      Direction.left (scanGapState kind)
  , transition (scanGapState kind) none none
      Direction.left (scanGapState kind)
  , transition (scanGapState kind) (some false) (some false)
      Direction.left (backTwoState kind)
  , transition (scanGapState kind) (some true) (some true)
      Direction.left (backTwoState kind)
  , transition (backTwoState kind) (some false) (some false)
      Direction.left (backOneState kind)
  , transition (backTwoState kind) (some true) (some true)
      Direction.left (backOneState kind)
  , transition (backOneState kind) (some false) (some false)
      Direction.left (prependStartState kind)
  , transition (backOneState kind) (some true) (some true)
      Direction.left (prependStartState kind)
  , transition (prependStartState kind) (some false) none
      Direction.left (prependScanState kind false)
  , transition (prependStartState kind) (some true) none
      Direction.left (prependScanState kind true) ] ++
    [false, true].flatMap (fun hit =>
      [ transition (prependScanState kind hit) (some false) (some false)
          Direction.left (prependScanState kind hit)
      , transition (prependScanState kind hit) (some true) (some true)
          Direction.left (prependScanState kind hit)
      , transition (prependScanState kind hit) none (some kind.b3)
          Direction.left (prependWriteTwoState kind hit)
      , transition (prependWriteTwoState kind hit) none (some kind.b2)
          Direction.left (prependWriteOneState kind hit)
      , transition (prependWriteOneState kind hit) none (some kind.b1)
          Direction.left (prependWriteZeroState kind hit)
      , transition (prependWriteZeroState kind hit) none (some kind.b0)
          Direction.right (prependReturnState kind hit)
      , transition (prependReturnState kind hit) (some false) (some false)
          Direction.right (prependReturnState kind hit)
      , transition (prependReturnState kind hit) (some true) (some true)
          Direction.right (prependReturnState kind hit)
      , transition (prependReturnState kind hit) none (some hit)
          Direction.left 85 ])

def commonTransitions : List TransitionDescription :=
  [ transition 1 (some true) (some true) Direction.left 2
  , transition 2 none none Direction.left 2
  , transition 2 (some false) none Direction.left 3
  , transition 2 (some true) none Direction.left 4

  -- A blank immediately left of the erased candidate identifies the guard.
  , transition 3 none none Direction.right 94
  , transition 4 none none Direction.right 94

  -- Reverse decode of the four supported eight-cell token encodings.
  , transition 3 (some true) none Direction.left 5
  , transition 4 (some false) none Direction.left 16
  , transition 5 (some false) none Direction.left 6
  , transition 5 (some true) none Direction.left 11
  , transition 6 (some true) none Direction.left 7
  , transition 7 (some true) none Direction.left 8
  , transition 8 (some false) none Direction.left 9
  , transition 9 (some true) none Direction.left 10
  , transition 10 (some false) none Direction.left (toGuardState .done)
  , transition 11 (some false) none Direction.left 12
  , transition 12 (some false) none Direction.left 13
  , transition 13 (some true) none Direction.left 14
  , transition 14 (some true) none Direction.left 15
  , transition 15 (some false) none Direction.left (toGuardState .zero)
  , transition 16 (some false) none Direction.left 17
  , transition 17 (some true) none Direction.left 18
  , transition 18 (some false) none Direction.left 22
  , transition 18 (some true) none Direction.left 19
  , transition 19 (some false) none Direction.left 20
  , transition 20 (some true) none Direction.left 21
  , transition 21 (some false) none Direction.left (toGuardState .tick)
  , transition 22 (some true) none Direction.left 23
  , transition 23 (some true) none Direction.left 24
  , transition 24 (some false) none Direction.left (toGuardState .one)

  -- Return from the fixed-token prepender to the source right marker.
  , transition 85 (some false) (some false) Direction.right 86
  , transition 85 (some true) (some true) Direction.right 86
  , transition 86 (some false) (some false) Direction.right 87
  , transition 86 (some true) (some true) Direction.right 87
  , transition 87 (some false) (some false) Direction.right 88
  , transition 87 (some true) (some true) Direction.right 88
  , transition 88 (some false) (some false) Direction.right 89
  , transition 88 (some true) (some true) Direction.right 89
  , transition 89 (some false) (some false) Direction.right 90
  , transition 89 (some true) (some true) Direction.right 90
  , transition 90 none none Direction.right 90
  , transition 90 (some false) (some false) Direction.right 91
  , transition 90 (some true) (some true) Direction.right 91
  , transition 91 (some false) (some false) Direction.right 91
  , transition 91 (some true) (some true) Direction.right 91
  , transition 91 none none Direction.right 92
  , transition 92 none none Direction.right 92
  , transition 92 (some true) (some true) Direction.left 93
  , transition 93 none none Direction.right 1

  -- Final pass: erase the right marker and return to the first tail bit.
  , transition 94 none none Direction.right 94
  , transition 94 (some true) none Direction.left 95
  , transition 95 none none Direction.left 95
  , transition 95 (some false) (some false) Direction.left 96
  , transition 95 (some true) (some true) Direction.left 96
  , transition 96 (some false) (some false) Direction.left 97
  , transition 96 (some true) (some true) Direction.left 97
  , transition 97 (some false) (some false) Direction.left 0
  , transition 97 (some true) (some true) Direction.left 0 ]

def description : MachineDescription where
  stateCount := 98
  start := 1
  halt := 0
  transitions := commonTransitions ++ kinds.flatMap tokenRouteTransitions

set_option maxRecDepth 100000 in
theorem description_subroutineReady : description.SubroutineReady :=
  machineDescription_subroutineReady_of_transition_checks
    description (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

def encodedTokenCells (kind : TokenKind) : List (Option Bool) :=
  (logicalCellListBits (kind.bits.map some)).map some

def encodedTokens : List TokenKind -> List (Option Bool)
  | [] => []
  | kind :: rest => encodedTokenCells kind ++ encodedTokens rest

@[simp] theorem encodedTokens_nil : encodedTokens [] = [] := rfl

@[simp] theorem encodedTokens_cons (kind : TokenKind)
    (rest : List TokenKind) :
    encodedTokens (kind :: rest) =
      encodedTokenCells kind ++ encodedTokens rest := rfl

@[simp] theorem encodedTokenCells_length (kind : TokenKind) :
    (encodedTokenCells kind).length = 8 := by
  cases kind <;> rfl

theorem encodedTokens_length (tokens : List TokenKind) :
    (encodedTokens tokens).length = 8 * tokens.length := by
  induction tokens with
  | nil => rfl
  | cons kind rest ih =>
      simp [ih]
      lia

def tokenBits (tokens : List TokenKind) : Word Bool :=
  (tokens.map TokenKind.bits).flatten

@[simp] theorem tokenBits_nil : tokenBits [] = [] := rfl

@[simp] theorem tokenBits_cons (kind : TokenKind)
    (rest : List TokenKind) :
    tokenBits (kind :: rest) =
      List.append kind.bits (tokenBits rest) := by
  cases kind <;> rfl

/-!
`loopTape` is stated at the right marker.  `processed` is the already copied
suffix in original token order, and `remaining` is the untouched prefix.
The four blanks per remaining token are the exact workspace consumed by the
left-of-head prepender.
-/
def loopTape (baseLeft : List (Option Bool))
    (emitted : Word Bool) (tailBits : Word Bool)
    (gap : Nat) (remaining processed : List TokenKind)
    (right : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append
      (List.replicate (8 * processed.length + 1) (none : Option Bool))
      (List.append (encodedTokens remaining).reverse
        (some false ::
          List.append (List.replicate gap (none : Option Bool))
            (List.append (tailBits.reverse.map some)
              (List.append
                ((List.append (tokenBits processed) emitted).reverse.map some)
                (List.append
                  (List.replicate (4 * remaining.length)
                    (none : Option Bool))
                  baseLeft))))))
    (some true :: right)

def sourceTape (baseLeft : List (Option Bool))
    (emitted : Word Bool) (tailBits : Word Bool)
    (gap : Nat) (tokens : List TokenKind)
    (right : List (Option Bool)) : Tape Bool :=
  loopTape baseLeft emitted tailBits gap tokens [] right

def targetTape (baseLeft : List (Option Bool))
    (emitted : Word Bool) (tailBits : Word Bool)
    (gap : Nat) (tokens : List TokenKind)
    (right : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append
      ((List.append (tokenBits tokens) emitted).reverse.map some)
      baseLeft)
    (List.append (tailBits.map some)
      (List.append
        (List.replicate
          (gap + 8 * tokens.length + 3) (none : Option Bool))
        right))

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

private theorem run_seek_erased_suffix
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

def decodeSourceTape (kind : TokenKind)
    (left right : List (Option Bool)) : Tape Bool :=
  match (encodedTokenCells kind).reverse with
  | [] => tapeAtCells left right
  | current :: rest =>
      tapeAtCells (List.append rest left) (current :: right)

set_option maxRecDepth 100000 in
private theorem run_decode_token
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
private theorem run_to_guard_present
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
private theorem run_gap_to_prepend_start
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

end GuardedEgress.MetadataTokenCopyScratch
end FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore

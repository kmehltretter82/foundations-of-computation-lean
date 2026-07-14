import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.GuardedEgress.TapeFieldPipeline

namespace FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
namespace GuardedEgress.MetadataTokenCopy

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

def decodeSourceTape (kind : TokenKind)
    (left right : List (Option Bool)) : Tape Bool :=
  match (encodedTokenCells kind).reverse with
  | [] => tapeAtCells left right
  | current :: rest =>
      tapeAtCells (List.append rest left) (current :: right)

end GuardedEgress.MetadataTokenCopy
end FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore

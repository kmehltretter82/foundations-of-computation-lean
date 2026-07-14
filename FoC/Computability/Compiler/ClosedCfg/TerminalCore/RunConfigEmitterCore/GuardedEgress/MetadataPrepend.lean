import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.GuardedEgress.MetadataRoute

namespace FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
namespace GuardedEgress.MetadataTokenCopy

open Languages MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace Execution

private def prependScanTape (remainingRev : Word Bool)
    (scratchBase right : List (Option Bool)) : Tape Bool :=
  match remainingRev with
  | [] => tapeAtCells scratchBase (none :: right)
  | bit :: rest =>
      tapeAtCells (List.append (rest.map some) (none :: scratchBase))
        (some bit :: right)

set_option maxRecDepth 100000 in
private theorem step_prepend_start
    (kind : TokenKind) (hit : Bool) (emitted : Word Bool)
    (scratchBase tail : List (Option Bool)) :
    description.runConfig 1
        { state := prependStartState kind
          tape := tapeAtCells
            (List.append (emitted.reverse.map some)
              (none :: scratchBase))
            (some hit :: tail) } =
      { state := prependScanState kind hit
        tape := prependScanTape emitted.reverse scratchBase
          (none :: tail) } := by
  cases kind <;> cases hit <;> cases hrev : emitted.reverse <;>
    simp_all [description, commonTransitions, kinds,
      tokenRouteTransitions, toGuardState, scanGapState,
      backTwoState, backOneState, prependStartState, prependScanState,
      prependWriteTwoState, prependWriteOneState,
      prependWriteZeroState, prependReturnState,
      TokenKind.b0, TokenKind.b1, TokenKind.b2, TokenKind.b3,
      prependScanTape,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft]

set_option maxRecDepth 100000 in
private theorem lookup_prepend_scan_present
    (kind : TokenKind) (hit bit : Bool) :
    lookupTransition description (prependScanState kind hit) (some bit) =
      some (transition (prependScanState kind hit) (some bit) (some bit)
        Direction.left (prependScanState kind hit)) := by
  cases kind <;> cases hit <;> cases bit <;> decide

set_option maxRecDepth 100000 in
private theorem step_prepend_scan
    (kind : TokenKind) (hit bit : Bool) (rest : Word Bool)
    (scratchBase right : List (Option Bool)) :
    description.runConfig 1
        { state := prependScanState kind hit
          tape := prependScanTape (bit :: rest) scratchBase right } =
      { state := prependScanState kind hit
        tape := prependScanTape rest scratchBase (some bit :: right) } := by
  cases rest <;>
    simp [prependScanTape, runConfig, stepConfig,
      lookup_prepend_scan_present, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft]

private theorem run_prepend_scan
    (kind : TokenKind) (hit : Bool) (remainingRev : Word Bool)
    (scratchBase right : List (Option Bool)) :
    description.runConfig remainingRev.length
        { state := prependScanState kind hit
          tape := prependScanTape remainingRev scratchBase right } =
      { state := prependScanState kind hit
        tape := tapeAtCells scratchBase
          (none :: List.append (remainingRev.reverse.map some) right) } := by
  induction remainingRev generalizing right with
  | nil =>
      simp [prependScanTape, runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by simp; lia]
      rw [runConfig_add]
      rw [step_prepend_scan]
      rw [ih (some bit :: right)]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

set_option maxRecDepth 100000 in
private theorem lookup_prepend_write
    (kind : TokenKind) (hit : Bool) :
    lookupTransition description (prependScanState kind hit) none =
        some (transition (prependScanState kind hit) none (some kind.b3)
          Direction.left (prependWriteTwoState kind hit)) ∧
      lookupTransition description (prependWriteTwoState kind hit) none =
        some (transition (prependWriteTwoState kind hit) none (some kind.b2)
          Direction.left (prependWriteOneState kind hit)) ∧
      lookupTransition description (prependWriteOneState kind hit) none =
        some (transition (prependWriteOneState kind hit) none (some kind.b1)
          Direction.left (prependWriteZeroState kind hit)) ∧
      lookupTransition description (prependWriteZeroState kind hit) none =
        some (transition (prependWriteZeroState kind hit) none (some kind.b0)
          Direction.right (prependReturnState kind hit)) := by
  cases kind <;> cases hit <;> decide

private theorem run_prepend_write
    (kind : TokenKind) (hit : Bool)
    (baseLeft right : List (Option Bool)) :
    description.runConfig 4
        { state := prependScanState kind hit
          tape := tapeAtCells
            (List.append (List.replicate 3 (none : Option Bool)) baseLeft)
            (none :: right) } =
      { state := prependReturnState kind hit
        tape := tapeAtCells (some kind.b0 :: baseLeft)
          (some kind.b1 :: some kind.b2 :: some kind.b3 :: right) } := by
  rcases lookup_prepend_write kind hit with
    ⟨hscan, htwo, hone, hzero⟩
  simp [runConfig, stepConfig, hscan, htwo, hone, hzero,
    transition, tapeAtCells, Tape.read, Tape.write,
    Tape.move, Tape.moveLeft, Tape.moveRight, List.replicate_succ]

set_option maxRecDepth 100000 in
private theorem lookup_prepend_return
    (kind : TokenKind) (hit bit : Bool) :
    lookupTransition description (prependReturnState kind hit) (some bit) =
        some (transition (prependReturnState kind hit) (some bit) (some bit)
          Direction.right (prependReturnState kind hit)) ∧
      lookupTransition description (prependReturnState kind hit) none =
        some (transition (prependReturnState kind hit) none (some hit)
          Direction.left 85) := by
  cases kind <;> cases hit <;> cases bit <;> decide

private theorem step_prepend_return_present
    (kind : TokenKind) (hit bit : Bool)
    (left right : List (Option Bool)) :
    description.runConfig 1
        { state := prependReturnState kind hit
          tape := tapeAtCells left (some bit :: right) } =
      { state := prependReturnState kind hit
        tape := tapeAtCells (some bit :: left) right } := by
  cases right <;>
    simp [runConfig, stepConfig,
      (lookup_prepend_return kind hit bit).1,
      transition, tapeAtCells, Tape.read, Tape.write,
      Tape.move, Tape.moveRight]

private theorem run_prepend_return_present
    (kind : TokenKind) (hit : Bool) (bits : Word Bool)
    (left right : List (Option Bool)) :
    description.runConfig bits.length
        { state := prependReturnState kind hit
          tape := tapeAtCells left
            (List.append (bits.map some) right) } =
      { state := prependReturnState kind hit
        tape := tapeAtCells
          (List.append (bits.reverse.map some) left) right } := by
  induction bits generalizing left with
  | nil =>
      simp [runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by simp; lia]
      rw [runConfig_add]
      change
        description.runConfig rest.length
            (description.runConfig 1
              { state := prependReturnState kind hit
                tape := tapeAtCells left
                  (some bit :: List.append (rest.map some) right) }) = _
      rw [step_prepend_return_present]
      rw [ih (some bit :: left)]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

private theorem step_prepend_restore
    (kind : TokenKind) (hit cell : Bool)
    (left tail : List (Option Bool)) :
    description.runConfig 1
        { state := prependReturnState kind hit
          tape := tapeAtCells (some cell :: left) (none :: tail) } =
      { state := 85
        tape := tapeAtCells left (some cell :: some hit :: tail) } := by
  simp [runConfig, stepConfig,
    (lookup_prepend_return kind hit cell).2,
    transition, tapeAtCells, Tape.read, Tape.write,
    Tape.move, Tape.moveLeft]

private theorem step_prepend_restore_move
    (kind : TokenKind) (hit : Bool)
    (left tail : List (Option Bool)) :
    description.runConfig 1
        { state := prependReturnState kind hit
          tape := tapeAtCells left (none :: tail) } =
      { state := 85
        tape := Tape.move Direction.left
          (tapeAtCells left (some hit :: tail)) } := by
  simp [runConfig, stepConfig,
    (lookup_prepend_return kind hit false).2,
    transition, tapeAtCells, Tape.read, Tape.write,
    Tape.move, Tape.moveLeft]

private def prependReturnBits (kind : TokenKind)
    (emitted : Word Bool) : Word Bool :=
  List.append [kind.b1, kind.b2, kind.b3] emitted

private theorem run_prepend_scan_write
    (kind : TokenKind) (hit : Bool) (emitted : Word Bool)
    (baseLeft tail : List (Option Bool)) :
    description.runConfig (emitted.reverse.length + 4)
        { state := prependScanState kind hit
          tape := prependScanTape emitted.reverse
            (List.append (List.replicate 3 (none : Option Bool)) baseLeft)
            (none :: tail) } =
      { state := prependReturnState kind hit
        tape := tapeAtCells (some kind.b0 :: baseLeft)
          (List.append ((prependReturnBits kind emitted).map some)
            (none :: tail)) } := by
  rw [runConfig_add, run_prepend_scan]
  simp only [List.reverse_reverse]
  rw [run_prepend_write]
  simp [prependReturnBits]

private theorem run_prepend_return_restore
    (kind : TokenKind) (hit : Bool) (bits : Word Bool)
    (left tail : List (Option Bool)) :
    description.runConfig (bits.length + 1)
        { state := prependReturnState kind hit
          tape := tapeAtCells left
            (List.append (bits.map some) (none :: tail)) } =
      { state := 85
        tape := Tape.move Direction.left
          (tapeAtCells
            (List.append (bits.reverse.map some) left)
            (some hit :: tail)) } := by
  rw [runConfig_add, run_prepend_return_present,
    step_prepend_restore_move]

private theorem run_prepend_start_to_return
    (kind : TokenKind) (hit : Bool) (emitted : Word Bool)
    (baseLeft tail : List (Option Bool)) :
    description.runConfig (emitted.reverse.length + 5)
        { state := prependStartState kind
          tape := tapeAtCells
            (List.append (emitted.reverse.map some)
              (List.append
                (List.replicate 4 (none : Option Bool)) baseLeft))
            (some hit :: tail) } =
      { state := prependReturnState kind hit
        tape := tapeAtCells (some kind.b0 :: baseLeft)
          (List.append ((prependReturnBits kind emitted).map some)
            (none :: tail)) } := by
  rw [show emitted.reverse.length + 5 =
    1 + (emitted.reverse.length + 4) by lia]
  rw [runConfig_add]
  rw [show List.replicate 4 (none : Option Bool) =
    none :: List.replicate 3 none by rfl]
  rw [show
    List.append (none :: List.replicate 3 (none : Option Bool)) baseLeft =
      none :: List.append (List.replicate 3 none) baseLeft by rfl]
  rw [step_prepend_start, run_prepend_scan_write]

theorem run_prepend
    (kind : TokenKind) (hit : Bool) (emitted : Word Bool)
    (baseLeft tail : List (Option Bool)) :
    description.runConfig
        ((emitted.reverse.length + 5) +
          ((prependReturnBits kind emitted).length + 1))
        { state := prependStartState kind
          tape := tapeAtCells
            (List.append (emitted.reverse.map some)
              (List.append
                (List.replicate 4 (none : Option Bool)) baseLeft))
            (some hit :: tail) } =
      { state := 85
        tape := Tape.move Direction.left
          (tapeAtCells
            (List.append
              ((List.append kind.bits emitted).reverse.map some)
              baseLeft)
            (some hit :: tail)) } := by
  rw [runConfig_add, run_prepend_start_to_return,
    run_prepend_return_restore]
  simp [prependReturnBits, TokenKind.bits_eq_components,
    List.map_append, List.append_assoc]

set_option maxRecDepth 100000 in
private theorem lookup_return_prefix_present (bit : Bool) :
    lookupTransition description 85 (some bit) =
        some (transition 85 (some bit) (some bit) Direction.right 86) ∧
      lookupTransition description 86 (some bit) =
        some (transition 86 (some bit) (some bit) Direction.right 87) ∧
      lookupTransition description 87 (some bit) =
        some (transition 87 (some bit) (some bit) Direction.right 88) ∧
      lookupTransition description 88 (some bit) =
        some (transition 88 (some bit) (some bit) Direction.right 89) ∧
      lookupTransition description 89 (some bit) =
        some (transition 89 (some bit) (some bit) Direction.right 90) := by
  cases bit <;> decide

private theorem run_return_prefix
    (word : Word Bool) (hword : word ≠ [])
    (h0 h1 h2 h3 : Bool)
    (baseLeft right : List (Option Bool)) :
    description.runConfig 5
        { state := 85
          tape := Tape.move Direction.left
            (tapeAtCells
              (List.append (word.reverse.map some) baseLeft)
              (some h0 :: some h1 :: some h2 :: some h3 :: right)) } =
      { state := 90
        tape := tapeAtCells
          (some h3 :: some h2 :: some h1 :: some h0 ::
            List.append (word.reverse.map some) baseLeft)
          right } := by
  cases hrev : word.reverse with
  | nil =>
      exfalso
      apply hword
      change @Eq (List Bool) word []
      simpa using congrArg List.reverse hrev
  | cons out rest =>
      cases right
      all_goals
        simp [runConfig, stepConfig,
          (lookup_return_prefix_present out).1,
          (lookup_return_prefix_present h0).2.1,
          (lookup_return_prefix_present h1).2.2.1,
          (lookup_return_prefix_present h2).2.2.2.1,
          (lookup_return_prefix_present h3).2.2.2.2,
          transition, tapeAtCells, Tape.read, Tape.write,
          Tape.move, Tape.moveLeft, Tape.moveRight]

set_option maxRecDepth 100000 in
private theorem lookup_return_scans (bit : Bool) :
    lookupTransition description 90 none =
        some (transition 90 none none Direction.right 90) ∧
      lookupTransition description 90 (some bit) =
        some (transition 90 (some bit) (some bit) Direction.right 91) ∧
      lookupTransition description 91 (some bit) =
        some (transition 91 (some bit) (some bit) Direction.right 91) ∧
      lookupTransition description 91 none =
        some (transition 91 none none Direction.right 92) ∧
      lookupTransition description 92 none =
        some (transition 92 none none Direction.right 92) ∧
      lookupTransition description 92 (some true) =
        some (transition 92 (some true) (some true) Direction.left 93) ∧
      lookupTransition description 93 none =
        some (transition 93 none none Direction.right 1) := by
  cases bit <;> decide

private theorem step_return_90_blank
    (left right : List (Option Bool)) :
    description.runConfig 1
        { state := 90
          tape := tapeAtCells left (none :: right) } =
      { state := 90
        tape := tapeAtCells (none :: left) right } := by
  cases right <;>
    simp [runConfig, stepConfig, (lookup_return_scans false).1,
      transition, tapeAtCells, Tape.read, Tape.write,
      Tape.move, Tape.moveRight]

private theorem step_return_90_present
    (bit : Bool) (left right : List (Option Bool)) :
    description.runConfig 1
        { state := 90
          tape := tapeAtCells left (some bit :: right) } =
      { state := 91
        tape := tapeAtCells (some bit :: left) right } := by
  cases right <;>
    simp [runConfig, stepConfig, (lookup_return_scans bit).2.1,
      transition, tapeAtCells, Tape.read, Tape.write,
      Tape.move, Tape.moveRight]

private theorem step_return_91_present
    (bit : Bool) (left right : List (Option Bool)) :
    description.runConfig 1
        { state := 91
          tape := tapeAtCells left (some bit :: right) } =
      { state := 91
        tape := tapeAtCells (some bit :: left) right } := by
  cases right <;>
    simp [runConfig, stepConfig, (lookup_return_scans bit).2.2.1,
      transition, tapeAtCells, Tape.read, Tape.write,
      Tape.move, Tape.moveRight]

private theorem step_return_91_blank
    (left right : List (Option Bool)) :
    description.runConfig 1
        { state := 91
          tape := tapeAtCells left (none :: right) } =
      { state := 92
        tape := tapeAtCells (none :: left) right } := by
  cases right <;>
    simp [runConfig, stepConfig,
      (lookup_return_scans false).2.2.2.1,
      transition, tapeAtCells, Tape.read, Tape.write,
      Tape.move, Tape.moveRight]

private theorem step_return_92_blank
    (left right : List (Option Bool)) :
    description.runConfig 1
        { state := 92
          tape := tapeAtCells left (none :: right) } =
      { state := 92
        tape := tapeAtCells (none :: left) right } := by
  cases right <;>
    simp [runConfig, stepConfig,
      (lookup_return_scans false).2.2.2.2.1,
      transition, tapeAtCells, Tape.read, Tape.write,
      Tape.move, Tape.moveRight]

private theorem step_return_92_marker
    (left right : List (Option Bool)) :
    description.runConfig 1
        { state := 92
          tape := tapeAtCells left (some true :: right) } =
      { state := 93
        tape := Tape.move Direction.left
          (tapeAtCells left (some true :: right)) } := by
  cases right <;>
    simp [runConfig, stepConfig,
      (lookup_return_scans false).2.2.2.2.2.1,
      transition, tapeAtCells, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft]

private theorem step_return_93_blank
    (left right : List (Option Bool)) :
    description.runConfig 1
        { state := 93
          tape := tapeAtCells left (none :: right) } =
      { state := 1
        tape := tapeAtCells (none :: left) right } := by
  cases right <;>
    simp [runConfig, stepConfig,
      (lookup_return_scans false).2.2.2.2.2.2,
      transition, tapeAtCells, Tape.read, Tape.write,
      Tape.move, Tape.moveRight]

private theorem run_return_90_blanks
    (n : Nat) (left right : List (Option Bool)) :
    description.runConfig n
        { state := 90
          tape := tapeAtCells left
            (List.append (List.replicate n (none : Option Bool)) right) } =
      { state := 90
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
      rw [step_return_90_blank]
      rw [ih (none :: left)]
      rw [replicate_none_append_none_cons]
      rfl

private theorem run_return_91_present
    (bits : Word Bool) (left right : List (Option Bool)) :
    description.runConfig bits.length
        { state := 91
          tape := tapeAtCells left
            (List.append (bits.map some) right) } =
      { state := 91
        tape := tapeAtCells
          (List.append (bits.reverse.map some) left) right } := by
  induction bits generalizing left with
  | nil => simp [runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by simp; lia]
      rw [runConfig_add]
      change
        description.runConfig rest.length
            (description.runConfig 1
              { state := 91
                tape := tapeAtCells left
                  (some bit :: List.append (rest.map some) right) }) = _
      rw [step_return_91_present]
      rw [ih (some bit :: left)]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

private theorem run_return_92_blanks
    (n : Nat) (left right : List (Option Bool)) :
    description.runConfig n
        { state := 92
          tape := tapeAtCells left
            (List.append (List.replicate n (none : Option Bool)) right) } =
      { state := 92
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
      rw [step_return_92_blank]
      rw [ih (none :: left)]
      rw [replicate_none_append_none_cons]
      rfl

private theorem run_return_marker_bounce
    (left right : List (Option Bool)) :
    description.runConfig 2
        { state := 92
          tape := tapeAtCells (none :: left) (some true :: right) } =
      { state := 1
        tape := tapeAtCells (none :: left) (some true :: right) } := by
  rw [show 2 = 1 + 1 by rfl]
  rw [runConfig_add]
  rw [step_return_92_marker]
  change
    description.runConfig 1
        { state := 93
          tape := tapeAtCells left (none :: some true :: right) } = _
  rw [step_return_93_blank]

private def returnRight
    (h0 h1 h2 h3 : Bool) (gap : Nat)
    (present : Word Bool) (erased : Nat)
    (right : List (Option Bool)) : List (Option Bool) :=
  some h0 :: some h1 :: some h2 :: some h3 ::
    List.append (List.replicate gap (none : Option Bool))
      (some false ::
        List.append (present.map some)
          (List.append (List.replicate (erased + 1) none)
            (some true :: right)))

private def returnLeft
    (word : Word Bool) (h0 h1 h2 h3 : Bool) (gap : Nat)
    (present : Word Bool) (erased : Nat)
    (baseLeft : List (Option Bool)) : List (Option Bool) :=
  List.append (List.replicate (erased + 1) (none : Option Bool))
    (List.append (present.reverse.map some)
      (some false ::
        List.append (List.replicate gap none)
          (some h3 :: some h2 :: some h1 :: some h0 ::
            List.append (word.reverse.map some) baseLeft)))

theorem run_return_to_start
    (word : Word Bool) (hword : word ≠ [])
    (h0 h1 h2 h3 : Bool) (gap : Nat)
    (present : Word Bool) (erased : Nat)
    (baseLeft right : List (Option Bool)) :
    description.runConfig
        (5 + (gap + (1 +
          (present.length + (1 + (erased + 2))))))
        { state := 85
          tape := Tape.move Direction.left
            (tapeAtCells
              (List.append (word.reverse.map some) baseLeft)
              (returnRight h0 h1 h2 h3 gap present erased right)) } =
      { state := 1
        tape := tapeAtCells (returnLeft word h0 h1 h2 h3
          gap present erased baseLeft)
          (some true :: right) } := by
  unfold returnRight returnLeft
  rw [runConfig_add]
  rw [run_return_prefix word hword h0 h1 h2 h3 baseLeft]
  rw [runConfig_add]
  rw [run_return_90_blanks]
  rw [runConfig_add]
  rw [step_return_90_present false]
  rw [runConfig_add]
  rw [run_return_91_present]
  rw [runConfig_add]
  rw [show List.replicate (erased + 1) (none : Option Bool) =
    none :: List.replicate erased none by
      rw [show erased + 1 = Nat.succ erased by lia]
      rfl]
  rw [show
    List.append (none :: List.replicate erased (none : Option Bool))
        (some true :: right) =
      none :: List.append (List.replicate erased none)
        (some true :: right) by rfl]
  rw [step_return_91_blank]
  rw [runConfig_add]
  rw [run_return_92_blanks]
  rw [replicate_none_append_none_cons]
  rw [run_return_marker_bounce]
  rfl

end Execution

end GuardedEgress.MetadataTokenCopy
end FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore

import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.GuardedEgress.MetadataPrepend

namespace FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
namespace GuardedEgress.MetadataTokenCopy

open Languages MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace Execution

private def encodedTokenBits (kind : TokenKind) : Word Bool :=
  logicalCellListBits (kind.bits.map some)

private def encodedTokensBits : List TokenKind -> Word Bool
  | [] => []
  | kind :: rest =>
      List.append (encodedTokenBits kind)
        (encodedTokensBits rest)

private theorem encodedTokenCells_eq_map (kind : TokenKind) :
    encodedTokenCells kind = (encodedTokenBits kind).map some := by
  rfl

private theorem encodedTokens_eq_map (tokens : List TokenKind) :
    encodedTokens tokens = (encodedTokensBits tokens).map some := by
  induction tokens with
  | nil => rfl
  | cons kind rest ih =>
      simp [encodedTokensBits, encodedTokenCells_eq_map, ih,
        List.map_append]

@[simp] private theorem encodedTokenBits_length (kind : TokenKind) :
    (encodedTokenBits kind).length = 8 := by
  cases kind <;> rfl

@[simp] private theorem encodedTokensBits_length
    (tokens : List TokenKind) :
    (encodedTokensBits tokens).length = 8 * tokens.length := by
  induction tokens with
  | nil => rfl
  | cons kind rest ih =>
      simp [encodedTokensBits, ih]
      lia

private theorem encodedTokensBits_append
    (xs ys : List TokenKind) :
    encodedTokensBits (xs ++ ys) =
      List.append (encodedTokensBits xs)
        (encodedTokensBits ys) := by
  induction xs with
  | nil => rfl
  | cons kind rest ih =>
      simp [encodedTokensBits, ih, List.append_assoc]

private theorem encodedTokens_append
    (xs ys : List TokenKind) :
    encodedTokens (xs ++ ys) =
      List.append (encodedTokens xs) (encodedTokens ys) := by
  induction xs with
  | nil => rfl
  | cons kind rest ih =>
      simp [ih]

private theorem tokenBits_append
    (xs ys : List TokenKind) :
    tokenBits (xs ++ ys) =
      List.append (tokenBits xs) (tokenBits ys) := by
  induction xs with
  | nil => rfl
  | cons kind rest ih =>
      simp [ih]

private theorem run_decode_to_gap
    (kind : TokenKind) (pending : Word Bool) (hpending : pending ≠ [])
    (left right : List (Option Bool)) :
    description.runConfig (8 + (pending.length + 1))
        { state := 2
          tape := decodeSourceTape kind
            (List.append (pending.map some) (none :: left)) right } =
      { state := scanGapState kind
        tape := Tape.move Direction.left
          (tapeAtCells left
            (none ::
              List.append (pending.reverse.map some)
                (List.append (List.replicate 8 (none : Option Bool))
                  right))) } := by
  cases pending with
  | nil => contradiction
  | cons current rest =>
      rw [runConfig_add]
      simp only [List.map_cons]
      rw [show
        List.append (some current :: rest.map some) (none :: left) =
          some current :: List.append (rest.map some) (none :: left) by rfl]
      rw [run_decode_token kind current
        (List.append (rest.map some) (none :: left)) right]
      rw [show (current :: rest).length + 1 = rest.length + 2 by
        simp]
      rw [run_to_guard_present kind current rest left
        (List.append (List.replicate 8 (none : Option Bool)) right)]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

private theorem run_seek_decode_to_gap
    (kind : TokenKind) (n : Nat)
    (pending : Word Bool) (hpending : pending ≠ [])
    (left right : List (Option Bool)) :
    description.runConfig
        ((n + 1) + (8 + (pending.length + 1)))
        { state := description.start
          tape := tapeAtCells
            (List.append (List.replicate n (none : Option Bool))
              (List.append (encodedTokenCells kind).reverse
                (List.append (pending.map some) (none :: left))))
            (some true :: right) } =
      { state := scanGapState kind
        tape := Tape.move Direction.left
          (tapeAtCells left
            (none ::
              List.append (pending.reverse.map some)
                (List.append (List.replicate 8 (none : Option Bool))
                  (List.append (List.replicate n none)
                    (some true :: right))))) } := by
  cases hbits : (encodedTokenBits kind).reverse with
  | nil =>
      have hlength := congrArg List.length hbits
      simp at hlength
  | cons boundary rest =>
      have htoken :
          (encodedTokenCells kind).reverse =
            some boundary :: rest.map some := by
        rw [encodedTokenCells_eq_map]
        rw [← List.map_reverse]
        rw [hbits]
        rfl
      have hdecode :
          decodeSourceTape kind
              (List.append (pending.map some) (none :: left))
              (List.append (List.replicate n (none : Option Bool))
                (some true :: right)) =
            tapeAtCells
              (List.append (rest.map some)
                (List.append (pending.map some) (none :: left)))
              (some boundary ::
                List.append (List.replicate n (none : Option Bool))
                  (some true :: right)) := by
        simp [decodeSourceTape, htoken]
      rw [runConfig_add]
      rw [htoken]
      rw [show
        List.append (some boundary :: rest.map some)
            (List.append (pending.map some) (none :: left)) =
          some boundary ::
            List.append (rest.map some)
              (List.append (pending.map some) (none :: left)) by rfl]
      rw [run_seek_erased_suffix n boundary
        (List.append (rest.map some)
          (List.append (pending.map some) (none :: left))) right]
      rw [← hdecode]
      rw [run_decode_to_gap kind pending hpending left
        (List.append (List.replicate n (none : Option Bool))
          (some true :: right))]

private theorem run_return_explicit
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
              (some h0 :: some h1 :: some h2 :: some h3 ::
                List.append (List.replicate gap (none : Option Bool))
                  (some false ::
                    List.append (present.map some)
                      (List.append (List.replicate (erased + 1) none)
                        (some true :: right))))) } =
      { state := 1
        tape := tapeAtCells
          (List.append (List.replicate (erased + 1) (none : Option Bool))
            (List.append (present.reverse.map some)
              (some false ::
                List.append (List.replicate gap none)
                  (some h3 :: some h2 :: some h1 :: some h0 ::
                    List.append (word.reverse.map some) baseLeft))))
          (some true :: right) } := by
  exact run_return_to_start word hword h0 h1 h2 h3 gap present erased
    baseLeft right

private theorem run_prepend_exists
    (kind : TokenKind) (hit : Bool) (emitted : Word Bool)
    (baseLeft tail : List (Option Bool)) :
    exists steps : Nat,
      description.runConfig steps
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
  exact ⟨_, run_prepend kind hit emitted baseLeft tail⟩

private def cyclePriorWord
    (emitted : Word Bool) (processed : List TokenKind) : Word Bool :=
  List.append (tokenBits processed) emitted

private def cyclePendingWord (remaining : List TokenKind) : Word Bool :=
  List.append (encodedTokensBits remaining).reverse [false]

private def cycleNextBase
    (baseLeft : List (Option Bool)) (remaining : List TokenKind) :
    List (Option Bool) :=
  List.append
    (List.replicate (4 * remaining.length) (none : Option Bool))
    baseLeft

private def cyclePrependLeft
    (baseLeft : List (Option Bool)) (emitted : Word Bool)
    (remaining processed : List TokenKind) : List (Option Bool) :=
  List.append
    ((cyclePriorWord emitted processed).reverse.map some)
    (List.append (List.replicate 4 (none : Option Bool))
      (cycleNextBase baseLeft remaining))

private def cycleAfterGapLeft
    (baseLeft : List (Option Bool)) (emitted : Word Bool)
    (h0 h1 h2 h3 : Bool) (gap : Nat)
    (remaining processed : List TokenKind) : List (Option Bool) :=
  List.append (List.replicate gap (none : Option Bool))
    (some h3 :: some h2 :: some h1 :: some h0 ::
      cyclePrependLeft baseLeft emitted remaining processed)

private def cycleDecodedRight
    (remaining processed : List TokenKind)
    (right : List (Option Bool)) : List (Option Bool) :=
  List.append ((cyclePendingWord remaining).reverse.map some)
    (List.append (List.replicate 8 (none : Option Bool))
      (List.append
        (List.replicate (8 * processed.length + 1) none)
        (some true :: right)))

private theorem run_cycle_seek
    (baseLeft : List (Option Bool)) (emitted : Word Bool)
    (h0 h1 h2 h3 : Bool) (gap : Nat)
    (remaining processed : List TokenKind) (kind : TokenKind)
    (right : List (Option Bool)) :
    description.runConfig
        (((8 * processed.length + 1) + 1) +
          (8 + ((cyclePendingWord remaining).length + 1)))
        { state := description.start
          tape := loopTape baseLeft emitted [h0, h1, h2, h3]
            (gap + 1) (List.append remaining [kind]) processed right } =
      { state := scanGapState kind
        tape := Tape.move Direction.left
          (tapeAtCells
            (cycleAfterGapLeft baseLeft emitted h0 h1 h2 h3 gap
              remaining processed)
            (none :: cycleDecodedRight remaining processed right)) } := by
  have hpending : cyclePendingWord remaining ≠ [] := by
    intro hnil
    have hlength := congrArg List.length hnil
    simp [cyclePendingWord] at hlength
  have hscratch :
      List.replicate (4 * (remaining.length + 1))
          (none : Option Bool) =
        List.append (List.replicate 4 none)
          (List.replicate (4 * remaining.length) none) := by
    rw [show 4 * (remaining.length + 1) =
      4 + 4 * remaining.length by lia]
    exact (List.replicate_append_replicate
      (n := 4) (m := 4 * remaining.length)
      (a := (none : Option Bool))).symm
  have hgap :
      List.replicate (gap + 1) (none : Option Bool) =
        none :: List.replicate gap none := by
    rw [show gap + 1 = Nat.succ gap by lia]
    rfl
  have hrun := run_seek_decode_to_gap kind
    (8 * processed.length + 1) (cyclePendingWord remaining) hpending
    (cycleAfterGapLeft baseLeft emitted h0 h1 h2 h3 gap
      remaining processed) right
  simpa [loopTape, cyclePendingWord, cycleAfterGapLeft,
    cyclePrependLeft, cycleNextBase, cyclePriorWord,
    cycleDecodedRight, encodedTokens_append,
    encodedTokens_eq_map, encodedTokenCells_eq_map,
    encodedTokensBits_append, encodedTokensBits,
    List.reverse_append,
    List.map_reverse, List.map_append, List.append_assoc,
    hscratch, hgap] using hrun

private def cyclePrependRight
    (h0 h1 h2 h3 : Bool) (gap : Nat)
    (remaining processed : List TokenKind)
    (right : List (Option Bool)) : List (Option Bool) :=
  some h0 :: some h1 :: some h2 :: some h3 ::
    List.append (List.replicate gap (none : Option Bool))
      (none :: cycleDecodedRight remaining processed right)

private theorem run_cycle_gap
    (baseLeft : List (Option Bool)) (emitted : Word Bool)
    (h0 h1 h2 h3 : Bool) (gap : Nat)
    (remaining processed : List TokenKind) (kind : TokenKind)
    (right : List (Option Bool)) :
    description.runConfig (gap + 3)
        { state := scanGapState kind
          tape := Tape.move Direction.left
            (tapeAtCells
              (cycleAfterGapLeft baseLeft emitted h0 h1 h2 h3 gap
                remaining processed)
              (none :: cycleDecodedRight remaining processed right)) } =
      { state := prependStartState kind
        tape := tapeAtCells
          (cyclePrependLeft baseLeft emitted remaining processed)
          (cyclePrependRight h0 h1 h2 h3 gap
            remaining processed right) } := by
  exact run_gap_to_prepend_start kind gap h0 h1 h2 h3
    (cyclePrependLeft baseLeft emitted remaining processed)
    (cycleDecodedRight remaining processed right)

private def cycleCopiedWord
    (kind : TokenKind) (emitted : Word Bool)
    (processed : List TokenKind) : Word Bool :=
  List.append kind.bits (cyclePriorWord emitted processed)

private def cyclePrependedLeft
    (baseLeft : List (Option Bool)) (kind : TokenKind)
    (emitted : Word Bool) (remaining processed : List TokenKind) :
    List (Option Bool) :=
  List.append
    ((cycleCopiedWord kind emitted processed).reverse.map some)
    (cycleNextBase baseLeft remaining)

private theorem run_cycle_prepend
    (baseLeft : List (Option Bool)) (emitted : Word Bool)
    (h0 h1 h2 h3 : Bool) (gap : Nat)
    (remaining processed : List TokenKind) (kind : TokenKind)
    (right : List (Option Bool)) :
    exists steps : Nat,
      description.runConfig steps
          { state := prependStartState kind
            tape := tapeAtCells
              (cyclePrependLeft baseLeft emitted remaining processed)
              (cyclePrependRight h0 h1 h2 h3 gap
                remaining processed right) } =
        { state := 85
          tape := Tape.move Direction.left
            (tapeAtCells
              (cyclePrependedLeft baseLeft kind emitted
                remaining processed)
              (cyclePrependRight h0 h1 h2 h3 gap
                remaining processed right)) } := by
  let tail : List (Option Bool) :=
    some h1 :: some h2 :: some h3 ::
      List.append (List.replicate gap (none : Option Bool))
        (none :: cycleDecodedRight remaining processed right)
  rcases run_prepend_exists kind h0
      (cyclePriorWord emitted processed)
      (cycleNextBase baseLeft remaining) tail with
    ⟨steps, hrun⟩
  refine ⟨steps, ?_⟩
  simpa [cyclePrependLeft, cyclePrependRight,
    cyclePrependedLeft, cycleCopiedWord, tail] using hrun

private theorem run_cycle_return
    (baseLeft : List (Option Bool)) (emitted : Word Bool)
    (h0 h1 h2 h3 : Bool) (gap : Nat)
    (remaining processed : List TokenKind) (kind : TokenKind)
    (right : List (Option Bool)) :
    exists steps : Nat,
      description.runConfig steps
          { state := 85
            tape := Tape.move Direction.left
              (tapeAtCells
                (cyclePrependedLeft baseLeft kind emitted
                  remaining processed)
                (cyclePrependRight h0 h1 h2 h3 gap
                  remaining processed right)) } =
        { state := description.start
          tape := loopTape baseLeft emitted [h0, h1, h2, h3]
            (gap + 1) remaining (kind :: processed) right } := by
  have hword : cycleCopiedWord kind emitted processed ≠ [] := by
    cases kind <;>
      simp [cycleCopiedWord, cyclePriorWord, TokenKind.bits]
  have herased :
      List.append (List.replicate 8 (none : Option Bool))
          (List.replicate (8 * processed.length + 1) none) =
        List.replicate (8 * (processed.length + 1) + 1) none := by
    calc
      _ = List.replicate (8 + (8 * processed.length + 1)) none :=
        List.replicate_append_replicate
      _ = List.replicate (8 * (processed.length + 1) + 1) none := by
        congr 1
        lia
  have hrun := run_return_explicit
    (cycleCopiedWord kind emitted processed) hword
    h0 h1 h2 h3 (gap + 1)
    (encodedTokensBits remaining)
    (8 * (processed.length + 1))
    (cycleNextBase baseLeft remaining) right
  have hpendingReverse :
      (cyclePendingWord remaining).reverse =
        false :: encodedTokensBits remaining := by
    simp [cyclePendingWord]
  have hblankTail :
      List.append (List.replicate 8 (none : Option Bool))
          (List.append (List.replicate (8 * processed.length + 1) none)
            (some true :: right)) =
        List.append
          (List.replicate (8 * (processed.length + 1) + 1) none)
          (some true :: right) := by
    calc
      _ = List.append
          (List.append (List.replicate 8 (none : Option Bool))
            (List.replicate (8 * processed.length + 1) none))
          (some true :: right) :=
        (List.append_assoc _ _ _).symm
      _ = _ := by rw [herased]
  have hdecoded :
      cycleDecodedRight remaining processed right =
        some false ::
          List.append ((encodedTokensBits remaining).map some)
            (List.append
              (List.replicate (8 * (processed.length + 1) + 1) none)
              (some true :: right)) := by
    unfold cycleDecodedRight
    rw [hpendingReverse]
    rw [show
      (false :: encodedTokensBits remaining).map some =
        some false :: (encodedTokensBits remaining).map some by rfl]
    rw [show
      List.append
          (some false :: (encodedTokensBits remaining).map some)
          (List.append (List.replicate 8 (none : Option Bool))
            (List.append
              (List.replicate (8 * processed.length + 1) none)
              (some true :: right))) =
        some false ::
          List.append ((encodedTokensBits remaining).map some)
            (List.append (List.replicate 8 none)
              (List.append
                (List.replicate (8 * processed.length + 1) none)
                (some true :: right))) by rfl]
    rw [hblankTail]
  have hright :
      cyclePrependRight h0 h1 h2 h3 gap remaining processed right =
        some h0 :: some h1 :: some h2 :: some h3 ::
          List.append (List.replicate (gap + 1) (none : Option Bool))
            (some false ::
              List.append ((encodedTokensBits remaining).map some)
                (List.append
                  (List.replicate
                    (8 * (processed.length + 1) + 1) none)
                  (some true :: right))) := by
    unfold cyclePrependRight
    rw [hdecoded]
    rw [replicate_none_append_none_cons]
    rw [show gap + 1 = Nat.succ gap by lia]
    rfl
  refine ⟨5 + ((gap + 1) + (1 +
    ((encodedTokensBits remaining).length +
      (1 + (8 * (processed.length + 1) + 2))))), ?_⟩
  simpa [loopTape, cyclePrependedLeft, cycleCopiedWord,
    cyclePriorWord, cycleNextBase, encodedTokens_eq_map,
    tokenBits_cons, List.reverse_append, List.map_reverse,
    List.map_append, List.append_assoc, hright, description] using hrun

private theorem run_cycle
    (baseLeft : List (Option Bool)) (emitted : Word Bool)
    (h0 h1 h2 h3 : Bool) (gap : Nat)
    (remaining processed : List TokenKind) (kind : TokenKind)
    (right : List (Option Bool)) :
    exists steps : Nat,
      description.runConfig steps
          { state := description.start
            tape := loopTape baseLeft emitted [h0, h1, h2, h3]
              (gap + 1) (List.append remaining [kind]) processed right } =
        { state := description.start
          tape := loopTape baseLeft emitted [h0, h1, h2, h3]
            (gap + 1) remaining (kind :: processed) right } := by
  let seekSteps : Nat :=
    ((8 * processed.length + 1) + 1) +
      (8 + ((cyclePendingWord remaining).length + 1))
  have hseek := run_cycle_seek baseLeft emitted h0 h1 h2 h3 gap
    remaining processed kind right
  have hgap := run_cycle_gap baseLeft emitted h0 h1 h2 h3 gap
    remaining processed kind right
  rcases run_cycle_prepend baseLeft emitted h0 h1 h2 h3 gap
      remaining processed kind right with
    ⟨prependSteps, hprepend⟩
  rcases run_cycle_return baseLeft emitted h0 h1 h2 h3 gap
      remaining processed kind right with
    ⟨returnSteps, hreturn⟩
  refine ⟨seekSteps + ((gap + 3) + (prependSteps + returnSteps)), ?_⟩
  unfold seekSteps
  rw [runConfig_add]
  rw [hseek]
  rw [runConfig_add]
  rw [hgap]
  rw [runConfig_add]
  rw [hprepend]
  rw [hreturn]

private theorem run_cycles_rev
    (baseLeft : List (Option Bool)) (emitted : Word Bool)
    (h0 h1 h2 h3 : Bool) (gap : Nat)
    (rev processed : List TokenKind)
    (right : List (Option Bool)) :
    exists steps : Nat,
      description.runConfig steps
          { state := description.start
            tape := loopTape baseLeft emitted [h0, h1, h2, h3]
              (gap + 1) rev.reverse processed right } =
        { state := description.start
          tape := loopTape baseLeft emitted [h0, h1, h2, h3]
            (gap + 1) [] (List.append rev.reverse processed) right } := by
  induction rev generalizing processed with
  | nil =>
      refine ⟨0, ?_⟩
      simp [runConfig]
  | cons kind rest ih =>
      rcases run_cycle baseLeft emitted h0 h1 h2 h3 gap
          rest.reverse processed kind right with
        ⟨firstSteps, hfirst⟩
      rcases ih (kind :: processed) with ⟨restSteps, hrest⟩
      have hreverse :
          (kind :: rest).reverse =
            List.append rest.reverse [kind] := by
        rw [List.reverse_cons]
        change List.append rest.reverse [kind] =
          List.append rest.reverse [kind]
        rfl
      have hfirst' :
          description.runConfig firstSteps
              { state := description.start
                tape := loopTape baseLeft emitted [h0, h1, h2, h3]
                  (gap + 1) (kind :: rest).reverse processed right } =
            { state := description.start
              tape := loopTape baseLeft emitted [h0, h1, h2, h3]
                (gap + 1) rest.reverse (kind :: processed) right } := by
        rw [hreverse]
        exact hfirst
      refine ⟨firstSteps + restSteps, ?_⟩
      rw [runConfig_add]
      rw [hfirst']
      rw [hrest]
      simp [List.reverse_cons, List.append_assoc]

theorem run_cycles
    (baseLeft : List (Option Bool)) (emitted : Word Bool)
    (h0 h1 h2 h3 : Bool) (gap : Nat)
    (remaining processed : List TokenKind)
    (right : List (Option Bool)) :
    exists steps : Nat,
      description.runConfig steps
          { state := description.start
            tape := loopTape baseLeft emitted [h0, h1, h2, h3]
              (gap + 1) remaining processed right } =
        { state := description.start
          tape := loopTape baseLeft emitted [h0, h1, h2, h3]
            (gap + 1) [] (List.append remaining processed) right } := by
  simpa using run_cycles_rev baseLeft emitted h0 h1 h2 h3 gap
    remaining.reverse processed right

end Execution

end GuardedEgress.MetadataTokenCopy
end FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
